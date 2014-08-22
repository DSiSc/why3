(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Why3
open Stdlib
open Theory

let usage_msg = sprintf
  "Usage: %s [options] -D <driver> -o <dir> [[file|-] [-T <theory>]...]..."
  (Filename.basename Sys.argv.(0))

let opt_queue = Queue.create ()

let opt_input = ref None

let add_opt_file x =
  let tlist = Queue.create () in
  Queue.push (Some x, tlist) opt_queue;
  opt_input := Some tlist

let add_opt_theory x =
  let l = Strings.split '.' x in
  let p, t = match List.rev l with
    | t::p -> List.rev p, t
    | _ -> assert false
  in
  match !opt_input, p with
  | None, [] ->
      eprintf "Option '-T'/'--theory' with a non-qualified \
        argument requires an input file.@.";
      exit 1
  | Some tlist, [] ->
      Queue.push (x, p, t) tlist
  | _ ->
      let tlist = Queue.create () in
      Queue.push (None, tlist) opt_queue;
      opt_input := None;
      Queue.push (x, p, t) tlist

let opt_parser = ref None
let opt_driver = ref None
let opt_output = ref None

let option_list = [
  "-", Arg.Unit (fun () -> add_opt_file "-"),
      " read the input file from stdin";
  "-T", Arg.String add_opt_theory,
      "<theory> select <theory> in the input file or in the library";
  "--backend-c", Arg.Unit (fun () -> Mlw_backends.Switch.(set C)),
      " enables the C backend. WhyML will preduce a C program instead \
       of an OCaml one";
  "--theory", Arg.String add_opt_theory,
      " same as -T";
  "-F", Arg.String (fun s -> opt_parser := Some s),
      "<format> select input format (default: \"why\")";
  "--format", Arg.String (fun s -> opt_parser := Some s),
      " same as -F";
  "-D", Arg.String (fun s -> opt_driver := Some s),
      "<file> specify a driver";
  "--driver", Arg.String (fun s -> opt_driver := Some s),
      " same as -D";
  "-o", Arg.String (fun s -> opt_output := Some s),
      "<dir> print the selected goals to separate files in <dir>";
  "--output", Arg.String (fun s -> opt_output := Some s),
      " same as -o" ]

let config, _, env =
  Whyconf.Args.initialize option_list add_opt_file usage_msg

let () =
  if Queue.is_empty opt_queue then
    Whyconf.Args.exit_with_usage option_list usage_msg

let opt_output =
  match !opt_output with
  | None ->
    eprintf "Output directory (-o) is required.@.";
    exit 1
  | Some d -> d

let opt_driver =
  match !opt_driver with
  | None ->
    eprintf "Driver (-D) is required.@.";
    exit 1
  | Some s ->
    let s =
      if Sys.file_exists s || String.contains s '/' || String.contains s '.' then s
      else Filename.concat Config.datadir (Filename.concat "drivers" (s ^ ".drv")) in
    let lib = Mlw_main.library_of_env env in
    Mlw_driver.load_driver lib s []

let extract_to ?fname th extract =
  let file = Filename.concat opt_output (Mlw_ocaml.extract_filename ?fname th) in
  let old =
    if Sys.file_exists file then begin
      let backup = file ^ ".bak" in
      Sys.rename file backup;
      Some (open_in backup)
    end else None in
  let cout = open_out file in
  extract file ?old (formatter_of_out_channel cout);
  close_out cout

let extract_to =
  let visited = Ident.Hid.create 17 in
  fun ?fname th extract ->
    if not (Ident.Hid.mem visited th.th_name) then begin
      Ident.Hid.add visited th.th_name ();
      extract_to ?fname th extract
    end

let extract_to_c ~fname th =
  let file = Filename.concat opt_output (Mlw_c.extract_filename ?fname th) in
  let old =
    if Sys.file_exists file then begin
      let backup = file ^ ".bak" in
      Sys.rename file backup;
      Some (open_in backup)
    end else None in
  let cout = open_out file in
  let fmt = formatter_of_out_channel cout in
  fun ?fname:_ _ extract ->
    extract file ?old fmt cout

let extract_to_c =
  let visited = Ident.Hid.create 17 in
  fun ~fname th ->
    let extract_to = extract_to_c ~fname th in
    fun ?fname th extract ->
      if not (Ident.Hid.mem visited th.th_name) then begin
        Ident.Hid.add visited th.th_name ();
        extract_to ?fname th extract;
      end

let use_iter f th =
  List.iter (fun d -> match d.td_node with Use t -> f t | _ -> ()) th.th_decls

let rec do_extract_theory ~extract_to ?fname th =
  let extract_use th' =
    let fname = if th'.th_path = [] then fname else None in
    do_extract_theory ~extract_to ?fname th' in
  use_iter extract_use th;
  let extract file ?old fmt cout =
    let tname = th.th_name.Ident.id_string in
    Debug.dprintf Mlw_backends.debug "extract theory %s to file %s@." tname file;
    Mlw_backends.extract_theory opt_driver ?old ?fname fmt cout th
  in
  extract_to ?fname th extract

let rec do_extract_module ~extract_to ?fname m =
  let extract_use th' =
    let fname = if th'.th_path = [] then fname else None in
    match
      try Some (Mlw_module.restore_module th') with Not_found -> None
    with
      | Some m' -> do_extract_module ~extract_to ?fname m'
      | None    -> do_extract_theory ~extract_to ?fname th' in
  use_iter extract_use m.Mlw_module.mod_theory;
  let extract file ?old fmt cout =
    let tname = m.Mlw_module.mod_theory.th_name.Ident.id_string in
    Debug.dprintf Mlw_backends.debug "extract module %s to file %s@." tname file;
    Mlw_backends.extract_module opt_driver ?old ?fname fmt cout m
  in
  extract_to ?fname m.Mlw_module.mod_theory extract

let do_extract_theory ?fname th =
  let extract_to =
    match Mlw_backends.Switch.get () with
    | Mlw_backends.Switch.C -> extract_to_c ~fname th
    | Mlw_backends.Switch.OCaml -> extract_to
  in
  do_extract_theory ~extract_to ?fname th;
  Mlw_backends.finalize ()

let do_extract_module ?fname m =
  let extract_to =
    match Mlw_backends.Switch.get () with
    | Mlw_backends.Switch.C -> extract_to_c ~fname m.Mlw_module.mod_theory
    | Mlw_backends.Switch.OCaml -> extract_to
  in
  do_extract_module ~extract_to ?fname m;
  Mlw_backends.finalize ()

let do_global_extract (tname,p,t) =
  let lib = opt_driver.Mlw_driver.drv_lib in
  try
    let mm, thm = Env.read_lib_file lib p in
    try
      let m = Mstr.find t mm in
      do_extract_module m
    with Not_found ->
      let th = Mstr.find t thm in
      do_extract_theory th
  with Env.LibFileNotFound _ | Not_found -> try
    let format = Opt.get_def "why" !opt_parser in
    let env = Env.env_of_library lib in
    let th = Env.read_theory ~format env p t in
    do_extract_theory th
  with Env.LibFileNotFound _ | Env.TheoryNotFound _ ->
    eprintf "Theory/module '%s' not found.@." tname;
    exit 1

let do_extract_theory_from fname m (tname,_,t) =
  let th = try Mstr.find t m with Not_found ->
    eprintf "Theory '%s' not found in file '%s'.@." tname fname;
    exit 1
  in
  do_extract_theory ~fname th

let do_extract_module_from fname mm thm (tname,_,t) =
  try
    let m = Mstr.find t mm in do_extract_module ~fname m
  with Not_found -> try
    let th = Mstr.find t thm in do_extract_theory ~fname th
  with Not_found ->
    eprintf "Theory/module '%s' not found in file '%s'.@." tname fname;
    exit 1

let do_local_extract fname cin tlist =
  let lib = opt_driver.Mlw_driver.drv_lib in
  if !opt_parser = Some "whyml" || Filename.check_suffix fname ".mlw" then begin
    let mm, thm = Mlw_main.read_channel lib [] fname cin in
    if Queue.is_empty tlist then begin
      let do_m t m thm =
        do_extract_module ~fname m; Mstr.remove t thm in
      let thm = Mstr.fold do_m mm thm in
      Mstr.iter (fun _ th -> do_extract_theory ~fname th) thm
    end else
      Queue.iter (do_extract_module_from fname mm thm) tlist
  end else begin
    let m = Env.read_channel ?format:!opt_parser env fname cin in
    if Queue.is_empty tlist then
      let add_th t th mi = Ident.Mid.add th.th_name (t,th) mi in
      let do_th _ (_,th) = do_extract_theory ~fname th in
      Ident.Mid.iter do_th (Mstr.fold add_th m Ident.Mid.empty)
    else
      Queue.iter (do_extract_theory_from fname m) tlist
  end

let do_input = function
  | None, tlist ->
    Queue.iter do_global_extract tlist
  | Some f, tlist ->
    let fname, cin = match f with
      | "-" -> "stdin", stdin
      | f   -> f, open_in f in
    do_local_extract fname cin tlist;
    close_in cin

let () =
  try
    Queue.iter do_input opt_queue;
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
