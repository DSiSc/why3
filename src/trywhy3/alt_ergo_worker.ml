open Format
open Worker_proto

module SAT = (val (Sat_solvers.get_current ()) : Sat_solvers.S)
module FE = Frontend.Make (SAT)

let print_status fmt _d status steps =
  match status with
  | FE.Unsat _dep ->
    fprintf fmt "Proved (%Ld steps)" steps
  | FE.Inconsistent -> ()
    (* fprintf fmt "Inconsistent assumption" *)
  | FE.Unknown _t | FE.Sat _t ->
      fprintf fmt "Unknown (%Ld steps)@." steps


let report_status report _d status _steps =
  match status with
  | FE.Unsat _dep -> report Valid
  | FE.Inconsistent -> ()
  | FE.Unknown _t | FE.Sat _t -> report (Unknown "unknown")

let run_alt_ergo_on_task text =
  let lb = Lexing.from_string text in
(* from Alt-Ergo, src/main/frontend.ml *)
  let a = Why_parser.file Why_lexer.token lb in
  Parsing.clear_parser ();
  let ltd, _typ_env = Why_typing.file false Why_typing.empty_env a in
  match Why_typing.split_goals ltd with
  | [d] ->
    let d = Cnf.make (List.map (fun (f, _env) -> f, true) d) in
    SAT.reset_steps ();
    let stat = ref (Invalid "no answer from Alt-Ergo") in
    let f s = stat := s in
    begin
      try
        let _x = Queue.fold (FE.process_decl (report_status f))
          (SAT.empty (), true, Explanation.empty) d
        in
        !stat
      with Sat_solvers.StepsLimitReached -> Unknown "steps limit reached"
    end
  | _ -> Invalid "zero or more than 1 goal to solve"




let () =
  Options.set_steps_bound 100;
  Worker.set_onmessage (fun msg ->
			let (id, text) = unmarshal msg in
			let result = run_alt_ergo_on_task text in
			Worker.post_message (marshal (id,result)))