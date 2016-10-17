(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2016   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Why3

let () = Debug.set_flag Glob.flag

(* command line parsing *)

let spec = []

let usage_msg = sprintf
  "Usage: %s [options...] [files...]"
  (Filename.basename Sys.argv.(0))

let usage = fun () ->
  Arg.usage spec usage_msg; exit 1

let fname = ref None

let set_file f = match !fname with
  | None when Filename.check_suffix f ".lmlw" -> fname := Some f
  | _ -> usage ()

let () =
  Arg.parse spec set_file usage_msg

let fname = match !fname with
  | None -> usage ()
  | Some f -> f

let print_position fmt (bpos, epos) =
  let b = bpos.Lexing.pos_cnum - bpos.Lexing.pos_bol in
  let e = epos.Lexing.pos_cnum - epos.Lexing.pos_bol in
  fprintf fmt "File %S, line %d, characters %d-%d:" fname bpos.Lexing.pos_lnum b e

let () =
  let fmt1_name = (Filename.chop_extension fname ^ ".tex") in
  let fmt2_name = (Filename.chop_extension fname ^ ".mlw") in
  let c1 = open_out fmt1_name in
  let c2 = open_out fmt2_name in
  let fmt1 = formatter_of_out_channel c1 in
  let fmt2 = formatter_of_out_channel c2 in
  Literate_lexer.do_file fmt1 fmt2 fname;
  fprintf fmt1 "@.";
  fprintf fmt2 "@.";
  close_out c1;
  close_out c2


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3literate.opt"
End:
*)
