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

{

  open Format
  open Lexing
  open Why3

  let output_comments = ref true

  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }

  let backtrack lexbuf =
    lexbuf.lex_curr_pos <- lexbuf.lex_start_pos;
    lexbuf.lex_curr_p <- lexbuf.lex_start_p

  let get_loc lb =
    Loc.extract (Lexing.lexeme_start_p lb, Lexing.lexeme_end_p lb)

}

let space = [' ' '\t']

let begin_code = "\\begin{code}"
let end_code   = "\\end{code}"
let begin_spec = "\\begin{spec}"
let end_spec   = "\\end{spec}"

rule scan fmt1 fmt2 = parse
  | begin_code { pp_print_string fmt1 "\\begin{why3}";
                 print_code fmt1 fmt2 true lexbuf;
                 scan fmt1 fmt2 lexbuf }
  | begin_spec { pp_print_string fmt1 "\\begin{why3}";
                 print_code fmt1 fmt2 false lexbuf;
                 scan fmt1 fmt2 lexbuf }
  | eof { () }
  | _ as s     { pp_print_char fmt1 s;
                 scan fmt1 fmt2 lexbuf }

and print_code fmt1 fmt2 is_code = parse
  | space* "\n"? end_code { pp_print_string fmt1 "\\end{why3}" }
(* TODO: use [is_code] to check if we are in a [code] or [spec] section *)
  | space* "\n"? end_spec { pp_print_string fmt1 "\\end{why3}" }
  | eof { () }
  | _ as s     { pp_print_char fmt1 s;
                 if is_code then pp_print_char fmt2 s;
                 print_code fmt1 fmt2 is_code lexbuf }

{

  let do_file fmt1 fmt2 fname =
    (* current_file := fname; *)
    (* input *)
    let cin = open_in fname in
    let lb = Lexing.from_channel cin in
    lb.Lexing.lex_curr_p <-
      { lb.Lexing.lex_curr_p with Lexing.pos_fname = fname };
    (* output *)
    scan fmt1 fmt2 lb;
    close_in cin

}

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3literate.opt"
End:
*)
