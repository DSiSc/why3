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

  let inter_mlw = ref false

  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }

  let backtrack lexbuf =
    lexbuf.lex_curr_pos <- lexbuf.lex_start_pos;
    lexbuf.lex_curr_p <- lexbuf.lex_start_p

  let get_loc lb =
    Loc.extract (Lexing.lexeme_start_p lb, Lexing.lexeme_end_p lb)

  let print_sharp lb fmt =
    let loc = get_loc lb in
    let (f, line, _, _) = Loc.get loc in
    fprintf fmt "## %S %d %d ##" f line 0

}

let space = [' ' '\t']

let begin_why3 = "\\begin{why3}"
let end_why3   = "\\end{why3}"
let begin_wtex = "\\begin{why3tex}"
let end_wtex   = "\\end{why3tex}"
let begin_mlw  = "\\begin{why3mlw}"
let end_mlw    = "\\end{why3mlw}"

rule scan tex mlw = parse
  | '\n'       { newline lexbuf;
                 pp_print_newline tex ();
                 scan tex mlw lexbuf }
  | begin_why3 { pp_print_string tex "\\begin{why3}";
                 print_sharp lexbuf mlw;
                 print_why3 tex mlw lexbuf;
                 scan tex mlw lexbuf }
  | begin_wtex { pp_print_string tex "\\begin{why3}";
                 print_tex tex lexbuf;
                 scan tex mlw lexbuf }
  | begin_mlw  { print_sharp lexbuf mlw;
                 print_mlw mlw lexbuf;
                 scan tex mlw lexbuf }
  | eof        { () }
  | _ as s     { pp_print_char tex s;
                 scan tex mlw lexbuf }

and print_why3 tex mlw = parse
  | '\n'       { newline lexbuf;
                 List.iter (fun fmt -> pp_print_newline fmt ())
                           [tex; mlw];
                 print_why3 tex mlw lexbuf }
  | begin_mlw  { print_sharp lexbuf mlw;
                 print_mlw mlw lexbuf;
                 print_why3 tex mlw lexbuf }
  | begin_wtex { pp_print_string tex "*?";
                 print_escape tex lexbuf;
                 print_why3 tex mlw lexbuf }
  | end_why3   { pp_print_string tex "\\end{why3}" }
  | eof        { () }
  | _ as c     { List.iter (fun fmt -> pp_print_char fmt c)
                           [tex; mlw];
                 print_why3 tex mlw lexbuf }

and print_mlw mlw = parse
  | '\n'       { newline lexbuf;
                 pp_print_newline mlw ();
                 print_mlw mlw lexbuf }
  | end_mlw space* '\n'?
               { newline lexbuf }
  | eof        { () }
  | _ as c     { pp_print_char mlw c;
                 print_mlw mlw lexbuf }

and print_tex tex = parse
  | '\n'       { newline lexbuf;
                 pp_print_newline tex ();
                 print_tex tex lexbuf }
  | end_wtex   { pp_print_string tex "\\end{why3}" }
  | eof        { () }
  | _ as c     { pp_print_char tex c;
                 print_tex tex lexbuf }

and print_escape tex = parse
  | '\n'       { newline lexbuf;
                 pp_print_newline tex ();
                 print_escape tex lexbuf }
  | end_wtex   { pp_print_string tex "?*" }
  | eof        { () }
  | _ as c     { pp_print_char tex c;
                 print_escape tex lexbuf }
(* and print_code tex mlw is_tex is_mlw = parse *)
(*   | '\n'       { newline lexbuf; *)
(*                  if is_tex && not !inter_mlw then pp_print_newline tex (); *)
(*                  if is_mlw then pp_print_newline mlw (); *)
(*                  print_code tex mlw is_tex is_mlw lexbuf } *)
(*   | end_why3   { inter_mlw := false; *)
(*                  pp_print_string tex "\\end{why3}" } *)
(* (\* TODO: use [is_code] to check if we are in a [code] or [spec] section *\) *)
(*   | end_wtex   { pp_print_string tex "\\end{why3}" } *)
(*   | end_mlw    { if !inter_mlw then *)
(*                    print_code tex mlw true true lexbuf } *)
(*   | begin_mlw  { if !inter_mlw then begin *)
(*                      print_sharp lexbuf mlw; *)
(*                      print_code tex mlw false true lexbuf; *)
(*                    end *)
(*                  else () (\* TODO: raise an exception *\) } *)
(*   | eof        { () } *)
(*   | _ as s     { if is_tex then pp_print_char tex s; *)
(*                  if is_mlw then pp_print_char mlw s; *)
(*                  print_code tex mlw is_tex is_mlw lexbuf } *)

{

  let do_file tex mlw fname =
    (* current_file := fname; *)
    (* input *)
    let cin = open_in fname in
    let lb = Lexing.from_channel cin in
    lb.Lexing.lex_curr_p <-
      { lb.Lexing.lex_curr_p with Lexing.pos_fname = fname };
    (* output *)
    scan tex mlw lb;
    close_in cin

}

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3literate.opt"
End:
*)
