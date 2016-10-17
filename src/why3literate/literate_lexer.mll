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

(* Why3 to HTML *)

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

  let make_table l =
    let ht = Hashtbl.create 97 in
    List.iter (fun s -> Hashtbl.add ht s ()) l;
    Hashtbl.mem ht

  let is_keyword1 = make_table [ "as"; "axiom"; "clone"; "coinductive";
    "constant"; "else"; "end"; "epsilon"; "exists"; "export"; "false";
    "forall"; "function"; "goal"; "if"; "import"; "in"; "inductive";
    "lemma"; "let"; "match"; "meta"; "not"; "predicate"; "prop";
    "scope"; "then"; "theory"; "true"; "type"; "use"; "with";
    (* programs *) "abstract"; "any";
    "begin"; "do"; "done"; "downto"; "exception";
    "for"; "fun"; "ghost"; "loop"; "model"; "module";
    "mutable"; "private"; "raise"; "rec";
    "to"; "try"; "val"; "while"; ]

  let is_keyword2 = make_table [ "absurd"; "assert"; "assume";
    "ensures"; "check"; "invariant"; "raises"; "reads"; "requires";
    "returns"; "variant"; "writes"; "diverges"; ]

  let get_loc lb =
    Loc.extract (Lexing.lexeme_start_p lb, Lexing.lexeme_end_p lb)

  (* let current_file = ref "" *)

  (* let print_ident fmt lexbuf s = *)
  (*   if is_keyword1 s then *)
  (*     fprintf fmt "<span class=\"keyword1\">%s</span>" s *)
  (*   else if is_keyword2 s then *)
  (*     fprintf fmt "<span class=\"keyword2\">%s</span>" s *)
  (*   else begin *)
  (*     let (\* f,l,c as *\) loc = get_loc lexbuf in *)
  (*     (\* Format.eprintf "  IDENT %s/%d/%d@." f l c; *\) *)
  (*     (\* is this a def point? *\) *)
  (*     try *)
  (*       let id, def = Glob.find loc in *)
  (*       match id.Ident.id_loc with *)
  (*       | None -> raise Not_found *)
  (*       | Some _ -> *)
  (*         match def with *)
  (*         | Glob.Def -> *)
  (*           fprintf fmt "<a name=\"%a\">%a</a>" *)
  (*             Doc_def.pp_anchor id Pp.html_string s *)
  (*         | Glob.Use -> *)
  (*           fprintf fmt "<a href=\"%a\">%a</a>" *)
  (*             Doc_def.pp_locate id Pp.html_string s *)
  (*     with Not_found -> *)
  (*       (\* otherwise, just print it *\) *)
  (*       pp_print_string fmt s *)
  (*   end *)

  (* type empty_line = PrevEmpty | CurrEmpty | NotEmpty *)

}

let op_char_1 = ['=' '<' '>' '~']
let op_char_2 = ['+' '-']
let op_char_3 = ['*' '/' '%']
let op_char_4 = ['!' '$' '&' '?' '@' '^' '.' ':' '|' '#']
let op_char_34 = op_char_3 | op_char_4
let op_char_234 = op_char_2 | op_char_34
let op_char_1234 = op_char_1 | op_char_234
let op_char_pref = ['!' '?']
let prefix_op =
    op_char_1234* op_char_1 op_char_1234*
  | op_char_234*  op_char_2 op_char_234*
  | op_char_34* op_char_3 op_char_34*
  | op_char_4+
let operator =
    op_char_pref op_char_4*
  | prefix_op
  | prefix_op '_'
  | "[]"
  | "[<-]"
  | "[]<-"

let space = [' ' '\t']
let ident = ['A'-'Z' 'a'-'z' '_'] ['A'-'Z' 'a'-'z' '0'-'9' '_']* | operator
let special = ['\'' '"' '<' '>' '&']

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
  | "'\"'"
  | _ as s     { pp_print_string fmt1 s;
                 scan fmt1 fmt2 lexbuf }

and print_code fmt1 fmt2 is_code = parse
  | end_code { pp_print_string fmt1 "\\end{why3}" }
(* TODO: use [is_code] to check if we are in a [code] or [spec] section *)
  | end_spec { pp_print_string fmt1 "\\end{why3}" }
  | eof { () }
  | "'\"'"
  | _ as s     { pp_print_string fmt1 s;
                 if is_code then pp_print_string fmt2 s;
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
