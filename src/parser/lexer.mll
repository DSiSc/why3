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
  open Parser

  exception IllegalCharacter of char

  let () = Exn_printer.register (fun fmt e -> match e with
    | IllegalCharacter c -> fprintf fmt "illegal character %c" c
    | _ -> raise e)

  let keywords = Hashtbl.create 97
  let () =
    List.iter
      (fun (x,y) -> Hashtbl.add keywords x y)
      [
        "as", AS;
        "axiom", AXIOM;
        "by", BY;
        "clone", CLONE;
        "coinductive", COINDUCTIVE;
        "constant", CONSTANT;
        "else", ELSE;
        "end", END;
        "epsilon", EPSILON;
        "exists", EXISTS;
        "export", EXPORT;
        "false", FALSE;
        "forall", FORALL;
        "function", FUNCTION;
        "goal", GOAL;
        "if", IF;
        "import", IMPORT;
        "in", IN;
        "inductive", INDUCTIVE;
        "lemma", LEMMA;
        "let", LET;
        "match", MATCH;
        "meta", META;
        "not", NOT;
        "predicate", PREDICATE;
        "scope", SCOPE;
        "so", SO;
        "then", THEN;
        "theory", THEORY;
        "true", TRUE;
        "type", TYPE;
        "use", USE;
        "with", WITH;
        (* programs *)
        "abstract", ABSTRACT;
        "absurd", ABSURD;
        "alias", ALIAS;
        "any", ANY;
        "assert", ASSERT;
        "assume", ASSUME;
        "at", AT;
        "begin", BEGIN;
        "check", CHECK;
        "diverges", DIVERGES;
        "do", DO;
        "done", DONE;
        "downto", DOWNTO;
        "ensures", ENSURES;
        "exception", EXCEPTION;
        "for", FOR;
        "fun", FUN;
        "ghost", GHOST;
        "invariant", INVARIANT;
        "label", LABEL;
        "module", MODULE;
        "mutable", MUTABLE;
        "old", OLD;
        "private", PRIVATE;
        "raise", RAISE;
        "raises", RAISES;
        "reads", READS;
        "rec", REC;
        "requires", REQUIRES;
        "returns", RETURNS;
        "to", TO;
        "try", TRY;
        "val", VAL;
        "variant", VARIANT;
        "while", WHILE;
        "writes", WRITES;
      ]
}

let space = [' ' '\t' '\r']
let lalpha = ['a'-'z' '_']
let ualpha = ['A'-'Z']
let alpha = lalpha | ualpha
let digit = ['0'-'9']
let lident = lalpha (alpha | digit | '\'')*
let uident = ualpha (alpha | digit | '\'')*
let hexadigit = ['0'-'9' 'a'-'f' 'A'-'F']

let op_char_1 = ['=' '<' '>' '~']
let op_char_2 = ['+' '-']
let op_char_3 = ['*' '/' '\\' '%']
let op_char_4 = ['!' '$' '&' '?' '@' '^' '.' ':' '|' '#']
let op_char_34 = op_char_3 | op_char_4
let op_char_234 = op_char_2 | op_char_34
let op_char_1234 = op_char_1 | op_char_234

let op_char_pref = ['!' '?']

rule token = parse
  | "##" space* ("\"" ([^ '\010' '\013' '"' ]* as file) "\"")?
    space* (digit+ as line) space* (digit+ as char) space* "##"
      { Lexlib.update_loc lexbuf file (int_of_string line) (int_of_string char);
        token lexbuf }
  | "#" space* "\"" ([^ '\010' '\013' '"' ]* as file) "\""
    space* (digit+ as line) space* (digit+ as bchar) space*
    (digit+ as echar) space* "#"
      { POSITION (Loc.user_position file (int_of_string line)
                 (int_of_string bchar) (int_of_string echar)) }
  | '\n'
      { Lexlib.newline lexbuf; token lexbuf }
  | space+
      { token lexbuf }
  | '_'
      { UNDERSCORE }
  | lident as id
      { try Hashtbl.find keywords id with Not_found -> LIDENT id }
  | uident as id
      { UIDENT id }
  | ['0'-'9'] ['0'-'9' '_']* as s
      { INTEGER (Number.int_const_dec (Lexlib.remove_underscores s)) }
  | '0' ['x' 'X'] (['0'-'9' 'A'-'F' 'a'-'f']['0'-'9' 'A'-'F' 'a'-'f' '_']* as s)
      { INTEGER (Number.int_const_hex (Lexlib.remove_underscores s)) }
  | '0' ['o' 'O'] (['0'-'7'] ['0'-'7' '_']* as s)
      { INTEGER (Number.int_const_oct (Lexlib.remove_underscores s)) }
  | '0' ['b' 'B'] (['0'-'1'] ['0'-'1' '_']* as s)
      { INTEGER (Number.int_const_bin (Lexlib.remove_underscores s)) }
  | (digit+ as i) ("" as f) ['e' 'E'] (['-' '+']? digit+ as e)
  | (digit+ as i) '.' (digit* as f) (['e' 'E'] (['-' '+']? digit+ as e))?
  | (digit* as i) '.' (digit+ as f) (['e' 'E'] (['-' '+']? digit+ as e))?
      { FLOAT (Number.real_const_dec i f
          (Opt.map Lexlib.remove_leading_plus e)) }
  | '0' ['x' 'X'] (hexadigit+ as i) ("" as f) ['p' 'P'] (['-' '+']? digit+ as e)
  | '0' ['x' 'X'] (hexadigit+ as i) '.' (hexadigit* as f)
        (['p' 'P'] (['-' '+']? digit+ as e))?
  | '0' ['x' 'X'] (hexadigit* as i) '.' (hexadigit+ as f)
        (['p' 'P'] (['-' '+']? digit+ as e))?
      { FLOAT (Number.real_const_hex i f
          (Opt.map Lexlib.remove_leading_plus e)) }
  | "(*)"
      { LEFTPAR_STAR_RIGHTPAR }
  | "(*"
      { Lexlib.comment lexbuf; token lexbuf }
  | "'" (lident as id)
      { QUOTE_LIDENT id }
  | ","
      { COMMA }
  | "("
      { LEFTPAR }
  | ")"
      { RIGHTPAR }
  | "{"
      { LEFTBRC }
  | "}"
      { RIGHTBRC }
  | ":"
      { COLON }
  | ";"
      { SEMICOLON }
  | "->"
      { ARROW }
  | "<-"
      { LARROW }
  | "<->"
      { LRARROW }
  | "&&"
      { AMPAMP }
  | "||"
      { BARBAR }
  | "/\\"
      { AND }
  | "\\/"
      { OR }
  | "."
      { DOT }
  | ".."
      { DOTDOT }
  | "|"
      { BAR }
  | "="
      { EQUAL }
  | "<>"
      { LTGT }
  | "~"
      { TILDE }
  | "["
      { LEFTSQ }
  | "]"
      { RIGHTSQ }
  | op_char_pref op_char_4* as s
      { OPPREF s }
  | op_char_1234* op_char_1 op_char_1234* as s
      { OP1 s }
  | op_char_234*  op_char_2 op_char_234*  as s
      { OP2 s }
  | op_char_34*   op_char_3 op_char_34*  as s
      { OP3 s }
  | op_char_4+ as s
      { OP4 s }
  | "\""
      { STRING (Lexlib.string lexbuf) }
  | eof
      { EOF }
  | _ as c
      { raise (IllegalCharacter c) }

{
  let debug = Debug.register_info_flag "print_modules"
    ~desc:"Print@ program@ modules@ after@ typechecking."

  open Stdlib
  open Ident
  open Theory
  open Pmodule

  let read_channel env path file c =
    let lb = Lexing.from_channel c in
    Loc.set_file file lb;
    Typing.open_file env path;
    let mm = Loc.with_location (mlw_file token) lb in
    if path = [] && Debug.test_flag debug then begin
      let print_m _ m = Format.eprintf "%a@\n@." print_module m in
      let add_m _ m mm = Mid.add m.mod_theory.th_name m mm in
      Mid.iter print_m (Mstr.fold add_m mm Mid.empty)
    end;
    mm

  let () = Env.register_format mlw_language "whyml" ["mlw";"why"] read_channel
    ~desc:"WhyML@ programming@ and@ specification@ language"
}
