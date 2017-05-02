(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
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
        "float", FLOAT;
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
        "namespace", NAMESPACE;
        "not", NOT;
        "predicate", PREDICATE;
        "prop", PROP;
        "range", RANGE;
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
        "any", ANY;
        "assert", ASSERT;
        "assume", ASSUME;
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
        "loop", LOOP;
        "model", MODEL;
        "module", MODULE;
        "mutable", MUTABLE;
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
let digit_or_us = ['0'-'9' '_']
let alpha_no_us = ['a'-'z' 'A'-'Z']
let suffix = (alpha_no_us | '\''* digit_or_us)* '\''*
let lident = lalpha suffix
let uident = ualpha suffix
let lident_quote = lident ('\'' alpha_no_us suffix)+
let uident_quote = uident ('\'' alpha_no_us suffix)+
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
  | lident_quote as id
      { LIDENT_QUOTE id }
  | uident as id
      { UIDENT id }
  | uident_quote as id
      { UIDENT_QUOTE id }
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
      { REAL (Number.real_const_dec i f
          (Opt.map Lexlib.remove_leading_plus e)) }
  | '0' ['x' 'X'] (hexadigit+ as i) ("" as f) ['p' 'P'] (['-' '+']? digit+ as e)
  | '0' ['x' 'X'] (hexadigit+ as i) '.' (hexadigit* as f)
        (['p' 'P'] (['-' '+']? digit+ as e))?
  | '0' ['x' 'X'] (hexadigit* as i) '.' (hexadigit+ as f)
        (['p' 'P'] (['-' '+']? digit+ as e))?
      { REAL (Number.real_const_hex i f
          (Opt.map Lexlib.remove_leading_plus e)) }
  | "(*)"
      { LEFTPAR_STAR_RIGHTPAR }
  | "(*"
      { Lexlib.comment lexbuf; token lexbuf }
  | "~'" (lident as id)
      { OPAQUE_QUOTE_LIDENT id }
  | "'" (lident as id)
      { QUOTE_LIDENT id }
  | "'" (uident as id)
      { QUOTE_UIDENT id }
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
  | "\\"
      { LAMBDA }
  | "."
      { DOT }
  | ".."
      { DOTDOT }
  | "|"
      { BAR }
  | "<"
      { LT }
  | ">"
      { GT }
  | "<>"
      { LTGT }
  | "="
      { EQUAL }
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

exception Error of string

let () = Exn_printer.register (fun fmt exn -> match exn with
    | Error s -> Format.fprintf fmt "%s" s
    | _ -> raise exn)

let match_tokens t =
  match t with
  | None -> assert false (* TODO *)
  | Some t ->
      match t with
      | LIDENT _ -> "LIDENT"
      | LIDENT_QUOTE _ -> "LIDENT_QUOTE"
      | UIDENT _ -> "UIDENT"
      | UIDENT_QUOTE _ -> "UIDENT_QUOTE"
      | INTEGER _ -> "INTEGER"
      | OP1 _ -> "OP1"
      | OP2 _ -> "OP2"
      | OP3 _ -> "OP3"
      | OP4 _ -> "OP4"
      | OPPREF _ -> "OPPREF"
      | REAL _ -> "REAL"
      | STRING _ -> "STRING"
      | POSITION _ -> "POSITION"
      | QUOTE_UIDENT _ -> "QUOTE_UIDENT"
      | QUOTE_LIDENT _ -> "QUOTE_LIDENT"
      | OPAQUE_QUOTE_LIDENT _ -> "OPAQUE_QUOTE_LIDENT"
      | AS -> "AS"
      | AXIOM -> "AXIOM"
      | BY -> "BY"
      | CLONE -> "CLONE"
      | COINDUCTIVE -> "COINDUCTIVE"
      | CONSTANT -> "CONSTANT"
      | ELSE -> "ELSE"
      | END -> "END"
      | EPSILON -> "EPSILON"
      | EXISTS -> "EXISTS"
      | EXPORT -> "EXPORT"
      | FALSE -> "FALSE"
      | FLOAT -> "FLOAT"
      | FORALL -> "FORALL"
      | FUNCTION -> "FUNCTION"
      | GOAL -> "GOAL"
      | IF -> "IF"
      | IMPORT -> "IMPORT"
      | IN -> "IN"
      | INDUCTIVE -> "INDUCTIVE"
      | LEMMA -> "LEMMA"
      | LET -> "LET"
      | MATCH -> "MATCH"
      | META -> "META"
      | NAMESPACE -> "NAMESPACE"
      | NOT -> "NOT"
      | PROP -> "PROP"
      | PREDICATE -> "PREDICATE"
      | RANGE -> "RANGE"
      | SO -> "SO"
      | THEN -> "THEN"
      | THEORY -> "THEORY"
      | TRUE -> "TRUE"
      | TYPE -> "TYPE"
      | USE -> "USE"
      | WITH -> "WITH"

      | _ -> "TODO unrecognized token please report" (* TODO




(* program keywords *)

%token ABSTRACT ABSURD ANY ASSERT ASSUME BEGIN CHECK
%token DIVERGES DO DONE DOWNTO ENSURES EXCEPTION FOR
%token FUN GHOST INVARIANT LOOP MODEL MODULE MUTABLE
%token PRIVATE RAISE RAISES READS REC REQUIRES RETURNS
%token TO TRY VAL VARIANT WHILE WRITES

(* symbols *)

%token AND ARROW
%token BAR
%token COLON COMMA
%token DOT DOTDOT EQUAL LAMBDA LT GT LTGT
%token LEFTPAR LEFTPAR_STAR_RIGHTPAR LEFTSQ
%token LARROW LRARROW OR
%token RIGHTPAR RIGHTSQ
%token UNDERSCORE

%token EOF

(* program symbols *)

%token AMPAMP BARBAR LEFTBRC RIGHTBRC SEMICOLON
*)

  let parse_logic_file env path lb =
    (* This records the last token which was read (for error messages) *)
    let last = ref None in
    let module I = Parser.MenhirInterpreter in
    open_file token (Lexing.from_string "") (Typing.open_file env path);
    let checkpoint = Parser.Incremental.logic_file lb.Lexing.lex_curr_p
    and supplier =
      I.lexer_lexbuf_to_supplier (fun x -> let t = token x in last := Some t; t) lb
    and succeed _t = ()
    and fail checkpoint =
      let t = Lexing.lexeme lb in
      let token = match_tokens !last in
      let s = Report.report (t, token) checkpoint in
      Loc.with_location (fun _x -> raise (Error s)) lb
    in
    I.loop_handle succeed fail supplier checkpoint;
    Typing.close_file ()

  let parse_program_file inc lb =
    let last = ref None in
    let module I = Parser.MenhirInterpreter in
    open_file token (Lexing.from_string "") inc;
    let checkpoint = Parser.Incremental.program_file lb.Lexing.lex_curr_p
    and supplier =
      I.lexer_lexbuf_to_supplier (fun x -> let t = token x in last := Some t; t) lb
    and succeed _t = ()
    and fail checkpoint =
      let t = Lexing.lexeme lb in
      let token = match_tokens !last in
      let s = Report.report (t, token) checkpoint in
      Loc.with_location (fun _x -> raise (Error s)) lb
    in
    I.loop_handle succeed fail supplier checkpoint

  let read_channel env path file c =
    let lb = Lexing.from_channel c in
    Loc.set_file file lb;
    parse_logic_file env path lb

  let () = Env.register_format Env.base_language "why" ["why"] read_channel
    ~desc:"WhyML@ logical@ language"
}
