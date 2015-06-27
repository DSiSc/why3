(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2015   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

%{
  open Ptree

  let infix  s = "infix "  ^ s
  let prefix s = "prefix " ^ s
  let mixfix s = "mixfix " ^ s

  let qualid_last = function Qident x | Qdot (_, x) -> x.id_str

  let floc s e = Loc.extract (s,e)

  let add_lab id l = { id with id_lab = l }

  let id_anonymous loc = { id_str = "_"; id_lab = []; id_loc = loc }

  let mk_id id s e = { id_str = id; id_lab = []; id_loc = floc s e }

  let get_op s e = Qident (mk_id (mixfix "[]") s e)
  let set_op s e = Qident (mk_id (mixfix "[<-]") s e)
  let sub_op s e = Qident (mk_id (mixfix "[_.._]") s e)
  let above_op s e = Qident (mk_id (mixfix "[_..]") s e)
  let below_op s e = Qident (mk_id (mixfix "[.._]") s e)

  let mk_pat  d s e = { pat_desc  = d; pat_loc  = floc s e }
  let mk_term d s e = { term_desc = d; term_loc = floc s e }
  let mk_expr d s e = { expr_desc = d; expr_loc = floc s e }

  let variant_union v1 v2 = match v1, v2 with
    | _, [] -> v1
    | [], _ -> v2
    | _, ({term_loc = loc},_)::_ -> Loc.errorm ~loc
        "multiple `variant' clauses are not allowed"

  let empty_spec = {
    sp_pre     = [];
    sp_post    = [];
    sp_xpost   = [];
    sp_reads   = [];
    sp_writes  = [];
    sp_variant = [];
    sp_checkrw = false;
    sp_diverge = false;
  }

  let spec_union s1 s2 = {
    sp_pre     = s1.sp_pre @ s2.sp_pre;
    sp_post    = s1.sp_post @ s2.sp_post;
    sp_xpost   = s1.sp_xpost @ s2.sp_xpost;
    sp_reads   = s1.sp_reads @ s2.sp_reads;
    sp_writes  = s1.sp_writes @ s2.sp_writes;
    sp_variant = variant_union s1.sp_variant s2.sp_variant;
    sp_checkrw = s1.sp_checkrw || s2.sp_checkrw;
    sp_diverge = s1.sp_diverge || s2.sp_diverge;
  }

(* dead code
  let add_init_mark e =
    let init = { id_str = "Init"; id_lab = []; id_loc = e.expr_loc } in
    { e with expr_desc = Emark (init, e) }
*)

  let small_integer i =
    try match i with
      | Number.IConstDec s -> int_of_string s
      | Number.IConstHex s -> int_of_string ("0x"^s)
      | Number.IConstOct s -> int_of_string ("0o"^s)
      | Number.IConstBin s -> int_of_string ("0b"^s)
    with Failure _ -> raise Error

  let error_param loc =
    Loc.errorm ~loc "cannot determine the type of the parameter"

  let error_loc loc = Loc.error ~loc Error

  let () = Exn_printer.register (fun fmt exn -> match exn with
    | Error -> Format.fprintf fmt "syntax error"
    | _ -> raise exn)
%}

(* Tokens *)

%token <string> LIDENT UIDENT
%token <Ptree.integer_constant> INTEGER
%token <string> OP1 OP2 OP3 OP4 OPPREF
%token <Ptree.real_constant> FLOAT
%token <string> STRING
%token <Loc.position> POSITION
%token <string> QUOTE_UIDENT QUOTE_LIDENT

(* keywords *)

%token AS AXIOM CLONE COINDUCTIVE CONSTANT
%token ELSE END EPSILON EXISTS EXPORT FALSE FORALL FUNCTION
%token GOAL IF IMPORT IN INDUCTIVE LEMMA
%token LET MATCH META NOT PREDICATE PROP SCOPE
%token THEN THEORY TRUE TYPE USE WITH

(* program keywords *)

%token ABSTRACT ABSURD ANY ASSERT ASSUME BEGIN CHECK
%token DIVERGES DO DONE DOWNTO ENSURES EXCEPTION FOR
%token FUN GHOST INVARIANT LOOP MODULE MUTABLE
%token PRIVATE RAISE RAISES READS REC REQUIRES RETURNS
%token TO TRY VAL VARIANT WHILE WRITES

(* symbols *)

%token AND ARROW
%token BAR
%token COLON COMMA
%token DOT DOTDOT EQUAL LTGT
%token LEFTPAR LEFTPAR_STAR_RIGHTPAR LEFTSQ
%token LARROW LRARROW OR
%token RIGHTPAR RIGHTSQ
%token UNDERSCORE

%token EOF

(* program symbols *)

%token AMPAMP BARBAR LEFTBRC RIGHTBRC SEMICOLON

(* Precedences *)

%nonassoc IN
%nonassoc below_SEMI
%nonassoc SEMICOLON
%nonassoc LET VAL
%nonassoc prec_no_else
%nonassoc DOT ELSE GHOST
%nonassoc prec_named
%nonassoc COLON

%right ARROW LRARROW
%right OR BARBAR
%right AND AMPAMP
%nonassoc NOT
%left EQUAL LTGT OP1
%nonassoc LARROW
%nonassoc RIGHTSQ    (* stronger than <- for e1[e2 <- e3] *)
%left OP2
%left OP3
%left OP4
%nonassoc prec_prefix_op
%nonassoc LEFTSQ
%nonassoc OPPREF

(* Entry points *)

%start <Pmodule.pmodule Stdlib.Mstr.t> mlw_file
%%

(* Theories, modules, namespaces *)

mlw_file:
| theory_or_module* EOF { Typing.close_file () }
(* TODO
| module_decl* EOF { Typing.close_file () }
*)

theory_or_module:
| module_head module_decl* END
    { Typing.close_module (floc $startpos($3) $endpos($3)) }

module_head:
| THEORY labels(uident)  { Typing.open_module $2 ~theory:true  }
| MODULE labels(uident)  { Typing.open_module $2 ~theory:false }

module_decl:
| decl            { Typing.add_decl  (floc $startpos $endpos) $1 }
| use_clone       { Typing.use_clone (floc $startpos $endpos) $1 }
| namespace_head module_decl* END
    { Typing.close_namespace (floc $startpos($1) $endpos($1)) ~import:$1 }

namespace_head:
| SCOPE boption(IMPORT) uident  { Typing.open_namespace $3; $2 }

(* Use and clone *)

use_clone:
| USE use                                 { ($2, None) }
| CLONE use                               { ($2, Some []) }
| CLONE use WITH comma_list1(clone_subst) { ($2, Some $4) }

use:
| boption(IMPORT) tqualid
    { { use_module = $2; use_import = Some ($1, qualid_last $2) } }
| boption(IMPORT) tqualid AS uident
    { { use_module = $2; use_import = Some ($1, $4.id_str) } }
| EXPORT tqualid
    { { use_module = $2; use_import = None } }

clone_subst:
| SCOPE     ns     EQUAL ns     { CSns    (floc $startpos $endpos, $2,$4) }
| TYPE qualid ty_var* EQUAL ty  { CStsym  (floc $startpos $endpos, $2,$3,$5) }
| CONSTANT  qualid EQUAL qualid { CSfsym  (floc $startpos $endpos, $2,$4) }
| FUNCTION  qualid EQUAL qualid { CSfsym  (floc $startpos $endpos, $2,$4) }
| PREDICATE qualid EQUAL qualid { CSpsym  (floc $startpos $endpos, $2,$4) }
| VAL       qualid EQUAL qualid { CSvsym  (floc $startpos $endpos, $2,$4) }
| LEMMA     qualid              { CSlemma (floc $startpos $endpos, $2) }
| GOAL      qualid              { CSgoal  (floc $startpos $endpos, $2) }

ns:
| uqualid { Some $1 }
| DOT     { None }

(* Theory declarations *)

decl:
| TYPE with_list1(type_decl)                { Dtype $2 }
| CONSTANT  constant_decl                   { Dlogic [$2] }
| FUNCTION  function_decl  with_logic_decl* { Dlogic ($2::$3) }
| PREDICATE predicate_decl with_logic_decl* { Dlogic ($2::$3) }
| INDUCTIVE   with_list1(inductive_decl)    { Dind (Decl.Ind, $2) }
| COINDUCTIVE with_list1(inductive_decl)    { Dind (Decl.Coind, $2) }
| AXIOM labels(ident) COLON term            { Dprop (Decl.Paxiom, $2, $4) }
| LEMMA labels(ident) COLON term            { Dprop (Decl.Plemma, $2, $4) }
| GOAL  labels(ident) COLON term            { Dprop (Decl.Pgoal, $2, $4) }
| META sident comma_list1(meta_arg)         { Dmeta ($2, $3) }
| pdecl                                     { $1 }

meta_arg:
| TYPE      ty      { Mty $2 }
| CONSTANT  qualid  { Mfs $2 }
| FUNCTION  qualid  { Mfs $2 }
| PREDICATE qualid  { Mps $2 }
| PROP      qualid  { Mpr $2 }
| STRING            { Mstr $1 }
| INTEGER           { Mint (small_integer $1) }

(* Type declarations *)

type_decl:
| labels(lident) ty_var* typedefn invariant*
  { let (vis, mut), def = $3 in
    { td_ident = $1; td_params = $2;
      td_vis = vis; td_mut = mut;
      td_inv = $4; td_def = def;
      td_loc = floc $startpos $endpos } }

ty_var:
| labels(quote_lident) { $1 }

(* TODO: should global "mutable" imply "private"?
  "type t 'a = mutable { x : int }"
    - if "x" is immutable then the type can only be private
    - if "x" is automatically mutable then I don't like it
    - if there are known mutable fields, then a global "mutable"
      is redundant, unless it also means "private" *)
(* TODO: what should be the syntax for mutable private records
    without known fields? *)
typedefn:
| (* epsilon *)
    { (Public, false), TDabstract }
| EQUAL vis_mut bar_list1(type_case)
    { $2, TDalgebraic $3 }
| EQUAL vis_mut LEFTBRC semicolon_list1(type_field) RIGHTBRC
    { $2, TDrecord $4 }
| EQUAL vis_mut ty
    { $2, TDalias $3 }

vis_mut:
| (* epsilon *)     { Public, false }
| MUTABLE           { Public, true  }
| abstract          { $1, false }
| abstract MUTABLE  { $1, true }
| MUTABLE abstract  { $2, true }

abstract:
| PRIVATE           { Private }
| ABSTRACT          { Abstract }

type_field:
| field_modifiers labels(lident) cast
  { { f_ident = $2; f_mutable = fst $1; f_ghost = snd $1;
      f_pty = $3; f_loc = floc $startpos $endpos } }

field_modifiers:
| (* epsilon *) { false, false }
| MUTABLE       { true,  false }
| GHOST         { false, true  }
| GHOST MUTABLE { true,  true  }
| MUTABLE GHOST { true,  true  }

type_case:
| labels(uident) params { floc $startpos $endpos, $1, $2 }

(* Logic declarations *)

constant_decl:
| labels(lident_rich) cast preceded(EQUAL,term)?
  { { ld_ident = $1; ld_params = []; ld_type = Some $2;
      ld_def = $3; ld_loc = floc $startpos $endpos } }

function_decl:
| labels(lident_rich) params cast preceded(EQUAL,term)?
  { { ld_ident = $1; ld_params = $2; ld_type = Some $3;
      ld_def = $4; ld_loc = floc $startpos $endpos } }

predicate_decl:
| labels(lident_rich) params preceded(EQUAL,term)?
  { { ld_ident = $1; ld_params = $2; ld_type = None;
      ld_def = $3; ld_loc = floc $startpos $endpos } }

with_logic_decl:
| WITH labels(lident_rich) params cast? preceded(EQUAL,term)?
  { { ld_ident = $2; ld_params = $3; ld_type = $4;
      ld_def = $5; ld_loc = floc $startpos $endpos } }

(* Inductive declarations *)

inductive_decl:
| labels(lident_rich) params ind_defn
  { { in_ident = $1; in_params = $2;
      in_def = $3; in_loc = floc $startpos $endpos } }

ind_defn:
| (* epsilon *)             { [] }
| EQUAL bar_list1(ind_case) { $2 }

ind_case:
| labels(ident) COLON term  { floc $startpos $endpos, $1, $3 }

(* Type expressions *)

ty:
| ty_arg          { $1 }
| lqualid ty_arg+ { PTtyapp ($1, $2) }
| ty ARROW ty     { PTarrow ($1, $3) }

ty_arg:
| lqualid                           { PTtyapp ($1, []) }
| quote_lident                      { PTtyvar $1 }
| LEFTPAR comma_list2(ty) RIGHTPAR  { PTtuple $2 }
| LEFTPAR RIGHTPAR                  { PTtuple [] }
| LEFTPAR ty RIGHTPAR               { PTparen $2 }

cast:
| COLON ty  { $2 }

(* Parameters and binders *)

(* [param] and [binder] below must have the same grammar
   and raise [Error] in the same cases. Interpretaion of
   single-standing untyped [Qident]'s is different: [param]
   treats them as type expressions, [binder], as parameter
   names, whose type must be inferred. *)

params:  param*  { List.concat $1 }

binders: binder+ { List.concat $1 }

param:
| anon_binder
    { error_param (floc $startpos $endpos) }
| ty_arg
    { [floc $startpos $endpos, None, false, $1] }
| LEFTPAR GHOST ty RIGHTPAR
    { [floc $startpos $endpos, None, true, $3] }
| ty_arg label label*
    { match $1 with
      | PTtyapp (Qident _, []) ->
             error_param (floc $startpos $endpos)
      | _ -> error_loc (floc $startpos($2) $endpos($2)) }
| LEFTPAR binder_vars_rest RIGHTPAR
    { match $2 with [l,_] -> error_param l
      | _ -> error_loc (floc $startpos($3) $endpos($3)) }
| LEFTPAR GHOST binder_vars_rest RIGHTPAR
    { match $3 with [l,_] -> error_param l
      | _ -> error_loc (floc $startpos($4) $endpos($4)) }
| LEFTPAR binder_vars cast RIGHTPAR
    { List.map (fun (l,i) -> l, i, false, $3) $2 }
| LEFTPAR GHOST binder_vars cast RIGHTPAR
    { List.map (fun (l,i) -> l, i, true, $4) $3 }

binder:
| anon_binder
    { error_param (floc $startpos $endpos) }
| ty_arg
    { match $1 with
      | PTtyapp (Qident id, [])
      | PTparen (PTtyapp (Qident id, [])) ->
             [floc $startpos $endpos, Some id, false, None]
      | _ -> [floc $startpos $endpos, None, false, Some $1] }
| LEFTPAR GHOST ty RIGHTPAR
    { match $3 with
      | PTtyapp (Qident id, []) ->
             [floc $startpos $endpos, Some id, true, None]
      | _ -> [floc $startpos $endpos, None, true, Some $3] }
| ty_arg label label*
    { match $1 with
      | PTtyapp (Qident id, []) ->
             let id = add_lab id ($2::$3) in
             [floc $startpos $endpos, Some id, false, None]
      | _ -> error_loc (floc $startpos($2) $endpos($2)) }
| LEFTPAR binder_vars_rest RIGHTPAR
    { match $2 with [l,i] -> [l, i, false, None]
      | _ -> error_loc (floc $startpos($3) $endpos($3)) }
| LEFTPAR GHOST binder_vars_rest RIGHTPAR
    { match $3 with [l,i] -> [l, i, true, None]
      | _ -> error_loc (floc $startpos($4) $endpos($4)) }
| LEFTPAR binder_vars cast RIGHTPAR
    { List.map (fun (l,i) -> l, i, false, Some $3) $2 }
| LEFTPAR GHOST binder_vars cast RIGHTPAR
    { List.map (fun (l,i) -> l, i, true, Some $4) $3 }

binder_vars:
| binder_vars_head  { List.rev $1 }
| binder_vars_rest  { $1 }

binder_vars_rest:
| binder_vars_head label label* binder_var*
    { List.rev_append (match $1 with
        | (l, Some id) :: bl ->
            let l3 = floc $startpos($3) $endpos($3) in
            (Loc.join l l3, Some (add_lab id ($2::$3))) :: bl
        | _ -> assert false) $4 }
| binder_vars_head anon_binder binder_var*
   { List.rev_append $1 ($2 :: $3) }
| anon_binder binder_var*
   { $1 :: $2 }

binder_vars_head:
| ty {
    let of_id id = id.id_loc, Some id in
    let push acc = function
      | PTtyapp (Qident id, []) -> of_id id :: acc
      | _ -> Loc.error ~loc:(floc $startpos $endpos) Error in
    match $1 with
      | PTtyapp (Qident id, l) -> List.fold_left push [of_id id] l
      | _ -> Loc.error ~loc:(floc $startpos $endpos) Error }

binder_var:
| labels(lident)  { floc $startpos $endpos, Some $1 }
| anon_binder     { $1 }

anon_binder:
| UNDERSCORE      { floc $startpos $endpos, None }

(* Logical terms *)

mk_term(X): d = X { mk_term d $startpos $endpos }

term: t = mk_term(term_) { t }

term_:
| term_arg_
    { match $1 with (* break the infix relation chain *)
      | Tinfix (l,o,r) -> Tinnfix (l,o,r) | d -> d }
| NOT term
    { Tunop (Tnot, $2) }
| prefix_op term %prec prec_prefix_op
    { Tidapp (Qident $1, [$2]) }
| l = term ; o = bin_op ; r = term
    { Tbinop (l, o, r) }
| l = term ; o = infix_op ; r = term
    { Tinfix (l, o, r) }
| term_arg located(term_arg)+ (* FIXME/TODO: "term term_arg" *)
    { let join f (a,_,e) = mk_term (Tapply (f,a)) $startpos e in
      (List.fold_left join $1 $2).term_desc }
| IF term THEN term ELSE term
    { Tif ($2, $4, $6) }
| LET pattern EQUAL term IN term
    { match $2.pat_desc with
      | Pvar id -> Tlet (id, $4, $6)
      | Pwild -> Tlet (id_anonymous $2.pat_loc, $4, $6)
      | Ptuple [] -> Tlet (id_anonymous $2.pat_loc,
          { $4 with term_desc = Tcast ($4, PTtuple []) }, $6)
      | Pcast ({pat_desc = Pvar id}, ty) ->
          Tlet (id, { $4 with term_desc = Tcast ($4, ty) }, $6)
      | Pcast ({pat_desc = Pwild}, ty) ->
          let id = id_anonymous $2.pat_loc in
          Tlet (id, { $4 with term_desc = Tcast ($4, ty) }, $6)
      | _ -> Tmatch ($4, [$2, $6]) }
| LET labels(lident_op_id) EQUAL term IN term
    { Tlet ($2, $4, $6) }
| LET labels(lident) mk_term(lam_defn) IN term
    { Tlet ($2, $3, $5) }
| LET labels(lident_op_id) mk_term(lam_defn) IN term
    { Tlet ($2, $3, $5) }
| MATCH term WITH match_cases(term) END
    { Tmatch ($2, $4) }
| MATCH comma_list2(term) WITH match_cases(term) END
    { Tmatch (mk_term (Ttuple $2) $startpos($2) $endpos($2), $4) }
| quant comma_list1(quant_vars) triggers DOT term
    { Tquant ($1, List.concat $2, $3, $5) }
| FUN binders ARROW term
    { Tquant (Tlambda, $2, [], $4) }
| EPSILON
    { Loc.errorm "Epsilon terms are currently not supported in WhyML" }
| label term %prec prec_named
    { Tnamed ($1, $2) }
| term cast
    { Tcast ($1, $2) }

lam_defn:
| binders EQUAL term  { Tquant (Tlambda, $1, [], $3) }

term_arg: mk_term(term_arg_) { $1 }
term_dot: mk_term(term_dot_) { $1 }

term_arg_:
| qualid                    { Tident $1 }
| numeral                   { Tconst $1 }
| TRUE                      { Ttrue }
| FALSE                     { Tfalse }
| quote_uident              { Tident (Qident $1) }
| o = oppref ; a = term_arg { Tidapp (Qident o, [a]) }
| term_sub_                 { $1 }

term_dot_:
| lqualid                   { Tident $1 }
| o = oppref ; a = term_dot { Tidapp (Qident o, [a]) }
| term_sub_                 { $1 }

term_sub_:
| term_dot DOT lqualid_rich                         { Tidapp ($3,[$1]) }
| LEFTPAR term RIGHTPAR                             { $2.term_desc }
| LEFTPAR RIGHTPAR                                  { Ttuple [] }
| LEFTPAR comma_list2(term) RIGHTPAR                { Ttuple $2 }
| LEFTBRC field_list1(term) RIGHTBRC                { Trecord $2 }
| LEFTBRC term_arg WITH field_list1(term) RIGHTBRC  { Tupdate ($2,$4) }
| term_arg LEFTSQ term RIGHTSQ
    { Tidapp (get_op $startpos($2) $endpos($2), [$1;$3]) }
| term_arg LEFTSQ term LARROW term RIGHTSQ
    { Tidapp (set_op $startpos($2) $endpos($2), [$1;$3;$5]) }
| term_arg LEFTSQ term DOTDOT term RIGHTSQ
    { Tidapp (sub_op $startpos($2) $endpos($2), [$1;$3;$5]) }
| term_arg LEFTSQ term DOTDOT RIGHTSQ
    { Tidapp (above_op $startpos($2) $endpos($2), [$1;$3]) }
| term_arg LEFTSQ DOTDOT term RIGHTSQ
    { Tidapp (below_op $startpos($2) $endpos($2), [$1;$4]) }

field_list1(X):
| fl = semicolon_list1(separated_pair(lqualid, EQUAL, X)) { fl }

match_cases(X):
| cl = bar_list1(separated_pair(pattern, ARROW, X)) { cl }

quant_vars:
| binder_var+ cast? { List.map (fun (l,i) -> l, i, false, $2) $1 }

triggers:
| (* epsilon *)                                                 { [] }
| LEFTSQ separated_nonempty_list(BAR,comma_list1(term)) RIGHTSQ { $2 }

%inline bin_op:
| ARROW   { Timplies }
| LRARROW { Tiff }
| OR      { Tor }
| BARBAR  { Tor_asym }
| AND     { Tand }
| AMPAMP  { Tand_asym }

quant:
| FORALL  { Tforall }
| EXISTS  { Texists }

numeral:
| INTEGER { Number.ConstInt $1 }
| FLOAT   { Number.ConstReal $1 }

(* Program declarations *)

pdecl:
| VAL ghost kind labels(lident_rich) mk_expr(val_defn) { Dlet ($4, $2, $3, $5) }
| LET ghost kind labels(lident_rich) mk_expr(fun_defn) { Dlet ($4, $2, $3, $5) }
| LET ghost kind labels(lident_rich) EQUAL expr        { Dlet ($4, $2, $3, $6) }
| LET REC with_list1(rec_defn)                         { Drec $3 }
| EXCEPTION labels(uident)                             { Dexn ($2, PTtuple []) }
| EXCEPTION labels(uident) ty                          { Dexn ($2, $3) }

ghost:
| (* epsilon *) { false }
| GHOST         { true }

kind:
| (* epsilon *) { Expr.RKnone }
| FUNCTION      { Expr.RKfunc }
| CONSTANT      { Expr.RKfunc }
| PREDICATE     { Expr.RKpred }
| LEMMA         { Expr.RKlemma }

(* Function definitions *)

rec_defn:
| ghost kind labels(lident_rich) binders cast? spec EQUAL spec seq_expr
    { $3, $1, $2, $4, $5, spec_union $6 $8, $9 }

fun_defn:
| binders cast? spec EQUAL spec seq_expr
    { Efun ($1, $2, spec_union $3 $5, $6) }

val_defn:
| params cast spec  { Eany ($1, $2, $3) }

(* Program expressions *)

mk_expr(X): d = X { mk_expr d $startpos $endpos }

seq_expr:
| expr %prec below_SEMI   { $1 }
| expr SEMICOLON          { $1 }
| expr SEMICOLON seq_expr { mk_expr (Esequence ($1, $3)) $startpos $endpos }

expr: e = mk_expr(expr_) { e }

expr_:
| expr_arg_
    { match $1 with (* break the infix relation chain *)
      | Einfix (l,o,r) -> Einnfix (l,o,r) | d -> d }
| expr AMPAMP expr
    { Eand ($1, $3) }
| expr BARBAR expr
    { Eor ($1, $3) }
| NOT expr %prec prec_prefix_op
    { Enot $2 }
| prefix_op expr %prec prec_prefix_op
    { Eidapp (Qident $1, [$2]) }
| l = expr ; o = infix_op ; r = expr
    { Einfix (l,o,r) }
| expr_arg located(expr_arg)+ (* FIXME/TODO: "expr expr_arg" *)
    { let join f (a,_,e) = mk_expr (Eapply (f,a)) $startpos e in
      (List.fold_left join $1 $2).expr_desc }
| IF seq_expr THEN expr ELSE expr
    { Eif ($2, $4, $6) }
| IF seq_expr THEN expr %prec prec_no_else
    { Eif ($2, $4, mk_expr (Etuple []) $startpos $endpos) }
| expr LARROW expr
    { match $1.expr_desc with
      | Eidapp (q, [e1]) -> Eassign (e1, q, $3)
      | Eidapp (Qident id, [e1;e2]) when id.id_str = mixfix "[]" ->
          Eidapp (Qident {id with id_str = mixfix "[]<-"}, [e1;e2;$3])
      | _ -> raise Error }
| LET ghost kind pattern EQUAL seq_expr IN seq_expr
    { match $4.pat_desc with
      | Pvar id -> Elet (id, $2, $3, $6, $8)
      | Pwild -> Elet (id_anonymous $4.pat_loc, $2, $3, $6, $8)
      | Ptuple [] -> Elet (id_anonymous $4.pat_loc, $2, $3,
          { $6 with expr_desc = Ecast ($6, PTtuple []) }, $8)
      | Pcast ({pat_desc = Pvar id}, ty) ->
          Elet (id, $2, $3, { $6 with expr_desc = Ecast ($6, ty) }, $8)
      | Pcast ({pat_desc = Pwild}, ty) ->
          let id = id_anonymous $4.pat_loc in
          Elet (id, $2, $3, { $6 with expr_desc = Ecast ($6, ty) }, $8)
      | _ ->
          let e = if $2 then { $6 with expr_desc = Eghost $6 } else $6 in
          (match $3 with
          | Expr.RKnone -> Ematch (e, [$4, $8])
          | _ -> Loc.errorm ~loc:($4.pat_loc)
              "`let <kind>' cannot be used with complex patterns") }
| LET ghost kind labels(lident_op_id) EQUAL seq_expr IN seq_expr
    { Elet ($4, $2, $3, $6, $8) }
| LET ghost kind labels(lident) mk_expr(fun_defn) IN seq_expr
    { Elet ($4, $2, $3, $5, $7) }
| LET ghost kind labels(lident_op_id) mk_expr(fun_defn) IN seq_expr
    { Elet ($4, $2, $3, $5, $7) }
| LET REC with_list1(rec_defn) IN seq_expr
    { Erec ($3, $5) }
| FUN binders spec ARROW spec seq_expr
    { Efun ($2, None, spec_union $3 $5, $6) }
| ABSTRACT spec seq_expr END
    { Efun ([], None, $2, $3) }
| ANY ty spec
    { Eany ([], $2, $3) }
| VAL ghost kind labels(lident_rich) mk_expr(val_defn) IN seq_expr
    { Elet ($4, $2, $3, $5, $7) }
| MATCH seq_expr WITH match_cases(seq_expr) END
    { Ematch ($2, $4) }
| MATCH comma_list2(expr) WITH match_cases(seq_expr) END
    { Ematch (mk_expr (Etuple $2) $startpos($2) $endpos($2), $4) }
| quote_uident COLON seq_expr
    { Emark ($1, $3) }
| LOOP loop_annotation seq_expr END
    { let inv, var = $2 in Eloop (inv, var, $3) }
| WHILE seq_expr DO loop_annotation seq_expr DONE
    { let inv, var = $4 in Ewhile ($2, inv, var, $5) }
| FOR lident EQUAL seq_expr for_direction seq_expr DO invariant* seq_expr DONE
    { Efor ($2, $4, $5, $6, $8, $9) }
| ABSURD
    { Eabsurd }
| RAISE uqualid
    { Eraise ($2, None) }
| RAISE LEFTPAR uqualid seq_expr RIGHTPAR
    { Eraise ($3, Some $4) }
| TRY seq_expr WITH bar_list1(exn_handler) END
    { Etry ($2, $4) }
| GHOST expr
    { Eghost $2 }
| assertion_kind LEFTBRC term RIGHTBRC
    { Eassert ($1, $3) }
| label expr %prec prec_named
    { Enamed ($1, $2) }
| expr cast
    { Ecast ($1, $2) }

expr_arg: e = mk_expr(expr_arg_) { e }
expr_dot: e = mk_expr(expr_dot_) { e }

expr_arg_:
| qualid                    { Eident $1 }
| numeral                   { Econst $1 }
| TRUE                      { Etrue }
| FALSE                     { Efalse }
| o = oppref ; a = expr_arg { Eidapp (Qident o, [a]) }
| expr_sub                  { $1 }

expr_dot_:
| lqualid                   { Eident $1 }
| o = oppref ; a = expr_dot { Eidapp (Qident o, [a]) }
| expr_sub                  { $1 }

expr_sub:
| expr_dot DOT lqualid_rich                         { Eidapp ($3, [$1]) }
| BEGIN seq_expr END                                { $2.expr_desc }
| LEFTPAR seq_expr RIGHTPAR                         { $2.expr_desc }
| BEGIN END                                         { Etuple [] }
| LEFTPAR RIGHTPAR                                  { Etuple [] }
| LEFTPAR comma_list2(expr) RIGHTPAR                { Etuple $2 }
| LEFTBRC field_list1(expr) RIGHTBRC                { Erecord $2 }
| LEFTBRC expr_arg WITH field_list1(expr) RIGHTBRC  { Eupdate ($2, $4) }
| expr_arg LEFTSQ expr RIGHTSQ
    { Eidapp (get_op $startpos($2) $endpos($2), [$1;$3]) }
| expr_arg LEFTSQ expr LARROW expr RIGHTSQ
    { Eidapp (set_op $startpos($2) $endpos($2), [$1;$3;$5]) }
| expr_arg LEFTSQ expr DOTDOT expr RIGHTSQ
    { Eidapp (sub_op $startpos($2) $endpos($2), [$1;$3;$5]) }
| expr_arg LEFTSQ expr DOTDOT RIGHTSQ
    { Eidapp (above_op $startpos($2) $endpos($2), [$1;$3]) }
| expr_arg LEFTSQ DOTDOT expr RIGHTSQ
    { Eidapp (below_op $startpos($2) $endpos($2), [$1;$4]) }

loop_annotation:
| (* epsilon *)
    { [], [] }
| invariant loop_annotation
    { let inv, var = $2 in $1 :: inv, var }
| variant loop_annotation
    { let inv, var = $2 in inv, variant_union $1 var }

exn_handler:
| uqualid pat_arg? ARROW seq_expr { $1, $2, $4 }

assertion_kind:
| ASSERT  { Expr.Assert }
| ASSUME  { Expr.Assume }
| CHECK   { Expr.Check }

for_direction:
| TO      { Expr.To }
| DOWNTO  { Expr.DownTo }

(* Specification *)

spec:
| (* epsilon *)     { empty_spec }
| single_spec spec  { spec_union $1 $2 }

single_spec:
| REQUIRES LEFTBRC term RIGHTBRC
    { { empty_spec with sp_pre = [$3] } }
| ENSURES LEFTBRC ensures RIGHTBRC
    { { empty_spec with sp_post = [floc $startpos($3) $endpos($3), $3] } }
| RETURNS LEFTBRC match_cases(term) RIGHTBRC
    { { empty_spec with sp_post = [floc $startpos($3) $endpos($3), $3] } }
| RAISES LEFTBRC bar_list1(raises) RIGHTBRC
    { { empty_spec with sp_xpost = [floc $startpos($3) $endpos($3), $3] } }
| READS  LEFTBRC comma_list0(lqualid) RIGHTBRC
    { { empty_spec with sp_reads = $3; sp_checkrw = true } }
| WRITES LEFTBRC comma_list0(term) RIGHTBRC
    { { empty_spec with sp_writes = $3; sp_checkrw = true } }
| RAISES LEFTBRC comma_list1(xsymbol) RIGHTBRC
    { { empty_spec with sp_xpost = [floc $startpos($3) $endpos($3), $3] } }
| DIVERGES
    { { empty_spec with sp_diverge = true } }
| variant
    { { empty_spec with sp_variant = $1 } }

ensures:
| term
    { let id = mk_id "result" $startpos $endpos in
      [mk_pat (Pvar id) $startpos $endpos, $1] }

raises:
| uqualid ARROW term
    { $1, mk_pat (Ptuple []) $startpos($1) $endpos($1), $3 }
| uqualid pat_arg ARROW term
    { $1, $2, $4 }

xsymbol:
| uqualid
    { $1, mk_pat Pwild $startpos $endpos, mk_term Ttrue $startpos $endpos }

invariant:
| INVARIANT LEFTBRC term RIGHTBRC { $3 }

variant:
| VARIANT LEFTBRC comma_list1(single_variant) RIGHTBRC { $3 }

single_variant:
| term preceded(WITH,lqualid)? { $1, $2 }

(* Patterns *)

mk_pat(X): X { mk_pat $1 $startpos $endpos }

pattern: mk_pat(pattern_) { $1 }
pat_arg: mk_pat(pat_arg_) { $1 }

pattern_:
| pat_conj_                             { $1 }
| mk_pat(pat_conj_) BAR pattern         { Por ($1,$3) }

pat_conj_:
| pat_uni_                              { $1 }
| comma_list2(mk_pat(pat_uni_))         { Ptuple $1 }

pat_uni_:
| pat_arg_                              { $1 }
| uqualid pat_arg+                      { Papp ($1,$2) }
| mk_pat(pat_uni_) AS labels(lident)    { Pas ($1,$3) }
| mk_pat(pat_uni_) cast                 { Pcast($1,$2) }

pat_arg_:
| UNDERSCORE                            { Pwild }
| labels(lident)                        { Pvar $1 }
| uqualid                               { Papp ($1,[]) }
| LEFTPAR RIGHTPAR                      { Ptuple [] }
| LEFTPAR pattern_ RIGHTPAR             { $2 }
| LEFTBRC field_list1(pattern) RIGHTBRC { Prec $2 }

(* Idents *)

ident:
| uident { $1 }
| lident { $1 }

uident:
| UIDENT          { mk_id $1 $startpos $endpos }

lident:
| LIDENT          { mk_id $1 $startpos $endpos }

quote_uident:
| QUOTE_UIDENT  { mk_id ("'" ^ $1) $startpos $endpos }

quote_lident:
| QUOTE_LIDENT  { mk_id $1 $startpos $endpos }

(* Idents + symbolic operation names *)

ident_rich:
| uident        { $1 }
| lident_rich   { $1 }

lident_rich:
| lident        { $1 }
| lident_op_id  { $1 }

lident_op_id:
| LEFTPAR lident_op RIGHTPAR  { mk_id $2 $startpos $endpos }
| LEFTPAR_STAR_RIGHTPAR       { mk_id (infix "*") $startpos $endpos }

lident_op:
| op_symbol               { infix $1 }
| op_symbol UNDERSCORE    { prefix $1 }
| EQUAL                   { infix "=" }
| OPPREF                  { prefix $1 }
| LEFTSQ RIGHTSQ          { mixfix "[]" }
| LEFTSQ LARROW RIGHTSQ   { mixfix "[<-]" }
| LEFTSQ RIGHTSQ LARROW   { mixfix "[]<-" }
| LEFTSQ UNDERSCORE DOTDOT UNDERSCORE RIGHTSQ { mixfix "[_.._]" }
| LEFTSQ            DOTDOT UNDERSCORE RIGHTSQ { mixfix "[.._]" }
| LEFTSQ UNDERSCORE DOTDOT            RIGHTSQ { mixfix "[_..]" }

op_symbol:
| OP1 { $1 }
| OP2 { $1 }
| OP3 { $1 }
| OP4 { $1 }

%inline oppref:
| o = OPPREF { mk_id (prefix o)  $startpos $endpos }

prefix_op:
| op_symbol { mk_id (prefix $1)  $startpos $endpos }

%inline infix_op:
| o = OP1   { mk_id (infix o)    $startpos $endpos }
| o = OP2   { mk_id (infix o)    $startpos $endpos }
| o = OP3   { mk_id (infix o)    $startpos $endpos }
| o = OP4   { mk_id (infix o)    $startpos $endpos }
| EQUAL     { mk_id (infix "=")  $startpos $endpos }
| LTGT      { mk_id (infix "<>") $startpos $endpos }

(* Qualified idents *)

qualid:
| ident_rich              { Qident $1 }
| uqualid DOT ident_rich  { Qdot ($1, $3) }

lqualid_rich:
| lident_rich             { Qident $1 }
| uqualid DOT lident_rich { Qdot ($1, $3) }

lqualid:
| lident              { Qident $1 }
| uqualid DOT lident  { Qdot ($1, $3) }

uqualid:
| uident              { Qident $1 }
| uqualid DOT uident  { Qdot ($1, $3) }

(* Theory/Module names *)

tqualid:
| uident                { Qident $1 }
| any_qualid DOT uident { Qdot ($1, $3) }

any_qualid:
| sident                { Qident $1 }
| any_qualid DOT sident { Qdot ($1, $3) }

sident:
| ident   { $1 }
| STRING  { mk_id $1 $startpos $endpos }

(* Labels and position markers *)

labels(X): X label* { add_lab $1 $2 }

label:
| STRING    { Lstr (Ident.create_label $1) }
| POSITION  { Lpos $1 }

(* Miscellaneous *)

bar_list1(X):
| ioption(BAR) ; xl = separated_nonempty_list(BAR, X) { xl }

with_list1(X):
| separated_nonempty_list(WITH, X)  { $1 }

comma_list2(X):
| X COMMA comma_list1(X) { $1 :: $3 }

comma_list1(X):
| separated_nonempty_list(COMMA, X) { $1 }

comma_list0(X):
| xl = separated_list(COMMA, X) { xl }

semicolon_list1(X):
| x = X ; ioption(SEMICOLON)                  { [x] }
| x = X ; SEMICOLON ; xl = semicolon_list1(X) { x :: xl }

located(X): X { $1, $startpos, $endpos }
