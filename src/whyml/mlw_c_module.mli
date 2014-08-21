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

type builder
type value

type ty =
  | TyValue
  | TyValuePtr
  | TyExnTag

(*******************)
(* General purpose *)
(*******************)

type info = {
  info_syn: Printer.syntax_map;
  converters: Printer.syntax_map;
  current_theory: Theory.theory;
  current_module: Mlw_module.modul option;
  th_known_map: Decl.known_map;
  mo_known_map: Mlw_decl.known_map;
  fname: string option;
}

val clean_fname : string -> string

val modulename : ?separator:string -> ?fname:string -> string list -> string -> string

val get_ident : ?separator:string -> info -> Ident.ident -> value

val define_global_closure : info -> Ident.ident -> value -> unit

val define_global_constructor : info -> Ident.ident -> int -> unit

val dump : Format.formatter -> unit

(******************)
(* Builtin values *)
(******************)

val unit_value : value
val null_value : value
val true_value : value
val false_value : value
val env_value : value

(******************)
(* Value creation *)
(******************)

val create_value : ?ty:ty -> value -> builder -> value
val create_named_value : info -> Ident.ident -> value -> builder -> value
val create_array : int -> builder -> value
val create_exn : builder -> value
val create_mpz : string -> int -> builder -> value

val clone_mpz : value -> builder -> value

val cast_to_closure : value -> builder -> value
val cast_to_record : st:value -> value -> builder -> value
val cast_to_variant : value -> builder -> value

val malloc_closure : builder -> value
val malloc_exn : builder -> value
val malloc_env : int -> builder -> value
val malloc_variant : builder -> value
val malloc_record : value -> builder -> value

val create_function :
  info ->
  ?name:Ident.ident ->
  params:Ident.ident list ->
  raises:bool ->
  (raise_expr:(value -> builder -> unit) -> params:value list -> builder -> value) ->
  value

val create_pure_function :
  info ->
  name:Ident.ident ->
  params:Ident.ident list ->
  (params:value list -> builder -> value) ->
  value

(**********************)
(* Statement creation *)
(**********************)

val build_equal : value -> value -> builder -> value
val build_store : value -> value -> builder -> unit
val build_store_array : value -> int -> value -> builder -> unit
val build_store_array_from_array : value -> int -> value -> int -> builder -> unit
val build_store_field : value -> string -> value -> builder -> unit
val build_store_field_int : value -> string -> int -> builder -> unit
val build_break : builder -> unit
val build_if_not_null : value -> (builder -> unit) -> builder -> unit
val build_if_true : value -> (builder -> unit) -> builder -> unit
val build_if_false : value -> (builder -> unit) -> builder -> unit
val build_if_cmp_zero : value -> string -> (builder -> unit) -> builder -> unit
val build_else : (builder -> unit) -> builder -> unit
val build_if_else_if_else : (value * (builder -> unit)) list -> (builder -> unit) -> builder -> unit
val build_access_array : value -> int -> builder -> value
val build_access_field : ?ty:ty -> value -> string -> builder -> value
val build_not : value -> builder -> value
val build_do_while : (builder -> unit) -> builder -> unit
val build_abort : builder -> unit
val build_switch : value -> (int option * (builder -> unit)) list -> builder -> unit
val build_while : (builder -> unit) -> builder -> unit
val build_mpz_cmp : value -> value -> builder -> value
val build_mpz_succ : value -> builder -> unit
val build_call : value -> value list -> ?exn:value -> builder -> value
val build_pure_call : value -> value list -> builder -> value

(**********************)
(* Constant statement *)
(**********************)

val const_access_array : value -> int -> value
val const_equal : value -> value -> value

(******************)
(* Global objects *)
(******************)

val append_global_exn : value -> value -> unit
val define_record : value -> string list -> unit

(*******************)
(* Syntax handling *)
(*******************)

val query_syntax : Printer.syntax_map -> Ident.ident -> value option
val syntax_arguments : value -> value list -> builder -> value
