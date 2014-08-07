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

(*******************)
(* General purpose *)
(*******************)

val define_global : value -> unit

val value_of_string : string -> value

val init_builder : builder

val dump : Format.formatter -> unit
val finalize : Format.formatter -> unit

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

val create_value : value -> builder -> value
val create_named_value : Ident.ident -> value -> builder -> value
val create_array : int -> builder -> value
val create_exn : builder -> value
val create_mpz : string -> int -> builder -> value

val clone_mpz : value -> builder -> value

val cast_to_closure : raises:bool -> value -> builder -> value
val cast_to_record : st:value -> value -> builder -> value
val cast_to_variant : value -> builder -> value

val malloc_closure : raises:bool -> builder -> value
val malloc_exn : builder -> value
val malloc_env : int -> builder -> value
val malloc_variant : builder -> value
val malloc_record : value -> builder -> value

val create_lambda :
  param:Ident.ident ->
  raises:bool ->
  (raise_expr:(value -> builder -> unit) -> param:value -> builder -> value) ->
  value

(**********************)
(* Statement creation *)
(**********************)

val build_equal : value -> value -> builder -> value
val build_store : value -> value -> builder -> unit
val build_store_field : value -> string -> value -> builder -> unit
val build_store_field_int : value -> string -> int -> builder -> unit
val build_break : builder -> unit
val build_if_not_null : value -> (builder -> unit) -> builder -> unit
val build_if_true : value -> (builder -> unit) -> builder -> unit
val build_if_false : value -> (builder -> unit) -> builder -> unit
val build_if_cmp_zero : value -> string -> (builder -> unit) -> builder -> unit
val build_else : (builder -> unit) -> builder -> unit
val build_if_else_if_else : (value * (builder -> unit)) list -> (builder -> unit) -> builder -> unit
val build_access_field : value -> string -> builder -> value
val build_not : value -> builder -> value
val build_do_while : (builder -> unit) -> builder -> unit
val build_abort : builder -> unit
val build_switch : value -> (int option * (builder -> unit)) list -> builder -> unit
val build_while : (builder -> unit) -> builder -> unit
val build_mpz_cmp : value -> value -> builder -> value
val build_mpz_succ : value -> builder -> unit

(**********************)
(* Constant statement *)
(**********************)

val const_access_field : value -> string -> value
val const_access_array : value -> int -> value
val const_call_lambda : value -> value -> value
val const_call_lambda_exn : value -> value -> value -> value
val const_tag : value -> value
val const_equal : value -> value -> value

(******************)
(* Global objects *)
(******************)

val append_global_exn : value -> value -> unit
val define_record : value -> string list -> unit

(*******************)
(* Syntax handling *)
(*******************)

val syntax_arguments : string -> value list -> builder -> value
