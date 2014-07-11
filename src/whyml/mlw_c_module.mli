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

val append_function : string -> (builder -> unit) -> unit
val append_global : name:string -> value:string -> unit
val define_global : value -> unit
val append_block : string -> (builder -> unit) -> builder -> unit
val append_expr : string -> builder -> unit
val append_header : string -> unit

val create_global_fresh_name : unit -> value

val value_of_string : string -> value
val string_of_value : value -> string

val init_builder : builder

val to_string : unit -> string

(************************)
(* High-level functions *)
(************************)

val unit_value : value
val null_value : value

val create_value : string -> builder -> value
val create_named_value : string -> value -> builder -> value
val create_array : int -> builder -> value
val create_exn : builder -> value

val cast_to_closure : raises:bool -> value -> builder -> value
val cast_to_record : st:value -> value -> builder -> value
val cast_to_variant : value -> builder -> value

val malloc_closure : raises:bool -> builder -> value
val malloc_exn : builder -> value
val malloc_env : int -> builder -> value
val malloc_variant : builder -> value
val malloc_record : value -> builder -> value

val create_lambda :
  param_name:string ->
  raises:bool ->
  (raise_expr:(value -> builder -> unit) -> param:value -> builder -> value) ->
  value

val define_record : value -> string list -> unit

val build_equal : value -> value -> builder -> value
val build_store : value -> value -> builder -> unit
val build_store_field : value -> string -> value -> builder -> unit
val build_store_field_int : value -> string -> int -> builder -> unit
val build_default_case : builder -> unit
val build_case : int -> builder -> unit
val build_break : builder -> unit
