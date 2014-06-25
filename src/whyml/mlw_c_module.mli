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
val create_array : int -> builder -> value
val create_exn : builder -> value

val malloc_closure : builder -> value
val malloc_exn : builder -> value

val create_lambda :
  raises:bool ->
  (raise_expr:(value -> builder -> unit) -> builder -> value) ->
  value

val create_closure : lambda:value -> env:value -> builder -> value
