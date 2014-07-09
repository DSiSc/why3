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

let fmt = Printf.sprintf

type builder =
  { mutable builder : string list
  ; mutable ident : int
  ; mutable indent_level : int
  }

type value = string

module M = Hashtbl.Make(struct
  type t = string
  let equal = (=)
  let hash = Hashtbl.hash
end)

let header = ref []
let modul = M.create 64
let ident = ref 0

let initial_indent_level = 2

let define_global () =
  { builder = []
  ; ident = 0
  ; indent_level = initial_indent_level
  }

let create_block builder =
  { builder = []
  ; ident = builder.ident
  ; indent_level = builder.indent_level + initial_indent_level
  }

let create_global_fresh_name () =
  let name = fmt "Lambda%d__" !ident in
  incr ident;
  name

let create_fresh_name builder =
  let v = fmt "X%i__" builder.ident in
  builder.ident <- succ builder.ident;
  v

let string_of_builder builder =
  let builder = List.rev builder.builder in
  String.concat "\n" builder

let value_of_string x = x

let string_of_value x = x

let append_global ~name x =
  if not (M.mem modul name) then
    M.add modul name x

let append_function name g =
  let builder = define_global () in
  g builder;
  let x = name ^ "\n" in
  let x = x ^ "{\n" in
  let x = x ^ string_of_builder builder ^ "\n" in
  let x = x ^ "}" in
  append_global ~name x

let append_global ~name ~value =
  append_global ~name (fmt "%s = %s;" name value)

let append_builder x builder =
  let indent = String.make builder.indent_level ' ' in
  builder.builder <- (indent ^ x) :: builder.builder

let append_expr x builder =
  append_builder (x ^ ";") builder

let append_header str =
  header := str :: !header

let define_global name =
  append_header ("value " ^ name ^ ";")

let define_local_var ty name value builder =
  append_builder (fmt "%s %s = %s;" ty name value) builder

let append_block x g builder =
  let builder' = create_block builder in
  g builder';
  append_builder x builder;
  append_builder "{" builder;
  builder.builder <- (string_of_builder builder') :: builder.builder;
  append_builder "}" builder

let init_builder =
  { builder = []
  ; ident = 0
  ; indent_level = initial_indent_level
  }

let to_string () =
  let buf = Buffer.create 64 in
  let aux x =
    Buffer.add_char buf '\n';
    Buffer.add_string buf x;
    Buffer.add_char buf '\n';
  in
  let header = List.rev !header in
  List.iter (fun x -> Buffer.add_string buf x; Buffer.add_string buf "\n") header;
  M.iter (fun x _ -> aux (x ^ ";")) modul;
  Buffer.add_char buf '\n';
  M.iter (fun _ -> aux) modul;
  Buffer.add_char buf '\n';
  Buffer.add_string buf "void __init__()\n";
  Buffer.add_string buf "{\n";
  Buffer.add_string buf (string_of_builder init_builder ^ "\n");
  Buffer.add_string buf "}\n";
  Buffer.contents buf

let () = begin
  append_header "#include <stdlib.h>";
  append_header "#include <stdbool.h>";
  append_header "#include <gc.h>";
  append_header "#include <gmp.h>";
  append_header "";
  append_header "typedef void* value;";
  append_header "typedef char const * exn_tag;";
  append_header "struct variant {int key; value val;};";
  append_header "struct exn {exn_tag key; value val;};";
  append_header "struct closure {value (*f)(value, value*); value* env;};";
  append_header "struct closure_with_exn {value (*f)(value, value*, struct exn **); value* env;};";
  append_header "";
  append_header "struct variant ___False = {0, NULL};";
  append_header "value __False = &___False;";
  append_header "struct variant ___True = {1, NULL};";
  append_header "value __True = &___True;";
  append_header "struct variant ___Tuple0 = {0, NULL};";
  append_header "value why3__Tuple0__Tuple0 = &___Tuple0;";
  append_header "\n";
end

(************************)
(* High-level functions *)
(************************)

let get_closure_name raises =
  if raises then "closure_with_exn" else "closure"

let unit_value = "why3__Tuple0__Tuple0"
let null_value = "NULL"

let create_value value builder =
  let name = create_fresh_name builder in
  define_local_var "value" name value builder;
  name

let create_exn builder =
  let name = create_fresh_name builder in
  define_local_var "struct exn*" name null_value builder;
  name

let create_array size builder =
  let name = create_fresh_name builder in
  append_builder (fmt "value %s[%d] = {NULL};" name size) builder;
  name

let cast_to_closure ~raises value builder =
  let name = create_fresh_name builder in
  let closure = get_closure_name raises in
  define_local_var (fmt "struct %s*" closure) name value builder;
  name

let cast_to_record ~st value builder =
  let name = create_fresh_name builder in
  define_local_var (fmt "struct %s*" st) name value builder;
  name

let malloc_closure ~raises builder =
  let name = create_fresh_name builder in
  let closure = get_closure_name raises in
  define_local_var (fmt "struct %s*" closure) name (fmt "GC_malloc(sizeof(struct %s))" closure) builder;
  name

let malloc_exn builder =
  let name = create_fresh_name builder in
  define_local_var "struct exn*" name "GC_malloc(sizeof(struct exn))" builder;
  name

let malloc_env size builder =
  let name = create_fresh_name builder in
  define_local_var "value*" name (fmt "GC_malloc(sizeof(value) * %d)" size) builder;
  name

let malloc_variant builder =
  let name = create_fresh_name builder in
  define_local_var "struct variant*" name "GC_malloc(sizeof(struct variant))" builder;
  name

let malloc_record st builder =
  let name = create_fresh_name builder in
  define_local_var (fmt "struct %s*" st) name (fmt "GC_malloc(sizeof(struct %s))" st) builder;
  name

let create_lambda ~raises f =
  let name = create_global_fresh_name () in
  let exn = if raises then ", struct exn **Exn__0" else "" in
  let f builder =
    let raise_expr value builder =
      if raises then begin
        append_expr (fmt "*Exn__0 = %s" value) builder;
      end
    in
    let v = f ~raise_expr builder in
    append_expr (fmt "return %s" v) builder
  in
  append_function (fmt "value %s(value Param__0, value* Env__0%s)" name exn) f;
  name

let define_record name fields =
  let fields =
    let aux = fmt "%s  value %s;\n" in
    List.fold_left aux "" fields
  in
  append_header (fmt "struct %s {\n%s};" name fields)

let build_equal x y builder =
  create_value (fmt "%s == %s" x y) builder

let build_store x y builder =
  append_expr (fmt "%s = %s" x y) builder

let build_store_field x field y builder =
  append_expr (fmt "%s->%s = %s" x field y) builder

let build_store_field_int x field y builder =
  append_expr (fmt "%s->%s = %d" x field y) builder
