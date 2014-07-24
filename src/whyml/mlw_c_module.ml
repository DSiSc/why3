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
  ; mutable ident : Ident.ident_printer
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

let c_keywords =
  [ "auto"; "break"; "case"; "char"; "const"; "continue"; "default"; "do"
  ; "double"; "else"; "enum"; "extern"; "float"; "for"; "goto"; "if"; "int"
  ; "long"; "register"; "return"; "short"; "signed"; "sizeof"; "static"
  ; "struct"; "switch"; "typedef"; "union"; "unsigned"; "void"; "volatile"
  ; "while"
  ]

let define_global_builder () =
  { builder = []
  ; ident = Ident.create_ident_printer c_keywords
  ; indent_level = initial_indent_level
  }

let create_block builder =
  { builder = []
  ; ident = builder.ident
  ; indent_level = builder.indent_level + initial_indent_level
  }

let create_global_fresh_name () =
  let name = fmt "Lambda%d" !ident in
  incr ident;
  name

let create_fresh_name ?(name = "X") builder =
  Ident.string_unique builder.ident name

let string_of_builder builder =
  let builder = List.rev builder.builder in
  String.concat "\n" builder

let value_of_string x = x

let string_of_value x = x

let append_global ~name x =
  if not (M.mem modul name) then
    M.add modul name x

let append_function name g =
  let builder = define_global_builder () in
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
  define_global_builder ()

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
  Buffer.add_string buf "void Init()\n";
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
  append_header "struct variant {int key; value* val;};";
  append_header "struct exn {exn_tag key; value val;};";
  append_header "struct closure {value (*f)(value, value*); value* env;};";
  append_header "struct closure_with_exn {value (*f)(value, value*, struct exn **); value* env;};";
  append_header "";
  append_header "struct variant ___False = {0, NULL};";
  append_header "value why3__Bool__False = &___False;";
  append_header "struct variant ___True = {1, NULL};";
  append_header "value why3__Bool__True = &___True;";
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
let true_value = "why3__Bool__True"
let false_value = "why3__Bool__False"

let create_value value builder =
  let name = create_fresh_name builder in
  define_local_var "value" name value builder;
  name

let create_named_value name value builder =
  let name = create_fresh_name ~name builder in
  define_local_var "value" name value builder;
  name

let create_exn builder =
  let name = create_fresh_name builder in
  define_local_var "struct exn*" name null_value builder;
  name

let create_mpz str base builder =
  let name = create_fresh_name builder in
  append_expr (fmt "mpz_t %s" name) builder;
  append_expr (fmt "mpz_init_set_str(%s, %S, %d)" name str base) builder;
  name

let create_array size builder =
  let name = create_fresh_name builder in
  append_builder (fmt "value %s[%d] = {NULL};" name size) builder;
  name

let clone_value = create_value

let clone_mpz value builder =
  let name = create_fresh_name builder in
  append_expr (fmt "mpz_t %s" name) builder;
  append_expr (fmt "mpz_init_set(%s, %s)" name value) builder;
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

let cast_to_variant value builder =
  let name = create_fresh_name builder in
  define_local_var "struct variant*" name value builder;
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

let malloc_env size builder = match size with
  | 0 ->
      null_value
  | size ->
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

let create_lambda ~param_name ~raises f =
  let name = create_global_fresh_name () in
  let exn = if raises then ", struct exn **Exn" else "" in
  let f builder =
    if Ident.string_unique builder.ident param_name <> param_name then
      assert false;
    if Ident.string_unique builder.ident "Env" <> "Env" then
      assert false;
    if Ident.string_unique builder.ident "Exn" <> "Exn" then
      assert false;
    let raise_expr value builder =
      if raises then begin
        append_expr (fmt "*Exn = %s" value) builder;
      end else begin
        append_expr "abort()" builder;
      end
    in
    let v = f ~raise_expr ~param:param_name builder in
    append_expr (fmt "return %s" v) builder
  in
  append_function (fmt "value %s(value %s, value* Env%s)" name param_name exn) f;
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

let build_break =
  append_expr "break"

let build_if_not_null v f builder =
  append_block (fmt "if(%s != NULL)" v) f builder

let build_if_true v f builder =
  append_block (fmt "if(%s == %s)" v true_value) f builder

let build_if_false v f builder =
  append_block (fmt "if(%s == %s)" v false_value) f builder

let build_if_cmp_zero cmp signe f =
  append_block (fmt "if(%s %s 0)" cmp signe) f

let build_else f =
  append_block "else" f

let build_access_field v field builder =
  create_value (fmt "%s->%s" v field) builder

let build_not v builder =
  create_value
    (fmt "((struct variant*)(%s)->key) ? %s : %s" v false_value true_value)
    builder

let build_do_while f builder =
  append_block "do" f builder;
  append_expr "while(false)" builder

let build_abort =
  append_expr "abort()"

let build_switch e l =
  let aux builder = function
    | (None, f) ->
        append_block "default: " f builder;
        build_break builder;
    | (Some i, f) ->
        append_block (fmt "case %d: " i) f builder;
        build_break builder;
  in
  append_block
    (fmt "switch(%s->key)" e)
    (fun builder -> List.iter (aux builder) l)

let build_while f =
  append_block "while(true)" f

let build_mpz_cmp x y builder =
  let name = create_fresh_name builder in
  define_local_var "int" name (fmt "mpz_cmp(%s, %s)" x y) builder;
  name

let build_mpz_succ value =
  append_expr (fmt "mpz_add_ui(%s, %s, 1)" value value)
