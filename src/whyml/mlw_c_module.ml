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

type builder = line list ref

and line =
  | Text of string
  | Block of (string * builder)

type global =
  | Global of string
  | Function of (string * builder)

type value = string

let c_keywords =
  [ "auto"; "break"; "case"; "char"; "const"; "continue"; "default"; "do"
  ; "double"; "else"; "enum"; "extern"; "float"; "for"; "goto"; "if"; "int"
  ; "long"; "register"; "return"; "short"; "signed"; "sizeof"; "static"
  ; "struct"; "switch"; "typedef"; "union"; "unsigned"; "void"; "volatile"
  ; "while"
  ]

let header = ref []
let modul = Hashtbl.create 64
let printer = Ident.create_ident_printer c_keywords

let id_unique = function
  | Some id -> Ident.id_unique printer id
  | None -> Ident.string_unique printer "X__"

let value_of_string x = x

let append_global ~name x =
  if not (Hashtbl.mem modul name) then
    Hashtbl.add modul name x

let append_function name g =
  let builder = ref [] in
  g builder;
  append_global ~name (Function (name, builder))

let append_global ~name ~value =
  append_global ~name (Global (fmt "%s = %s" name value))

let append_expr x builder =
  builder := Text x :: !builder

let append_header str =
  header := str :: !header

let define_global name =
  append_header ("value " ^ name)

let define_local_var ty name value builder =
  append_expr (fmt "%s %s = %s" ty name value) builder

let append_block x g builder =
  let builder' = ref [] in
  g builder';
  builder := Block (x, builder') :: !builder

let init_builder = ref []

let dump_builder buf builder =
  let indent_level = 2 in
  let add_string indent str =
    Buffer.add_string buf (String.make indent ' ');
    Buffer.add_string buf str;
  in
  let rec aux indent = function
    | Text s ->
        add_string indent s;
        Buffer.add_string buf ";\n";
    | Block (s, builder) ->
        add_string indent s;
        Buffer.add_char buf '\n';
        add_string indent "{\n";
        let builder = List.rev !builder in
        List.iter (aux (indent + indent_level)) builder;
        add_string indent "}\n";
  in
  let builder = List.rev !builder in
  List.iter (aux indent_level) builder

let dump_global buf = function
  | Global s ->
      Buffer.add_char buf '\n';
      Buffer.add_string buf s;
      Buffer.add_string buf ";\n";
  | Function (s, builder) ->
      Buffer.add_char buf '\n';
      Buffer.add_string buf s;
      Buffer.add_string buf "\n{\n";
      dump_builder buf builder;
      Buffer.add_string buf "}\n"

let to_string () =
  let buf = Buffer.create 4096 in
  let aux x =
    Buffer.add_char buf '\n';
    Buffer.add_string buf x;
    Buffer.add_char buf ';';
  in
  let header = List.rev !header in
  Buffer.add_string buf "#include \"why3.c\"\n";
  List.iter aux header;
  Buffer.add_char buf '\n';
  Hashtbl.iter (fun x _ -> aux x) modul;
  Buffer.add_char buf '\n';
  Hashtbl.iter (fun _ -> dump_global buf) modul;
  Buffer.add_char buf '\n';
  Buffer.add_string buf "void Init()\n";
  Buffer.add_string buf "{\n";
  dump_builder buf init_builder;
  Buffer.add_string buf "}\n";
  Buffer.contents buf

(************************)
(* High-level functions *)
(************************)

let get_closure_name raises =
  if raises then "closure_with_exn" else "closure"

let unit_value = "why3__Tuple0__Tuple0"
let null_value = "NULL"
let true_value = "why3__Bool__True"
let false_value = "why3__Bool__False"
let env_value = "Env"

let create_value value builder =
  let name = id_unique None in
  define_local_var "value" name value builder;
  name

let create_named_value id value builder =
  let name = id_unique (Some id) in
  define_local_var "value" name value builder;
  name

let create_exn builder =
  let name = id_unique None in
  define_local_var "struct exn*" name null_value builder;
  name

let create_mpz str base builder =
  let name = id_unique None in
  append_expr (fmt "mpz_t %s" name) builder;
  append_expr (fmt "mpz_init_set_str(%s, %S, %d)" name str base) builder;
  name

let create_array size builder =
  let name = id_unique None in
  append_expr (fmt "value %s[%d] = {NULL}" name size) builder;
  name

let clone_mpz value builder =
  let name = id_unique None in
  append_expr (fmt "mpz_t %s" name) builder;
  append_expr (fmt "mpz_init_set(%s, %s)" name value) builder;
  name

let cast_to_closure ~raises value builder =
  let name = id_unique None in
  let closure = get_closure_name raises in
  define_local_var (fmt "struct %s*" closure) name value builder;
  name

let cast_to_record ~st value builder =
  let name = id_unique None in
  define_local_var (fmt "struct %s*" st) name value builder;
  name

let cast_to_variant value builder =
  let name = id_unique None in
  define_local_var "struct variant*" name value builder;
  name

let malloc_closure ~raises builder =
  let name = id_unique None in
  let closure = get_closure_name raises in
  define_local_var (fmt "struct %s*" closure) name (fmt "GC_malloc(sizeof(struct %s))" closure) builder;
  name

let malloc_exn builder =
  let name = id_unique None in
  define_local_var "struct exn*" name "GC_malloc(sizeof(struct exn))" builder;
  name

let malloc_env size builder = match size with
  | 0 ->
      null_value
  | size ->
      let name = id_unique None in
      define_local_var "value*" name (fmt "GC_malloc(sizeof(value) * %d)" size) builder;
      name

let malloc_variant builder =
  let name = id_unique None in
  define_local_var "struct variant*" name "GC_malloc(sizeof(struct variant))" builder;
  name

let malloc_record st builder =
  let name = id_unique None in
  define_local_var (fmt "struct %s*" st) name (fmt "GC_malloc(sizeof(struct %s))" st) builder;
  name

let create_lambda ~param ~raises f =
  let name = id_unique None in
  let param = id_unique (Some param) in
  let exn = if raises then ", struct exn **Exn" else "" in
  let f builder =
    let raise_expr value builder =
      if raises then begin
        append_expr (fmt "*Exn = %s" value) builder;
      end else begin
        append_expr "abort()" builder;
      end
    in
    let v = f ~raise_expr ~param builder in
    append_expr (fmt "return %s" v) builder
  in
  append_function (fmt "value %s(value %s, value* Env%s)" name param exn) f;
  name

let define_record name fields =
  let fields =
    let aux = fmt "%s value %s;\n" in
    List.fold_left aux "" fields
  in
  append_header (fmt "struct %s {\n%s}" name fields)

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

let build_if cmp f =
  append_block (fmt "if(%s)" cmp) f

let build_else_if cmp f =
  append_block (fmt "else if(%s)" cmp) f

let build_else f =
  append_block "else" f

let build_if_else_if_else l else_case builder =
  let aux (cond, f) = build_else_if cond f builder in
  match l with
  | [] -> else_case builder
  | (cmp, f)::xs ->
      build_if cmp f builder;
      List.iter aux xs;
      build_else else_case builder

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
  let name = id_unique None in
  define_local_var "int" name (fmt "mpz_cmp(%s, %s)" x y) builder;
  name

let build_mpz_succ value =
  append_expr (fmt "mpz_add_ui(%s, %s, 1)" value value)

let const_access_field = fmt "%s->%s"

let const_access_array = fmt "%s[%d]"

let const_call_lambda closure param =
  fmt "(%s->f)(%s, %s->env)" closure param closure

let const_call_lambda_exn closure param exn =
  fmt "(%s->f)(%s, %s->env, &%s)" closure param closure exn

let const_tag = fmt "tag_%s"

let const_equal = fmt "%s == %s"

let append_global_exn name value =
  append_global ~name:(fmt "exn_tag %s" name) ~value:(fmt "\"%s\"" value)
