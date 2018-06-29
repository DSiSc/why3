(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Wstdlib

(** Attributes *)

type attribute = {
  attr_string : string;
  attr_tag    : int;
}

module Attr = MakeMSH (struct
  type t = attribute
  let tag a = a.attr_tag
end)

module Sattr = Attr.S
module Mattr = Attr.M

module Hsattr = Hashcons.Make (struct
  type t = attribute
  let equal a1 a2 = a1.attr_string = a2.attr_string
  let hash a = Hashtbl.hash a.attr_string
  let tag n a = { a with attr_tag = n }
end)

let create_attribute s = Hsattr.hashcons {
  attr_string = s;
  attr_tag    = -1
}

let list_attributes () =
  let acc = ref [] in
  Hsattr.iter (fun a -> acc := a.attr_string :: !acc);
  !acc

let attr_equal : attribute -> attribute -> bool = (==)
let attr_hash a = a.attr_tag
let attr_compare a1 a2 = Pervasives.compare a1.attr_tag a2.attr_tag

(** Naming convention *)

let infix  s = "infix "  ^ s
let prefix s = "prefix " ^ s
let mixfix s = "mixfix " ^ s

let kind_of_fix s =
  let len = String.length s in
  if len < 7 then `None else
  let inf = String.sub s 0 6 in
  if inf = "infix "  then `Infix (String.sub s 6 (len - 6)) else
  let prf = String.sub s 0 7 in
  if prf = "prefix " then `Prefix (String.sub s 7 (len - 7)) else
  let prf = String.sub s 0 7 in
  if prf = "mixfix " then `Mixfix (String.sub s 7 (len - 7)) else
  `None


(** Identifiers *)

type string_name = string

let print_name fmt n = Format.fprintf fmt "%s" n

let to_string_name n = n

let name_to_string n = n

let tuple_theory_name s =
  let l = String.length s in
  if l < 6 then None else
  let p = String.sub s 0 5 in
  if p <> "Tuple" then None else
  let q = String.sub s 5 (l - 5) in
  let i = try int_of_string q with _ -> 0 in
  (* we only accept the decimal notation *)
  if q <> string_of_int i then None else
  Some i

(* TODO this does not look very good... *)
let name_concat_prepend (s: string) (name: string_name) =
  match name with
  | _ when Strings.has_prefix "infix " name ->
      s ^ Strings.remove_prefix "infix " name
  | _ when Strings.has_prefix "mixfix " name ->
      s ^ Strings.remove_prefix "mixfix " name
  | _ when Strings.has_prefix "prefix " name ->
      s ^ Strings.remove_prefix "prefix " name
  | _ ->
      s ^ name

let name_concat_append (name: string_name) (s: string) =
  match name with
  | _ when Strings.has_prefix "infix " name ->
      (Strings.remove_prefix "infix " name) ^ s
  | _ when Strings.has_prefix "mixfix " name ->
      (Strings.remove_prefix "mixfix " name) ^ s
  | _ when Strings.has_prefix "prefix " name ->
      (Strings.remove_prefix "prefix " name) ^ s
  | _ ->
      name ^ s

let middle_insertion (name1: string_name) (ins: string) (name2: string_name) =
  name1 ^ ins ^ name2

let check_used (var: string_name) : bool =
  var = "" || var.[0] <> '_'

let is_record_name (s: string_name) =
  Strings.has_prefix "mk " s

type ident = {
  id_string : string_name;          (* non-unique name *)
  id_attrs  : Sattr.t;              (* identifier attributes *)
  id_loc    : Loc.position option;  (* optional location *)
  id_tag    : Weakhtbl.tag;         (* unique magical tag *)
}

module Id = MakeMSHW (struct
  type t = ident
  let tag id = id.id_tag
end)

module Sid = Id.S
module Mid = Id.M
module Hid = Id.H
module Wid = Id.W

type preid = {
  pre_name  : string;
  pre_attrs : Sattr.t;
  pre_loc   : Loc.position option;
}

let id_equal : ident -> ident -> bool = (==)
let id_hash id = Weakhtbl.tag_hash id.id_tag
let id_compare id1 id2 = Pervasives.compare (id_hash id1) (id_hash id2)

(* constructors *)

let id_register = let r = ref 0 in fun id -> {
  id_string = id.pre_name;
  id_attrs  = id.pre_attrs;
  id_loc    = id.pre_loc;
  id_tag    = (incr r; Weakhtbl.create_tag !r);
}

let create_ident name attrs loc = {
  pre_name  = name;
  pre_attrs = attrs;
  pre_loc   = loc;
}

let id_fresh ?(attrs = Sattr.empty) ?loc nm =
  create_ident nm attrs loc

let id_user ?(attrs = Sattr.empty) nm loc =
  create_ident nm attrs (Some loc)

let id_attr id attrs =
  create_ident id.id_string attrs id.id_loc

let id_clone ?(attrs = Sattr.empty) id =
  let aa = Sattr.union attrs id.id_attrs in
  create_ident id.id_string aa id.id_loc

let id_derive ?(attrs = Sattr.empty) nm id =
  let aa = Sattr.union attrs id.id_attrs in
  create_ident nm aa id.id_loc

let preid_name id = id.pre_name

(** Unique names for pretty printing *)

type ident_printer = {
  indices   : int Hstr.t;
  values    : string Hid.t;
  sanitizer : string -> string;
  blacklist : string list;
}

(* name is already sanitized *)
let find_unique indices name =
  let specname ind =
    let rec repeat n s =
      if n <= 0 then s else repeat (n-1) (s ^ "^")
    in
    (* In the case, the symbol is infix/prefix *and* the name has not been
       sanitized for provers (the space " " is still there), we don't want to
       disambiguate with a number but with a symbol: "+" becomes "+." "+.." etc.
       It allows to parse the ident again (for transformations).
    *)
    if Strings.has_prefix "infix " name ||
       Strings.has_prefix "prefix " name then
      (repeat ind name)
    else
      if ind < 0 then
        name
      else
        name ^ string_of_int ind
  in
  let testname ind = Hstr.mem indices (specname ind) in
  let rec advance ind =
    if testname ind then advance (succ ind) else ind in
  let rec retreat ind =
    if ind = 1 || testname (pred ind) then ind else retreat (pred ind) in
  let fetch ind =
    if testname ind then advance (succ ind) else retreat ind in
  let name = try
    let ind = fetch (succ (Hstr.find indices name)) in
    Hstr.replace indices name ind;
    specname ind
  with Not_found -> name in
  Hstr.replace indices name 0;
  name

let reserve indices name = ignore (find_unique indices name)

let same x = x

let create_ident_printer ?(sanitizer = same) sl =
  let indices = Hstr.create 1997 in
  List.iter (reserve indices) sl;
  { indices   = indices;
    values    = Hid.create 1997;
    sanitizer = sanitizer;
    blacklist = sl }

let known_id printer id =
  try
    (let _ = Hid.find printer.values id in true)
  with Not_found ->
    false

let id_unique printer ?(sanitizer = same) id =
  try
    Hid.find printer.values id
  with Not_found ->
    let name = sanitizer (printer.sanitizer id.id_string) in
    let name = find_unique printer.indices name in
    Hid.replace printer.values id name;
    name

let string_unique printer s = find_unique printer.indices s

let forget_id printer id =
  try
    let name = Hid.find printer.values id in
    Hstr.remove printer.indices name;
    Hid.remove printer.values id
  with Not_found -> ()

let forget_all printer =
  Hid.clear printer.values;
  Hstr.clear printer.indices;
  List.iter (reserve printer.indices) printer.blacklist

(** Sanitizers *)

let char_to_alpha c = match c with
  | 'a'..'z' | 'A'..'Z' -> String.make 1 c
  | ' ' -> "sp" | '_'  -> "us" | '#' -> "sh"
  | '`' -> "bq" | '~'  -> "tl" | '!' -> "ex"
  | '@' -> "at" | '$'  -> "dl" | '%' -> "pc"
  | '^' -> "cf" | '&'  -> "et" | '*' -> "as"
  | '(' -> "lp" | ')'  -> "rp" | '-' -> "mn"
  | '+' -> "pl" | '='  -> "eq" | '[' -> "lb"
  | ']' -> "rb" | '{'  -> "lc" | '}' -> "rc"
  | ':' -> "cl" | '\'' -> "qt" | '"' -> "dq"
  | '<' -> "ls" | '>'  -> "gt" | '/' -> "sl"
  | '?' -> "qu" | '\\' -> "bs" | '|' -> "br"
  | ';' -> "sc" | ','  -> "cm" | '.' -> "dt"
  | '0' -> "zr" | '1'  -> "un" | '2' -> "du"
  | '3' -> "tr" | '4'  -> "qr" | '5' -> "qn"
  | '6' -> "sx" | '7'  -> "st" | '8' -> "oc"
  | '9' -> "nn" | '\n' -> "br" |  _  -> "zz"

let char_to_lalpha c = Strings.uncapitalize (char_to_alpha c)
let char_to_ualpha c = Strings.capitalize (char_to_alpha c)

let char_to_alnum c =
  match c with '0'..'9' -> String.make 1 c | _ -> char_to_alpha c

let char_to_lalnum c =
  match c with '0'..'9' -> String.make 1 c | _ -> char_to_lalpha c

let char_to_alnumus c =
  match c with '_' | ' ' -> "_" | _ -> char_to_alnum c

let char_to_lalnumus c =
  match c with '_' | ' ' -> "_" | _ -> char_to_lalnum c

let sanitizer' head rest last n =
  let lst = ref [] in
  let code i c = lst :=
    (if i = 0 then head
     else if i = String.length n - 1 then last
     else rest) c :: !lst in
  let n = if n = "" then "zilch" else n in
  String.iteri code n;
  String.concat "" (List.rev !lst)

let sanitizer head rest n = sanitizer' head rest rest n


(** {2 functions for working with counterexample attributes} *)

let model_attr = create_attribute "model"
let model_projected_attr = create_attribute "model_projected"
let model_vc_attr = create_attribute "model_vc"
let model_vc_post_attr = create_attribute "model_vc_post"
let model_vc_havoc_attr = create_attribute "model_vc_havoc"

let create_model_trace_attr s = create_attribute ("model_trace:" ^ s)

let is_counterexample_attr l =
  l = model_attr || l = model_projected_attr

let has_a_model_attr id =
  Sattr.exists is_counterexample_attr id.id_attrs

let remove_model_attrs ~attrs =
  Sattr.filter (fun l -> not (is_counterexample_attr l)) attrs

let is_model_trace_attr a =
  Strings.has_prefix "model_trace:" a.attr_string

let get_model_trace_attr ~attrs =
  Sattr.choose (Sattr.filter is_model_trace_attr attrs)

let transform_model_trace_attr attrs trans_fun =
  try
    let trace_attr = get_model_trace_attr ~attrs in
    let attrs_without_trace = Sattr.remove trace_attr attrs in
    let new_trace_attr = create_attribute (trans_fun trace_attr.attr_string) in
    Sattr.add new_trace_attr attrs_without_trace
  with Not_found -> attrs

let append_to_model_element_name ~attrs ~to_append =
  let trans attr_str =
    let splitted = Strings.bounded_split '@' attr_str 2 in
    match splitted with
    | [before; after] -> before ^ to_append ^ "@" ^ after
    | _ -> attr_str^to_append in
  transform_model_trace_attr attrs trans

let append_to_model_trace_attr ~attrs ~to_append =
    let trans attr_str = attr_str ^ to_append in
    transform_model_trace_attr attrs trans

let get_model_element_name ~attrs =
  let trace_attr = get_model_trace_attr ~attrs in
  let splitted1 = Strings.bounded_split ':' trace_attr.attr_string 2 in
  match splitted1 with
  | [_; content] ->
    begin
      let splitted2 = Strings.bounded_split '@' content 2 in
      match splitted2 with
      | [el_name; _] -> el_name
      | [el_name] -> el_name
      | _ -> raise Not_found
    end;
  | [_] -> ""
  | _ -> assert false

let get_model_trace_string ~attrs =
  let tl = get_model_trace_attr ~attrs in
  let splitted = Strings.bounded_split ':' tl.attr_string 2 in
  match splitted with
  | [_; t_str] -> t_str
  | _ -> ""


(* Functions for working with ITP attributes *)

let is_name_attr a =
  Strings.has_prefix "name:" a.attr_string

let get_name_attr ~attrs =
  try Some (Sattr.choose (Sattr.filter is_name_attr attrs))
  with Not_found -> None

let get_element_name ~attrs =
  match get_name_attr ~attrs with
  | None -> None
  | Some name_attr ->
    let splitted1 = Strings.bounded_split ':' name_attr.attr_string 2 in
    let correct_word = Str.regexp "^\\([A-Za-z]+\\)\\([A-Za-z0-9_']*\\)$" in
    match splitted1 with
    | ["name"; content] when Str.string_match correct_word content 0 ->
        Some content
    | _ -> None

let id_unique_attr printer ?(sanitizer = same) id =
  try
    Hid.find printer.values id
  with Not_found ->
    let attrs = id.id_attrs in
    let name =
      match (get_element_name ~attrs) with
      | Some x -> x
      | None -> printer.sanitizer id.id_string
    in
    let name = sanitizer name in
    let name = find_unique printer.indices name in
    Hid.replace printer.values id name;
    name
