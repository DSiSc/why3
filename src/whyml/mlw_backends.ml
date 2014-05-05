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

type t =
  | OCaml
  | C

let backend = ref OCaml

let switch_to_c () =
  backend := C

let debug =
  Debug.register_info_flag "extraction"
    ~desc:"Print@ details@ of@ program@ extraction."

let extract_filename ?fname theory = match !backend with
  | OCaml -> Mlw_ocaml.extract_filename ?fname theory
  | C -> assert false

let extract_theory driver ?old ?fname formatter theory = match !backend with
  | OCaml -> Mlw_ocaml.extract_theory driver ?old ?fname formatter theory
  | C -> assert false

let extract_module driver ?old ?fname formatter modul = match !backend with
  | OCaml -> Mlw_ocaml.extract_module driver ?old ?fname formatter modul
  | C -> assert false
