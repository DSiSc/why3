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

let debug =
  Debug.register_info_flag "extraction"
    ~desc:"Print@ details@ of@ program@ extraction."

let switch driver =
  match driver.Mlw_driver.drv_printer with
  | Some "ocaml" -> OCaml
  | Some "c" -> C
  | Some name -> Loc.errorm "Unknown printer '%s'" name
  | None -> Loc.errorm "No printer name specified"

let extract_filename driver ?fname th =
  match switch driver with
  | OCaml -> Mlw_ocaml.extract_filename ?fname th
  | C -> Mlw_c.extract_filename ?fname th

let extract_theory driver ?old ?fname formatter theory =
  match switch driver with
  | OCaml -> Mlw_ocaml.extract_theory driver ?old ?fname formatter theory
  | C -> Mlw_c.extract_theory driver ?fname formatter theory

let extract_module driver ?old ?fname formatter modul =
  match switch driver with
  | OCaml -> Mlw_ocaml.extract_module driver ?old ?fname formatter modul
  | C -> Mlw_c.extract_module driver ?fname formatter modul
