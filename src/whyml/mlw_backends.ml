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

module Switch = struct
  type t =
    | OCaml
    | C

  let backend = ref OCaml

  let set = (:=) backend
  let get () = !backend
end

open Switch

let cout_c = ref None

let set_cout_c fmt cout = match !cout_c with
  | None -> cout_c := Some (fmt, cout)
  | Some (fmt_c, cout_c) when fmt_c == fmt && cout_c == cout -> ()
  | Some _ -> assert false

let debug =
  Debug.register_info_flag "extraction"
    ~desc:"Print@ details@ of@ program@ extraction."

let extract_theory driver ?old ?fname formatter cout theory = match !backend with
  | OCaml -> Mlw_ocaml.extract_theory driver ?old ?fname formatter theory
  | C ->
      set_cout_c formatter cout;
      Mlw_c.extract_theory driver ?fname formatter theory

let extract_module driver ?old ?fname formatter cout modul = match !backend with
  | OCaml -> Mlw_ocaml.extract_module driver ?old ?fname formatter modul
  | C ->
      set_cout_c formatter cout;
      Mlw_c.extract_module driver ?fname formatter modul

let finalize () = match !backend, !cout_c with
  | OCaml, _ -> ()
  | C, None -> assert false
  | C, Some (_fmt, cout) ->
      (* The formatter can be usefull if we have toplevel values in the futur *)
      close_out cout
