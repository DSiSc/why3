(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Why

(*
type prover_data = Session.prover_data
*)

type t =
    { mutable window_width : int;
      mutable window_height : int;
      mutable tree_width : int;
      mutable task_height : int;
      mutable time_limit : int;
      mutable mem_limit : int;
      mutable verbose : int;
      mutable max_running_processes : int;
(*
      mutable provers : prover_data Util.Mstr.t;
*)
      mutable default_editor : string;
      mutable show_labels : bool;
      mutable saving_policy : int;
      mutable env : Why.Env.env;
      mutable config : Whyconf.config;
    }

(*
val get_prover_data : Why.Env.env -> string ->
  Why.Whyconf.config_prover ->
  prover_data Why.Util.Mstr.t -> prover_data Why.Util.Mstr.t
*)

val save_config : unit -> unit

val config : t

val get_main : unit -> Whyconf.main

(***************)
(* boomy icons *)
(***************)

val image_yes : GdkPixbuf.pixbuf ref

(* tree object icons *)
val image_directory : GdkPixbuf.pixbuf ref
val image_file : GdkPixbuf.pixbuf ref
val image_prover : GdkPixbuf.pixbuf ref
val image_transf : GdkPixbuf.pixbuf ref
val image_editor : GdkPixbuf.pixbuf ref
val image_replay : GdkPixbuf.pixbuf ref
val image_cancel : GdkPixbuf.pixbuf ref
val image_reload : GdkPixbuf.pixbuf ref
val image_remove : GdkPixbuf.pixbuf ref
val image_cleaning : GdkPixbuf.pixbuf ref

(* status icons *)
val image_undone : GdkPixbuf.pixbuf ref
val image_scheduled : GdkPixbuf.pixbuf ref
val image_running : GdkPixbuf.pixbuf ref
val image_valid : GdkPixbuf.pixbuf ref
val image_invalid : GdkPixbuf.pixbuf ref
val image_timeout : GdkPixbuf.pixbuf ref
val image_unknown : GdkPixbuf.pixbuf ref
val image_failure : GdkPixbuf.pixbuf ref
val image_valid_obs : GdkPixbuf.pixbuf ref
val image_invalid_obs : GdkPixbuf.pixbuf ref
val image_timeout_obs : GdkPixbuf.pixbuf ref
val image_unknown_obs : GdkPixbuf.pixbuf ref
val image_failure_obs : GdkPixbuf.pixbuf ref

(*************************)
(* miscellaneous dialogs *)
(*************************)

val show_legend_window : unit -> unit
val show_about_window : unit -> unit
val preferences : t -> unit

val run_auto_detection : t -> unit

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3ide.byte"
End:
*)
