(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
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

(** Proof database *)

(** {2 data types} *)

type file
(** a database contains a (ordered?) set of files *)

type theory
(** each files contains an ordered sequence of theories *)

type goal
(** each theory contains an ordered sequences of goals *)

type proof_attempt 
(** each goal has a set of proof attempts, indeed a map indexed
    by provers *)

type transf
(** each goal also has a set of transformations, indeed a map indexed
    by transformation names *)

type prover
(** a prover *)

(** status of an external proof attempt *)
type proof_status =
  | Success (** external proof attempt succeeded *)
  | Timeout (** external proof attempt was interrupted *)
  | Unknown (** external prover answered ``don't know'' or equivalent *)
  | Failure (** external prover call failed *)

(** parent of a goal: either a theory (for "toplevel" goals) 
    or a transformation (for "subgoals") *)
(* useful ?
type goal_parent =
  | Theory of theory
  | Transf of transf
*)

(** {2 accessors} *)

(** prover accessors *)
val prover_id : prover -> string

(** proof_attempt accessors *)
val prover : proof_attempt -> prover
(*
val proof_goal : proof_attempt -> goal
*)
val status : proof_attempt -> proof_status
val proof_obsolete : proof_attempt -> bool
val time : proof_attempt -> float
val edited_as : proof_attempt -> string

(** goal accessors *)
(*
val parent : goal -> goal_parent
*)
val task_checksum : goal -> string (** checksum *)
val proved : goal -> bool
val external_proofs: (string, proof_attempt) Hashtbl.t
val transformations : (string, transf) Hashtbl.t

(** transf accessors *)
(*
val parent_goal : transf -> goal
*)
val transf_name : transf -> string
val subgoals : transf -> goal list

(** theory accessors *)        
val theory_name : theory -> string
val goals : theory -> goal list
val verified : theory -> bool

(** file accessors *)
val file_name : file -> string
val theories : file -> theory list

(** {2 The persistent database} *)

val init_base : string -> unit
(** opens or creates the current database, from given file name *)

val files : unit -> file list
(** returns the current set of files *)


(** {2 Updates} *)

exception AlreadyExist

(** {3 provers} *)
val prover_from_id : string -> prover
(** retrieves existing prover data from its name.
    creates prover data if not existing yet *)

(** {3 external proof attempts} *)

val add_proof_attempt : goal -> prover -> proof_attempt
(** adds a proof attempt for this prover, with status is set to Unknown.
    @raise AlreadyExist if an attempt for the same prover
    is already there *)

(* todo: remove_proof_attempt *)

val set_status : proof_attempt -> proof_status -> float -> unit
(** sets the proof status for this prover, and its time.
*)

val set_obsolete : proof_attempt -> unit
(** marks this proof as obsolete *)

val set_edited_as : proof_attempt -> string -> unit
(** sets the file name where this proof can be edited *)

(** {3 transformations} *)

val add_transformation : goal -> string -> goal list -> transf
(** adds a transformation for this goal, with the given subgoals
    @raise AlreadyExist if a transformation with the same name
    is already there *)

(* todo: remove_transformation *)

(** {3 goals} *)

val add_goal : theory -> string -> string -> goal
(** [add_goal th id sum] adds to theory [th] a new goal named [id], with
    [sum] as the checksum of its task. 
    @raise AlreadyExist if a goal with the same id already exists
    in this theory *)

(* todo: remove_goal *)

(** {3 theories} *)

val add_theory : file -> string -> string -> unit
(** [add_goal th id sum] adds to theory [th] a new goal named [id], with
    [sum] as the checksum of its task.
    @raise AlreadyExist if a goal with the same id already exists
    in this theory *)

(* todo: remove_theory *)


(** {3 files} *)

val add_file :  string -> file
(** adds a file to the database.
    @raise AlreadyExist if a file with the same id already exists *)

(* todo: remove_file *)





  
