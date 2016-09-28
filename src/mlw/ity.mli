(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2016   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ident
open Ty
open Term

(** {2 Individual types (first-order types without effects)} *)

type itysymbol = private {
  its_ts      : tysymbol;       (** logical type symbol *)
  its_nonfree : bool;           (** has an invariant *)
  its_private : bool;           (** private type *)
  its_mutable : bool;           (** mutable type *)
  its_mfields : pvsymbol list;  (** mutable record fields *)
  its_regions : region list;    (** shareable components *)
  its_arg_imm : bool list;      (** non-updatable parameters *)
  its_arg_exp : bool list;      (** exposed type parameters *)
  its_arg_vis : bool list;      (** non-ghost type parameters *)
  its_arg_frz : bool list;      (** irreplaceable parameters *)
  its_reg_imm : bool list;      (** non-updatable components *)
  its_reg_exp : bool list;      (** exposed shareable components *)
  its_reg_vis : bool list;      (** non-ghost shareable components *)
  its_reg_frz : bool list;      (** irreplaceable shareable components *)
  its_def     : ity option;     (** type alias *)
}

and ity = private {
  ity_node : ity_node;
  ity_imm  : bool;
  ity_tag  : Weakhtbl.tag;
}

and ity_node = private
  | Ityreg of region
    (** record with mutable fields and shareable components *)
  | Ityapp of itysymbol * ity list * ity list
    (** immutable type with shareable components *)
  | Ityvar of tvsymbol * bool
    (** type variable and its purity status *)

and region = private {
  reg_name : ident;
  reg_its  : itysymbol;
  reg_args : ity list;
  reg_regs : ity list;
}

and pvsymbol = private {
  pv_vs    : vsymbol;
  pv_ity   : ity;
  pv_ghost : bool;
}

module Mits : Extmap.S with type key = itysymbol
module Sits : Extset.S with module M = Mits
module Hits : Exthtbl.S with type key = itysymbol
module Wits : Weakhtbl.S with type key = itysymbol

module Mity : Extmap.S with type key = ity
module Sity : Extset.S with module M = Mity
module Hity : Exthtbl.S with type key = ity
module Wity : Weakhtbl.S with type key = ity

module Mreg : Extmap.S with type key = region
module Sreg : Extset.S with module M = Mreg
module Hreg : Exthtbl.S with type key = region
module Wreg : Weakhtbl.S with type key = region

module Mpv  : Extmap.S with type key = pvsymbol
module Spv  : Extset.S with module M = Mpv
module Hpv  : Exthtbl.S with type key = pvsymbol
module Wpv  : Weakhtbl.S with type key = pvsymbol

val its_compare : itysymbol -> itysymbol -> int
val ity_compare : ity -> ity -> int
val reg_compare : region -> region -> int
val pv_compare  : pvsymbol -> pvsymbol -> int

val its_equal : itysymbol -> itysymbol -> bool
val ity_equal : ity -> ity -> bool
val reg_equal : region -> region -> bool
val pv_equal  : pvsymbol -> pvsymbol -> bool

val its_hash : itysymbol -> int
val ity_hash : ity -> int
val reg_hash : region -> int
val pv_hash  : pvsymbol -> int

exception DuplicateRegion of region
exception UnboundRegion of region

(** creation of a type symbol in programs *)

val create_plain_record_itysymbol : priv:bool -> mut:bool ->
  preid -> tvsymbol list -> bool Mpv.t -> term list -> itysymbol
(** [create_plain_record_itysymbol ~priv ~mut id args fields inv] creates
    a new type symbol for a non-recursive record type, possibly private
    or mutable. Every known field is represented by a [pvsymbol] mapped
    to its mutability status in [fields]. Variables corresponding to
    mutable fields are stored in the created type symbol and used in
    effects. The [priv] flag should be set to [true] for private records.
    The [mut] flag should be set to [true] to mark the new type as mutable
    even if it does not have known mutable fields. The [inv] parameter
    contains the list of invariant formulas that may only depend on
    variables from [fields]. Abstract types are considered to be private
    immutable records with no fields. *)

val create_plain_variant_itysymbol :
  preid -> tvsymbol list -> Spv.t list -> itysymbol
(** [create_plain_variant_itysymbol id args fields] creates a new type
    symbol for a non-recursive algebraic type. *)

val create_rec_itysymbol : preid -> tvsymbol list -> itysymbol
(** [create_rec_itysymbol id args] creates a new type symbol for
    a recursively defined type. *)

val create_alias_itysymbol : preid -> tvsymbol list -> ity -> itysymbol
(** [create_alias_itysymbol id args def] creates a new type alias. *)

val restore_its : tysymbol -> itysymbol
(** raises [Not_found] if the argument is not a [its_ts] *)

(* {2 Basic properties} *)

val its_immutable : itysymbol -> bool
(** an immutable type symbol is not a mutable record nor an alias for one *)

val its_pure : itysymbol -> bool
(** a pure type symbol is immutable and has no mutable components *)

val ity_immutable : ity -> bool
(** an immutable type contains no regions (returns the [ity_imm] field) *)

val ity_pure : ity -> bool
(** a pure type is immutable and all type variables in it are pure *)

val ity_closed : ity -> bool
(** a closed type contains no type variables *)

(** {2 Type constructors} *)

exception BadItyArity of itysymbol * int
exception BadRegArity of itysymbol * int

val create_region : preid -> itysymbol -> ity list -> ity list -> region
(** [create_region id s tl rl] creates a fresh region.
    Type symbol [s] must be a mutable record or an alias for one.
    If [rl] is empty, fresh subregions are created when needed. *)

val ity_app : itysymbol -> ity list -> ity list -> ity
(** [ity_app s tl rl] creates
    - an [Ityapp] type, if [s] is immutable, or
    - an [Ityreg] type on top of a fresh region, otherwise.
    If [rl] is empty, fresh subregions are created when needed. *)

val ity_app_pure : itysymbol -> ity list -> ity list -> ity
(** [ity_app s tl rl] creates an [Ityapp] type.
    If [rl] is empty, pure snapshots are substituted when needed. *)

val ity_reg : region -> ity

val ity_var : tvsymbol -> ity

val ity_var_pure : tvsymbol -> ity

val ity_purify : ity -> ity
(** replaces regions with pure snapshots and variables with pure variables. *)

val ity_of_ty : ty -> ity
(** fresh regions are created when needed and all variables are impure.
    Raises [Invalid_argument] for any non-its tysymbol. *)

val ity_of_ty_pure : ty -> ity
(** pure snapshots are substituted when needed and all variables are pure.
    Raises [Invalid_argument] for any non-its tysymbol. *)

val ty_of_ity : ity -> ty

(** {2 Generic traversal functions} *)

val ity_fold : ('a -> ity -> 'a) -> 'a -> ity -> 'a
val reg_fold : ('a -> ity -> 'a) -> 'a -> region -> 'a

(** {2 Traversal functions on type symbols} *)

val ity_s_fold : ('a -> itysymbol -> 'a) -> 'a -> ity -> 'a
val reg_s_fold : ('a -> itysymbol -> 'a) -> 'a -> region -> 'a

(** {2 Traversal functions on type variables} *)

val ity_v_fold : ('a -> tvsymbol -> 'a) -> 'a -> ity -> 'a
val reg_v_fold : ('a -> tvsymbol -> 'a) -> 'a -> region -> 'a

val ity_freevars : Stv.t -> ity -> Stv.t
val reg_freevars : Stv.t -> region -> Stv.t

val ity_v_occurs : tvsymbol -> ity -> bool
val reg_v_occurs : tvsymbol -> region -> bool

(** {2 Traversal functions on top regions} *)

val ity_r_fold : ('a -> region -> 'a) -> 'a -> ity -> 'a
val reg_r_fold : ('a -> region -> 'a) -> 'a -> region -> 'a

val ity_freeregs : Sreg.t -> ity -> Sreg.t
val reg_freeregs : Sreg.t -> region -> Sreg.t

val ity_r_occurs : region -> ity -> bool
val reg_r_occurs : region -> region -> bool

(** {2 Traversal functions on exposed and reachable regions} *)

val ity_exp_fold : ('a -> region -> 'a) -> 'a -> ity -> 'a
val reg_exp_fold : ('a -> region -> 'a) -> 'a -> region -> 'a

val ity_rch_fold : ('a -> region -> 'a) -> 'a -> ity -> 'a
val reg_rch_fold : ('a -> region -> 'a) -> 'a -> region -> 'a

val ity_r_reachable : region -> ity -> bool
val reg_r_reachable : region -> region -> bool

val ity_r_stale : Sreg.t -> Sreg.t -> ity -> bool
val reg_r_stale : Sreg.t -> Sreg.t -> region -> bool

(** {2 Built-in types} *)

val ts_unit : tysymbol (** the same as [Ty.ts_tuple 0] *)
val ty_unit : ty

val its_int  : itysymbol
val its_real : itysymbol
val its_bool : itysymbol
val its_unit : itysymbol
val its_func : itysymbol

val ity_int  : ity
val ity_real : ity
val ity_bool : ity
val ity_unit : ity
val ity_func : ity -> ity -> ity
val ity_pred : ity -> ity (* ity_pred 'a == ity_func 'a ity_bool *)

val its_tuple : int -> itysymbol
val ity_tuple : ity list -> ity

(** {2 Type matching and instantiation} *)

type ity_subst = private {
  isb_var : ity Mtv.t;
  isb_pur : ity Mtv.t;
  isb_reg : ity Mreg.t;
}

exception TypeMismatch of ity * ity * ity_subst
exception ImpureType of tvsymbol * ity

val isb_empty : ity_subst

val ity_match : ity_subst -> ity -> ity -> ity_subst
val reg_match : ity_subst -> region -> ity -> ity_subst

val its_match_args : itysymbol -> ity list -> ity_subst
val its_match_regs : itysymbol -> ity list -> ity list -> ity_subst

val ity_freeze : ity_subst -> ity -> ity_subst (* self-match *)
val reg_freeze : ity_subst -> region -> ity_subst (* self-match *)

val ity_equal_check : ity -> ity -> unit
val reg_equal_check : region -> region -> unit

val ity_full_inst : ity_subst -> ity -> ity
val reg_full_inst : ity_subst -> region -> ity

(** {2 Program variables} *)

val create_pvsymbol : preid -> ?ghost:bool -> ity -> pvsymbol

val restore_pv : vsymbol -> pvsymbol
(** raises [Not_found] if the argument is not a [pv_vs] *)

val t_freepvs : Spv.t -> term -> Spv.t
(** raises [Not_found] if the term contains a free variable
    which is not a [pv_vs] *)

val pvs_of_vss : Spv.t -> 'a Mvs.t -> Spv.t

(** {2 Exception symbols} *)

type mask =
  | MaskVisible
  | MaskTuple of mask list
  | MaskGhost

val mask_ghost : mask -> bool

val mask_of_pv : pvsymbol -> mask

val mask_union : mask -> mask -> mask

val mask_equal : mask -> mask -> bool

val mask_spill : mask -> mask -> bool

type xsymbol = private {
  xs_name : ident;
  xs_ity  : ity; (** closed and immutable *)
  xs_mask : mask;
}

module Mexn : Extmap.S with type key = xsymbol
module Sexn : Extset.S with module M = Mexn

val xs_compare : xsymbol -> xsymbol -> int
val xs_equal : xsymbol -> xsymbol -> bool
val xs_hash : xsymbol -> int

val create_xsymbol : preid -> ?mask:mask -> ity -> xsymbol

(** {2 Effects} *)

exception IllegalSnapshot of ity
exception IllegalAlias of region
exception AssignPrivate of region
exception IllegalUpdate of pvsymbol * region
exception StaleVariable of pvsymbol * region
exception BadGhostWrite of pvsymbol * region
exception DuplicateField of region * pvsymbol
exception IllegalAssign of region * region * region
exception GhostDivergence

type effect = private {
  eff_reads  : Spv.t;         (* known variables *)
  eff_writes : Spv.t Mreg.t;  (* writes to fields *)
  eff_taints : Sreg.t;        (* ghost code writes *)
  eff_covers : Sreg.t;        (* surviving writes *)
  eff_resets : Sreg.t;        (* locked by covers *)
  eff_raises : Sexn.t;        (* raised exceptions *)
  eff_oneway : bool;          (* non-termination *)
  eff_ghost  : bool;          (* ghost status *)
}

val eff_empty : effect

val eff_equal : effect -> effect -> bool
val eff_pure : effect -> bool

val eff_read : Spv.t -> effect
val eff_write : Spv.t -> Spv.t Mreg.t -> effect (* drops writes outside reads *)
val eff_assign : (pvsymbol * pvsymbol * pvsymbol) list -> effect (* r,field,v *)

val eff_read_pre  : Spv.t -> effect -> effect (* no stale-variable check *)
val eff_read_post : effect -> Spv.t -> effect (* checks for stale variables *)
val eff_bind      : Spv.t -> effect -> effect (* removes variables from reads *)

val eff_read_single      : pvsymbol -> effect
val eff_read_single_pre  : pvsymbol -> effect -> effect
val eff_read_single_post : effect -> pvsymbol -> effect
val eff_bind_single      : pvsymbol -> effect -> effect

val eff_reset : effect -> Sreg.t -> effect    (* confine to an empty cover *)
val eff_reset_overwritten : effect -> effect  (* confine regions under writes *)

val eff_raise : effect -> xsymbol -> effect
val eff_catch : effect -> xsymbol -> effect

val eff_diverge : effect -> effect                (* forbidden if ghost *)
val eff_ghostify : bool -> effect -> effect       (* forbidden if diverges *)
val eff_ghostify_weak : bool -> effect -> effect  (* only if has no effect *)

val eff_union_seq : effect -> effect -> effect  (* checks for stale variables *)
val eff_union_par : effect -> effect -> effect  (* no stale-variable check *)

val mask_adjust : effect -> ity -> mask -> mask

(** {2 Computation types (higher-order types with effects)} *)

type pre = term   (** precondition: pre_fmla *)
type post = term  (** postcondition: eps result . post_fmla *)

val open_post : post -> vsymbol * term
val open_post_with : term -> post -> term

val create_post : vsymbol -> term -> post

type cty = private {
  cty_args   : pvsymbol list;
  cty_pre    : pre list;
  cty_post   : post list;
  cty_xpost  : post list Mexn.t;
  cty_oldies : pvsymbol Mpv.t;
  cty_effect : effect;
  cty_result : ity;
  cty_mask   : mask;
  cty_freeze : ity_subst;
}

val create_cty : ?mask:mask -> pvsymbol list ->
  pre list -> post list -> post list Mexn.t ->
  pvsymbol Mpv.t -> effect -> ity -> cty
(** [create_cty ?mask args pre post xpost oldies effect result] creates
    a computation type. [post] and [mask] must be consistent with [result].
    The [cty_xpost] field does not have to cover all raised exceptions.
    [cty_effect.eff_reads] is completed wrt the specification and [args].
    [cty_freeze] freezes every unbound pvsymbol in [cty_effect.eff_reads].
    All effects on regions outside [cty_effect.eff_reads] are removed.
    Fresh regions in [result] are reset. Every type variable in [pre],
    [post], and [xpost] must come from [cty_reads], [args] or [result].
    [oldies] maps ghost pure snapshots of the parameters and external
    reads to the original pvsymbols: these snapshots are removed from
    [cty_effect.eff_reads] and replaced with the originals. *)

val cty_apply : cty -> pvsymbol list -> ity list -> ity -> cty
(** [cty_apply cty pvl rest res] instantiates [cty] up to the types in
    [pvl], [rest], and [res], then applies it to the arguments in [pvl],
    and returns the computation type of the result, [rest -> res],
    with every type variable and region in [pvl] being frozen. *)

val cty_tuple : pvsymbol list -> cty
(** [cty_tuple pvl] returns a nullary tuple-valued cty with
    an appropriate [cty_mask]. *)

val cty_exec : cty -> cty
(** [cty_exec cty] converts a cty of a partial application into
    a cty of a fully applied application, returning a mapping.
    The original cty must be effectless. *)

val cty_exec_post : cty -> post list
(** [cty_exec_post cty] returns a post-condition appropriate
    for use with local let-functions in VC generation. *)

val cty_ghost : cty -> bool
(** [cty_ghost cty] returns [cty.cty_effect.eff_ghost] *)

val cty_pure : cty -> bool
(** [cty_pure cty] verifies that [cty] has no side effects
    except allocations. *)

val cty_ghostify : bool -> cty -> cty
(** [cty_ghostify ghost cty] ghostifies the effect of [cty]. *)

val cty_reads : cty -> Spv.t
(** [cty_reads cty] returns the set of external dependencies of [cty]. *)

val cty_read_pre : Spv.t -> cty -> cty
(** [cty_read_pre pvs cty] adds [pvs] to [cty.cty_effect.eff_reads].
    This function performs capture: if some variables in [pvs] occur
    in [cty.cty_args], they are not frozen. *)

val cty_read_post : cty -> Spv.t -> cty
(** [cty_read_post cty pvs] adds [pvs] to [cty.cty_effect.eff_reads].
    This function performs capture: if some variables in [pvs] occur
    in [cty.cty_args], they are not frozen. *)

val cty_add_pre : pre list -> cty -> cty
(** [cty_add_pre fl cty] appends pre-conditions in [fl] to [cty.cty_pre].
    This function performs capture: the formulas in [fl] may refer to
    the variables in [cty.cty_args]. Only the new external dependencies
    in [fl] are added to [cty.cty_effect.eff_reads] and frozen. *)

val cty_add_post : cty -> post list -> cty
(** [cty_add_post cty fl] appends post-conditions in [fl] to [cty.cty_post].
    This function performs capture: the formulas in [fl] may refer to the
    variables in [cty.cty_args]. Only the new external dependencies in [fl]
    are added to [cty.cty_effect.eff_reads] and frozen. *)

(** {2 Pretty-printing} *)

val forget_reg : region -> unit   (* flush id_unique for a region *)
val forget_pv  : pvsymbol -> unit (* flush for a program variable *)
val forget_cty : cty -> unit      (* forget arguments and oldies *)

val print_its : Format.formatter -> itysymbol -> unit (* type symbol *)
val print_reg : Format.formatter -> region -> unit    (* region *)
val print_reg_name : Format.formatter -> region -> unit    (* region *)
val print_ity : Format.formatter -> ity -> unit       (* individual type *)
val print_ity_full : Format.formatter -> ity -> unit  (* type with regions *)

val print_xs   : Format.formatter -> xsymbol -> unit  (* exception symbol *)
val print_pv   : Format.formatter -> pvsymbol -> unit (* program variable *)
val print_pvty : Format.formatter -> pvsymbol -> unit (* pvsymbol : type *)
val print_cty  : Format.formatter -> cty -> unit      (* computation type *)

val print_spec :
  pvsymbol list -> pre list -> post list -> post list Mexn.t -> pvsymbol Mpv.t
    -> effect -> Format.formatter -> ity option -> unit (* piecemeal cty *)
