(*========================================================================*)
(*                                                                        *)
(*                    CompcertTSO                                         *)
(*                                                                        *)
(*          Jaroslav Sevcik, University of Cambridge                      *)
(*          Viktor Vafeiadis, University of Cambridge                     *)
(*          Francesco Zappa Nardelli, INRIA Rocquencourt                  *)
(*          Suresh Jagannathan, Purdue University                         *)
(*          Peter Sewell, University of Cambridge                         *)
(*                                                                        *)
(*          (building on CompCert 1.5 and a 1.8 pre-release)              *)
(*                                                                        *)
(*  This document and the CompCertTSO sources are copyright 2005, 2006,   *)
(*  2007, 2008, 2009, 2010, 2011 Institut National de Recherche en        *)
(*  Informatique et en Automatique (INRIA), and Suresh Jagannathan,       *)
(*  Jaroslav Sevcik, Peter Sewell and Viktor Vafeiadis.                   *)
(*                                                                        *)
(*  All rights reserved.  This file is distributed under the terms of     *)
(*  the INRIA Non-Commercial License Agreement.                           *)
(*                                                                        *)
(*                                                                        *)
(*                                                                        *)
(*                                                                        *)
(*                                                                        *)
(*========================================================================*)

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Function calling conventions and other conventions regarding the use of 
    machine registers and stack slots. *)

Require Import Coqlib.
Require Import Ast.
Require Import Locations.

(** * Classification of machine registers *)

(** Machine registers (type [mreg] in module [Locations]) are divided in
  the following groups:
- Temporaries used for spilling, reloading, and parallel move operations.
- Allocatable registers, that can be assigned to RTL pseudo-registers.
  These are further divided into:
-- Callee-save registers, whose value is preserved across a function call.
-- Caller-save registers that can be modified during a function call. *)

(* Think if it is better to declare RA as callee or caller save: given
   our compilation strategy we might ignore the x86 calling
   conventions here *)

Definition int_caller_save_regs : list mreg := nil.

Definition float_caller_save_regs :=
  rXMM0 :: rXMM1 :: rXMM2 :: rXMM3 :: rXMM4 :: rXMM5 :: nil.

Definition int_callee_save_regs : list mreg :=
  rEBX :: rESI :: rEDI :: rEBP :: nil.

Definition float_callee_save_regs : list mreg := 
  nil.

Definition destroyed_at_call_regs :=
  int_caller_save_regs ++ float_caller_save_regs.

Definition destroyed_at_call :=
  List.map R destroyed_at_call_regs.

Definition int_temporaries := IT1 :: IT2 :: rEAX :: nil.

Definition float_temporaries := FT1 :: FT2 :: FP0 :: nil.
  
Definition temporaries := 
  R IT1 :: R IT2 :: R rEAX :: R FT1 :: R FT2 :: R FP0 :: nil.

(* These are used as dummy registers in Coloring. *)
Definition dummy_int_reg := rEBX.
Definition dummy_float_reg := rXMM0.

(** The [index_int_callee_save] and [index_float_callee_save] associate
  a unique positive integer to callee-save registers.  This integer is
  used in [Stacking] to determine where to save these registers in
  the activation record if they are used by the current function. *)

Definition index_int_callee_save (r: mreg) :=
  match r with
  | rEBX => 1 | rESI => 2 | rEDI => 3 | rEBP => 4 | _ => -1
  end.

Definition index_float_callee_save (r: mreg) := -1.

Ltac ElimOrEq :=
  match goal with
  |  |- (?x = ?y) \/ _ -> _ =>
       let H := fresh in
       (intro H; elim H; clear H;
        [intro H; rewrite <- H; clear H | ElimOrEq])
  |  |- False -> _ =>
       let H := fresh in (intro H; contradiction)
  end.

Ltac OrEq :=
  match goal with
  | |- (?x = ?x) \/ _ => left; reflexivity
  | |- (?x = ?y) \/ _ => right; OrEq
  | |- False => fail
  end.

Ltac NotOrEq :=
  match goal with
  | |- (?x = ?y) \/ _ -> False =>
       let H := fresh in (
       intro H; elim H; clear H; [intro; discriminate | NotOrEq])
  | |- False -> False =>
       contradiction
  end.

Lemma index_int_callee_save_pos:
  forall r, In r int_callee_save_regs -> index_int_callee_save r >= 0.
Proof.
  intro r. simpl; ElimOrEq; unfold index_int_callee_save; omega.
Qed.

Lemma index_float_callee_save_pos:
  forall r, In r float_callee_save_regs -> index_float_callee_save r >= 0.
Proof.
  intro r. simpl; ElimOrEq; unfold index_float_callee_save; omega.
Qed.

Lemma index_int_callee_save_pos2:
  forall r, index_int_callee_save r >= 0 -> In r int_callee_save_regs.
Proof.  
  unfold index_int_callee_save; destruct r; simpl; intro; omegaContradiction || OrEq. 
Qed.

Lemma index_float_callee_save_pos2:
  forall r, index_float_callee_save r >= 0 -> In r float_callee_save_regs.
Proof.
  unfold index_float_callee_save; destruct r; simpl; intro; omegaContradiction || OrEq.
Qed.

Lemma index_int_callee_save_inj:
  forall r1 r2, 
  In r1 int_callee_save_regs ->
  In r2 int_callee_save_regs ->
  r1 <> r2 ->
  index_int_callee_save r1 <> index_int_callee_save r2.
Proof.
  by intros r1 r2; simpl; ElimOrEq; ElimOrEq. 
Qed.

Lemma index_float_callee_save_inj:
  forall r1 r2, 
  In r1 float_callee_save_regs ->
  In r2 float_callee_save_regs ->
  r1 <> r2 ->
  index_float_callee_save r1 <> index_float_callee_save r2.
Proof.
  by intros r1 r2; simpl; ElimOrEq; ElimOrEq. 
Qed.

(** The following lemmas show that
    (temporaries, destroyed at call, integer callee-save, float callee-save)
    is a partition of the set of machine registers. *)

Lemma int_float_callee_save_disjoint:
  list_disjoint int_callee_save_regs float_callee_save_regs.
Proof.
  red; intros r1 r2. simpl; ElimOrEq; ElimOrEq; discriminate.
Qed.

Lemma register_classification:
  forall r, 
  (In (R r) temporaries \/ In (R r) destroyed_at_call) \/
  (In r int_callee_save_regs \/ In r float_callee_save_regs).
Proof.
  destruct r; 
  try (left; left; simpl; OrEq);
  try (left; right; simpl; OrEq);
  try (right; left; simpl; OrEq);
  try (right; right; simpl; OrEq);
  try auto.
Qed.

Lemma int_callee_save_not_destroyed:
  forall r, 
    In (R r) temporaries \/ In (R r) destroyed_at_call ->
    ~(In r int_callee_save_regs).
Proof.
  intros; red; intros. elim H.
  generalize H0. simpl; ElimOrEq; NotOrEq.
  generalize H0. simpl; ElimOrEq; NotOrEq.
Qed.

Lemma float_callee_save_not_destroyed:
  forall r, 
    In (R r) temporaries \/ In (R r) destroyed_at_call ->
    ~(In r float_callee_save_regs).
Proof.
  intros; red; intros. elim H.
  generalize H0. simpl; ElimOrEq; NotOrEq.
  generalize H0. simpl; ElimOrEq; NotOrEq.
Qed.

Lemma int_callee_save_type:
  forall r, In r int_callee_save_regs -> mreg_type r = Tint.
Proof.
  by intro; simpl; ElimOrEq.
Qed.

Lemma float_callee_save_type:
  forall r, In r float_callee_save_regs -> mreg_type r = Tfloat.
Proof.
  by intro; simpl; ElimOrEq.
Qed.

Ltac NoRepet :=
  match goal with
  | |- NoDup nil =>
      apply NoDup_nil
  | |- NoDup (?a :: ?b) =>
      apply NoDup_cons; [simpl; intuition discriminate | NoRepet]
  end.

Lemma int_callee_save_norepet:
  NoDup int_callee_save_regs.
Proof.
  unfold int_callee_save_regs; NoRepet.
Qed.

Lemma float_callee_save_norepet:
  NoDup float_callee_save_regs.
Proof.
  unfold float_callee_save_regs; NoRepet.
Qed.

(** * Acceptable locations for register allocation *)

(** The following predicate describes the locations that can be assigned
  to an RTL pseudo-register during register allocation: a non-temporary
  machine register or a [Local] stack slot are acceptable. *)

Definition loc_acceptable (l: loc) : Prop :=
  match l with
  | R r => ~(In l temporaries)
  | S (Local ofs ty) => ofs >= 0
  | S (Incoming _ _) => False
  | S (Outgoing _ _) => False
  end.

Definition locs_acceptable (ll: list loc) : Prop :=
  forall l, In l ll -> loc_acceptable l.

Lemma temporaries_not_acceptable:
  forall l, loc_acceptable l -> Loc.notin l temporaries.
Proof.
  unfold loc_acceptable; destruct l.
  simpl. intuition congruence.
  destruct s; try contradiction. 
  intro. simpl. tauto.
Qed.
Hint Resolve temporaries_not_acceptable: locs.

Lemma locs_acceptable_disj_temporaries:
  forall ll, locs_acceptable ll -> Loc.disjoint ll temporaries.
Proof.
  intros. apply Loc.notin_disjoint. intros.
  apply temporaries_not_acceptable. auto. 
Qed.

Lemma loc_acceptable_noteq_diff:
  forall l1 l2,
  loc_acceptable l1 -> l1 <> l2 -> Loc.diff l1 l2.
Proof.
  unfold loc_acceptable, Loc.diff; destruct l1; destruct l2;
  try (destruct s); try (destruct s0); intros; auto; try congruence.
  case (zeq z z0); intro. 
  compare t t0; intro.
  subst z0; subst t0; tauto.
  tauto. tauto.
  contradiction. contradiction.
Qed.

Lemma loc_acceptable_notin_notin:
  forall r ll,
  loc_acceptable r ->
  ~(In r ll) -> Loc.notin r ll.
Proof.
  induction ll; simpl; intros.
  auto.
  split. apply loc_acceptable_noteq_diff. assumption. 
  apply sym_not_equal. tauto. 
  apply IHll. assumption. tauto. 
Qed.

(** * Function calling conventions *)

(** The functions in this section determine the locations (machine registers
  and stack slots) used to communicate arguments and results between the
  caller and the callee during function calls.  These locations are functions
  of the signature of the function and of the call instruction.  
  Agreement between the caller and the callee on the locations to use
  is guaranteed by our dynamic semantics for Cminor and RTL, which demand 
  that the signature of the call instruction is identical to that of the
  called function.

  Calling conventions are largely arbitrary: they must respect the properties
  proved in this section (such as no overlapping between the locations
  of function arguments), but this leaves much liberty in choosing actual
  locations.  To ensure binary interoperability of code generated by our
  compiler with libraries compiled by another PowerPC compiler, we
  implement the standard conventions defined in the PowerPC/MacOS X
  application binary interface. *)

(** ** Location of function result *)

(** The result value of a function is passed back to the caller in
  registers [REAX] or [F1], depending on the type of the returned value.
  We treat a function without result as a function with one integer result. *)

Definition loc_result (s: signature) : mreg :=
  match s.(sig_res) with
  | None => rEAX
  | Some Tint => rEAX
  | Some Tfloat => FP0
  end.

(** The result location has the type stated in the signature. *)

Lemma loc_result_type:
  forall sig,
  mreg_type (loc_result sig) =
  match sig.(sig_res) with None => Tint | Some ty => ty end.
Proof.
  intros; unfold loc_result.
  destruct (sig_res sig). 
  destruct t; reflexivity.
  reflexivity.
Qed.

(** The result location is a temporary *)

Lemma loc_result_temporary:
  forall (s: signature), 
  In (R (loc_result s)) temporaries.
Proof.
  intros; unfold loc_result.
  destruct (sig_res s). 
  destruct t; simpl; tauto.
  simpl; tauto.
Qed.

(** The result location is not a callee-save register. *)

Lemma loc_result_not_callee_save:
  forall (s: signature),
  ~(In (loc_result s) int_callee_save_regs \/ In (loc_result s) float_callee_save_regs).
Proof.
  intros. intro. destruct H.
  unfold int_callee_save_regs in H. unfold loc_result in H.  inv H.
    case_eq (sig_res s); intros. try destruct t; rewrite H in H0; inv H0.
    rewrite H in H0; inv H0.
   case_eq (sig_res s); intros. try destruct t; rewrite H in H0; inv H0; inv H1; try inv H0; try inv H1.
   rewrite H in H0; inv H0; inv H1; try inv H0; try inv H1.
   inv H.
Qed.

(** All arguments are passed on the stack. *)

Fixpoint loc_arguments_rec
    (tyl: list typ) (ofs: Z) {struct tyl} : list loc :=
  match tyl with
  | nil => nil
  | Tint :: tys => S (Outgoing ofs Tint) :: loc_arguments_rec tys (ofs + 1)
  | Tfloat :: tys => S (Outgoing ofs Tfloat) :: loc_arguments_rec tys (ofs + 2)
  end.

(** [loc_arguments s] returns the list of locations where to store arguments
  when calling a function with signature [s].  *)

Definition loc_arguments (s: signature) : list loc :=
  loc_arguments_rec s.(sig_args) 0.

(** [size_arguments s] returns the number of [Outgoing] slots used
  to call a function with signature [s]. *)

Fixpoint size_arguments_rec
    (tyl: list typ) (ofs: Z) {struct tyl} : Z :=
  match tyl with
  | nil => ofs
  | Tint :: tys => size_arguments_rec tys (ofs + 1)
  | Tfloat :: tys => size_arguments_rec tys (ofs + 2)
  end.

Definition size_arguments (s: signature) : Z :=
  size_arguments_rec s.(sig_args) 0.

(** Argument locations are either non-temporary registers or [Outgoing] 
  stack slots at nonnegative offsets. *)

Definition loc_argument_acceptable (l: loc) : Prop :=
  match l with
  | R r => ~(In l temporaries)
  | S (Outgoing ofs ty) => ofs >= 0
  | _ => False
  end.

Remark loc_arguments_rec_charact:
  forall tyl ofs l,
  In l (loc_arguments_rec tyl ofs) ->
  match l with
  | S (Outgoing ofs' ty) => ofs' >= ofs
  | _ => False
  end.
Proof.
  induction tyl; simpl loc_arguments_rec; intros.
  elim H.
  destruct a; simpl in H; destruct H.
  subst l. omega.
  generalize (IHtyl _ _ H). destruct l; auto. destruct s; auto. omega. 
  subst l. omega.
  generalize (IHtyl _ _ H). destruct l; auto. destruct s; auto. omega. 
Qed.

Lemma loc_arguments_acceptable:
  forall (s: signature) (r: loc),
  In r (loc_arguments s) -> loc_argument_acceptable r.
Proof.
 unfold loc_arguments; intros.
  generalize (loc_arguments_rec_charact  _ _ _ H).
  destruct r; tauto.
Qed.
Hint Resolve loc_arguments_acceptable: locs.

(** Arguments are parwise disjoint (in the sense of [Loc.norepet]). *)

Remark loc_arguments_rec_notin_reg:
  forall tyl ofs r,
  Loc.notin (R r) (loc_arguments_rec tyl ofs).
Proof.
  induction tyl; simpl; intros.
  auto.
  destruct a.
  simpl. split; auto.
  simpl. split; auto.
Qed.

Remark loc_arguments_rec_notin_local:
  forall tyl ofs ofs0 ty0,
  Loc.notin (S (Local ofs0 ty0)) (loc_arguments_rec tyl ofs).
Proof.
  induction tyl; simpl; intros.
  auto.
  destruct a; simpl; auto.
Qed.

Remark loc_arguments_rec_notin_outgoing:
  forall tyl ofs ofs0 ty0,
  ofs0 + typesize ty0 <= ofs ->
  Loc.notin (S (Outgoing ofs0 ty0)) (loc_arguments_rec tyl ofs).
Proof.
  induction tyl; simpl; intros.
  auto.
  destruct a.
  split. simpl. omega. eapply IHtyl. omega.
  split. simpl. omega. eapply IHtyl. omega.
Qed.

Lemma loc_arguments_norepet:
  forall (s: signature), Loc.norepet (loc_arguments s).
Proof.
  intros. unfold loc_arguments. generalize (sig_args s) 0.
  induction l; simpl; intros.
  constructor.
  destruct a; constructor.
  apply loc_arguments_rec_notin_outgoing. simpl; omega. auto.
  apply loc_arguments_rec_notin_outgoing. simpl; omega. auto.
Qed.

(** The offsets of [Outgoing] arguments are below [size_arguments s]. *)

Remark size_arguments_rec_above:
  forall tyl ofs0,
  ofs0 <= size_arguments_rec tyl ofs0.
Proof.
  induction tyl; simpl; intros.
  omega.
  destruct a.
  apply Zle_trans with (ofs0 + 1); auto; omega. 
  apply Zle_trans with (ofs0 + 2); auto; omega. 
Qed.

Lemma size_arguments_above:
  forall s, size_arguments s >= 0.
Proof.
  intros; unfold size_arguments. apply Zle_ge. apply Zle_trans with 0. omega. 
  apply size_arguments_rec_above.
Qed.

Lemma loc_arguments_bounded:
  forall (s: signature) (ofs: Z) (ty: typ),
  In (S (Outgoing ofs ty)) (loc_arguments s) ->
  ofs + typesize ty <= size_arguments s.
Proof.
  intros until ty. unfold loc_arguments, size_arguments. generalize (sig_args s) 0.
  induction l; simpl; intros.
  elim H.
  destruct a; simpl in H; destruct H.
  inv H. apply size_arguments_rec_above.
  auto.
  inv H. apply size_arguments_rec_above.
  auto.
Qed.

(** Temporary registers do not overlap with argument locations. *)

Lemma loc_arguments_not_temporaries:
  forall sig, Loc.disjoint (loc_arguments sig) temporaries.
Proof.
  intros; red; intros x1 x2 H.
  generalize (loc_arguments_rec_charact _ _ _ H).
  destruct x1. tauto. 
  destruct s; intuition. 
  revert H1. simpl; ElimOrEq; auto.
Qed.
Hint Resolve loc_arguments_not_temporaries: locs.

(** Argument registers are caller-save. *)

Lemma arguments_caller_save:
  forall sig r,
  In (R r) (loc_arguments sig) -> In (R r) destroyed_at_call.
Proof.
  unfold loc_arguments; intros.
  elim (loc_arguments_rec_charact _ _ _ H); simpl.
Qed.

(** Callee-save registers do not overlap with argument locations. *)

Lemma arguments_not_preserved:
  forall sig l,
  Loc.notin l destroyed_at_call -> loc_acceptable l ->
  Loc.notin l (loc_arguments sig).
Proof.
  intros. unfold loc_arguments. destruct l.
  apply loc_arguments_rec_notin_reg.  
  destruct s; simpl in H0; try contradiction. 
  apply loc_arguments_rec_notin_local.
Qed.
Hint Resolve arguments_not_preserved: locs.

(** Argument locations agree in number with the function signature. *)

Lemma loc_arguments_length:
  forall sig,
  List.length (loc_arguments sig) = List.length sig.(sig_args).
Proof.
  intros. unfold loc_arguments. generalize (sig_args sig) 0.
  induction l; simpl; intros. auto. destruct a; simpl; decEq; auto.
Qed.

(** Argument locations agree in types with the function signature. *)

Lemma loc_arguments_type:
  forall sig, List.map Loc.type (loc_arguments sig) = sig.(sig_args).
Proof.
  intros. unfold loc_arguments. generalize (sig_args sig) 0. 
  induction l; simpl; intros. auto. destruct a; simpl; decEq; auto.
Qed.

(** There is no partial overlap between an argument location and an
  acceptable location: they are either identical or disjoint. *)

Lemma no_overlap_arguments:
  forall args sg,
  locs_acceptable args ->
  Loc.no_overlap args (loc_arguments sg).
Proof.
  unfold Loc.no_overlap; intros.
  generalize (H r H0).
  generalize (loc_arguments_acceptable _ _ H1).
  destruct s; destruct r; simpl.
  intros. case (mreg_eq m0 m); intro. left; congruence. tauto.
  intros. right; destruct s; auto.
  intros. right. auto.
  destruct s; try tauto. destruct s0; tauto.
Qed.

(** ** Location of function parameters *)

(** A function finds the values of its parameter in the same locations
  where its caller stored them, except that the stack-allocated arguments,
  viewed as [Outgoing] slots by the caller, are accessed via [Incoming]
  slots (at the same offsets and types) in the callee. *)

Definition parameter_of_argument (l: loc) : loc :=
  match l with
  | S (Outgoing n ty) => S (Incoming n ty)
  | _ => l
  end.

Definition loc_parameters (s: signature) :=
  List.map parameter_of_argument (loc_arguments s).

Lemma loc_parameters_type:
  forall sig, List.map Loc.type (loc_parameters sig) = sig.(sig_args).
Proof.
  intros. unfold loc_parameters.
  rewrite list_map_compose. 
  rewrite <- loc_arguments_type.
  apply list_map_exten.
  intros. destruct x; simpl. auto. 
  destruct s; reflexivity.
Qed.

Lemma loc_parameters_length:
  forall sg, List.length (loc_parameters sg) = List.length sg.(sig_args).
Proof.
  intros. unfold loc_parameters. rewrite list_length_map. 
  apply loc_arguments_length.
Qed.

Lemma loc_parameters_not_temporaries:
  forall sig, Loc.disjoint (loc_parameters sig) temporaries.
Proof.
  intro; red; intros.
  unfold loc_parameters in H. 
  elim (list_in_map_inv _ _ _ H). intros y [EQ IN].
  generalize (loc_arguments_not_temporaries sig y x2 IN H0).
  subst x1. destruct x2.
  destruct y; simpl. auto. destruct s; auto.
  byContradiction. generalize H0. simpl. NotOrEq.
Qed.

Lemma no_overlap_parameters:
  forall params sg,
  locs_acceptable params ->
  Loc.no_overlap (loc_parameters sg) params.
Proof.
  unfold Loc.no_overlap; intros.
  unfold loc_parameters in H0. 
  elim (list_in_map_inv _ _ _ H0). intros t [EQ IN].
  rewrite EQ. 
  generalize (loc_arguments_acceptable _ _ IN).
  generalize (H s H1).
  destruct s; destruct t; simpl.
  intros. case (mreg_eq m0 m); intro. left; congruence. tauto.
  intros. right; destruct s; simpl; auto.
  intros; right; auto.
  destruct s; try tauto. destruct s0; try tauto. 
  intros; simpl. tauto.
Qed.

(** Locations destroyed by thread-create. *)
Definition destroyed_at_threadcreate_regs :=
  loc_result thread_create_sig :: int_caller_save_regs ++ float_caller_save_regs.

Definition destroyed_at_threadcreate :=
  List.map R destroyed_at_threadcreate_regs.

 