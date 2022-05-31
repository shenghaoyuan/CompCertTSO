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

(** Type system for the Mach intermediate language. *)

Require Import Coqlib.
Require Import Maps.
Require Import Ast.
Require Import Mem.
Require Import Integers.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import Conventions.
Require Import Mach.
Require Import Libtactics.
Require Import Stacklayout.

(** * Typing rules *)

Inductive wt_instr : instruction -> Prop :=
  | wt_Mlabel:
     forall lbl,
     wt_instr (Mlabel lbl)
  | wt_Mgetstack:
     forall ofs ty r,
     mreg_type r = ty ->
     wt_instr (Mgetstack ofs ty r)
  | wt_Msetstack:
     forall ofs ty r,
     mreg_type r = ty ->
     wt_instr (Msetstack r ofs ty)
  | wt_Mgetparam:
     forall ofs ty r,
     mreg_type r = ty ->
     wt_instr (Mgetparam ofs ty r)
  | wt_Mopmove:
     forall r1 r,
     mreg_type r1 = mreg_type r ->
     wt_instr (Mop Omove (r1 :: nil) r)
  | wt_Mop:
     forall op args res,
      op <> Omove ->
      (List.map mreg_type args, mreg_type res) = type_of_operation op ->
      wt_instr (Mop op args res)
  | wt_Mload:
      forall chunk addr args dst,
      List.map mreg_type args = type_of_addressing addr ->
      mreg_type dst = type_of_chunk chunk ->
      wt_instr (Mload chunk addr args dst)
  | wt_Mstore:
      forall chunk addr args src,
      List.map mreg_type args = type_of_addressing addr ->
      mreg_type src = type_of_chunk chunk ->
      wt_instr (Mstore chunk addr args src)
  | wt_Mcall:
      forall sig ros,
      match ros with inl r => mreg_type r = Tint | inr s => True end ->
      wt_instr (Mcall sig ros)
  | wt_Mgoto:
      forall lbl,
      wt_instr (Mgoto lbl)
  | wt_Mcond:
      forall cond args lbl,
      List.map mreg_type args = type_of_condition cond ->
      wt_instr (Mcond cond args lbl)
  | wt_Mreturn: 
      wt_instr Mreturn
  | wt_Matomic:
      forall op args res,
      (List.map mreg_type args, mreg_type res) = type_of_atomic_statement op ->
      wt_instr (Matomic op args res)
  | wt_Mfence:
      wt_instr (Mfence)
  | wt_Mthreadcreate:
      wt_instr (Mthreadcreate).

Record wt_function (f: function) : Prop := mk_wt_function {
  wt_function_instrs:
    forall instr, In instr f.(fn_code) -> wt_instr instr;
(*  wt_function_stacksize:
    Int.lt Int.zero f.(fn_stacksize) \/ Int.zero = f.(fn_stacksize); *)
  wt_function_framesize:
    0 <= f.(fn_framesize);
  wt_function_stacksizepadding:
    Int.unsigned f.(fn_stacksize) <= f.(fn_paddedstacksize);
  wt_function_size:
    0 <= f.(fn_framesize) + f.(fn_paddedstacksize) + fe_retaddrsize < Int.half_modulus;
  wt_function_stack_aligned:
    (align_size (Int.unsigned f.(fn_stacksize)) | f.(fn_framesize));
(*  wt_function_link:
    0 <= Int.signed f.(fn_link_ofs)
    /\ Int.signed f.(fn_link_ofs) + 4 <= f.(fn_framesize); 
  wt_function_link_aligned:
    (4 | Int.signed f.(fn_link_ofs)); *)
  wt_function_framesize_aligned:
    (16 | (f.(fn_paddedstacksize) + f.(fn_framesize) + fe_retaddrsize));
  wt_function_retaddr:
    4 <= fe_retaddrsize;
(*
    0 <= Int.signed f.(fn_retaddr_ofs)
    /\ Int.signed f.(fn_retaddr_ofs) + 4 <= f.(fn_framesize); *)
  wt_function_retaddr_aligned:
    (4 | fe_retaddrsize);
(*  wt_function_link_retaddr:
    Int.signed f.(fn_retaddr_ofs) + 4 <= Int.signed f.(fn_link_ofs)
    \/ Int.signed f.(fn_link_ofs) + 4 <= Int.signed f.(fn_retaddr_ofs) *)
  wt_function_args:
    size_arguments f.(fn_sig)  * 4 + fe_retaddrsize < Int.half_modulus
}.

Inductive wt_fundef: fundef -> Prop :=
  | wt_fundef_external: forall ef,
      wt_fundef (External ef)
  | wt_function_internal: forall f,
      wt_function f ->
      wt_fundef (Internal f).

Definition wt_program (p : program) :=
  forall id f, In (id, f) (prog_funct p) -> wt_fundef f.

Definition wt_genv (ge: genv): Prop :=
  forall v f, Genv.find_funct ge v = Some f -> wt_fundef f.

(** * Type soundness *)

Require Import Machabstr.

(** We show a weak type soundness result for the abstract semantics
    of Mach: for a well-typed Mach program, if a transition is taken
    from a state where registers hold values of their static types,
    registers in the final state hold values of their static types
    as well.  This is a subject reduction theorem for our type system.
    It is used in the proof of implication from the abstract Mach
    semantics to the concrete Mach semantics (file [Machabstr2concr]).
*)

Definition wt_regset (rs: regset) : Prop :=
  forall r, Val.has_type (rs r) (mreg_type r).

Definition wt_frame (fr: frame) : Prop :=
  forall ty ofs, Val.has_type (fr ty ofs) ty.

Lemma wt_setreg:
  forall (rs: regset) (r: mreg) (v: val),
  Val.has_type v (mreg_type r) ->
  wt_regset rs -> wt_regset (rs#r <- v).
Proof.
  intros; red; intros. unfold Regmap.set. 
  case (RegEq.eq r0 r); intro.
  subst r0; assumption.
  apply H0.
Qed.

Lemma wt_get_slot:
  forall f fr ty ofs v,
  get_slot f fr ty ofs = Some v ->
  wt_frame fr ->
  Val.has_type v ty. 
Proof.
  unfold get_slot.
  by intros; destruct (slot_valid_dec f ty ofs); clarify.
Qed.

Lemma wt_set_slot:
  forall f fr ty ofs v fr',
  set_slot f fr ty ofs v = Some fr' ->
  wt_frame fr ->
  Val.has_type v ty ->
  wt_frame fr'.
Proof.
  unfold set_slot.
  intros; destruct (slot_valid_dec f ty ofs); clarify.
  unfold update, wt_frame.
intros.
  destruct zeq; clarify.
    by destruct (typ_eq ty ty0); clarify.
  destruct zle; clarify.
  destruct zle; clarify.
Qed.

Lemma is_tail_find_label:
  forall lbl c c', find_label lbl c = Some c' -> is_tail c' c.
Proof.
  induction c; simpl.
  intros; discriminate.
  case (is_label lbl a); intros.
  injection H; intro; subst c'. constructor. constructor.
  constructor; auto.
Qed.

Lemma wt_undef_temps:
  forall rs, wt_regset rs -> wt_regset (undef_temps rs).
Proof.
  unfold undef_temps. 
  generalize (int_temporaries ++ float_temporaries).
  induction l; simpl; intros. auto.
  apply IHl. red; intros. unfold Regmap.set.
  destruct (RegEq.eq r a). constructor. auto. 
Qed.

Lemma wt_undef_op:
  forall op rs, wt_regset rs -> wt_regset (undef_op op rs).
Proof.
  intros. set (W := wt_undef_temps rs H). 
  destruct op; simpl; auto.
Qed.

Section SUBJECT_REDUCTION.

Inductive wt_stackframes: stackframes -> Prop :=
  | wt_stackframes_base: forall fr sz,
      0 <= sz + fe_retaddrsize < Int.half_modulus ->
      wt_frame fr ->
      wt_stackframes (Stackbase fr sz)
  | wt_stackframes_intro: forall f sp c fr s,
      wt_function f ->
      is_tail c f.(fn_code) ->
      match sp with None => f.(fn_stacksize) = Int.zero | Some _ => f.(fn_stacksize) <> Int.zero end ->
      wt_frame fr ->
      wt_stackframes s ->
      wt_stackframes (Stackframe f sp c fr s).

Inductive wt_state: state -> Prop :=
  | wt_state_intro: forall stk f sp c rs fr
      (STK: wt_stackframes stk)
      (WTF: wt_function f)
      (TAIL: is_tail c f.(fn_code))
      (WTRS: wt_regset rs)
      (WTFR: wt_frame fr)
      (WSIZE: match sp with None => f.(fn_stacksize) = Int.zero | Some _ => f.(fn_stacksize) <> Int.zero end),
      wt_state (State stk f sp c rs fr)
  | wt_state_call: forall stk f rs,
      wt_stackframes stk ->
      wt_fundef f ->
      wt_regset rs ->
      wt_state (Callstate stk f rs)
  | wt_state_return: forall stk rs,
      wt_stackframes stk ->
      wt_regset rs ->
      wt_state (Returnstate stk rs)
  | wt_state_blocked: forall stk efsig rs,
      wt_stackframes stk ->
      wt_regset rs ->
      wt_state (Blockedstate stk rs efsig).

Variable (ge : genv).
Hypothesis wt_ge: wt_genv ge.


Lemma subject_reduction:
  forall s1 t s2, ma_step ge s1 t s2 ->
  forall (WTS: wt_state s1), wt_state s2.
Proof.
  (ma_step_cases (induction 1) Case); intros; inv WTS;
  try (generalize (wt_function_instrs _ WTF _ (is_tail_in TAIL)); intro;
       eapply wt_state_intro; eauto with coqlib); try (by apply wt_undef_temps).

  Case "exec_Mgetstack".
  apply wt_setreg; auto. 
  inversion H. rewrite H1. eapply wt_get_slot; eauto.

  Case "exec_Msetstack".
  inversion H. eapply wt_set_slot; eauto. 
  rewrite <- H1. apply WTRS.

  Case "exec_Mgetparam".
  assert (wt_frame (parent_frame s)) by (by inv STK).
  inversion H. apply wt_setreg; auto.
  rewrite H2. eapply wt_get_slot; eauto.

  Case "exec_Mop".
  apply wt_setreg; auto. inv H.
    simpl in EVAL. 
    rewrite <- H1. replace v with (rs r1). apply WTRS. congruence.
    replace (mreg_type res) with (snd (type_of_operation op)).
    apply type_of_operation_sound with fundef ge rs##args sp; auto.
    rewrite <- H4; reflexivity.
    by apply wt_undef_op.

  Case "exec_Mload".
  by apply wt_setreg, wt_undef_temps; auto; inversion H; rewrite H5.

  Case "exec_Mcall".
  assert (WTFD: wt_fundef f').
    destruct ros as [|i]; simpl in *; [eby eapply wt_ge|].
    destruct (Genv.find_symbol ge i) as [p|]; try done.
    by apply (wt_ge (Vptr p)).
  econstructor; eauto.
  constructor; eauto with coqlib. 

  Case "exec_Mgoto".
  apply is_tail_find_label with lbl; congruence.

  Case "exec_Mcond_true".
  apply is_tail_find_label with lbl; congruence. 

  Case "exec_Mreturn".
  econstructor; eauto.

  Case "exec_Matomic".
  apply wt_setreg; [|by apply wt_undef_temps]. inv H.
  replace (mreg_type res) with Tint. done.
  by inv ASME; inv H1.

  Case "exec_function_internal_empty".
  econstructor; eauto with coqlib; try done. 
  by inv H3; auto. 

  Case "exec_function_internal_nonempty".
  econstructor; eauto with coqlib; try done. 
  by inv H3; auto. 

  Case "exec_function_external_call".
  econstructor; eauto. 

  Case "exec_function_external_return".
  econstructor; eauto. apply wt_setreg; auto.
  unfold proj_sig_res, loc_result.
  destruct (sig_res efsig) as [[]|]; auto.

  Case "exec_return".
  inv H1; econstructor; eauto. 

  Case "exec_return_exit".
  vauto.
Qed.

End SUBJECT_REDUCTION.

