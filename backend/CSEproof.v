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

(** Correctness proof for common subexpression elimination. *)

Require Import Coqlib.
Require Import Maps.
Require Import Ast.
Require Import Integers.
Require Import Pointers.
Require Import Floats.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Kildall.
Require Import CSE.
Require Import Memcomp Traces.
Require Import Simulations MCsimulation.
Require Import Libtactics.

(** * Semantic properties of value numberings *)

(** ** Well-formedness of numberings *)

(** A numbering is well-formed if all registers mentioned in equations
  are less than the ``next'' register number given in the numbering.
  This guarantees that the next register is fresh with respect to
  the equations. *)

Definition wf_rhs (next: valnum) (rh: rhs) : Prop :=
  match rh with
  | Op op vl => forall v, In v vl -> Plt v next
  end.

Definition wf_equation (next: valnum) (vr: valnum) (rh: rhs) : Prop :=
  Plt vr next /\ wf_rhs next rh.

Definition wf_numbering (n: numbering) : Prop :=
  (forall v rh,
    In (v, rh) n.(num_eqs) -> wf_equation n.(num_next) v rh)
/\
  (forall r v,
    PTree.get r n.(num_reg) = Some v -> Plt v n.(num_next)).

Lemma wf_empty_numbering:
  wf_numbering empty_numbering.
Proof.
  unfold empty_numbering; split; simpl; intros.
  elim H.
  rewrite PTree.gempty in H. congruence.
Qed.

Lemma wf_rhs_increasing:
  forall next1 next2 rh,
  Ple next1 next2 ->
  wf_rhs next1 rh -> wf_rhs next2 rh.
Proof.
  intros; destruct rh; simpl; intros; apply Plt_Ple_trans with next1; auto.
Qed.

Lemma wf_equation_increasing:
  forall next1 next2 vr rh,
  Ple next1 next2 ->
  wf_equation next1 vr rh -> wf_equation next2 vr rh.
Proof.
  intros. elim H0; intros. split. 
  apply Plt_Ple_trans with next1; auto.
  apply wf_rhs_increasing with next1; auto.
Qed.

(** We now show that all operations over numberings 
  preserve well-formedness. *)

Lemma wf_valnum_reg:
  forall n r n' v,
  wf_numbering n ->
  valnum_reg n r = (n', v) ->
  wf_numbering n' /\ Plt v n'.(num_next) /\ Ple n.(num_next) n'.(num_next).
Proof.
  intros until v. intros WF. inversion WF.
  generalize (H0 r v).
  unfold valnum_reg. destruct ((num_reg n)!r).
  intros. replace n' with n. split. auto. 
  split. apply H1. congruence. 
  apply Ple_refl.
  congruence. 
  intros. inversion H2. simpl. split.
  split; simpl; intros. 
  apply wf_equation_increasing with (num_next n). apply Ple_succ. auto. 
  rewrite PTree.gsspec in H3. destruct (peq r0 r). 
  replace v0 with (num_next n). apply Plt_succ. congruence.
  apply Plt_trans_succ; eauto. 
  split. apply Plt_succ. apply Ple_succ.
Qed.

Lemma wf_valnum_regs:
  forall rl n n' vl,
  wf_numbering n ->
  valnum_regs n rl = (n', vl) ->
  wf_numbering n' /\
  (forall v, In v vl -> Plt v n'.(num_next)) /\
  Ple n.(num_next) n'.(num_next).
Proof.
  induction rl; intros.
  simpl in H0. inversion H0. subst n'; subst vl. 
  simpl. intuition. 
  simpl in H0. 
  caseEq (valnum_reg n a). intros n1 v1 EQ1.
  caseEq (valnum_regs n1 rl). intros ns vs EQS.
  rewrite EQ1 in H0; rewrite EQS in H0; simpl in H0.
  inversion H0. subst n'; subst vl. 
  generalize (wf_valnum_reg _ _ _ _ H EQ1); intros [A1 [B1 C1]].
  generalize (IHrl _ _ _ A1 EQS); intros [As [Bs Cs]].
  split. auto.
  split. simpl; intros. elim H1; intro.
    subst v. eapply Plt_Ple_trans; eauto.
    auto.
  eapply Ple_trans; eauto.
Qed.

Lemma find_valnum_rhs_correct:
  forall rh vn eqs,
  find_valnum_rhs rh eqs = Some vn -> In (vn, rh) eqs.
Proof.
  induction eqs; simpl.
  congruence.
  case a; intros v r'. case (eq_rhs rh r'); intro.
  intro. left. congruence.
  intro. right. auto.
Qed.

Lemma wf_add_rhs:
  forall n rd rh,
  wf_numbering n ->
  wf_rhs n.(num_next) rh ->
  wf_numbering (add_rhs n rd rh).
Proof.
  intros. inversion H. unfold add_rhs. 
  caseEq (find_valnum_rhs rh n.(num_eqs)); intros.
  split; simpl. assumption. 
  intros r v0. rewrite PTree.gsspec. case (peq r rd); intros.
  inversion H4. subst v0. 
  elim (H1 v rh (find_valnum_rhs_correct _ _ _ H3)). auto.
  eauto.
  split; simpl.
  intros v rh0 [A1|A2]. inversion A1. subst rh0. 
  split. apply Plt_succ. apply wf_rhs_increasing with n.(num_next).
  apply Ple_succ. auto.
  apply wf_equation_increasing with n.(num_next). apply Ple_succ. auto.
  intros r v. rewrite PTree.gsspec. case (peq r rd); intro.
  intro. inversion H4. apply Plt_succ.
  intro. apply Plt_trans_succ. eauto. 
Qed.

Lemma wf_add_op:
  forall n rd op rs,
  wf_numbering n ->
  wf_numbering (add_op n rd op rs).
Proof.
  intros. unfold add_op. 
  case (is_move_operation op rs).
  intro r. caseEq (valnum_reg n r); intros n' v EQ.
  destruct (wf_valnum_reg _ _ _ _ H EQ) as [[A1 A2] [B C]].
  split; simpl. assumption. intros until v0. rewrite PTree.gsspec.
  case (peq r0 rd); intros. replace v0 with v. auto. congruence.
  eauto.
  caseEq (valnum_regs n rs). intros n' vl EQ. 
  generalize (wf_valnum_regs _ _ _ _ H EQ). intros [A [B C]].
  apply wf_add_rhs; auto.
Qed.

Lemma wf_add_unknown:
  forall n rd,
  wf_numbering n ->
  wf_numbering (add_unknown n rd).
Proof.
  intros. inversion H. unfold add_unknown. constructor; simpl.
  intros. eapply wf_equation_increasing; eauto. auto with coqlib. 
  intros until v. rewrite PTree.gsspec. case (peq r rd); intros.
  inversion H2. auto with coqlib.
  apply Plt_trans_succ. eauto.
Qed.

Lemma wf_transfer:
  forall f pc n, wf_numbering n -> wf_numbering (transfer f pc n).
Proof.
  intros. unfold transfer. 
  destruct (f.(fn_code)!pc); auto.
  destruct i; auto using wf_add_op, wf_add_unknown, wf_empty_numbering.
Qed.

(** As a consequence, the numberings computed by the static analysis
  are well formed. *)

Theorem wf_analyze:
  forall f pc, wf_numbering (analyze f)!!pc.
Proof.
  unfold analyze; intros.
  caseEq (Solver.fixpoint (successors f) (transfer f) (fn_entrypoint f)).
  intros approx EQ.
  eapply Solver.fixpoint_invariant with (P := wf_numbering); eauto.
  exact wf_empty_numbering.   
  exact (wf_transfer f).
  intro. rewrite PMap.gi. apply wf_empty_numbering.
Qed.

(** ** Properties of satisfiability of numberings *)

Module ValnumEq.
  Definition t := valnum.
  Definition eq := peq.
End ValnumEq.

Module VMap := EMap(ValnumEq).

Section SATISFIABILITY.

Variable ge: genv.
Variable sp: option pointer.

(** Agremment between two mappings from value numbers to values
  up to a given value number. *)

Definition valu_agree (valu1 valu2: valnum -> val) (upto: valnum) : Prop :=
  forall v, Plt v upto -> valu2 v = valu1 v.

Lemma valu_agree_refl:
  forall valu upto, valu_agree valu valu upto.
Proof.
  intros; red; auto.
Qed.

Lemma valu_agree_trans:
  forall valu1 valu2 valu3 upto12 upto23,
  valu_agree valu1 valu2 upto12 ->
  valu_agree valu2 valu3 upto23 ->
  Ple upto12 upto23 ->
  valu_agree valu1 valu3 upto12.
Proof.
  intros; red; intros. transitivity (valu2 v).
  apply H0. apply Plt_Ple_trans with upto12; auto.
  apply H; auto.
Qed.

Lemma valu_agree_list:
  forall valu1 valu2 upto vl,
  valu_agree valu1 valu2 upto ->
  (forall v, In v vl -> Plt v upto) ->
  map valu2 vl = map valu1 vl.
Proof.
  intros. apply list_map_exten. intros. symmetry. apply H. auto.
Qed.

(** The [numbering_holds] predicate (defined in file [CSE]) is
  extensional with respect to [valu_agree]. *)

Lemma numbering_holds_exten:
  forall valu1 valu2 n rs,
  valu_agree valu1 valu2 n.(num_next) ->
  wf_numbering n ->
  numbering_holds valu1 ge sp rs n ->
  numbering_holds valu2 ge sp rs n.
Proof.
  intros. inversion H0. inversion H1. split; intros.
  generalize (H2 _ _ H6). intro WFEQ.
  generalize (H4 _ _ H6). 
  unfold equation_holds; destruct rh.
  elim WFEQ; intros.
  rewrite (valu_agree_list valu1 valu2 n.(num_next)). 
  rewrite H. auto. auto. auto. exact H8. 
  rewrite H. auto. eauto.
Qed.

(** [valnum_reg] and [valnum_regs] preserve the [numbering_holds] predicate.
  Moreover, it is always the case that the returned value number has
  the value of the given register in the final assignment of values to
  value numbers. *)

Lemma valnum_reg_holds:
  forall valu1 rs n r n' v,
  wf_numbering n ->
  numbering_holds valu1 ge sp rs n ->
  valnum_reg n r = (n', v) ->
  exists valu2,
    numbering_holds valu2 ge sp rs n' /\
    valu2 v = rs#r /\
    valu_agree valu1 valu2 n.(num_next).
Proof.
  intros until v. unfold valnum_reg. 
  caseEq (n.(num_reg)!r).
  (* Register already has a value number *)
  intros. inversion H2. subst n'; subst v0. 
  inversion H1. 
  exists valu1. split. auto. 
  split. symmetry. auto.
  apply valu_agree_refl.
  (* Register gets a fresh value number *)
  intros. inversion H2. subst n'. subst v. inversion H1.
  set (valu2 := VMap.set n.(num_next) rs#r valu1).
  assert (AG: valu_agree valu1 valu2 n.(num_next)).
    red; intros. unfold valu2. apply VMap.gso. 
    auto with coqlib.
  elim (numbering_holds_exten _ _ _ _ AG H0 H1); intros.
  exists valu2. 
  split. split; simpl; intros. auto. 
  unfold valu2, VMap.set, ValnumEq.eq. 
  rewrite PTree.gsspec in H7. destruct (peq r0 r).
  inversion H7. rewrite peq_true. congruence.
  case (peq vn (num_next n)); intro. 
  inversion H0. generalize (H9 _ _ H7).  rewrite e. intro.
  elim (Plt_strict _ H10). 
  auto.
  split. unfold valu2. apply VMap.gss. 
  auto.
Qed.

Lemma valnum_regs_holds:
  forall rs rl valu1 n n' vl,
  wf_numbering n ->
  numbering_holds valu1 ge sp rs n ->
  valnum_regs n rl = (n', vl) ->
  exists valu2,
    numbering_holds valu2 ge sp rs n' /\
    List.map valu2 vl = rs##rl /\
    valu_agree valu1 valu2 n.(num_next).
Proof.
  induction rl; simpl; intros.
  (* base case *)
  inversion H1; subst n'; subst vl.
  exists valu1. split. auto. split. reflexivity. apply valu_agree_refl.
  (* inductive case *)
  caseEq (valnum_reg n a); intros n1 v1 EQ1.
  caseEq (valnum_regs n1 rl); intros ns vs EQs.
  rewrite EQ1 in H1; rewrite EQs in H1. inversion H1. subst vl; subst n'.
  generalize (valnum_reg_holds _ _ _ _ _ _ H H0 EQ1).
  intros [valu2 [A [B C]]].
  generalize (wf_valnum_reg _ _ _ _ H EQ1). intros [D [E F]].
  generalize (IHrl _ _ _ _ D A EQs). 
  intros [valu3 [P [Q R]]].
  exists valu3. 
  split. auto. 
  split. simpl. rewrite R. congruence. auto.
  eapply valu_agree_trans; eauto.
Qed.

(** A reformulation of the [equation_holds] predicate in terms
  of the value to which a right-hand side of an equation evaluates. *)

Definition rhs_evals_to
    (valu: valnum -> val) (rh: rhs) (v: val) : Prop :=
  match rh with
  | Op op vl => 
      eval_operation ge sp op (List.map valu vl) = Some v
  end.

Lemma equation_evals_to_holds_1:
  forall valu rh v vres,
  rhs_evals_to valu rh v ->
  equation_holds valu ge sp vres rh ->
  valu vres = v.
Proof.
  intros until vres. unfold rhs_evals_to, equation_holds.
  destruct rh. congruence.
Qed.

Lemma equation_evals_to_holds_2:
  forall valu rh v vres,
  wf_rhs vres rh ->
  rhs_evals_to valu rh v ->
  equation_holds (VMap.set vres v valu) ge sp vres rh.
Proof.
  intros until vres. unfold wf_rhs, rhs_evals_to, equation_holds.
  rewrite VMap.gss. 
  assert (forall vl: list valnum,
            (forall v, In v vl -> Plt v vres) ->
            map (VMap.set vres v valu) vl = map valu vl).
    intros. apply list_map_exten. intros. 
    symmetry. apply VMap.gso. apply Plt_ne. auto.
  destruct rh; intros; rewrite H; auto.
Qed.

(** The numbering obtained by adding an equation [rd = rhs] is satisfiable
  in a concrete register set where [rd] is set to the value of [rhs]. *)

Lemma add_rhs_satisfiable:
  forall n rh valu1 rs rd v,
  wf_numbering n ->
  wf_rhs n.(num_next) rh ->
  numbering_holds valu1 ge sp rs n ->
  rhs_evals_to valu1 rh v ->
  numbering_satisfiable ge sp (rs#rd <- v) (add_rhs n rd rh).
Proof.
  intros. unfold add_rhs. 
  caseEq (find_valnum_rhs rh n.(num_eqs)).
  (* RHS found *)
  intros vres FINDVN. inversion H1.
  exists valu1. split; simpl; intros.
  auto. 
  rewrite Regmap.gsspec. 
  rewrite PTree.gsspec in H5.
  destruct (peq r rd).
  symmetry. eapply equation_evals_to_holds_1; eauto.
  apply H3. apply find_valnum_rhs_correct. congruence.
  auto.
  (* RHS not found *)
  intro FINDVN. 
  set (valu2 := VMap.set n.(num_next) v valu1).
  assert (AG: valu_agree valu1 valu2 n.(num_next)).
    red; intros. unfold valu2. apply VMap.gso. 
    auto with coqlib.
  elim (numbering_holds_exten _ _ _ _ AG H H1); intros.
  exists valu2. split; simpl; intros.
  elim H5; intro.
  inversion H6; subst vn; subst rh0. 
  unfold valu2. eapply equation_evals_to_holds_2; eauto.
  auto.
  rewrite Regmap.gsspec. rewrite PTree.gsspec in H5. destruct (peq r rd).
  unfold valu2. inversion H5. symmetry. apply VMap.gss.
  auto.
Qed.

(** [add_op] returns a numbering that is satisfiable in the register
  set after execution of the corresponding [Iop] instruction. *)

Lemma add_op_satisfiable:
  forall n rs op args dst v,
  wf_numbering n ->
  numbering_satisfiable ge sp rs n ->
  eval_operation ge sp op rs##args = Some v ->
  numbering_satisfiable ge sp (rs#dst <- v) (add_op n dst op args).
Proof.
  intros. inversion H0.
  unfold add_op.
  caseEq (@is_move_operation reg op args).
  intros arg EQ. 
  destruct (is_move_operation_correct _ _ EQ) as [A B]. subst op args.
  caseEq (valnum_reg n arg). intros n1 v1 VL.
  generalize (valnum_reg_holds _ _ _ _ _ _ H H2 VL). intros [valu2 [A [B C]]].
  generalize (wf_valnum_reg _ _ _ _ H VL). intros [D [E F]].  
  elim A; intros. exists valu2; split; simpl; intros.
  auto. rewrite Regmap.gsspec. rewrite PTree.gsspec in H5.
  destruct (peq r dst). simpl in H1. congruence. auto.
  intro NEQ. caseEq (valnum_regs n args). intros n1 vl VRL.
  generalize (valnum_regs_holds _ _ _ _ _ _ H H2 VRL). intros [valu2 [A [B C]]].
  generalize (wf_valnum_regs _ _ _ _ H VRL). intros [D [E F]].
  apply add_rhs_satisfiable with valu2; auto.
  simpl. congruence. 
Qed.

(** [add_unknown] returns a numbering that is satisfiable in the
  register set after setting the target register to any value. *)

Lemma add_unknown_satisfiable:
  forall n rs dst v,
  wf_numbering n ->
  numbering_satisfiable ge sp rs n ->
  numbering_satisfiable ge sp 
     (rs#dst <- v) (add_unknown n dst).
Proof.
  intros. destruct H0 as [valu A]. 
  set (valu' := VMap.set n.(num_next) v valu).
  assert (numbering_holds valu' ge sp rs n). 
    eapply numbering_holds_exten; eauto.
    unfold valu'; red; intros. apply VMap.gso. auto with coqlib.
  destruct H0 as [B C].
  exists valu'; split; simpl; intros.
  eauto.
  rewrite PTree.gsspec in H0. rewrite Regmap.gsspec. 
  destruct (peq r dst). inversion H0. unfold valu'. rewrite VMap.gss; auto.
  eauto.
Qed.

(** Correctness of [reg_valnum]: if it returns a register [r],
  that register correctly maps back to the given value number. *)

Lemma reg_valnum_correct:
  forall n v r, reg_valnum n v = Some r -> n.(num_reg)!r = Some v.
Proof.
  intros until r. unfold reg_valnum. rewrite PTree.fold_spec.
  assert(forall l acc0,
    List.fold_left
     (fun (acc: option reg) (p: reg * valnum) => 
        if peq (snd p) v then Some (fst p) else acc)
     l acc0 = Some r ->
     In (r, v) l \/ acc0 = Some r).
  induction l; simpl.
  intros. tauto.
  case a; simpl; intros r1 v1 acc0 FL.
  generalize (IHl _ FL). 
  case (peq v1 v); intro. 
    subst v1. intros [A|B]. tauto. inversion B; subst r1. tauto.
    tauto.
  intro. elim (H _ _ H0); intro. 
  apply PTree.elements_complete; auto.
  discriminate.
Qed.

(** Correctness of [find_op] and [find_load]: if successful and in a
  satisfiable numbering, the returned register does contain the 
  result value of the operation or memory load. *)

Lemma find_rhs_correct:
  forall valu rs n rh r,
  numbering_holds valu ge sp rs n ->
  find_rhs n rh = Some r ->
  rhs_evals_to valu rh rs#r.
Proof.
  intros until r.  intros NH. 
  unfold find_rhs. 
  caseEq (find_valnum_rhs rh n.(num_eqs)); intros.
  generalize (find_valnum_rhs_correct _ _ _ H); intro.
  generalize (reg_valnum_correct _ _ _ H0); intro.
  inversion NH. 
  generalize (H3 _ _ H1). rewrite (H4 _ _ H2). 
  destruct rh; simpl; auto.
  discriminate.
Qed.

Lemma find_op_correct:
  forall rs n op args r,
  wf_numbering n ->
  numbering_satisfiable ge sp rs n ->
  find_op n op args = Some r ->
  eval_operation ge sp op rs##args = Some rs#r.
Proof.
  intros until r. intros WF [valu NH].
  unfold find_op. caseEq (valnum_regs n args). intros n' vl VR FIND.
  generalize (valnum_regs_holds _ _ _ _ _ _ WF NH VR).
  intros [valu2 [NH2 [EQ AG]]].
  rewrite <- EQ. 
  change (rhs_evals_to valu2 (Op op vl) rs#r).
  eapply find_rhs_correct; eauto.
Qed.

End SATISFIABILITY.

(** The numberings associated to each instruction by the static analysis
  are inductively satisfiable, in the following sense: the numbering
  at the function entry point is satisfiable, and for any RTL execution 
  from [pc] to [pc'], satisfiability at [pc] implies 
  satisfiability at [pc']. *)

Theorem analysis_correct_1:
  forall ge sp rs f pc pc' i,
  f.(fn_code)!pc = Some i -> In pc' (successors_instr i) ->
  numbering_satisfiable ge sp rs (transfer f pc (analyze f)!!pc) ->
  numbering_satisfiable ge sp rs (analyze f)!!pc'.
Proof.
  intros until i.
  generalize (wf_analyze f pc).
  unfold analyze.
  caseEq (Solver.fixpoint (successors f) (transfer f) (fn_entrypoint f)).
  intros res FIXPOINT WF AT SUCC.
  assert (Numbering.ge res!!pc' (transfer f pc res!!pc)).
    eapply Solver.fixpoint_solution; eauto.
    unfold successors_list, successors. rewrite PTree.gmap.
    rewrite AT. auto.
  apply H.
  intros. rewrite PMap.gi. apply empty_numbering_satisfiable.
Qed.

Theorem analysis_correct_entry:
  forall ge sp rs f,
  numbering_satisfiable ge sp rs (analyze f)!!(f.(fn_entrypoint)).
Proof.
  intros. 
  replace ((analyze f)!!(f.(fn_entrypoint)))
          with empty_numbering.
  apply empty_numbering_satisfiable.
  unfold analyze.
  caseEq (Solver.fixpoint (successors f) (transfer f) (fn_entrypoint f)).
  intros res FIXPOINT. 
  symmetry. change empty_numbering with Solver.L.top.
  eapply Solver.fixpoint_entry; eauto.
  intros. symmetry. apply PMap.gi. 
Qed.

(** * Semantic preservation *)

Definition genv_rel : genv -> genv -> Prop :=
 (fun x y => Genv.genv_match (fun a b => transf_fundef a = b) y x).

Section PRESERVATION.

(* Assume fixed global environments that are related: *)
Variables (ge tge : genv).
Hypothesis TRANSF: genv_rel ge tge.

Let lts := (mklts thread_labels (rtl_step ge)).
Let tlts := (mklts thread_labels (rtl_step tge)).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (transf_fundef f).
Proof.
  intros v f H.
  pose proof (proj2 TRANSF v).
  destruct (Genv.find_funct_ptr ge v);
   destruct (Genv.find_funct_ptr tge v); try done.
  clarify; eexists; done.
Qed.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof.
  intros v f H.
  destruct v as [| |p|]; try done; simpl in *.
  apply function_ptr_translated; done.
Qed.

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof. by intros; destruct TRANSF. Qed.

Lemma sig_preserved:
  forall f,
  funsig (transf_fundef f) = funsig f.
Proof. by intros [|]. Qed.

Lemma find_function_translated:
  forall ros ls f,
  find_function ge ros ls = Some f ->
  find_function tge ros ls = Some (transf_fundef f).
Proof.
  intros [l|] ls f; simpl.
    destruct (ls # l); try done; apply functions_translated; done.
  rewrite symbols_preserved; destruct (Genv.find_symbol ge i); try done.
  apply function_ptr_translated; done.
Qed.

(** The proof of semantic preservation is a simulation argument using
  diagrams of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                   |t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  Left: RTL execution in the original program.  Right: RTL execution in
  the optimized program.  Precondition (top) and postcondition (bottom):
  agreement between the states, including the fact that
  the numbering at [pc] (returned by the static analysis) is satisfiable.
*)

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
  match_stackframes_intro:
    forall res c sp pc rs f,
    c = f.(RTL.fn_code) ->
    (forall v, numbering_satisfiable ge sp (rs#res <- v) (analyze f)!!pc) ->
    match_stackframes
      (Stackframe res c sp pc rs)
      (Stackframe res (transf_code (analyze f) c) sp pc rs).

Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
      forall s c sp pc rs s' f
             (CF: c = f.(RTL.fn_code))
             (SAT: numbering_satisfiable ge sp rs (analyze f)!!pc)
             (STACKS: list_forall2 match_stackframes s s'),
      match_states (State s c sp pc rs)
                   (State s' (transf_code (analyze f) c) sp pc rs)
  | match_states_call:
      forall s f args s',
      list_forall2 match_stackframes s s' ->
      match_states (Callstate s f args)
                   (Callstate s' (transf_fundef f) args)
  | match_states_return:
      forall s s' v,
      list_forall2 match_stackframes s s' ->
      match_states (Returnstate s v)
                   (Returnstate s' v)
  | match_states_blocked:
      forall s s' v,
      list_forall2 match_stackframes s s' ->
      match_states (Blockedstate s v)
                   (Blockedstate s' v).

Ltac TransfInstr :=
  match goal with
  | H1: (PTree.get ?pc ?c = Some ?instr), f: function |- _ =>
      cut ((transf_code (analyze f) c)!pc = Some(transf_instr (analyze f)!!pc instr));
      [ simpl
      | unfold transf_code; rewrite PTree.gmap; 
        unfold option_map; rewrite H1; reflexivity ]
  end.

(** The proof of simulation is a case analysis over the transition
  in the source code. *)

Lemma transf_step_correct:
  forall s1 t s2, rtl_step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  exists s2', rtl_step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  (rtl_step_cases (induction 1) Case); intros; inv MS; 
    try (TransfInstr; intro C).

  Case "exec_Inop".
  exists (State s' (transf_code (analyze f) (fn_code f)) sp pc' rs); split.
  apply exec_Inop; auto.
  econstructor; eauto. 
  eapply analysis_correct_1; eauto. simpl; auto. 
  unfold transfer; rewrite H; auto.

  Case "exec_Iop".
  exists (State s' (transf_code (analyze f) (fn_code f)) sp pc' (rs#res <- v)); split.
  assert (eval_operation tge sp op rs##args = Some v).
    rewrite <- H0. apply eval_operation_preserved. exact symbols_preserved.
  generalize C; clear C.
  case (is_trivial_op op).
  intro. eapply exec_Iop; eauto. 
  caseEq (find_op (analyze f)!!pc op args). intros r FIND CODE.
  eapply exec_Iop; eauto. simpl. 
  assert (eval_operation ge sp op rs##args = Some rs#r).
    eapply find_op_correct; eauto.
    eapply wf_analyze; eauto.
  congruence.
  intros. eapply exec_Iop; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H. 
  eapply add_op_satisfiable; eauto. apply wf_analyze.

  Case "exec_Iload".
  exists (State s' (transf_code (analyze f) (fn_code f)) sp pc' (rs#dst <- v)); split.
  assert (eval_addressing tge sp addr rs##args = Some (Vptr a)).
    by rewrite <- H1; apply eval_addressing_preserved, symbols_preserved.
(*  generalize C; clear C. *)
(*  caseEq (find_load (analyze f)!!pc chunk addr args). intros r FIND CODE. *)

  intros. eapply exec_Iload; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto. 
  unfold transfer; rewrite H. 
  by auto using add_unknown_satisfiable, wf_analyze. 

  Case "exec_Istore".
  exists (State s' (transf_code (analyze f) (fn_code f)) sp pc' rs); split.
  assert (eval_addressing tge sp addr rs##args = Some (Vptr a)).
    by rewrite <- H0; apply eval_addressing_preserved, symbols_preserved.
  eapply exec_Istore; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto. 
  by unfold transfer; rewrite H. 

  Case "exec_Icall".
  exploit find_function_translated; eauto. intro FIND'.
  econstructor; split.
  eapply exec_Icall with (f := transf_fundef f); eauto.
  apply sig_preserved. 
  econstructor; eauto. 
  constructor; auto. 
  econstructor; eauto. 
  intros. eapply analysis_correct_1; eauto. simpl; auto. 
  unfold transfer; rewrite H. 
  apply empty_numbering_satisfiable.

  (* Case "exec_Itailcall". *)
  (* exploit find_function_translated; eauto. intro FIND'. *)
  (* econstructor; split. *)
  (* eapply exec_Itailcall with (f := transf_fundef f); eauto. *)
  (* apply sig_preserved.  *)
  (* econstructor; eauto.  *)

  Case "exec_Icond_true".
  econstructor; split.
  eapply exec_Icond_true; eauto. 
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H; auto.

  Case "exec_Icond_false".
  econstructor; split.
  eapply exec_Icond_false; eauto. 
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H; auto.

  Case "exec_Ireturn".
  econstructor; split.
  eapply exec_Ireturn; eauto.
  constructor; auto.

  Case "exec_Ithread_create".
  eexists; split.
  eapply exec_Ithread_create; eauto.
  constructor; eauto.
  eapply analysis_correct_1. edone. by vauto.
  by unfold transfer; rewrite H.

  Case "exec_Iatomic".
  eexists; split.
  eapply exec_Iatomic; eauto.
  constructor; eauto.
  eapply analysis_correct_1. edone. by vauto.
  unfold transfer. rewrite H.
  by auto using add_unknown_satisfiable, wf_analyze.   

  Case "exec_Ifence".
  eexists; split; [by vauto|].
  constructor; eauto.
  eapply analysis_correct_1; [edone|by vauto|].
  by unfold transfer; rewrite H.

  Case "exec_function_internal_empty".
  simpl. econstructor; split.
  eapply exec_function_internal_empty; eauto. 
  simpl. econstructor; eauto.
  apply analysis_correct_entry. 

  Case "exec_function_internal_nonempty".
  simpl. econstructor; split.
  change (fn_stacksize f) with (fn_stacksize (transf_function f)).
  eapply exec_function_internal_nonempty; eauto. 
  simpl. econstructor; eauto.
  apply analysis_correct_entry. 

  Case "exec_function_external_call".
  simpl. econstructor; split.
  eapply exec_function_external_call; eauto.
  econstructor; eauto.

  Case "exec_function_external_return".
  simpl. econstructor; split.
  eapply exec_function_external_return; eauto.
  econstructor; eauto.

  Case "exec_return".
  inv H2. inv H1.
  econstructor; split.
  eapply exec_return; eauto.
  econstructor; eauto. 

  Case "exec_return_exit".
  inv H2.
  eexists; split.
  eapply exec_return_exit. vauto. 
Qed.

Lemma init_sim_succ:
  forall {p vals tinit},
    rtl_init tge p vals = Some tinit ->
    exists sinit, rtl_init ge p vals = Some sinit /\ match_states sinit tinit.
Proof.
  intros p vals tinit INIT. unfold rtl_init in *.
  pose proof TRANSF as (MG & MF).
  specialize (MF p).
  destruct (Genv.find_funct_ptr tge p) as [[[]|]|]; try done;
    destruct (Genv.find_funct_ptr ge  p) as [[[]|]|]; try done; []; simpl in *.
  inv MF. destruct beq_nat; try done; [].
  eexists; split; try done; inv INIT; vauto. 
Qed.

Lemma init_sim_fail:
  forall {p vals},
    rtl_init tge p vals = None ->
    rtl_init ge p vals = None.
Proof.
  intros p vals INIT. unfold rtl_init in *.
  pose proof TRANSF as (MG & MF).
  specialize (MF p).
  destruct (Genv.find_funct_ptr tge p) as [[[]|]|]; try done;
    destruct (Genv.find_funct_ptr ge  p) as [[[]|]|]; try done; []; simpl in *.
  inv MF. by destruct beq_nat.
Qed.

Definition bsim_rel := @bsr _ lts tlts match_states.
Definition bsim_order := @bsc _ tlts.

End PRESERVATION.


Definition cse_match_prg (p  : rtl_sem.(SEM_PRG))
                               (p' : rtl_sem.(SEM_PRG)) : Prop :=
  transf_program p = p'.

Theorem cse_sim Mm : Sim.sim Mm Mm rtl_sem rtl_sem cse_match_prg.
Proof.
  eapply (MCsim.sim (false_pure_load_cond Mm) rtl_sem rtl_sem genv_rel
    bsim_rel (fun _ => bsim_order)); intros; simpl in *.
  - by inv MP; destruct GENVR as [GR _]. 
  - eapply Genv.exists_matching_genv_and_mem_rev
      with (match_var := fun a b => a = b), INIT.
    by apply transform_program_match, MP.
  - destruct (init_sim_succ _ _ GENVR INIT) as [si [INIT' MS]].
    by exists si; split; [|apply fsr_in_bsr].
  - eby eapply init_sim_fail.
  - eapply forward_to_backward_sim.
          apply rtl_sem.(SEM_receptive).
        apply rtl_sem.(SEM_determinate).
      apply rtl_sem.(SEM_progress_dec).
    split. by instantiate (1 := fun _ _ => False). 
    intros; exploit transf_step_correct; try edone; []; intros (? & ? & ?).
    eby right; left; eexists; split; [eapply step_weakstep|].
Qed.
