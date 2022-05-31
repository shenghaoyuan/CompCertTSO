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

(** Correctness proof for code linearization *)

Require Import Coqlib.
Require Import Maps.
Require Import Ordered.
Require Import FSets.
Require Import Ast.
Require Import Integers.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Errors.
Require Import Op.
Require Import Locations.
Require Import LTL.
Require Import LTLtyping.
Require Import LTLin.
Require Import Linearize.
Require Import Lattice.
Require Import Memcomp Traces.
Require Import Simulations MCsimulation.
Require Import Libtactics.

Module NodesetFacts := FSetFacts.Facts(Nodeset).


Definition genv_rel : LTL.genv -> LTLin.genv -> Prop :=
 (fun x y => Genv.genv_match (fun a b => transf_fundef a = OK b) y x).


Section LINEARIZATION.


(* Assume fixed global environments that are related: *)
Variables (ge : LTL.genv) (tge : LTLin.genv).
Hypothesis TRANSF: genv_rel ge tge.

Let lts := (mklts thread_labels (ltl_step ge)).
Let tlts := (mklts thread_labels (ltlin_step tge)).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  exists tf,
  Genv.find_funct_ptr tge v = Some tf /\ transf_fundef f = OK tf.
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
  exists tf,
  Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
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
  forall f tf,
  transf_fundef f = OK tf ->
  LTLin.funsig tf = LTL.funsig f.
Proof.
  intros [] ? H; monadInv H; [monadInv EQ|]; done.
Qed.

Lemma find_function_translated:
  forall ros ls f,
  LTL.find_function ge ros ls = Some f ->
  exists tf,
  find_function tge ros ls = Some tf /\ transf_fundef f = OK tf.
Proof.
  intros [l|] ls f; simpl.
    destruct (ls l); try done; apply functions_translated; done.
  rewrite symbols_preserved; destruct (Genv.find_symbol ge i); try done.
  apply function_ptr_translated; done.
Qed.


(** * Correctness of reachability analysis *)

(** The entry point of the function is reachable. *)

Lemma reachable_entrypoint:
  forall f, (reachable f)!!(f.(fn_entrypoint)) = true.
Proof.
  intros. unfold reachable.
  caseEq (reachable_aux f).
  unfold reachable_aux; intros reach A.
  assert (LBoolean.ge reach!!(f.(fn_entrypoint)) true).
  eapply DS.fixpoint_entry. eexact A. auto with coqlib.
  unfold LBoolean.ge in H. tauto.
  intros. apply PMap.gi.
Qed.

(** The successors of a reachable instruction are reachable. *)

Lemma reachable_successors:
  forall f pc pc' i,
  f.(LTL.fn_code)!pc = Some i -> In pc' (successors_instr i) ->
  (reachable f)!!pc = true ->
  (reachable f)!!pc' = true.
Proof.
  intro f. unfold reachable.
  caseEq (reachable_aux f).
  unfold reachable_aux. intro reach; intros.
  assert (LBoolean.ge reach!!pc' reach!!pc).
  change (reach!!pc) with ((fun pc r => r) pc (reach!!pc)).
  eapply DS.fixpoint_solution. eexact H.
  unfold Kildall.successors_list, successors. rewrite PTree.gmap.
  rewrite H0; auto.
  elim H3; intro. congruence. auto.
  intros. apply PMap.gi.
Qed.





(** * Properties of node enumeration *)

(** An enumeration of CFG nodes is correct if the following conditions hold:
- All nodes for reachable basic blocks must be in the list.
- The list is without repetition (so that no code duplication occurs).

We prove that the result of the [enumerate] function satisfies both
conditions. *)

Lemma nodeset_of_list_correct:
  forall l s s',
  nodeset_of_list l s = OK s' ->
  NoDup l
  /\ (forall pc, Nodeset.In pc s' <-> Nodeset.In pc s \/ In pc l)
  /\ (forall pc, In pc l -> ~Nodeset.In pc s).
Proof.
  induction l; simpl; intros. 
  inv H. split. constructor. split. intro; tauto. intros; tauto.
  generalize H; clear H; caseEq (Nodeset.mem a s); intros.
  inv H0.
  exploit IHl; eauto. intros [A [B C]].
  split. constructor; auto. red; intro. elim (C a H1). apply Nodeset.add_1. hnf. auto.
  split. intros. rewrite B. rewrite NodesetFacts.add_iff. 
  unfold Nodeset.E.eq. unfold OrderedPositive.eq. tauto.
  intros. destruct H1. subst pc. rewrite NodesetFacts.not_mem_iff. auto.
  generalize (C pc H1). rewrite NodesetFacts.add_iff. tauto.
Qed.

Lemma check_reachable_correct:
  forall f reach s pc i,
  check_reachable f reach s = true ->
  f.(LTL.fn_code)!pc = Some i ->
  reach!!pc = true ->
  Nodeset.In pc s.
Proof.
  intros f reach s.
  assert (forall l ok, 
    List.fold_left (fun a p => check_reachable_aux reach s a (fst p) (snd p)) l ok = true ->
    ok = true /\
    (forall pc i,
     In (pc, i) l ->
     reach!!pc = true ->
     Nodeset.In pc s)).
  induction l; simpl; intros.
  split. auto. intros. destruct H0.
  destruct a as [pc1 i1]. simpl in H. 
  exploit IHl; eauto. intros [A B].
  unfold check_reachable_aux in A. 
  split. destruct (reach!!pc1). elim (andb_prop _ _ A). auto. auto.
  intros. destruct H0. inv H0. rewrite H1 in A. destruct (andb_prop _ _ A). 
  apply Nodeset.mem_2; auto.
  eauto.

  intros pc i. unfold check_reachable. rewrite PTree.fold_spec. intros.
  exploit H; eauto. intros [A B]. eapply B; eauto. 
  apply PTree.elements_correct. eauto.
Qed.

Lemma enumerate_complete:
  forall f enum pc i,
  enumerate f = OK enum ->
  f.(LTL.fn_code)!pc = Some i ->
  (reachable f)!!pc = true ->
  In pc enum.
Proof.
  intros until i. unfold enumerate. 
  set (reach := reachable f).
  intros. monadInv H. 
  generalize EQ0; clear EQ0. caseEq (check_reachable f reach x); intros; inv EQ0.
  exploit check_reachable_correct; eauto. intro.
  exploit nodeset_of_list_correct; eauto. intros [A [B C]].
  rewrite B in H2. destruct H2. elim (Nodeset.empty_1 H2). auto.
Qed.

Lemma enumerate_norepet:
  forall f enum,
  enumerate f = OK enum ->
  NoDup enum.
Proof.
  intros until enum. unfold enumerate. 
  set (reach := reachable f).
  intros. monadInv H. 
  generalize EQ0; clear EQ0. caseEq (check_reachable f reach x); intros; inv EQ0.
  exploit nodeset_of_list_correct; eauto. intros [A [B C]]. auto.
Qed.

(** * Properties related to labels *)

(** If labels are globally unique and the LTLin code [c] contains
  a subsequence [Llabel lbl :: c1], then [find_label lbl c] returns [c1].
*)

Fixpoint unique_labels (c: code) : Prop :=
  match c with
  | nil => True
  | Llabel lbl :: c => ~(In (Llabel lbl) c) /\ unique_labels c
  | i :: c => unique_labels c
  end.

Lemma find_label_unique:
  forall lbl c1 c2 c3,
  is_tail (Llabel lbl :: c1) c2 ->
  unique_labels c2 ->
  find_label lbl c2 = Some c3 ->
  c1 = c3.
Proof.
  induction c2.
  simpl; intros; discriminate.
  intros c3 TAIL UNIQ. simpl.
  generalize (is_label_correct lbl a). case (is_label lbl a); intro ISLBL.
  subst a. intro. inversion TAIL. congruence. 
  elim UNIQ; intros. elim H4. apply is_tail_in with c1; auto.
  inversion TAIL. congruence. apply IHc2. auto. 
  destruct a; simpl in UNIQ; tauto.
Qed.

(** Correctness of the [starts_with] test. *)


Lemma starts_with_correct:
  forall lbl c1 c2 c3 s f sp ls,
  is_tail c1 c2 ->
  unique_labels c2 ->
  starts_with lbl c1 = true ->
  find_label lbl c2 = Some c3 ->
  weakstep tlts (State s f sp c1 ls) TEtau (State s f sp c3 ls).
Proof.
  induction c1.
  simpl; intros; try done.
  simpl starts_with. destruct a; try done. 
  intros.
  destruct (peq lbl l).
    eexists; eexists; repeat split; try apply taustar_refl; simpl.
    subst l.
    replace c3 with c1; [|apply find_label_unique with lbl c2; done].
    constructor.
  apply taustar_weakstep with (State s f sp c1 ls).
    econstructor; constructor; done.
  apply IHc1 with c2; try assumption.
  eapply is_tail_cons_left; eassumption.
Qed.


(** Connection between [find_label] and linearization. *)

Lemma find_label_add_branch:
  forall lbl k s,
  find_label lbl (add_branch s k) = find_label lbl k.
Proof.
  intros. unfold add_branch. destruct (starts_with s k); auto.
Qed.

Lemma find_label_lin_instr:
  forall lbl k b,
  find_label lbl (linearize_instr b k) = find_label lbl k.
Proof.
  intros lbl k. generalize (find_label_add_branch lbl k); intro.
  induction b; simpl; auto.
  case (starts_with n k); simpl; auto.
Qed.

Lemma find_label_lin_rec:
  forall f enum pc b,
  In pc enum ->
  f.(LTL.fn_code)!pc = Some b ->
  exists k, find_label pc (linearize_body f enum) = Some (linearize_instr b k).
Proof.
  induction enum; intros.
  elim H.
  case (peq a pc); intro.
  subst a. exists (linearize_body f enum).
  simpl. rewrite H0. simpl. rewrite peq_true. auto.
  assert (In pc enum). simpl in H. tauto.
  elim (IHenum pc b H1 H0). intros k FIND.
  exists k. simpl. destruct (LTL.fn_code f)!a. 
  simpl. rewrite peq_false. rewrite find_label_lin_instr. auto. auto.
  auto.
Qed.

Lemma find_label_lin:
  forall f tf pc b,
  transf_function f = OK tf ->
  f.(LTL.fn_code)!pc = Some b ->
  (reachable f)!!pc = true ->
  exists k,
  find_label pc (fn_code tf) = Some (linearize_instr b k).
Proof.
  intros. monadInv H. simpl. 
  rewrite find_label_add_branch. apply find_label_lin_rec.
  eapply enumerate_complete; eauto. auto.
Qed.

Lemma find_label_lin_inv:
  forall f tf pc b k,
  transf_function f = OK tf ->
  f.(LTL.fn_code)!pc = Some b ->
  (reachable f)!!pc = true ->
  find_label pc (fn_code tf) = Some k ->
  exists k', k = linearize_instr b k'.
Proof.
  intros. exploit find_label_lin; eauto. intros [k' FIND].
  exists k'. congruence.
Qed.

Lemma find_label_lin_succ:
  forall f tf s,
  transf_function f = OK tf ->
  valid_successor f s ->
  (reachable f)!!s = true ->
  exists k,
  find_label s (fn_code tf) = Some k.
Proof.
  intros f tf s H [i AT] H1.
  exploit find_label_lin; try eassumption. 
  intros [k FIND].
  exists (linearize_instr i k); assumption.
Qed.


(** Unique label property for linearized code. *)

Lemma label_in_add_branch:
  forall lbl s k,
  In (Llabel lbl) (add_branch s k) -> In (Llabel lbl) k.
Proof.
  intros until k; unfold add_branch.
  destruct (starts_with s k); simpl; intuition congruence.
Qed.

Lemma label_in_lin_instr:
  forall lbl k b,
  In (Llabel lbl) (linearize_instr b k) -> In (Llabel lbl) k.
Proof.
  induction b; simpl; intros;
  try (apply label_in_add_branch with n; intuition congruence);
  try (intuition congruence).
  destruct (starts_with n k); simpl in H.
  apply label_in_add_branch with n; intuition congruence.
  apply label_in_add_branch with n0; intuition congruence.
Qed.

Lemma label_in_lin_rec:
  forall f lbl enum,
  In (Llabel lbl) (linearize_body f enum) -> In lbl enum.
Proof.
  induction enum.
  simpl; auto.
  simpl. destruct (LTL.fn_code f)!a. 
  simpl. intros [A|B]. left; congruence. 
  right. apply IHenum. eapply label_in_lin_instr; eauto.
  intro; right; auto.
Qed.

Lemma unique_labels_add_branch:
  forall lbl k,
  unique_labels k -> unique_labels (add_branch lbl k).
Proof.
  intros; unfold add_branch. 
  destruct (starts_with lbl k); simpl; intuition.
Qed.

Lemma unique_labels_lin_instr:
  forall k b,
  unique_labels k -> unique_labels (linearize_instr b k).
Proof.
  induction b; intro; simpl; auto; try (apply unique_labels_add_branch; auto).
  case (starts_with n k); simpl; apply unique_labels_add_branch; auto.
Qed.

Lemma unique_labels_lin_rec:
  forall f enum,
  NoDup enum ->
  unique_labels (linearize_body f enum).
Proof.
  induction enum.
  simpl; auto.
  intro. simpl. destruct (LTL.fn_code f)!a. 
  simpl. split. red. intro. inversion H. elim H3.
  apply label_in_lin_rec with f. 
  apply label_in_lin_instr with i. auto.
  apply unique_labels_lin_instr. apply IHenum. inversion H; auto.
  apply IHenum. inversion H; auto.
Qed.

Lemma unique_labels_transf_function:
  forall f tf,
  transf_function f = OK tf ->
  unique_labels (fn_code tf).
Proof.
  intros. monadInv H. simpl.
  apply unique_labels_add_branch. 
  apply unique_labels_lin_rec. eapply enumerate_norepet; eauto.
Qed.

(** Correctness of [add_branch]. *)

Lemma is_tail_find_label:
  forall lbl c2 c1,
  find_label lbl c1 = Some c2 -> is_tail c2 c1.
Proof.
  induction c1; simpl.
  intros; discriminate.
  case (is_label lbl a). intro. injection H; intro. subst c2.
  constructor. constructor.
  intro. constructor. auto. 
Qed.

Lemma is_tail_add_branch:
  forall lbl c1 c2, is_tail (add_branch lbl c1) c2 -> is_tail c1 c2.
Proof.
  intros until c2. unfold add_branch. destruct (starts_with lbl c1).
  auto. eauto with coqlib.
Qed.

Lemma add_branch_correct:
  forall lbl c k s f tf sp ls,
  transf_function f = OK tf ->
  is_tail k tf.(fn_code) ->
  find_label lbl tf.(fn_code) = Some c ->
  weakstep tlts (State s tf sp (add_branch lbl k) ls)
          TEtau (State s tf sp c ls).
Proof.
  intros. unfold add_branch.
  caseEq (starts_with lbl k); intro SW.
  eapply starts_with_correct; eauto.
  eapply unique_labels_transf_function; eauto.
  eexists; eexists; repeat split; 
   [apply taustar_refl | constructor; eassumption | constructor].
Qed.

(** * Correctness of linearization *)

(** The proof of semantic preservation is a simulation argument
  based on diagrams of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                  +|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The invariant (horizontal lines above) is the [match_states]
  predicate defined below.  It captures the fact that the flow
  of data is the same in the source and linearized codes.
  Moreover, whenever the source state is at node [pc] in its
  control-flow graph, the transformed state is at a code
  sequence [c] that starts with the label [pc]. *)

Inductive match_stackframes: LTL.stackframe -> LTLin.stackframe -> Prop :=
  | match_stackframe_intro:
      forall res f sp pc ls tf c,
      transf_function f = OK tf ->
      (reachable f)!!pc = true ->
      valid_successor f pc ->
      is_tail c (fn_code tf) ->
      wt_function f ->
      match_stackframes
        (LTL.Stackframe res f sp ls pc)
        (LTLin.Stackframe res tf sp ls (add_branch pc c)).

Inductive match_states: LTL.state -> LTLin.state -> Prop :=
  | match_states_intro:
      forall s f sp pc ls tf ts c
        (STACKS: list_forall2 match_stackframes s ts)
        (TRF: transf_function f = OK tf)
        (REACH: (reachable f)!!pc = true)
        (AT: find_label pc (fn_code tf) = Some c)
        (WTF: wt_function f),
      match_states (LTL.State s f sp pc ls)
                   (LTLin.State ts tf sp c ls)
  | match_states_call:
      forall s f ls tf ts,
      list_forall2 match_stackframes s ts ->
      transf_fundef f = OK tf ->
      wt_fundef f ->
      match_states (LTL.Callstate s f ls)
                   (LTLin.Callstate ts tf ls)
  | match_states_return:
      forall s ls ts,
      list_forall2 match_stackframes s ts ->
      match_states (LTL.Returnstate s ls)
                   (LTLin.Returnstate ts ls)
  | match_states_blocked:
      forall s ts x,
      list_forall2 match_stackframes s ts ->
      match_states (LTL.Blockedstate s x)
                   (LTLin.Blockedstate ts x).

Definition order: LTL.state -> LTL.state -> Prop := fun x y => False.

Definition wt_genv := 
  forall f, match (Genv.find_funct ge f) with 
    | Some x => wt_fundef x 
    | None => True
    end.

Hypothesis WTGENV : wt_genv.

Lemma my_forward_sim:
  @forward_sim thread_labels lts tlts match_states order.
Proof.
  unfold lts,tlts.

  split; [ done |]; simpl.
  (ltl_step_cases (destruct 1) Case); intros MS; try (inv MS);
   try (generalize (wt_instrs _ WTF _ _ H); intro WTI); simpl;
   try (destruct (find_label_lin_inv _ _ _ _ _ TRF H REACH AT) as [c' EQ];
        simpl in EQ; subst c);
   right; left.

  Case "exec_Lnop".
  assert (REACH': (reachable f)!!pc' = true)
    by (eapply reachable_successors; eauto; simpl; auto).
  exploit find_label_lin_succ; eauto. inv WTI; auto. intros [c'' AT'].
  eexists; split; [|econstructor; eauto].
  eapply add_branch_correct; 
    [| eapply is_tail_add_branch; eapply is_tail_find_label |]; eassumption.

  Case "exec_Lop".
  assert (REACH': (reachable f)!!pc' = true)
    by (eapply reachable_successors; eauto; simpl; auto).
  exploit find_label_lin_succ; eauto. inv WTI; auto. intros [c'' AT'].
  eexists; split; [|econstructor;eauto].
  eapply steptau_weakstep.
  eapply exec_Lop with (v := v); eauto.
  rewrite <- H0. apply eval_operation_preserved. exact symbols_preserved.
  eapply add_branch_correct; 
    [| eapply is_tail_add_branch; eapply is_tail_cons_left; eapply is_tail_find_label|];
    eassumption.

  Case "exec_Lload".
  assert (REACH': (reachable f)!!pc' = true)
    by (eapply reachable_successors; eauto; simpl; auto).
  exploit find_label_lin_succ; eauto. inv WTI; auto. intros [c'' AT'].
  eexists; split; [|econstructor;eauto].
  eapply step_taustar_weakstep; simpl.
  apply exec_Lload; auto.
  rewrite <- H1. apply eval_addressing_preserved. exact symbols_preserved.
  apply weaksteptau_taustar; eapply add_branch_correct; 
    [|eapply is_tail_add_branch; eapply is_tail_cons_left; eapply is_tail_find_label|]; 
    eassumption.

  Case "exec_Lstore".
  assert (REACH': (reachable f)!!pc' = true)
    by (eapply reachable_successors; eauto; simpl; auto).
  exploit find_label_lin_succ; eauto. inv WTI; auto. intros [c'' AT'].
  eexists; split; [|econstructor;eauto].
  eapply step_taustar_weakstep; simpl.
  apply exec_Lstore; auto.
  rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
  apply weaksteptau_taustar; eapply add_branch_correct; 
    [|eapply is_tail_add_branch; eapply is_tail_cons_left; eapply is_tail_find_label|]; 
    eassumption.

  Case "exec_Lcall".
  assert (REACH': (reachable f)!!pc' = true)
    by (eapply reachable_successors; eauto; simpl; auto).
  assert (VALID: valid_successor f pc') by (inv WTI; auto).
  exploit find_function_translated; eauto. intros [tf' [A B]].
  eexists; split.
    apply step_weakstep.
    eapply exec_Lcall with (f' := tf'); eauto; symmetry; apply sig_preserved; done.

  econstructor; eauto.
    constructor; auto; econstructor; eauto;
    eapply is_tail_add_branch; eapply is_tail_cons_left; 
    eapply is_tail_find_label; eassumption.

  destruct ros as [l|i]; simpl in H0.
    specialize (WTGENV (rs l)); rewrite H0 in *; done.
  destruct (Genv.find_symbol ge i); try done.
  specialize (WTGENV (Vptr p)); simpl in *; rewrite H0 in *; done.

  (* Case "exec_Ltailcall". *)
  (* exploit find_function_translated; eauto. intros [tf' [A B]]. *)
  (* eexists; split. *)
  (*   eapply step_weakstep; simpl. *)
  (*   by eapply exec_Ltailcall with (f' := tf'); try done; symmetry; apply sig_preserved. *)
  (* econstructor; eauto. *)

  (* destruct ros as [l|i]; simpl in H0. *)
  (*   specialize (WTGENV (rs l)); rewrite H0 in *; done. *)
  (* destruct (Genv.find_symbol ge i); try done. *)
  (* specialize (WTGENV (Vptr p)); simpl in *; rewrite H0 in *; done. *)

  Case "exec_Lcond_true".
  assert (REACH': (reachable f)!!ifso = true)
    by (eapply reachable_successors; eauto; simpl; auto).
  exploit find_label_lin_succ; eauto. inv WTI; auto. intros [c'' AT'].
  destruct (starts_with ifso c').
    eexists; split; [|econstructor;eauto].
    eapply step_taustar_weakstep.  
      eapply exec_Lcond_false; eauto;
      change false with (negb true); apply eval_negate_condition; auto.
    apply weaksteptau_taustar; eapply add_branch_correct; 
      [|eapply is_tail_add_branch; eapply is_tail_cons_left; eapply is_tail_find_label|]; 
      eassumption.
  eexists; split; [|econstructor;eauto].
  eapply step_weakstep; eapply exec_Lcond_true; eauto. 

  Case "exec_Lcond_false".
  assert (REACH': (reachable f)!!ifnot = true)
    by (eapply reachable_successors; eauto; simpl; auto).
  exploit find_label_lin_succ; eauto. inv WTI; auto. intros [c'' AT'].
  destruct (starts_with ifso c').
    eexists; split; [|econstructor;eauto].
    apply step_weakstep.
    eapply exec_Lcond_true; eauto;
    change true with (negb false); apply eval_negate_condition; auto; done.
 
  eexists; split; [|econstructor;eauto].
  eapply step_taustar_weakstep; [apply exec_Lcond_false; done | ].
  apply weaksteptau_taustar; eapply add_branch_correct; 
    [|eapply is_tail_add_branch; eapply is_tail_cons_left; eapply is_tail_find_label|]; 
    eassumption.

  Case "exec_Lreturn".
  eexists; split; [|econstructor;eauto].
  apply step_weakstep; eapply exec_Lreturn; eauto.

  Case "exec_Lthreadcreate".
  assert (REACH': (reachable f)!!pc' = true)
    by (eapply reachable_successors; eauto; simpl; auto).
  exploit find_label_lin_succ; eauto. inv WTI; auto. intros [c'' AT'].
  eexists; split; [|econstructor;eauto].
  eapply step_taustar_weakstep.
  eapply exec_Lthreadcreate; eauto.
  apply weaksteptau_taustar; eapply add_branch_correct; 
    [| eapply is_tail_add_branch; eapply is_tail_cons_left; eapply is_tail_find_label|];
    eassumption.

  Case "exec_Latomic".
  assert (REACH': (reachable f)!!pc' = true)
    by (eapply reachable_successors; eauto; simpl; auto).
  exploit find_label_lin_succ; eauto. inv WTI; auto. intros [c'' AT'].
  eexists; split; [|econstructor;eauto].
  eapply step_taustar_weakstep.
  eapply exec_Latomic; eauto.
  apply weaksteptau_taustar; eapply add_branch_correct; 
    [| eapply is_tail_add_branch; eapply is_tail_cons_left; eapply is_tail_find_label|];
    eassumption.

  Case "exec_Lfence".
  assert (REACH': (reachable f)!!pc' = true)
    by (eapply reachable_successors; eauto; simpl; auto).
  exploit find_label_lin_succ; eauto. inv WTI; auto. intros [c'' AT'].
  eexists; split; [|econstructor;eauto].
  eapply step_taustar_weakstep.
  eapply exec_Lfence; eauto.
  apply weaksteptau_taustar; eapply add_branch_correct; 
    [| eapply is_tail_add_branch; eapply is_tail_cons_left; eapply is_tail_find_label|];
    eassumption.
 
  Case "exec_function_internal_empty".
  assert (REACH: (reachable f)!!(LTL.fn_entrypoint f) = true) 
    by apply reachable_entrypoint. 
  monadInv H7. inv H8.
  exploit (find_label_lin_succ _ _ f.(fn_entrypoint) EQ); try done.
    inv H1; done.
  intros [c'' AT'].

  generalize EQ; intro EQ'; simpl in *.
  monadInv EQ. simpl in *.
  eexists; split. 
    eapply step_taustar_weakstep.
      eapply exec_function_internal_empty; done.
    apply weaksteptau_taustar; eapply add_branch_correct;
      [ eassumption
      | eapply is_tail_add_branch; constructor
      | eassumption].
  by constructor. 

  Case "exec_function_internal_nonempty".
  assert (REACH: (reachable f)!!(LTL.fn_entrypoint f) = true) 
    by apply reachable_entrypoint. 
  monadInv H8. inv H9.
  exploit (find_label_lin_succ _ _ f.(fn_entrypoint) EQ);
    [inv H0; auto; done| assumption |]; intros [c'' AT'].

  generalize EQ; intro EQ'; simpl in *.
  monadInv EQ. simpl in *.
  eexists; split; [|econstructor; eassumption].
  eapply step_taustar_weakstep.
    eapply exec_function_internal_nonempty; done.
  apply weaksteptau_taustar; eapply add_branch_correct;
    [ eassumption
    | eapply is_tail_add_branch; constructor
    | eassumption].

  Case "exec_function_external_call".
  monadInv H6. 
  eexists; split; [|econstructor;eauto].
  apply step_weakstep; eapply exec_function_external_call; edone. 

  Case "exec_function_external_return".
  eexists; split; [|econstructor;eauto].
  apply step_weakstep; apply exec_function_external_return; done.

  Case "exec_return".
  inv H2. inv H1.
  exploit find_label_lin_succ; eauto; intros [c' AT].
  eexists; split; [|econstructor;eauto].
  eapply steptau_weakstep; [eapply exec_return; eauto; done|].
  eapply add_branch_correct; eassumption.

  Case "exec_return_exit". 
  inv H2.
  eexists; split.
  apply step_weakstep; eapply exec_return_exit. vauto.
Qed.

Lemma init_sim_succ:
  forall {p vals tinit},
    ltlin_init tge p vals = Some tinit ->
    exists sinit, ltl_init ge p vals = Some sinit /\ match_states sinit tinit.
Proof.
  intros p vals tinit INIT. unfold ltlin_init, ltl_init in *. 
  pose proof TRANSF as (MG & MF).
  specialize (MF p).
  destruct (Genv.find_funct_ptr tge p);
    destruct (Genv.find_funct_ptr ge  p) as [] _eqn:Eg; try done; [].
  destruct f0; destruct f; try done. 
  pose proof MF as MF'. monadInv MF. monadInv EQ; simpl in *.
  destruct beq_nat; inv INIT.
  eexists. split. edone. eapply match_states_call. constructor. done.
  specialize (WTGENV (Vptr p)). simpl in WTGENV. by rewrite Eg in WTGENV.
Qed.

Lemma init_sim_fail:
  forall {p vals},
    ltlin_init tge p vals = None ->
    ltl_init ge p vals = None.
Proof.
  intros p vals INIT. unfold ltlin_init, ltl_init in *. 
  pose proof TRANSF as (MG & MF).
  specialize (MF p).
  by destruct (Genv.find_funct_ptr tge p) as [[[]|]|]; try done;
    destruct (Genv.find_funct_ptr ge  p) as [[[]|]|]; try done; simpl in *;
      monadInv MF; monadInv EQ; destruct beq_nat.
Qed.

(* JS PARAM:
Lemma init_sim_succ:
  forall {p vals tinit},
    ltlin_init tge p vals = Some tinit ->
    exists sinit, ltl_init ge p vals = Some sinit /\ match_states sinit tinit.
Proof.
  intros p vals tinit INIT. unfold ltlin_init, ltl_init in *. 
  pose proof TRANSF as (MG & MF).
  specialize (MF p).
  destruct (Genv.find_funct_ptr tge p);
    destruct (Genv.find_funct_ptr ge  p) as [] _eqn:Eg; try done; [].
  destruct f0; destruct f; try done. 
  pose proof MF as MF'. inv MF.
  assert (SG: sig_args (LTL.fn_sig f0) = nil).
    monadInv H0.
    destruct f0. monadInv EQ. simpl in *. by destruct sig_args.
  rewrite SG. destruct sig_args; try done; [].
  eexists. split. edone. inv INIT. constructor. constructor. done.
  specialize (WTGENV (Vptr p)). simpl in WTGENV. by rewrite Eg in WTGENV.
Qed.

Lemma init_sim_fail:
  forall {p vals},
    ltlin_init tge p vals = None ->
    ltl_init ge p vals = None.
Proof.
  intros p vals INIT. unfold ltlin_init, ltl_init in *. 
  pose proof TRANSF as (MG & MF).
  specialize (MF p).
  destruct (Genv.find_funct_ptr tge p) as [[[]|]|]; try done;
    destruct (Genv.find_funct_ptr ge  p) as [[[]|]|]; try done; simpl in *;
      monadInv MF. 
  unfold transf_function in EQ. monadInv EQ.
  by destruct sig_args.
Qed.
*)

Definition bsim_rel := @bsr _ lts tlts match_states.
Definition bsim_order := @bsc _ tlts.

End LINEARIZATION.

Definition full_genv_rel (ge : LTL.genv) (tge : LTLin.genv) :=
  genv_rel ge tge /\ wt_genv ge.

Definition lin_match_prg (p  : ltl_sem.(SEM_PRG))
                         (p' : ltlin_sem.(SEM_PRG)) : Prop := 
  wt_program p /\ transf_program p = OK p'.

(** The whole-system backward simulation for the [Linearize]
    phase. *)
Theorem linearize_sim Mm : Sim.sim Mm Mm ltl_sem ltlin_sem lin_match_prg.
Proof.
  eapply (MCsim.sim (false_pure_load_cond Mm) ltl_sem ltlin_sem full_genv_rel 
    bsim_rel (fun _ => bsim_order)); intros; simpl in *.
  - destruct GENVR as [[GR FR] _]. rewrite GR.
    by rewrite (transform_partial_program_main _ _ (proj2 MP)).
  - destruct (Genv.exists_matching_genv_and_mem_rev
                  (transform_partial_program_match _ _ (proj2 MP)) INIT) 
      as [sge [INIT' GEM]].
    exists sge. split. done.
    split. done.
    intro f. 
    destruct (Genv.find_funct sge f) as [fd|] _eqn : Efd; [|done].
    set (P f' := exists id, In (id, f') src_prog.(prog_funct)).
    assert (II: forall id' f', In (id', f') src_prog.(prog_funct) -> P f').
      intros id' f' IN. eby eexists.
    pose proof (Genv.find_funct_prop P f INIT' II Efd) as [id IN].
    by specialize (proj1 MP _ _ IN).
  - destruct (init_sim_succ _ _ (proj1 GENVR) (proj2 GENVR) INIT) 
      as [si [INIT' MS]].
    exists si. split. done.
    by apply fsr_in_bsr. 
  - eby destruct GENVR; eapply init_sim_fail.
  - eapply forward_to_backward_sim. 
          apply ltl_sem.(SEM_receptive).
        apply ltlin_sem.(SEM_determinate).
      apply ltl_sem.(SEM_progress_dec).
    by destruct GENR; apply my_forward_sim.
Qed.
