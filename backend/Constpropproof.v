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

(** Correctness proof for constant propagation. *)

Require Import Coqlib.
Require Import Maps.
Require Import Ast.
Require Import Integers.
Require Import Pointers.
Require Import Floats.
Require Import Values.
Require Import Events.
Require Import Mem.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Lattice.
Require Import Kildall.
Require Import ConstpropOp.
Require Import Constprop.
Require Import ConstpropOpproof.
Require Import Memcomp Traces.
Require Import Simulations MCsimulation.
Require Import Libtactics.

(** * Correctness of the static analysis *)

Section MYANALYSIS.

Variable ge: genv.

Definition regs_match_approx (a: D.t) (rs: regset) : Prop :=
  forall r, val_match_approx ge (D.get r a) rs#r.

Lemma regs_match_approx_top:
  forall rs, regs_match_approx D.top rs.
Proof.
  intros. red; intros. simpl. rewrite PTree.gempty. 
  unfold Approx.top, val_match_approx. auto.
Qed.

Lemma val_match_approx_increasing:
  forall a1 a2 v,
  Approx.ge a1 a2 -> val_match_approx ge a2 v -> val_match_approx ge a1 v.
Proof.
  intros until v.
  intros [A|[B|C]].
  subst a1. simpl. auto.
  subst a2. simpl. tauto.
  subst a2. auto.
Qed.

Lemma regs_match_approx_increasing:
  forall a1 a2 rs,
  D.ge a1 a2 -> regs_match_approx a2 rs -> regs_match_approx a1 rs.
Proof.
  unfold D.ge, regs_match_approx. intros.
  apply val_match_approx_increasing with (D.get r a2); auto.
Qed.

Lemma regs_match_approx_update:
  forall ra rs a v r,
  val_match_approx ge a v ->
  regs_match_approx ra rs ->
  regs_match_approx (D.set r a ra) (rs#r <- v).
Proof.
  intros; red; intros. rewrite Regmap.gsspec. 
  case (peq r0 r); intro.
  subst r0. rewrite D.gss. auto.
  rewrite D.gso; auto. 
Qed.

Lemma approx_regs_val_list:
  forall ra rs rl,
  regs_match_approx ra rs ->
  val_list_match_approx ge (approx_regs ra rl) rs##rl.
Proof.
  induction rl; simpl; intros.
  constructor.
  constructor. apply H. auto.
Qed.


(** The correctness of the static analysis follows from the results
  of module [ConstpropOpproof] and the fact that the result of
  the static analysis is a solution of the forward dataflow inequations. *)

Lemma analyze_correct_1:
  forall f pc rs pc' i,
  f.(fn_code)!pc = Some i ->
  In pc' (successors_instr i) ->
  regs_match_approx (transfer f pc (analyze f)!!pc) rs ->
  regs_match_approx (analyze f)!!pc' rs.
Proof.
  intros until i. unfold analyze. 
  caseEq (DS.fixpoint (successors f) (transfer f)
                      ((fn_entrypoint f, D.top) :: nil)).
  intros approxs; intros.
  apply regs_match_approx_increasing with (transfer f pc approxs!!pc).
  eapply DS.fixpoint_solution; eauto.
  unfold successors_list, successors. rewrite PTree.gmap. rewrite H0. auto.
  auto.
  intros. rewrite PMap.gi. apply regs_match_approx_top. 
Qed.

Lemma analyze_correct_3:
  forall f rs,
  regs_match_approx (analyze f)!!(f.(fn_entrypoint)) rs.
Proof.
  intros. unfold analyze. 
  caseEq (DS.fixpoint (successors f) (transfer f)
                      ((fn_entrypoint f, D.top) :: nil)).
  intros approxs; intros.
  apply regs_match_approx_increasing with D.top.
  eapply DS.fixpoint_entry; eauto. auto with coqlib.
  apply regs_match_approx_top. 
  intros. rewrite PMap.gi. apply regs_match_approx_top.
Qed.

End MYANALYSIS.

(** * Correctness of the code transformation *)

(** We now show that the transformed code after constant propagation
  has the same semantics as the original code. *)

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

Lemma transf_ros_correct:
  forall ros rs f approx,
  regs_match_approx ge approx rs ->
  find_function ge ros rs = Some f ->
  find_function tge (transf_ros approx ros) rs = Some (transf_fundef f).
Proof.
  intros until approx; intro MATCH.
  destruct ros; simpl.
  intro.
  exploit functions_translated; eauto. intro FIND.  
  caseEq (D.get r approx); intros; auto.
  generalize (Int.eq_spec i0 Int.zero); case (Int.eq i0 Int.zero); intros; auto.
  generalize (MATCH r). rewrite H0. intros [b [A B]].
  rewrite <- symbols_preserved in A.
  rewrite B in FIND. rewrite H1 in FIND. 
  rewrite Genv.find_funct_find_funct_ptr in FIND.
  by simpl; rewrite MPtr.add_zero_r, A in *.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  intro. apply function_ptr_translated. auto.
  congruence.
Qed.

(** The proof of semantic preservation is a simulation argument
  based on diagrams of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                   |t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The left vertical arrow represents a transition in the
  original RTL code.  The top horizontal bar is the [match_states]
  invariant between the initial state [st1] in the original RTL code
  and an initial state [st2] in the transformed code.
  This invariant expresses that all code fragments appearing in [st2]
  are obtained by [transf_code] transformation of the corresponding
  fragments in [st1].  Moreover, the values of registers in [st1]
  must match their compile-time approximations at the current program
  point.
  These two parts of the diagram are the hypotheses.  In conclusions,
  we want to prove the other two parts: the right vertical arrow,
  which is a transition in the transformed RTL code, and the bottom
  horizontal bar, which means that the [match_state] predicate holds
  between the final states [st1'] and [st2']. *)

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
   match_stackframe_intro:
      forall res c sp pc rs f,
      c = f.(RTL.fn_code) ->
      (forall v, regs_match_approx ge (analyze f)!!pc (rs#res <- v)) ->
    match_stackframes
        (Stackframe res c sp pc rs)
        (Stackframe res (transf_code (analyze f) c) sp pc rs).

Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
      forall s c sp pc rs f s'
           (CF: c = f.(RTL.fn_code))
           (MATCH: regs_match_approx ge (analyze f)!!pc rs)
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

(** The proof of simulation proceeds by case analysis on the transition
  taken in the source code. *)

Lemma transf_step_correct:
  forall s1 t s2,
  rtl_step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  exists s2', rtl_step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  (rtl_step_cases (induction 1) Case); intros; inv MS.

  Case "exec_Inop".
  exists (State s' (transf_code (analyze f) (fn_code f)) sp pc' rs); split.
  TransfInstr; intro. eapply exec_Inop; eauto.
  econstructor; eauto.
  eapply analyze_correct_1 with (pc := pc); eauto.
  simpl; auto.
  unfold transfer; rewrite H. auto.

  Case "exec_Iop".
  exists (State s' (transf_code (analyze f) (fn_code f)) sp pc' (rs#res <- v)); split.
  TransfInstr. caseEq (op_strength_reduction (approx_reg (analyze f)!!pc) op args);
  intros op' args' OSR.
  assert (eval_operation tge sp op' rs##args' = Some v).
    rewrite (eval_operation_preserved symbols_preserved). 
    generalize (op_strength_reduction_correct ge (approx_reg (analyze f)!!pc) sp rs
                  MATCH op args v).
    rewrite OSR; simpl. auto.
  generalize (eval_static_operation_correct ge op sp
               (approx_regs (analyze f)!!pc args) rs##args v
               (approx_regs_val_list _ _ _ args MATCH) H0).
  case (eval_static_operation op (approx_regs (analyze f)!!pc args)); intros;
  simpl in H2;
  eapply exec_Iop; eauto; simpl.
  congruence.
  congruence.
  elim H2; intros b [A B]. rewrite symbols_preserved. 
  rewrite A; rewrite B; auto.
  econstructor; eauto. 
  eapply analyze_correct_1 with (pc := pc); eauto.
  simpl; auto.
  unfold transfer; rewrite H. 
  apply regs_match_approx_update; auto. 
  eapply eval_static_operation_correct; eauto.
  apply approx_regs_val_list; auto.

  Case "exec_Iload".
  caseEq (addr_strength_reduction (approx_reg (analyze f)!!pc) addr args);
  intros addr' args' ASR.
  assert (eval_addressing tge sp addr' rs##args' = Some (Vptr a)).
    rewrite (eval_addressing_preserved symbols_preserved). 
    generalize (addr_strength_reduction_correct ge (approx_reg (analyze f)!!pc) sp rs
                  MATCH addr args).
    rewrite ASR; simpl. congruence. 
  TransfInstr. rewrite ASR. intro.
  exists (State s' (transf_code (analyze f) (fn_code f)) sp pc' (rs#dst <- v)); split.
  eapply exec_Iload; eauto.
  econstructor; eauto. 
  eapply analyze_correct_1; eauto. simpl; auto. 
  unfold transfer; rewrite H. 
  apply regs_match_approx_update; auto. simpl; auto.

  Case "exec_Istore".
  caseEq (addr_strength_reduction (approx_reg (analyze f)!!pc) addr args);
  intros addr' args' ASR.
  assert (eval_addressing tge sp addr' rs##args' = Some (Vptr a)).
    rewrite (eval_addressing_preserved symbols_preserved). 
    generalize (addr_strength_reduction_correct ge (approx_reg (analyze f)!!pc) sp rs
                  MATCH addr args).
    rewrite ASR; simpl. congruence. 
  TransfInstr. rewrite ASR. intro.
  exists (State s' (transf_code (analyze f) (fn_code f)) sp pc' rs); split.
  eapply exec_Istore; eauto.
  econstructor; eauto. 
  eapply analyze_correct_1; eauto. simpl; auto. 
  unfold transfer; rewrite H. auto. 

  Case "exec_Icall".
  exploit transf_ros_correct; eauto. intro FIND'.
  TransfInstr; intro.
  econstructor; split.
  eapply exec_Icall; eauto. apply sig_preserved; auto.
  constructor; auto. constructor; auto.
  econstructor; eauto. 
  intros. eapply analyze_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  apply regs_match_approx_update; auto. simpl. auto.

  (* Case "exec_Itailcall". *)
  (* exploit transf_ros_correct; eauto. intros FIND'. *)
  (* TransfInstr; intro. *)
  (* econstructor; split. *)
  (* eapply exec_Itailcall; eauto. apply sig_preserved; auto. *)
  (* constructor; auto.  *)

  Case "exec_Icond_true".
  exists (State s' (transf_code (analyze f) (fn_code f)) sp ifso rs); split. 
  caseEq (cond_strength_reduction (approx_reg (analyze f)!!pc) cond args);
  intros cond' args' CSR.
  assert (eval_condition cond' rs##args' = Some true).
    generalize (cond_strength_reduction_correct
                  ge (approx_reg (analyze f)!!pc) rs MATCH cond args).
    rewrite CSR.  intro. congruence.
  TransfInstr. rewrite CSR. 
  caseEq (eval_static_condition cond (approx_regs (analyze f)!!pc args)).
  intros b ESC. 
  generalize (eval_static_condition_correct ge cond _ _ _
               (approx_regs_val_list _ _ _ args MATCH) ESC); intro.
  replace b with true. intro; eapply exec_Inop; eauto. congruence.
  intros. eapply exec_Icond_true; eauto.
  econstructor; eauto.
  eapply analyze_correct_1; eauto.
  simpl; auto.
  unfold transfer; rewrite H; auto.

  Case "exec_Icond_false".
  exists (State s' (transf_code (analyze f) (fn_code f)) sp ifnot rs); split. 
  caseEq (cond_strength_reduction (approx_reg (analyze f)!!pc) cond args);
  intros cond' args' CSR.
  assert (eval_condition cond' rs##args' = Some false).
    generalize (cond_strength_reduction_correct
                  ge (approx_reg (analyze f)!!pc) rs MATCH cond args).
    rewrite CSR.  intro. congruence.
  TransfInstr. rewrite CSR. 
  caseEq (eval_static_condition cond (approx_regs (analyze f)!!pc args)).
  intros b ESC. 
  generalize (eval_static_condition_correct ge cond _ _ _
               (approx_regs_val_list _ _ _ args MATCH) ESC); intro.
  replace b with false. intro; eapply exec_Inop; eauto. congruence.
  intros. eapply exec_Icond_false; eauto.
  econstructor; eauto.
  eapply analyze_correct_1; eauto.
  simpl; auto.
  unfold transfer; rewrite H; auto.

  Case "exec_Ireturn".
  exists (Returnstate s' (regmap_optget or Vundef rs)); split.
  eapply exec_Ireturn; eauto. TransfInstr; auto.
  constructor; auto.

  Case "exec_Ithread_create".
  TransfInstr; intro INSTR.
  eexists; split. eby eapply exec_Ithread_create. 
  econstructor; try done; [].
  eapply analyze_correct_1. by eauto. by vauto.
  by unfold transfer; rewrite H.

  Case "exec_Iatomic".
  TransfInstr; intro INSTR. 
  eexists; split.
  eby eapply exec_Iatomic. 
  econstructor; try edone; []. 
  eapply analyze_correct_1 with (pc := pc); eauto. by vauto.
  unfold transfer; rewrite H.
  by eapply regs_match_approx_update. 

  Case "exec_Ifence".
  TransfInstr; intro INSTR. 
  eexists; split.
  eby eapply exec_Ifence. 
  econstructor; try edone; []. 
  eapply analyze_correct_1 with (pc := pc); eauto. by vauto.
  by unfold transfer; rewrite H.

  Case "exec_function_internal_empty".
  simpl. unfold transf_function.
  econstructor; split.
  eapply exec_function_internal_empty; simpl; eauto.
  simpl. econstructor; eauto.
  apply analyze_correct_3; auto.

  Case "exec_function_internal_nonempty".
  simpl. unfold transf_function; simpl. 
  change (fn_stacksize f) with 
    (fn_stacksize
      (mkfunction (fn_sig f) (fn_params f) (fn_stacksize f)
        (transf_code (analyze f) (fn_code f)) 
        (fn_entrypoint f))).  
  econstructor; split.
  eapply exec_function_internal_nonempty; simpl; eauto.
  simpl. econstructor; eauto.
  by apply analyze_correct_3; auto. 

  Case "exec_function_external_call".
  simpl. econstructor; split.
  eapply exec_function_external_call; eauto.
  eby econstructor.

  Case "exec_function_external_return".
  simpl. econstructor; split.
  eapply exec_function_external_return; eauto.
  constructor; auto.

  Case "exec_return".
  inv H2. inv H1. 
  econstructor; split.
  eapply exec_return; eauto. 
  econstructor; eauto.

  Case "exec_return_exit".
  inv H2.
  eexists; split. 
  eapply exec_return_exit.
  constructor. constructor.
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


Definition constprop_match_prg (p  : rtl_sem.(SEM_PRG))
                               (p' : rtl_sem.(SEM_PRG)) : Prop :=
  transf_program p = p'.

Theorem constprop_sim Mm : Sim.sim Mm Mm rtl_sem rtl_sem constprop_match_prg.
Proof.
  eapply (@MCsim.sim _ _ (false_pure_load_cond Mm) rtl_sem rtl_sem genv_rel
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

