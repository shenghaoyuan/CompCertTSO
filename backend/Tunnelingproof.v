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

(** Correctness proof for the branch tunneling optimization. *)

Require Import Coqlib.
Require Import Maps.
Require Import UnionFind.
Require Import Ast.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import LTL.
Require Import Tunneling.
Require Import Simulations MCsimulation.
Require Import Memcomp Traces.
Require Import Libtactics.


(* Relation that maps global environments... *)
Definition genv_rel : genv -> genv -> Prop :=
 (fun x y => Genv.genv_match (fun a b => tunnel_fundef a = b) y x).

(** * Properties of the branch map computed using union-find. *)

(** A variant of [record_goto] that also incrementally computes a measure [f: node -> nat]
  counting the number of [Lnop] instructions starting at a given [pc] that were eliminated. *)

Definition measure_edge (u: U.t) (pc s: node) (f: node -> nat) : node -> nat :=
  fun x => if peq (U.repr u s) pc then f x
           else if peq (U.repr u x) pc then (f x + f s + 1)%nat
           else f x.

Definition record_goto' (uf: U.t * (node -> nat)) (pc: node) (i: instruction) : U.t * (node -> nat) :=
  match i with
  | Lnop s => let (u, f) := uf in (U.union u pc s, measure_edge u pc s f)
  | _ => uf
  end.

Definition branch_map_correct (c: code) (uf: U.t * (node -> nat)): Prop :=
  forall pc,
  match c!pc with
  | Some(Lnop s) =>
      U.repr (fst uf) pc = pc \/ (U.repr (fst uf) pc = U.repr (fst uf) s /\ snd uf s < snd uf pc)%nat
  | _ =>
      U.repr (fst uf) pc = pc
  end.

Lemma record_gotos'_correct:
  forall c,
  branch_map_correct c (PTree.fold record_goto' c (U.empty, fun (x: node) => O)).
Proof.
  intros.
  apply PTree_Properties.fold_rec with (P := fun c uf => branch_map_correct c uf).

(* extensionality *)
  intros. red; intros. rewrite <- H. apply H0.

(* base case *)
  red; intros; simpl. rewrite PTree.gempty. apply U.repr_empty.

(* inductive case *)
  intros m uf pc i; intros. destruct uf as [u f]. 
  assert (PC: U.repr u pc = pc). 
    generalize (H1 pc). rewrite H. auto.
  assert (record_goto' (u, f) pc i = (u, f)
          \/ exists s, i = Lnop s /\ record_goto' (u, f) pc i = (U.union u pc s, measure_edge u pc s f)).
    unfold record_goto'; simpl. destruct i; auto. right. exists n; auto.
  destruct H2 as [B | [s [EQ B]]].

(* u and f are unchanged *)
  rewrite B.
  red. intro pc'. simpl. rewrite PTree.gsspec. destruct peq. subst pc'. 
  destruct i; auto.
  apply H1. 

(* i is Lnop s, u becomes union u pc s, f becomes measure_edge u pc s f *)
  rewrite B.
  red. intro pc'. simpl. rewrite PTree.gsspec. destruct peq. subst pc'. rewrite EQ.

(* The new instruction *)
  rewrite (U.repr_union_2 u pc s); auto. rewrite U.repr_union_3. 
  unfold measure_edge. destruct (peq (U.repr u s) pc). auto. right. split. auto.
  rewrite PC. rewrite peq_true. omega.

(* An old instruction *)
  assert (U.repr u pc' = pc' -> U.repr (U.union u pc s) pc' = pc').
    intro. rewrite <- H2 at 2. apply U.repr_union_1. congruence. 
  generalize (H1 pc'). simpl. destruct (m!pc'); auto. destruct i0; auto.
  intros [P | [P Q]]. left; auto. right.
  split. apply U.sameclass_union_2. auto.
  unfold measure_edge. destruct (peq (U.repr u s) pc). auto.
  rewrite P. destruct (peq (U.repr u n0) pc). omega. auto. 
Qed.

Definition record_gotos' (f: function) :=
  PTree.fold record_goto' f.(fn_code) (U.empty, fun (x: node) => O).

Lemma record_gotos_gotos':
  forall f, fst (record_gotos' f) = record_gotos f.
Proof.
  intros. unfold record_gotos', record_gotos. 
  repeat rewrite PTree.fold_spec.
  generalize (PTree.elements (fn_code f)) (U.empty) (fun _ : node => O).
  induction l; intros; simpl.
  auto.
  unfold record_goto' at 2. unfold record_goto at 2. 
  destruct (snd a); apply IHl.
Qed.

Definition branch_target (f: function) (pc: node) : node :=
  U.repr (record_gotos f) pc.

Definition count_gotos (f: function) (pc: node) : nat :=
  snd (record_gotos' f) pc.

Theorem record_gotos_correct:
  forall f pc,
  match f.(fn_code)!pc with
  | Some(Lnop s) =>
       branch_target f pc = pc \/
       (branch_target f pc = branch_target f s /\ count_gotos f s < count_gotos f pc)%nat
  | _ => branch_target f pc = pc
  end.
Proof.
  intros. 
  generalize (record_gotos'_correct f.(fn_code) pc). simpl.
  fold (record_gotos' f). unfold branch_map_correct, branch_target, count_gotos.
  rewrite record_gotos_gotos'. auto.
Qed.

(** * Preservation of semantics *)

Section PRESERVATION.

(* Assume fixed global environments that are related: *)
Variables (ge tge : genv).
Hypothesis TRANSF: genv_rel ge tge.

Let lts := (mklts thread_labels (ltl_step ge)).
Let tlts := (mklts thread_labels (ltl_step tge)).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (tunnel_fundef f).
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
  Genv.find_funct tge v = Some (tunnel_fundef f).
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
  funsig (tunnel_fundef f) = funsig f.
Proof. intros []; done. Qed.

Lemma find_function_translated:
  forall ros ls f,
  find_function ge ros ls = Some f ->
  find_function tge ros ls = Some (tunnel_fundef f).
Proof.
  intros [l|] ls f; simpl.
    destruct (ls l); try done; apply functions_translated; done.
  rewrite symbols_preserved; destruct (Genv.find_symbol ge i); try done.
  apply function_ptr_translated; done.
Qed.

(** The proof of semantic preservation is a simulation argument
  based on diagrams of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                  ?|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The [match_states] predicate, defined below, captures the precondition
  between states [st1] and [st2], as well as the postcondition between
  [st1'] and [st2'].  One transition in the source code (left) can correspond
  to zero or one transition in the transformed code (right).  The
  "zero transition" case occurs when executing a [Lgoto] instruction
  in the source code that has been removed by tunneling.

  In the definition of [match_states], note that only the control-flow
  (in particular, the current program point [pc]) is changed:
  the values of locations and the memory states are identical in the
  original and transformed codes. *)

Definition tunneled_code (f: function) :=
  PTree.map (fun pc b => tunnel_instr (record_gotos f) b) (fn_code f).

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
  | match_stackframes_intro:
      forall res f sp ls0 pc,
      match_stackframes
         (Stackframe res f sp ls0 pc)
         (Stackframe res (tunnel_function f) sp ls0 (branch_target f pc)).

Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
      forall s f sp pc ls ts,
      list_forall2 match_stackframes s ts ->
      match_states (State s f sp pc ls)
                   (State ts (tunnel_function f) sp (branch_target f pc) ls)
  | match_states_call:
      forall s f ls ts,
      list_forall2 match_stackframes s ts ->
      match_states (Callstate s f ls)
                   (Callstate ts (tunnel_fundef f) ls)
  | match_states_return:
      forall s ls ts,
      list_forall2 match_stackframes s ts ->
      match_states (Returnstate s ls)
                   (Returnstate ts ls)
  | match_states_blocked:
      forall s efsig ts,
      list_forall2 match_stackframes s ts ->
      match_states (Blockedstate s efsig)
                   (Blockedstate ts efsig).

(** To preserve non-terminating behaviours, we show that the transformed
  code cannot take an infinity of "zero transition" cases.
  We use the following [measure] function over source states,
  which decreases strictly in the "zero transition" case. *)

Definition measure (st: state) : nat :=
  match st with
  | State s f sp pc ls => count_gotos f pc
  | Callstate _ _ _  => 0%nat
  | Returnstate _ _  => 0%nat
  | Blockedstate _ _ => 0%nat
  end.

Definition order (s s': state) : Prop := (measure s < measure s')%nat.

Lemma tunnel_function_lookup:
  forall f pc i,
  f.(fn_code)!pc = Some i ->
  (tunnel_function f).(fn_code)!pc = Some (tunnel_instr (record_gotos f) i).
Proof.
  intros. simpl. rewrite PTree.gmap. rewrite H. auto.
Qed.

Lemma tunnel_step_correct:
  forall st1 t st2, ltl_step ge st1 t st2 ->
  forall st1' (MS: match_states st1 st1'),
  (exists st2', ltl_step tge st1' t st2' /\ match_states st2 st2')
  \/ (measure st2 < measure st1 /\ t = TEtau /\ match_states st2 st1')%nat.
Proof.
  (ltl_step_cases (induction 1) Case); intros; try inv MS;
    try (generalize (record_gotos_correct f pc); rewrite H; intro A; rewrite A).

  Case "exec_Lnop".
  generalize (record_gotos_correct f pc); rewrite H. 
  intros [A | [A B]]; rewrite A.
    left; econstructor; split.
    eapply exec_Lnop. 
    rewrite (tunnel_function_lookup _ _ _ H); simpl; auto.  
    econstructor; eauto. 
  right. split. simpl. auto. split. auto. 
  by econstructor.
  Case "exec_Lop".
  left; econstructor; split.
  eapply exec_Lop with (v := v); eauto.
  rewrite (tunnel_function_lookup _ _ _ H); simpl; auto.  
  rewrite <- H0. apply eval_operation_preserved. exact symbols_preserved.
  by econstructor.
  Case "exec_Lload".
  left; econstructor; split.
  eapply exec_Lload with (a := a); eauto.
  rewrite (tunnel_function_lookup _ _ _ H); simpl; auto.
  rewrite <- H1. apply eval_addressing_preserved. exact symbols_preserved.
  eauto.
  by econstructor.
  Case "exec_Lstore".
  left; econstructor; split.
  eapply exec_Lstore with (a := a).
  rewrite (tunnel_function_lookup _ _ _ H); simpl; auto.  
  rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
  eauto.
  by econstructor.
  Case "exec_Lcall".
  left; econstructor; split. 
  eapply exec_Lcall with (f' := tunnel_fundef f'); eauto.
  rewrite (tunnel_function_lookup _ _ _ H); simpl.
  rewrite sig_preserved. auto.
  apply find_function_translated; auto.
  econstructor; eauto.
  constructor; auto. 
  constructor; auto.
  Case "exec_Lcond_true".
  left; econstructor; split.
  eapply exec_Lcond_true; eauto.
  rewrite (tunnel_function_lookup _ _ _ H); simpl; eauto.
  econstructor; eauto.
  Case "exec_Lcond_false".
  left; econstructor; split.
  eapply exec_Lcond_false; eauto.
  rewrite (tunnel_function_lookup _ _ _ H); simpl; eauto.
  econstructor; eauto.
  Case "exec_Lreturn".
  left; econstructor; split.
  eapply exec_Lreturn; eauto.
  rewrite (tunnel_function_lookup _ _ _ H); simpl; eauto.
  simpl. constructor; auto.
  Case "exec_Lthreadcreate".
  left; econstructor; split.
  eapply exec_Lthreadcreate; eauto.
  rewrite (tunnel_function_lookup _ _ _ H); simpl; eauto.
  simpl. constructor; auto.
  Case "exec_Latomic".
  left; econstructor; split.
  eapply exec_Latomic; eauto.
  rewrite (tunnel_function_lookup _ _ _ H); simpl; eauto.
  simpl. constructor; auto.
  Case "exec_Lfence".
  left; econstructor; split.
  eapply exec_Lfence; eauto.
  rewrite (tunnel_function_lookup _ _ _ H); simpl; eauto.
  simpl. constructor; auto.
  Case "exec_function_internal_empty".
  simpl. left; econstructor; split; [|econstructor; eauto].
  apply exec_function_internal_empty; done.
  Case "exec_function_internal_nonempty".
  simpl. left; econstructor; split; [|econstructor; eauto].
  apply exec_function_internal_nonempty; done.
  Case "exec_function_external_call".
  simpl. left; econstructor; split.
  eapply exec_function_external_call; eauto.
  simpl. econstructor; eauto. 
  Case "exec_function_external_return".
  simpl. left; econstructor; split.
  eapply exec_function_external_return; eauto.
  simpl. econstructor; eauto. 
  Case "exec_return".
  inv H2. inv H1.
  left; econstructor; split.
  eapply exec_return; eauto.
  constructor. auto.
  Case "exec_return_exit".
  inv H2.
  left; econstructor; split. apply exec_return_exit.
  vauto.
Qed.

Lemma my_forward_sim:
  @forward_sim thread_labels lts tlts match_states order.
Proof.
  unfold lts,tlts.
  split; [apply (well_founded_ltof)|]; simpl; intros; right.
  exploit tunnel_step_correct; try eassumption.
  intro M; destruct M as [[t' []]|[? []]].
    left; exists t'; split; [apply step_weakstep|]; assumption.
  auto.
Qed.

Lemma init_sim_succ:
  forall {p vals tinit},
    ltl_init tge p vals = Some tinit ->
    exists sinit, ltl_init ge p vals = Some sinit /\ match_states sinit tinit.
Proof.
  intros p vals tinit INIT. unfold ltl_init in *. 
  pose proof TRANSF as (MG & MF).
  specialize (MF p).
  destruct (Genv.find_funct_ptr tge p) as [[[]|]|]; try done;
    destruct (Genv.find_funct_ptr ge  p) as [[[]|]|]; try done; []; simpl in *.
  inv MF. destruct beq_nat; inv INIT.
  eexists. split. edone. constructor. constructor.
Qed.

Lemma init_sim_fail:
  forall {p vals},
    ltl_init tge p vals = None ->
    ltl_init ge p vals = None.
Proof.
  intros p vals INIT. unfold ltl_init in *. 
  pose proof TRANSF as (MG & MF).
  specialize (MF p).
  destruct (Genv.find_funct_ptr tge p) as [[[]|]|]; try done;
    destruct (Genv.find_funct_ptr ge  p) as [[[]|]|]; try done. 
  by inv MF; simpl in *; destruct beq_nat.
Qed.

(* JS PARAM:
Lemma init_sim_succ:
  forall {p vals tinit},
    ltl_init tge p vals = Some tinit ->
    exists sinit, ltl_init ge p vals = Some sinit /\ match_states sinit tinit.
Proof.
  intros p vals tinit INIT. unfold ltl_init in *. 
  pose proof TRANSF as (MG & MF).
  specialize (MF p).
  destruct (Genv.find_funct_ptr tge p) as [[[]|]|]; try done;
    destruct (Genv.find_funct_ptr ge  p) as [[[]|]|]; try done; []; simpl in *.
  inv MF. destruct (sig_args fn_sig); try done; [].
  eexists. split. edone. inv INIT. constructor. constructor.
Qed.

Lemma init_sim_fail:
  forall {p vals},
    ltl_init tge p vals = None ->
    ltl_init ge p vals = None.
Proof.
  intros p vals INIT. unfold ltl_init in *. 
  pose proof TRANSF as (MG & MF).
  specialize (MF p).
  destruct (Genv.find_funct_ptr tge p) as [[[]|]|]; try done;
    destruct (Genv.find_funct_ptr ge  p) as [[[]|]|]; try done; []; simpl in *.
  inv MF. by destruct sig_args.
Qed.
*)

Definition bsim_rel := @bsr _ lts tlts match_states.
Definition bsim_order := @bsc _ tlts.

End PRESERVATION.

Definition tunnel_match_prg (p p' : ltl_sem.(SEM_PRG)) : Prop := 
  tunnel_program p = p'.

(** The whole-system backward simulation for the [Tunneling]
    phase. *)
Theorem tunnel_sim Mm : Sim.sim Mm Mm ltl_sem ltl_sem tunnel_match_prg.
Proof.
  eapply (MCsim.sim (false_pure_load_cond Mm) ltl_sem ltl_sem genv_rel 
    bsim_rel (fun _ => bsim_order)); intros; simpl in *.
  - destruct GENVR as [GR FR]. rewrite GR.
    destruct src_prog; destruct tgt_prog. by inv MP.
  - eapply Genv.exists_matching_genv_and_mem_rev 
      with (match_var := fun a b => a = b), INIT.
    apply transform_program_match, MP.
  - destruct (init_sim_succ _ _ GENVR INIT) as [si [INIT' MS]].
    exists si. split. done. by apply fsr_in_bsr.
  - eby eapply init_sim_fail.
  - eapply forward_to_backward_sim. 
          apply ltl_sem.(SEM_receptive).
        apply ltl_sem.(SEM_determinate).
      apply ltl_sem.(SEM_progress_dec).
    by apply my_forward_sim.
Qed.
    
    
    
