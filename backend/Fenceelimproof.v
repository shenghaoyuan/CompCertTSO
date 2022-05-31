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
Require Import Fenceelim.
Require Import Simulations.
Require Import Memcomp Traces.
Require Import TSOmachine TSOsimulation.
Require Import Lattice.
Require Import Libtactics.

Definition genv_rel : genv -> genv -> Prop :=
 (fun x y => Genv.genv_match (fun a b => transf_fundef a = b) y x).

Section SIM.

Variable sge : genv. 
Variable tge : genv. 

Let s_lts := (mklts event_labels (Comp.step tso_mm rtl_sem sge)).
Let t_lts := (mklts event_labels (Comp.step tso_mm rtl_sem tge)).

Hypothesis TRANSF: genv_rel sge tge.

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
  match_stackframes_intro:
    forall res c sp pc rs f
    (ANAL_RET: (analyze f) # pc = LBoolean.top),
    c = f.(RTL.fn_code) ->
    match_stackframes
      (Stackframe res c sp pc rs)
      (Stackframe res (transf_code (analyze f) c) sp pc rs).

Inductive match_states (b: list buffer_item): state -> state -> Prop :=
  | match_states_intro:
      forall s c sp pc rs s' f
             (CF: c = f.(RTL.fn_code))
             (BREL : (analyze f) # pc = false -> b = nil) 
             (STACKS: list_forall2 match_stackframes s s'),
      match_states b (State s c sp pc rs)
                   (State s' (transf_code (analyze f) c) sp pc rs)
  | match_states_call:
      forall s f args s',
      list_forall2 match_stackframes s s' ->
      match_states b (Callstate s f args)
                   (Callstate s' (transf_fundef f) args)
  | match_states_return:
      forall s s' v,
      list_forall2 match_stackframes s s' ->
      match_states b (Returnstate s v)
                   (Returnstate s' v)
  | match_states_blocked:
      forall s s' v,
      list_forall2 match_stackframes s s' ->
      match_states b (Blockedstate s v)
                   (Blockedstate s' v).

Inductive tso_pc_related (ss : Comp.state tso_mm rtl_sem)
                         (ts : Comp.state tso_mm rtl_sem) : Prop :=
  tso_pc_related_intro: forall
    (bEQ:   fst ss = fst ts)
    (Mthr: forall tid, 
      match (snd ss) ! tid, (snd ts) ! tid with 
        | Some s, Some t => match_states (tso_buffers (fst ss) tid) s t
        | None, None => True 
        | _, _ => False
      end),
    tso_pc_related ss ts.

Definition tso_order (ts' ts : Comp.state tso_mm rtl_sem) := False.

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr sge v = Some f ->
  Genv.find_funct_ptr tge v = Some (transf_fundef f).
Proof.
  intros v f H.
  pose proof (proj2 TRANSF v).
  destruct (Genv.find_funct_ptr sge v);
   destruct (Genv.find_funct_ptr tge v); try done.
  clarify; eexists; done.
Qed.

Lemma functions_translated:
  forall v f,
  Genv.find_funct sge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof.
  intros v f H.
  destruct v as [| |p|]; try done; simpl in *.
  apply function_ptr_translated; done.
Qed.

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol sge id.
Proof. by intros; destruct TRANSF. Qed.

Lemma sig_preserved:
  forall f,
  funsig (transf_fundef f) = funsig f.
Proof. by intros [|]. Qed.

Lemma find_function_translated:
  forall ros ls f,
  find_function sge ros ls = Some f ->
  find_function tge ros ls = Some (transf_fundef f).
Proof.
  intros [l|] ls f; simpl.
    destruct (ls # l); try done; apply functions_translated; done.
  rewrite symbols_preserved; destruct (Genv.find_symbol sge i); try done.
  apply function_ptr_translated; done.
Qed.

Lemma function_ptr_translated_back:
  forall v f,
  Genv.find_funct_ptr tge v = Some f ->
  exists f', Genv.find_funct_ptr sge v = Some f' /\ f = (transf_fundef f').
Proof.
  intros; pose proof (proj2 TRANSF v).
  destruct (Genv.find_funct_ptr sge v);
    destruct (Genv.find_funct_ptr tge v); clarify; vauto. 
Qed.

Lemma functions_translated_back:
  forall v f,
  Genv.find_funct tge v = Some f ->
  exists f', Genv.find_funct sge v = Some f' /\ f = (transf_fundef f').
Proof.
  by intros [| |p|]; intros; clarify; apply function_ptr_translated_back.
Qed.

Lemma find_function_translated_back:
  forall ros ls f,
  find_function tge ros ls = Some f ->
  exists f', find_function sge ros ls = Some f' /\ f = (transf_fundef f').
Proof.
  intros [l|] ls f; simpl.
    destruct (ls # l); try done; apply functions_translated_back; done.
  rewrite symbols_preserved; destruct (Genv.find_symbol sge i); try done.
  apply function_ptr_translated_back; done.
Qed.

Ltac inv_asm :=
  unfold transf_code in *;
  try rewrite PTree.gmap in *;
  repeat match goal with
   | H : (if ?a then _ else _) = _ |- _ => destruct a as [] _eqn: ?; clarify
   | H : match ?a with
         | AScas => _
         | ASlkinc => _ end = _ |- _ => destruct a as [] _eqn: ?; clarify
   | H : option_map _ ?x = Some _ |- _ => destruct x as [[]|] _eqn: ?; simpl in *; clarify
  end.

Ltac sim_nop_tac :=
  unfold analyze in *;
  match goal with
   | H: (fn_code _) ! ?pc = Some _ |- context[(match ?a with Some _ => _ | None => _ end) # ?spc] => 
       let EQ := fresh "EQ" in 
       destruct a as [] _eqn: EQ; [|by rewrite !PMap.gi];
       try eapply DS.fixpoint_solution with (n := pc) (s := spc) in EQ; 
         [revert EQ; unfold transfer; rewrite H; intros [-> | ->]; clarify|];
       try (by unfold successors, successors_list; rewrite PTree.gmap, H; simpl; vauto)
   | |- context[(match ?a with Some _ => _ | None => _ end) # ?spc] => 
       let EQ := fresh "EQ" in 
       destruct a as [] _eqn: EQ; [|by rewrite !PMap.gi];
       eapply DS.fixpoint_entry in EQ; [|by left];
       by destruct EQ as [-> | ->]
  end.

(** Simulation theorems *) 

Lemma sim_eval_addressing:
  forall sp addr args,
    eval_addressing tge sp addr args = eval_addressing sge sp addr args.
Proof.
  by intros; destruct addr; destruct args; clarify;
     try (destruct v0; clarify; destruct args; clarify); simpl in *; 
     rewrite <- symbols_preserved. 
Qed.

Lemma sim_eval_operation:
  forall sp op args,
    eval_operation tge sp op args = eval_operation sge sp op args.
Proof.
  intros; destruct op; destruct args; clarify;
  try (destruct v0; clarify; destruct args; clarify); simpl in *;
  apply sim_eval_addressing. 
Qed.

Lemma sim_nop:
  forall t t' s b
    (tidSTEP : rtl_step tge t TEtau t')
    (MS : match_states b s t),
     (exists s', rtl_step sge s TEtau s' /\ match_states b s' t')
  \/ (exists s', b = nil /\ rtl_step sge s (TEmem MEfence) s' /\ match_states b s' t').
Proof.
  intros; remember TEtau; (rtl_step_cases (destruct tidSTEP) Case); clarify;
    inv MS; inv_asm; try by (left; eexists; split; vauto).

  Case "exec_Inop".
  - by left; eexists; split; econstructor; try edone; []; sim_nop_tac.
  right; eexists; split; auto; split; [by vauto|].
  by econstructor; try done; sim_nop_tac.

  Case "exec_Iop".
  left; eexists; split. 
    eby eapply exec_Iop; try eassumption; try edone; rewrite <- sim_eval_operation.
  by econstructor; try done; sim_nop_tac.

  Case "exec_Icall".
  eapply find_function_translated_back in H0; destruct H0 as (f' & ? & ?); clarify.
  left; eexists; split. 
    by eapply exec_Icall; try eassumption; rewrite <- sig_preserved.

  econstructor; try done.
  econstructor; try done.
  econstructor; try done.
  by sim_nop_tac.

  Case "exec_Icond_true".
  by left; eexists; split; [vauto | econstructor; try done; sim_nop_tac].

  Case "exec_Icond_false".
  by left; eexists; split; [vauto | econstructor; try done; sim_nop_tac].

  Case "exec_function_internal_empty".
  destruct f0; simpl in *; clarify; simpl in *.
  by left; eexists; split; [vauto | econstructor; try done; sim_nop_tac].

  Case "exec_return".
  destruct s1; inv H1; clarify; inv H3; clarify.
  by left; eexists; split; [vauto | econstructor; try done; rewrite ANAL_RET].
Qed.


Lemma sim_atomic:
  forall t t' s b ev
    (tidSTEP : rtl_step tge t ev t')
    (LAB: match ev with 
           | TEmem (MErmw _ _ _ _) => True
           | TEmem (MEfence) => True
           | _ => False
          end)
    (MS : match_states b s t),
  exists s', rtl_step sge s ev s' /\ match_states nil s' t'.
Proof.
  by intros; (rtl_step_cases (destruct tidSTEP) Case); clarify;
     inv MS; inv_asm; try by (eexists; split; vauto).
Qed.

Lemma sim_mem_upd:
  forall t t' s b ev
    (tidSTEP : rtl_step tge t ev t')
    (LAB: match ev with 
           | TEmem (MEwrite _ _ _) => True
           | TEmem (MEalloc _ _ _) => True
           | TEmem (MEfree _ _) => True
           | _ => False
          end)
    (MS : match_states b s t),
  exists s', rtl_step sge s ev s' /\ forall b', match_states b' s' t'.
Proof.
  intros; (rtl_step_cases (destruct tidSTEP) Case); clarify;
     inv MS; inv_asm; try (by inv ASME).

  Case "exec_Istore".
  eexists; split; [by econstructor; try edone; rewrite <- sim_eval_addressing|].
  by econstructor; try done; sim_nop_tac.

  Case "exec_Ireturn".
  destruct sp; clarify.
  eexists; split; [econstructor; try edone|].
  by econstructor; try done; sim_nop_tac.

  Case "exec_function_internal_nonempty".
  destruct f0; simpl in *; clarify; simpl in *.
  eexists; split; [econstructor; try edone|].
  by econstructor; try done; sim_nop_tac.
Qed.

Lemma sim_ord:
  forall t t' s b ev
    (tidSTEP : rtl_step tge t ev t')
    (LAB: match ev with 
           | TEtau => False
           | TEmem (MEread _ _ _) => True
           | TEmem _ => False
           | _ => True
          end)
    (MS : match_states b s t),
  exists s', rtl_step sge s ev s' /\ match_states b s' t'.
Proof.
  intros; (rtl_step_cases (destruct tidSTEP) Case); clarify;
   inv MS; inv_asm; try (by inv ASME); try by (eexists; split; vauto).

Case "exec_Iload".
  eexists; split; [by econstructor; try edone; rewrite <- sim_eval_addressing|].
  by econstructor; try edone; sim_nop_tac.

Case "exec_Ithread_create".
  eexists; split; [vauto|]. 
  by econstructor; try edone; sim_nop_tac.

Case "exec_function_external_call".
  by destruct f; simpl in *; clarify; eexists; split; vauto. 

Case "exec_return_exit".
  by inv H1; eexists; split; vauto. 
Qed.

Lemma sim_init:
  forall p v sinit
    (INIT: rtl_init tge p v = Some sinit),
    exists f, 
      sinit = Callstate nil (Internal (transf_function f)) 
        (Val.conv_list v (sig_args (fn_sig f))) /\
      rtl_init sge p v = Some (Callstate nil (Internal f) 
        (Val.conv_list v (sig_args (fn_sig f)))).
Proof.
  unfold rtl_init; intros.
  pose proof (proj2 TRANSF p).
  destruct (Genv.find_funct_ptr sge p) as [[]|];
   destruct (Genv.find_funct_ptr tge p) as [[]|]; try done.
  simpl in *; clarify; simpl in *.
  destruct beq_nat; vauto. 
Qed.

Lemma sim_init_none:
  forall p v,
    rtl_init tge p v = None ->
    rtl_init sge p v = None.
Proof.
  unfold rtl_init; intros.
  pose proof (proj2 TRANSF p).
  destruct (Genv.find_funct_ptr sge p) as [[]|];
   destruct (Genv.find_funct_ptr tge p) as [[]|]; try done.
  simpl in *; clarify; simpl in *.
  destruct beq_nat; vauto. 
Qed.

(** Simulation of stuck states *)

Lemma sim_stuck:
  forall b s s1
  (NOtidSTEP : forall (s' : state) (l' : thread_event), ~ rtl_step tge s l' s')
  (MS : match_states b s1 s),
  forall (s' : state) (l' : thread_event), ~ rtl_step sge s1 l' s'.
Proof.
  intros; intro X; (rtl_step_cases (inv X) Case); inv MS;
  try first [Case "exec_function_internal_nonempty"
   | eby eapply NOtidSTEP; unfold transf_code, transf_instr; simpl;
         econstructor (try (by rewrite PTree.gmap, H; simpl); 
         first [edone | rewrite sim_eval_operation | rewrite sim_eval_addressing])].

  Case "exec_Icall".
  eapply NOtidSTEP; unfold transf_code, transf_instr; simpl;
  eapply exec_Icall; try (by rewrite PTree.gmap, H; simpl);
  try eby eapply find_function_translated; simpl; try edone.
  by destruct f.

  Case "exec_Ifence". 
  destruct ((analyze f) # pc) as [] _eqn: A;
  eapply NOtidSTEP; unfold transf_code, transf_instr; simpl.
  - eby eapply exec_Ifence; try (by rewrite PTree.gmap, H; simpl; rewrite A). 
  - eby eapply exec_Inop; try (by rewrite PTree.gmap, H; simpl; rewrite A). 

  Case "exec_function_internal_nonempty".
  eapply NOtidSTEP; unfold transf_code, transf_instr; simpl.
  eby eapply exec_function_internal_nonempty with (stk := Ptr 0 Int.one).

  Case "exec_return".
  by inv H2; inv H1; eapply NOtidSTEP; eapply exec_return.

  Case "exec_return_exit".
  by inv H2; eapply NOtidSTEP; eapply exec_return_exit.
Qed.

(** Main backwards simulation theorem *)

Lemma fenceelim_bsim:
  forall sst tst tst' e
    (PCREL: tso_pc_related sst tst)
    (NOOM: e <> Eoutofmemory)
    (TSOST: t_lts.(stepr) tst e tst'),
  (exists sst', taustar s_lts sst sst' /\ can_do_error s_lts sst') \/
  (exists sst', taustep s_lts sst e sst' /\ tso_pc_related sst' tst').
Proof.
  intros [[sb sm] sthr] [[tb tm] tthr] [[tb' tm'] tthr'] e []; intros.
  (comp_step_cases (inv TSOST) Case); simpl in *; try done;
    (* finish the inapplicable cases *)
    try (by inv tidSTEP; try done; []; destruct sp).

  Case "step_ord".
  right; simpl in *.
  generalize (Mthr tid); rewrite Gtid; destruct (sthr ! tid) as [s1|] _eqn: GStid; intros MS; try done.
  remember (MMmem tid ev); (tso_step_cases (destruct tsoSTEP) SCase); clarify.
  
  SCase "tso_step_write".
  destruct (sim_mem_upd _ _ _ _ _ tidSTEP I MS) as (s2 & STEP & MS').
  eexists; split; [by eapply step_taustep; simpl; eapply Comp.step_ord; try edone; vauto|]. 
  constructor; try done; simpl.
  by intro j; specialize (Mthr j); destruct (peq j tid); 
     [subst; rewrite !PTree.gss | rewrite !PTree.gso, ?tupdate_o].

  SCase "tso_step_read".
  destruct (sim_ord _ _ _ _ _ tidSTEP I MS) as (s2 & STEP & MS').
  eexists; split; [by eapply step_taustep; simpl; eapply Comp.step_ord; try edone; vauto|]. 
  constructor; try done; simpl.
  by intro j; specialize (Mthr j); destruct (peq j tid); 
     [subst; rewrite !PTree.gss | rewrite !PTree.gso, ?tupdate_o].

  SCase "tso_step_alloc".
  destruct (sim_mem_upd _ _ _ _ _ tidSTEP I MS) as (s2 & STEP & MS').
  eexists; split; [by eapply step_taustep; simpl; eapply Comp.step_ord; try edone; vauto|]. 
  constructor; try done; simpl.
  by intro j; specialize (Mthr j); destruct (peq j tid); 
     [subst; rewrite !PTree.gss | rewrite !PTree.gso, ?tupdate_o].

  SCase "tso_step_free".
  destruct (sim_mem_upd _ _ _ _ _ tidSTEP I MS) as (s2 & STEP & MS').
  eexists; split; [by eapply step_taustep; simpl; eapply Comp.step_ord; try edone; vauto|]. 
  constructor; try done; simpl.
  by intro j; specialize (Mthr j); destruct (peq j tid); 
     [subst; rewrite !PTree.gss | rewrite !PTree.gso, ?tupdate_o].

  SCase "tso_step_mfence".
  destruct (sim_atomic _ _ _ _ _ tidSTEP I MS) as (s2 & STEP & MS').
  eexists; split; [by eapply step_taustep; simpl; eapply Comp.step_ord; try edone; vauto|]. 
  constructor; try done; simpl.
  intro j; specialize (Mthr j); destruct (peq j tid); 
     [subst; rewrite !PTree.gss | rewrite !PTree.gso, ?tupdate_o]; try done.
  by simpl in *; rewrite Bemp.

  SCase "tso_step_rmw".
  destruct (sim_atomic _ _ _ _ _ tidSTEP I MS) as (s2 & STEP & MS').
  eexists; split; [by eapply step_taustep; simpl; eapply Comp.step_ord; try edone; vauto|]. 
  constructor; try done; simpl.
  intro j; specialize (Mthr j); destruct (peq j tid); 
     [subst; rewrite !PTree.gss | rewrite !PTree.gso, ?tupdate_o]; try done.
  by simpl in *; rewrite Bemp.

  Case "step_ext".
  right; simpl in *.
  generalize (Mthr tid); rewrite Gtid; destruct (sthr ! tid) as [s1|] _eqn: GStid; intros MS; try done.
  destruct (sim_ord _ _ _ _ _ tidSTEP I MS) as (s2 & STEP & MS').
  eexists; split; [by eapply step_taustep; simpl; eapply Comp.step_ext; try edone; vauto|]. 
  constructor; try done; simpl.
  by intro j; specialize (Mthr j); destruct (peq j tid); 
     [subst; rewrite !PTree.gss | rewrite !PTree.gso, ?tupdate_o]; try done.

  Case "step_unbuf".
  right; clarify.
  inv tsoSTEP; clarify.
  eexists; split; [by eapply step_taustep; simpl; eapply Comp.step_unbuf; try edone; vauto|]. 
  constructor; try done; simpl.
  rename t into tid.
  intro j; specialize (Mthr j); destruct (peq j tid); 
     [subst; rewrite ?PTree.gss, ?tupdate_s | rewrite ?PTree.gso, ?tupdate_o]; try done.
  destruct (sthr ! tid); destruct (tthr' ! tid); clarify; revert Mthr; simpl in *; rewrite EQbufs; clear.
  by inversion 1; clarify; constructor; try done; []; intros X; apply BREL in X; clarify.

  Case "step_tau".
  right; clarify; simpl in *.
  generalize (Mthr tid); rewrite Gtid; destruct (sthr ! tid) as [s1|] _eqn: GStid; intros MS; try done.
  destruct (sim_nop _ _ _ _ tidSTEP MS) as [(s2 & STEP & MS') | (s2 & Bemp & STEP & MS')].

  eexists; split; [by eapply step_taustep; simpl; eapply Comp.step_tau; try edone; vauto|]. 
  constructor; try done; simpl.
  by intro j; specialize (Mthr j); destruct (peq j tid); 
     [subst; rewrite !PTree.gss | rewrite !PTree.gso, ?tupdate_o].

  eexists; split; [by eapply step_taustep; simpl; eapply Comp.step_ord; try edone; vauto|]. 
  constructor; try done; simpl.
  by intro j; specialize (Mthr j); destruct (peq j tid); 
     [subst; rewrite !PTree.gss | rewrite !PTree.gso, ?tupdate_o].
  
  Case "step_start".
  right; clarify; simpl in *.
  generalize (Mthr tid); rewrite Gtid; destruct (sthr ! tid) as [s1|] _eqn: GStid; intros MS; try done.
  destruct (sim_ord _ _ _ _ _ tidSTEP I MS) as (s2 & STEP & MS').
  destruct (sim_init _ _ _ INIT) as (f & ? & INIT'); clarify.
  inv tsoSTEP.
  eexists; split.
    eapply step_taustep; simpl; eapply Comp.step_start with (newtid := newtid); try edone; vauto.
    by generalize (Mthr newtid); rewrite Gnewtid; simpl in *; destruct (sthr ! newtid).
  
  constructor; clarify; simpl.
  intro j; specialize (Mthr j).
    destruct (peq j newtid); [subst; rewrite !PTree.gss, tupdate_s|rewrite tupdate_o; try done].
    vauto.
  by destruct (peq j tid); subst; repeat (first [rewrite PTree.gss | rewrite PTree.gso]; try done).

  Case "step_start_fail".
  generalize (Mthr tid); rewrite Gtid; destruct (sthr ! tid) as [s1|] _eqn: GStid; intros MS; try done.
  destruct (sim_ord _ _ _ _ _ tidSTEP I MS) as (s2 & STEP & MS').
  by left; eexists; split; [eapply taustar_refl|];
     eexists (_, _); exists (Evisible Efail); split; [done|simpl]; 
     eapply Comp.step_start_fail; try eassumption; apply sim_init_none.

  Case "step_exit".
  generalize (Mthr tid); rewrite Gtid; destruct (sthr ! tid) as [s1|] _eqn: GStid; intros MS; try done.
  destruct (sim_ord _ _ _ _ _ tidSTEP I MS) as (s2 & STEP & MS').
  right; clarify; simpl in *.
  inv tsoSTEP.
  eexists; split; [by eapply step_taustep; simpl; eapply Comp.step_exit; try edone; vauto|].
  constructor; try done; simpl.
  by intro j; specialize (Mthr j); destruct (peq j tid); 
     [subst; rewrite !PTree.grs|rewrite !PTree.gro].

  Case "step_read_fail".
  generalize (Mthr tid); rewrite Gtid; destruct (sthr ! tid) as [s1|] _eqn: GStid; intros MS; try done.
  destruct (sim_ord _ _ _ _ _ tidSTEP I MS) as (s2 & STEP & MS').
  inv tsoSTEP.
  by left; eexists; split; [eapply taustar_refl|];
     eexists (_, _); exists (Evisible Efail); split; [done|simpl]; 
     eapply Comp.step_read_fail; try edone; vauto.

  Case "step_write_fail".
  generalize (Mthr tid); rewrite Gtid; destruct (sthr ! tid) as [s1|] _eqn: GStid; intros MS; try done.
  destruct (sim_mem_upd _ _ _ _ _ tidSTEP I MS) as (s2 & STEP & MS').
  inv tsoSTEP.
  by left; eexists; split; [eapply taustar_refl|];
     eexists (_, _); exists (Evisible Efail); split; [done|simpl]; 
     eapply Comp.step_write_fail; try edone; vauto.

  Case "step_free_fail".
  generalize (Mthr tid); rewrite Gtid; destruct (sthr ! tid) as [s1|] _eqn: GStid; intros MS; try done.
  destruct (sim_mem_upd _ _ _ _ _ tidSTEP I MS) as (s2 & STEP & MS').
  inv tsoSTEP.
  by left; eexists; split; [eapply taustar_refl|];
     eexists (_, _); exists (Evisible Efail); split; [done|simpl]; 
     eapply Comp.step_free_fail; try edone; vauto.

  Case "step_rmw_fail".
  generalize (Mthr tid); rewrite Gtid; destruct (sthr ! tid) as [s1|] _eqn: GStid; intros MS; try done.
  destruct (sim_atomic _ _ _ _ _ tidSTEP I MS) as (s2 & STEP & MS').
  inv tsoSTEP.
  by left; eexists; split; [eapply taustar_refl|];
     eexists (_, _); exists (Evisible Efail); split; [done|simpl]; 
     eapply Comp.step_rmw_fail; try edone; vauto.

  Case "step_thread_stuck".
  generalize (Mthr tid); rewrite Gtid; destruct (sthr ! tid) as [s1|] _eqn: GStid; intros MS; try done.
  eby left; eexists; split; [eapply taustar_refl|];
      eexists (_, _); exists (Evisible Efail); split; [done|simpl]; 
      eapply Comp.step_thread_stuck; try eapply sim_stuck.
Qed.

End SIM.

Definition fenceelim_fullsim sge tge sst tst :=
  genv_rel sge tge /\ tso_pc_related sst tst.

Lemma match_program_transf:
  forall (prg : program),
    match_program (fun f1 f2 => transf_fundef f1 = f2)
                  (fun v1 v2 => v1 = v2)
                  prg (transf_program prg).
Proof.
  split; unfold transf_program; simpl.
  induction (prog_funct prg) as [|[id fd] l IH]; by constructor.
  split; [done|].
  induction (prog_vars prg) as [|[[id init] fd] l IH]; by constructor.
Qed.

Theorem fenceelim_initsim:
  forall prg args tge tst,
    Comp.init tso_mm rtl_sem (transf_program prg) args tge tst ->
    exists sge, exists sst,
      Comp.init tso_mm rtl_sem prg args sge sst /\
      fenceelim_fullsim sge tge sst tst.
Proof.
  intros prg args tge tst [mst [mtid [tm [mptr (GI & FM & IM & ->)]]]]; clarify.
  exploit Genv.exists_matching_genv_and_mem_rev; [apply match_program_transf|eapply GI|].
  intros (sge & SGI & REL).
  simpl in *; rewrite <- (proj1 REL) in FM.
  exists sge; apply sim_init with (sge := sge) in IM; destruct IM as (f & ? & IM); clarify.
  eexists; split; [eby eexists; eexists mtid; eexists; eexists; simpl|].
  repeat first [by vauto | split]; simpl. 
  by intro tid; destruct (peq tid mtid);
     [subst; rewrite !PTree.gss; vauto | rewrite !PTree.gso, !PTree.gempty ].
Qed.

Definition fenceelim_match_prg (p : rtl_sem.(SEM_PRG)) (p' : rtl_sem.(SEM_PRG)) := 
  transf_program p = p'.

(** Instantiate the simulation *)
Definition fenceelim_basic_sim : Bsim.sim tso_mm tso_mm rtl_sem rtl_sem fenceelim_match_prg.
Proof.
  eapply (Bsim.make fenceelim_match_prg fenceelim_fullsim (fun _ _ _ _ => False)); try done. 
  - intros; destruct REL as (? & ? & A).
    by eapply PTree.ext; intro tid; 
       generalize (A tid); rewrite EMPTY, !PTree.gempty;
       destruct ((snd s) ! tid); try done;
       destruct ((snd t) ! tid).
  - unfold fenceelim_match_prg; intros; clarify.
    eby exploit fenceelim_initsim. 
  intros; destruct REL; edestruct fenceelim_bsim; eauto.
  by des; right; left; eexists; split; try edone. 
Defined.

Lemma fenceelim_sim : Sim.sim tso_mm tso_mm rtl_sem rtl_sem fenceelim_match_prg.
Proof.
  apply (Sim.make fenceelim_basic_sim); vauto.
Qed.
