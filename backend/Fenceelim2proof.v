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
Require Import Memaux.
Require Import Memeq.
Require Import Events.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Kildall.
Require Import Fenceelim2.
Require Import Simulations.
Require Import TSOmachine TSOsimulation.
Require Import Lattice.
Require Import Memcomp Traces.
Require Import Libtactics.

Set Implicit Arguments.

Definition genv_rel: genv -> genv -> Prop :=
  (fun x y => Genv.genv_match (fun a b => transf_fundef a = b) y x).

Definition fenceelim2_match_prg p p' := 
  transf_program p = p'.

Ltac inv_asm :=
  unfold transf_code in * |-;
  try rewrite PTree.gmap in * |-;
  repeat match goal with
   | H : (if ?a then _ else _) = _ |- _ => destruct a as [] _eqn: ?; clarify
   | H : match ?a with
         | AScas => _
         | ASlkinc => _ end = _ |- _ => destruct a as [] _eqn: ?; clarify
   | H : option_map _ ?x = Some _ |- _ => destruct x as [[]|] _eqn: ?; simpl in *; clarify
  end.

Section BSIM.

Variable sge : genv.
Variable tge : genv.

Let s_lts := (mklts event_labels (Comp.step tso_mm rtl_sem sge)).
Let t_lts := (mklts event_labels (Comp.step tso_mm rtl_sem tge)).

(** [twf_reach s l s'] says that the thread state [s] can do a sequence of
    taus, memory writes and fences and end in state [s']: [l] is the sequence
    of writes done. *)
Inductive twf_reach : state -> list buffer_item -> state -> Prop :=
  | twf_reach_nil : forall s, twf_reach s nil s
  | twf_reach_tau : forall s s' l s''
      (STEP: rtl_step sge s TEtau s')
      (R: twf_reach s' l s''),
      twf_reach s l s''
  | twf_reach_fence : forall s s' l s''
      (STEP: rtl_step sge s (TEmem MEfence) s')
      (R: twf_reach s' l s''),
      twf_reach s l s''
  | twf_reach_write : forall s p c v s' l s'' l'
      (STEP: rtl_step sge s (TEmem (MEwrite p c v)) s')
      (R: twf_reach s' l s'')
      (BEQ: l' = BufferedWrite p c v :: l),
      twf_reach s l' s''.

Hint Constructors twf_reach : tw.

Lemma twf_reach_trans:
  forall s s' s'' l l',
    twf_reach s l s' -> twf_reach s' l' s'' -> twf_reach s (l ++ l') s''.
Proof.
  induction 1; intros; clarify; simpl; eauto with tw. 
Qed.

Lemma twf_reach_inv:
  forall s bi l s',
    twf_reach s (bi :: l) s' -> 
    exists p, exists c, exists v, exists s1, exists s2,
      bi = BufferedWrite p c v /\
      twf_reach s nil s1 /\
      rtl_step sge s1 (TEmem (MEwrite p c v)) s2 /\
      twf_reach s2 l s'.
Proof.
  intros; remember (bi :: l) as x; revert bi l Heqx; induction H; intros; clarify;
  try (exploit IHtwf_reach; try edone; []; intro; des); eauto 10 with tw.
Qed.

(** Equality on states *)

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
  match_stackframes_intro:
    forall res c sp pc rs f,
    c = f.(RTL.fn_code) ->
    match_stackframes
      (Stackframe res c sp pc rs)
      (Stackframe res (transf_code (analyze f) c) sp pc rs).

Inductive match_states (b: Prop): state -> state -> Prop :=
  | match_states_intro:
      forall s c sp pc rs s' f
             (CF: c = f.(RTL.fn_code))
             (BREL : transfer f pc (analyze f) # pc -> b) 
             (STACKS: list_forall2 match_stackframes s s'),
      match_states b (State s c sp pc rs)
                   (State s' (transf_code (analyze f) c) sp pc rs)
  | match_states_call:
      forall s f args s'
        (BREL: b)
        (STACKS: list_forall2 match_stackframes s s'),
      match_states b (Callstate s f args)
                   (Callstate s' (transf_fundef f) args)
  | match_states_return:
      forall s s' v
        (BREL: b)
        (STACKS: list_forall2 match_stackframes s s'),
      match_states b (Returnstate s v)
                   (Returnstate s' v)
  | match_states_blocked:
      forall s s' v
        (BREL: b)
        (STACKS: list_forall2 match_stackframes s s'),
      match_states b (Blockedstate s v)
                   (Blockedstate s' v).

(** Definition of the main simulation relation. *)

Inductive fenceelim2_sim (ss ts: Comp.state tso_mm rtl_sem) : Prop :=
 fenceelim2_sim_intro: forall
   (ENVR: genv_rel sge tge)
   (MR: tso_mem (fst ts) = tso_mem (fst ss))
   (Mthr: forall tid, 
     match (snd ss) ! tid, (snd ts) ! tid with 
        | Some s, Some t => 
                match_states True s t /\ (fst ts).(tso_buffers) tid = (fst ss).(tso_buffers) tid
            \/ (exists ff, exists sn, twf_reach s ff sn 
                         /\ (fst ts).(tso_buffers) tid = (fst ss).(tso_buffers) tid ++ ff
                         /\ match_states False sn t)
        | None, None => True 
        | _, _ => False
     end),
   fenceelim2_sim ss ts.

(** Definition of the weaker simulation relation. *)

Inductive fenceelim2_wsim (ss ts: Comp.state tso_mm rtl_sem) : Prop :=
 fenceelim2_wsim_intro: forall
   (ENVR: genv_rel sge tge)
   (Mthr: forall tid, 
     match (snd ss) ! tid, (snd ts) ! tid with 
        | Some s, Some t => 
            (exists ff, exists sn, twf_reach s ff sn /\ match_states True sn t)
        | None, None => True 
        | _, _ => False
     end),
   fenceelim2_wsim ss ts.

Lemma sim_meq: 
  forall ss ts, fenceelim2_sim ss ts -> tso_mem (fst ts) = tso_mem (fst ss).
Proof. by destruct 1. Qed.

Lemma sim_weaken: 
  forall ss ts, fenceelim2_sim ss ts -> fenceelim2_wsim ss ts.
Proof.
  destruct 1; split; try done. 
  intro tid; specialize (Mthr tid); 
    destruct ((snd ss) ! tid); try done;
    destruct ((snd ts) ! tid); try done; des.
  + by exists nil; eexists; split; try edone; vauto.
  + by eexists; eexists; split; try edone; inv H1; vauto. 
Qed.

Lemma sim_weaken2: 
  forall ss ts (SIM: fenceelim2_sim ss ts) tid,
    match (snd ss) ! tid, (snd ts) ! tid with 
        | Some s, Some t => 
            exists ff, exists sn, twf_reach s ff sn
              /\ (fst ts).(tso_buffers) tid = (fst ss).(tso_buffers) tid ++ ff
              /\ match_states True sn t
        | None, None => True
        | _, _ => False
     end.
Proof.
  intros; destruct SIM; specialize (Mthr tid).
    destruct ((snd ss) ! tid); try done;
    destruct ((snd ts) ! tid); try done; des.
  - by exists nil; eexists; repeat split; try edone; rewrite <- ?app_nil_end; vauto.
  - by eexists; eexists; split; try edone; inv H1; vauto. 
Qed.

Lemma twf_reach_taustar:
  forall tso thr tid s s'
    (R: twf_reach s nil s')
    (Gtid: thr ! tid = Some s)
    (Bemp: tso_buffers tso tid = nil),
    taustar (mklts event_labels (Comp.step tso_mm rtl_sem sge)) 
      (tso, thr) (tso, thr ! tid <- s').
Proof.
  intros until 1; remember (@nil buffer_item) as l; revert thr Heql; 
  induction R; intros; clarify;
    [by rewrite PTree.gsident; vauto| |];
    (by specialize (IHR (thr ! tid <- s')); rewrite PTree.gss, PTree.sss in *;
        econstructor; vauto; eauto).
Qed.

Lemma twf_reach_taustar2:
  forall tb tm thr ff tid s s'
    (R: twf_reach s ff s')
    (Gtid: thr ! tid = Some s)
    (Bemp: tb tid = nil)
    (FS: tso_fin_sup (mktsostate tb tm))
    (SAFE: unbuffer_safe (mktsostate tb tm)),
  (exists t,
    taustar (mklts event_labels (Comp.step tso_mm rtl_sem sge)) (mktsostate tb tm, thr) t 
    /\ can_do_error (mklts event_labels (Comp.step tso_mm rtl_sem sge)) t)
  \/ (exists m', taustar (mklts event_labels (Comp.step tso_mm rtl_sem sge)) 
        (mktsostate tb tm, thr) (mktsostate tb m', thr ! tid <- s')).
Proof.
  intros; revert tm thr Gtid FS SAFE; induction R; intros; clarify.
  - by right; rewrite PTree.gsident; [eexists|]; vauto.
  - exploit (IHR tm (thr ! tid <- s')); try rewrite PTree.gss; try rewrite PTree.sss; try done. 
    by intro; des; [left; eexists; split; try edone|right; eexists]; vauto.
  - exploit (IHR tm (thr ! tid <- s')); try rewrite PTree.gss; try rewrite PTree.sss; try done. 
    by intro; des; [left; eexists; split; try edone|right; eexists]; try edone; 
       eapply taustar_step; try edone; vauto.
  assert (FS' := fin_sup_buffer_insert tid (BufferedWrite p c v) _ FS).
  destruct (unbuffer_safe_dec _ FS') as [US|UNS].
  2: by destruct (tso_step_write_fail SAFE (not_unbuffer_safe FS' UNS)) as (? & ? & ? & ?); 
        left; eexists; split; [ eby eapply TSO.unbuffer_to_tsopc2
                              | eexists; exists (Evisible Efail); split; vauto].
  inversion US; clear UNBS; clarify; simpl in *.
  exploit (ABIS tid); [by rewrite tupdate_s, Bemp|intro; des]; clear ABIS.
  exploit (IHR m' (thr ! tid <- s')); 
      try rewrite PTree.gss; try rewrite PTree.sss; try done. 
  - eby eapply unbuffer_safe_arange, SAFE; eapply arange_eq_sym, arange_eq_store.
  intro; des; [left; eexists; split; try edone|right; eexists; try edone];
     eapply taustar_step, taustar_step; try edone; vauto;
     eapply (Comp.step_unbuf tso_mm rtl_sem sge); vauto;
     (econstructor; simpl; 
         [ by rewrite tupdate_s, Bemp 
         | by rewrite tupdate_red, <- Bemp, tupdate_red2 | done]).
Qed.

Section TraslThms.

Hypothesis (TRANSF: genv_rel sge tge).

Lemma function_ptr_translated:
  forall v f
    (H: Genv.find_funct_ptr sge v = Some f),
  Genv.find_funct_ptr tge v = Some (transf_fundef f).
Proof.
  intros; generalize (proj2 TRANSF v).
  destruct (Genv.find_funct_ptr sge v);
   destruct (Genv.find_funct_ptr tge v); try done.
  congruence.
Qed.

Lemma functions_translated:
  forall v f
    (H: Genv.find_funct sge v = Some f),
  Genv.find_funct tge v = Some (transf_fundef f).
Proof.
  intros; destruct v as [| |p|]; try done; simpl in *.
  by apply function_ptr_translated.
Qed.

Lemma symbols_preserved:
  forall id, Genv.find_symbol tge id = Genv.find_symbol sge id.
Proof. by intros; destruct TRANSF. Qed.

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = funsig f.
Proof. by intros [|]. Qed.

Lemma find_function_translated:
  forall ros ls f
    (FIND: find_function sge ros ls = Some f),
  find_function tge ros ls = Some (transf_fundef f).
Proof.
  intros [l|] ls f; simpl.
    by destruct (ls # l); try done; apply functions_translated.
  rewrite symbols_preserved; destruct (Genv.find_symbol sge i); try done.
  apply function_ptr_translated; done.
Qed.

Lemma function_ptr_translated_back:
  forall v f
    (FIND: Genv.find_funct_ptr tge v = Some f),
  exists f', Genv.find_funct_ptr sge v = Some f' /\ f = (transf_fundef f').
Proof.
  intros; pose proof (proj2 TRANSF v).
  destruct (Genv.find_funct_ptr sge v);
    destruct (Genv.find_funct_ptr tge v); clarify; vauto. 
Qed.

Lemma functions_translated_back:
  forall v f
    (FIND: Genv.find_funct tge v = Some f),
  exists f', Genv.find_funct sge v = Some f' /\ f = (transf_fundef f').
Proof.
  by intros [| |p|]; intros; clarify; apply function_ptr_translated_back.
Qed.

Lemma find_function_translated_back:
  forall ros ls f
    (FIND: find_function tge ros ls = Some f),
  exists f', find_function sge ros ls = Some f' /\ f = (transf_fundef f').
Proof.
  intros [l|] ls f; simpl.
    destruct (ls # l); try done; apply functions_translated_back; done.
  rewrite symbols_preserved; destruct (Genv.find_symbol sge i); try done.
  apply function_ptr_translated_back; done.
Qed.

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

Lemma sim_init:
  forall p v sinit,
    rtl_init tge p v = Some sinit ->
    exists f, exists l,
      sinit = Callstate nil (Internal (transf_function f)) l /\
      rtl_init sge p v = Some (Callstate nil (Internal f) l).
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
  by inv STACKS; inv H1; eapply NOtidSTEP; eapply exec_return.

  Case "exec_return_exit".
  by inv STACKS; eapply NOtidSTEP; eapply exec_return_exit.
Qed.

Ltac sim_tac B :=
  unfold analyze in *;
  match goal with
   | H: (fn_code _) ! ?pc = Some _ |- context[(match ?a with Some _ => _ | None => _ end) # ?spc] => 
       let EQ := fresh "EQ" in 
       destruct a as [] _eqn: EQ; [|rewrite !PMap.gi in *];
       try (eapply DS.fixpoint_solution with (n := pc) (s := spc) in EQ); 
       try (intro; apply B; unfold transfer; rewrite H; clarify; destruct EQ as [-> | ->]; clarify);
       try (by unfold successors, successors_list; rewrite PTree.gmap, H; simpl; vauto)
  end.

Lemma sim_step:
  forall b s t l t'
  (STEP : rtl_step tge t l t')
  (MS : match_states b s t),
  (exists s', rtl_step sge s l s' /\ match_states b s' t')
  \/ (exists s', l = TEtau /\ rtl_step sge s (TEmem MEfence) s' /\ match_states False s' t')
  \/ (match l with TEmem MEfence => True | TEmem (MErmw _ _ _ _) => True | _ => False end
     /\ exists s', rtl_step sge s l s' /\ match_states True s' t').
Proof.
  intros; (rtl_step_cases (destruct STEP) Case); clarify; inv MS; clarify; inv_asm;
   rewrite ?sim_eval_addressing, ?sim_eval_operation in *;
   try (by left; eexists; split; [vauto|econstructor; vauto; sim_tac BREL]);
   try (by right; right; split; [try inv ASME; done|eexists; split; [vauto|econstructor; vauto]]).

  Case "exec_Inop".
  right; left; eexists; split; split; [by vauto|econstructor; vauto; sim_tac BREL; clarify].
  by rewrite Heqt in *; destruct EQ as [<- |].

  Case "exec_Icall".
  eapply find_function_translated_back in H0; des; clarify; simpl in *.
  left; eexists; split; [by eapply exec_Icall; try eassumption; destruct f'|]. 
  econstructor; vauto; [].
  by apply BREL; unfold transfer; rewrite Heqo.
 
  Case "exec_Ireturn".
  left; eexists; split; vauto; [].
  econstructor; vauto; [].
  by apply BREL; unfold transfer; rewrite Heqo.

  Case "exec_function_internal_empty".
  by destruct f0; simpl in *; clarify; simpl; left; eexists; split; vauto. 

  Case "exec_function_internal_nonempty".
  by destruct f0; simpl in *; clarify; simpl; left; eexists; split; vauto. 

  Case "exec_function_external_call".
  by destruct f; simpl in *; clarify; simpl; left; eexists; split; vauto. 

  Case "exec_return".
  by left; inv STACKS; inv H2; eexists; split; vauto. 

  Case "exec_return_exit".
  by left; inv STACKS; eexists; split; vauto. 
Qed.

End TraslThms.

End BSIM.

Lemma match_program_transf:
  forall (prg : program),
    match_program (fun f1 f2 => transf_fundef f1 = f2)
                  (fun v1 v2 => v1 = v2)
                  prg (transf_program prg).
Proof.
  repeat split; unfold transf_program; simpl.
  induction (prog_funct prg) as [|[id fd] l IH]; vauto. 
  induction (prog_vars prg) as [|[[id init] fd] l IH]; vauto. 
Qed.

Lemma MScontra:
  forall tge t l t' s
    (tidSTEP : rtl_step tge t l t')
    (MS : match_states False s t),
   match l with
     | TEtau => True
     | TEmem (MEwrite _ _ _) => True
     | TEmem (MErmw _ _ _ _) => True
     | TEmem (MEfence) => True
     | _ => False
   end.
Proof.
  inversion 1; clarify; try (by inv ASME);
  inversion 1; clarify; 
  by elim BREL; inv_asm; unfold transfer; rewrite Heqo.
Qed.

(** Definition of [mystep] used as the "[order]" of the weaktau simulation.
    This is contains that [Comp.step]s for which we stutter using the normal
    simulation relation. *)

Inductive mystep ge : Comp.state tso_mm rtl_sem -> Comp.state tso_mm rtl_sem -> Prop :=
  | mystep_ord: (**r Ordinary memory events synchronize with the TSO machine *)
    forall s s' ev tid tso tso' st st'
      (tidSTEP: rtl_step ge s (TEmem ev) s')
      (tsoSTEP: tso_step tso (MMmem tid ev) tso')
      (Gtid: st ! tid = Some s)
      (WHAT: match ev with | MEwrite _ _ _ => True | _ => False end)
      (EQst': st' = st ! tid <- s'), 
    mystep ge (tso, st) (tso', st')
  | mystep_tau: (**r Thread tau action *)
    forall s s' tid tso st st'
      (tidSTEP: rtl_step ge s TEtau s')
      (Gtid: st ! tid = Some s)
      (EQst': st' = st ! tid <- s'),
    mystep ge (tso, st) (tso, st').

Lemma sim_step_ord:
  forall tge sge sb sm sthr ts ts' ev tid
     tb tm tthr tb' tm' tthr'
   (tidSTEP: rtl_step tge ts (TEmem ev) ts')
   (tsoSTEP: tso_step (mktsostate tb tm) (MMmem tid ev) (mktsostate tb' tm'))
   (Gtid: tthr ! tid = Some ts)
   (EQ: tthr' = tthr ! tid <- ts')
   (REL: fenceelim2_sim sge tge (mktsostate sb sm, sthr) (mktsostate tb tm, tthr))
   (tCONS: Comp.consistent tso_mm rtl_sem (mktsostate tb tm, tthr))
   (sCONS: Comp.consistent tso_mm rtl_sem (mktsostate sb sm, sthr)),
   (exists s'0,
      taustar (mklts event_labels (Comp.step tso_mm rtl_sem sge))
        (mktsostate sb sm, sthr) s'0 /\
      can_do_error (mklts event_labels (Comp.step tso_mm rtl_sem sge)) s'0) \/
   (exists s'0,
      taustep (mklts event_labels (Comp.step tso_mm rtl_sem sge))
        (mktsostate sb sm, sthr) Etau s'0 /\
      fenceelim2_sim sge tge s'0 (mktsostate tb' tm', tthr')) \/
   mystep tge (mktsostate tb tm, tthr) (mktsostate tb' tm', tthr') /\
   fenceelim2_sim sge tge (mktsostate sb sm, sthr) (mktsostate tb' tm', tthr').
Proof.
  intros; clarify.
  assert (M := sim_weaken2 REL).
  destruct REL; simpl in *; clarify. 
  generalize (Mthr tid); rewrite Gtid.
  destruct (sthr ! tid) as [s|] _eqn: GStid; clarify; 
    intros [(MS & BREL)|(ff & sn & R & BREL & MS)];
    [|pose proof (MScontra tidSTEP MS)].

  destruct (sim_step ENVR tidSTEP MS) as [(s' & STEP & MS')|[(? & ? & ?)|]]; 
    des; clarify; simpl in *; clarify;
  inv tsoSTEP; subst; simpl in *; unfold buffer_insert in *; clarify; try rewrite BREL in *;
  try (right; left; eexists; (split; [by eexists; split; vauto|]);
       split; simpl; vauto;
       try (intros tid'; generalize (Mthr tid'); destruct (peq tid' tid);
            [ by subst; rewrite !PTree.gss, ?tupdate_s, GStid; intros _; vauto
            | by rewrite !PTree.gso, ?tupdate_o; clarify])).

  SCase "tso_step_write".
  assert (FS' := fin_sup_buffer_insert tid (BufferedWrite p c v) _ 
                      (TSO.tso_cons_impl_fin_sup _ _ sCONS)).
  destruct (unbuffer_safe_dec _ FS') as [US|UNS].
  2: by destruct (tso_step_write_fail (proj2 sCONS) (not_unbuffer_safe FS' UNS)) 
           as (? & ? & ? & ?); 
        left; eexists; split; [ eby eapply TSO.unbuffer_to_tsopc2
                              | eexists; exists (Evisible Efail); split; vauto].

  right; left; eexists; split.
    by eexists; split; vauto.
  split; simpl; vauto.
  intros tid'; generalize (Mthr tid'); destruct (peq tid' tid);
    [by subst; rewrite !PTree.gss, !tupdate_s, GStid, BREL; left
    | by rewrite !PTree.gso, !tupdate_o; clarify].

  SCase "tso_step_alloc".
  assert (SF := fin_sup_buffer_insert tid (BufferedAlloc p i k) _
                                (TSO.tso_cons_impl_fin_sup _ _ sCONS)).
  destruct (unbuffer_safe_dec _ SF) as [US|NS].
  - right; left; eexists; split.
      by eexists; split; vauto.
    split; simpl; vauto.
    intros tid'; generalize (Mthr tid'); destruct (peq tid' tid);
      [ by subst; rewrite !PTree.gss, ?tupdate_s, GStid; intros _; vauto
      | by rewrite !PTree.gso, ?tupdate_o; clarify].
   - simpl in *.
  apply (not_unbuffer_safe SF) in NS.
  edestruct unbuffer_unsafe_not_safe; try eapply UNS. 
  clear Mthr.
  assert (N: forall tid, exists ff, tb tid = sb tid ++ ff).
    intro j; generalize (M j), (proj1 sCONS j), (proj1 tCONS j); simpl.
    rewrite !PTree.gmap.
    clear; destruct (sthr ! j); clarify; destruct (tthr ! j); clarify.
    - by intros; des; vauto.
    by intros _ X Y; rewrite X, Y; vauto. 
  end_assert N.
  revert NS N; clear; unfold buffer_insert; simpl.
  generalize (sb tid ++ BufferedAlloc p i k :: nil); intros l NS.
  remember (mktsostate (tupdate tid l sb) sm) as x;
  revert sb tb sm l Heqx; induction NS; intros; clarify; simpl in *.
    destruct (N tid0) as [x EQ].
    constructor 1 with tid0 bi (if peq tid0 tid then b else b ++ x); simpl; try done.
    destruct (peq tid0 tid); subst; rewrite ?tupdate_s, ?tupdate_o in BEQ |- *; try done. 
    by rewrite BEQ in *; simpl in *.

  destruct (N tid0) as [x EQ].
  constructor 2 with tid0 bi (if peq tid0 tid then b else b ++ x) m; simpl; try done.
    destruct (peq tid0 tid); subst; rewrite ?tupdate_s, ?tupdate_o in BEQ |- *; try done. 
    by rewrite BEQ in *; simpl in *.
  destruct (peq tid0 tid); subst.
  - by rewrite tupdate_red; eapply IHNS; try rewrite tupdate_red.
  rewrite tupdate_comm; try congruence.
  eapply (IHNS (tupdate tid0 b sb)); try rewrite tupdate_comm; try congruence.
  by intro j; destruct (peq j tid0); subst; rewrite ?tupdate_s, ?tupdate_o; vauto.

  SCase "tso_step_free".
  assert (SF := fin_sup_buffer_insert tid (BufferedFree p k) _ 
                        (TSO.tso_cons_impl_fin_sup _ _ sCONS)).
  destruct (unbuffer_safe_dec _ SF) as [US|NS].
  2: left; destruct (TSO.taustep_free_fail rtl_sem sge STEP NS GStid sCONS) as (? & ? & ? & ?); 
     eby eexists; split; [|eexists; exists (Evisible Efail)].

  right; left; eexists; split.
    by eexists; split; vauto.
  split; simpl; vauto.
  intros tid'; generalize (Mthr tid'); destruct (peq tid' tid);
    [ by subst; rewrite !PTree.gss, ?tupdate_s, GStid; intros _; vauto
    | by rewrite !PTree.gso, ?tupdate_o; clarify].

(* .......... *)

  destruct (sim_step ENVR tidSTEP MS) as [(sn' & STEP & MS')|[(? & ? & ?)|]]; 
    des; clarify; simpl in *; clarify;

  inversion tsoSTEP; subst; simpl in *; unfold buffer_insert in *; clarify; try rewrite BREL in *;
  try (right; right; split; [eby eapply mystep_ord|]; split; simpl; vauto;
       intros tid'; generalize (Mthr tid'); destruct (peq tid' tid);
            [ subst; rewrite !PTree.gss, ?tupdate_s, GStid; intros _; vauto
            | by rewrite !PTree.gso, ?tupdate_o; clarify]; 
       try apply app_eq_nil in Bemp; des; clarify;

  by right; try rewrite app_ass; eexists; eexists; split; 
     [eapply twf_reach_trans|split]; try edone; vauto).

  apply app_eq_nil in Bemp; des; clarify; rewrite H0 in *; simpl in *; clarify.
  right; left; eexists; split.
    eexists; split; [eby eapply twf_reach_taustar|].
    by eapply Comp.step_ord; eauto using PTree.gss; vauto.
  split; simpl; vauto.
  intros tid'; generalize (Mthr tid'); destruct (peq tid' tid);
    [ subst; rewrite !PTree.gss, ?tupdate_s, GStid; intros _; vauto
    | by rewrite !PTree.gso, ?tupdate_o; clarify].
  by right; eexists (nil); eexists sn'; split;
     [|split]; try edone; vauto; rewrite H0. 

  apply app_eq_nil in Bemp; des; clarify; simpl in *; clarify.
  right; left; eexists; split.
    eexists; split; [eby eapply twf_reach_taustar|].
    by eapply Comp.step_ord; eauto using PTree.gss; vauto.
  split; simpl; vauto.
  intros tid'; generalize (Mthr tid'); destruct (peq tid' tid);
    [ subst; rewrite !PTree.gss, ?tupdate_s, GStid; intros _; vauto
    | by rewrite !PTree.gso, ?tupdate_o; clarify].
  by right; eexists; eexists; vauto.

  apply app_eq_nil in Bemp; des; clarify; rewrite H3 in *; simpl in *; clarify.
  right; left; eexists; split.
    eexists; split; [eby eapply twf_reach_taustar|].
    by eapply Comp.step_ord; eauto using PTree.gss; vauto.
  split; simpl; vauto.
  intros tid'; generalize (Mthr tid'); destruct (peq tid' tid);
    [ subst; rewrite !PTree.gss, ?tupdate_s, GStid; intros _; vauto
    | by rewrite !PTree.gso, ?tupdate_o; clarify].
  left; split; try done; congruence.

  apply app_eq_nil in Bemp; des; clarify; rewrite H3 in *; simpl in *; clarify.
  right; left; eexists; split.
    eexists; split; [eby eapply twf_reach_taustar|].
    by eapply Comp.step_ord; eauto using PTree.gss; vauto.
  split; simpl; vauto.
  intros tid'; generalize (Mthr tid'); destruct (peq tid' tid);
    [ subst; rewrite !PTree.gss, ?tupdate_s, GStid; intros _; vauto
    | by rewrite !PTree.gso, ?tupdate_o; clarify].
  left; split; try done; congruence.
Qed.

Lemma sim_step_unbuf:
 forall sge tge sb sm sthr
   (tso tso' : tso_state) (st : PTree.t state)
   (tsoSTEP: tso_step tso (MMtau) tso')
   (SIM: fenceelim2_sim sge tge (mktsostate sb sm, sthr) (tso, st))
   (sCONS: Comp.consistent tso_mm rtl_sem (mktsostate sb sm, sthr))
   (tCONS: Comp.consistent tso_mm rtl_sem (tso, st)),
   (exists s' : Comp.state tso_mm rtl_sem,
      taustar (mklts event_labels (Comp.step tso_mm rtl_sem sge))
        (mktsostate sb sm, sthr) s' /\
      can_do_error (mklts event_labels (Comp.step tso_mm rtl_sem sge)) s') \/
   (exists s' : Comp.state tso_mm rtl_sem,
      taustep (mklts event_labels (Comp.step tso_mm rtl_sem sge))
        (mktsostate sb sm, sthr) Etau s' /\
      fenceelim2_sim sge tge s' (tso', st)).
Proof.
  intros; destruct SIM; simpl in *; clarify.
  inv tsoSTEP.
  rename t into tid.
  generalize (Mthr tid).
  generalize (proj1 tCONS tid); simpl; rewrite EQbufs at 1.
  rewrite PTree.gmap.
  destruct (st ! tid) as [?|] _eqn: Gtid; [intros _| by intro X; exploit X].
  destruct (sthr ! tid) as [ss|] _eqn: GStid; clarify;
    intros [(MS & BREL)|(ff & sn & R & BREL & MS)];
    simpl in *; rewrite BREL in *. 
  right; eexists; split. 
  - by eexists; split; vauto.
  split; simpl; vauto.
  intros tid'; generalize (Mthr tid'); destruct (peq tid' tid);
    [ by subst; rewrite ?PTree.gss, ?tupdate_s, GStid, Gtid; intros _; vauto
    | by rewrite ?PTree.gso, ?tupdate_o; clarify].

  destruct (sb tid) as [] _eqn: SB; simpl in *; clarify.
    eapply twf_reach_inv in R; des; clarify.
  SSCase "unbuffering from ff".
  assert (FS' := fin_sup_buffer_insert tid (BufferedWrite p c v) _ 
                      (TSO.tso_cons_impl_fin_sup _ _ sCONS)).
  destruct (unbuffer_safe_dec _ FS') as [US|UNS].
  2: by destruct (tso_step_write_fail (proj2 sCONS) (not_unbuffer_safe FS' UNS))
          as (? & ? & ? & ?);
        left; eexists; split;
        [ eby eapply taustar_trans; [eapply twf_reach_taustar|eapply TSO.unbuffer_to_tsopc2]
        | eexists; exists (Evisible Efail); split; [|eapply Comp.step_write_fail]; 
          eauto using PTree.gss; vauto].
  right; eexists; split. 
    eapply taustar_taustep; [eby eapply twf_reach_taustar|].
    eapply taustar_taustep; [eapply taustar_step; vauto|].
      by eapply Comp.step_ord; eauto using PTree.gss; vauto.
    eapply step_taustep; eapply Comp.step_unbuf.
    by econstructor; simpl; try edone; rewrite tupdate_s, SB.
  split; simpl; vauto.
  intros tid'; generalize (Mthr tid'); destruct (peq tid' tid);
    [ subst; rewrite ?PTree.gss, ?tupdate_s, GStid, Gtid; intros _; vauto
    | by rewrite ?PTree.gso, ?tupdate_o; clarify].
  eby right; eexists; eexists.

  SSCase "unbuffering from sb".
  right; eexists; split. 
  - by eexists; split; vauto.
  split; simpl; vauto.
  intros tid'; generalize (Mthr tid'); destruct (peq tid' tid);
    [ subst; rewrite ?PTree.gss, ?tupdate_s, GStid, Gtid; intros _; vauto
    | by rewrite ?PTree.gso, ?tupdate_o; clarify].
  by right; eexists; eexists; vauto.
Qed.

Lemma sim_machine_step:
 forall (sge tge : SEM_GE rtl_sem) (s t t' : Comp.state tso_mm rtl_sem)
     (e : fullevent)
   (STEP: Comp.step tso_mm rtl_sem tge t e t')
   (SIM: fenceelim2_sim sge tge s t)
   (sCONS: Comp.consistent _ _ s)
   (tCONS: Comp.consistent _ _ t)
   (NOM: e <> Eoutofmemory),
   (exists s' : St (mklts event_labels (Comp.step tso_mm rtl_sem sge)),
      taustar (mklts event_labels (Comp.step tso_mm rtl_sem sge)) s s' /\
      can_do_error (mklts event_labels (Comp.step tso_mm rtl_sem sge)) s') \/
   (exists s' : St (mklts event_labels (Comp.step tso_mm rtl_sem sge)),
        taustep (mklts event_labels (Comp.step tso_mm rtl_sem sge)) s e s' /\
        fenceelim2_sim sge tge s' t') \/
   (e = Etau /\ mystep tge t t' /\ fenceelim2_sim sge tge s t').
Proof.
  intros sge tge [[sb sm] sthr] t t' e STEP.
  (comp_step_cases (case STEP) Case); clear t e t' STEP; simpl in *; try done;
    try (by inversion 1; clarify; first [by destruct sp | by inv ASME]).

  Case "step_ord".
  intros; destruct tso; destruct tso'; exploit sim_step_ord; try eassumption.
  by intro; des; eauto.

  Case "step_ext".
  intros; destruct SIM; simpl in *; clarify. 
  generalize (Mthr tid); rewrite Gtid.
  destruct (sthr ! tid) as [ss|] _eqn: GStid; clarify; 
   intros [(MS & BREL)|(ff & sn & R & BREL & MS)];
   [|by pose proof (MScontra tidSTEP MS)].

  destruct (sim_step ENVR tidSTEP MS) as [(ss' & STEP & MS')|[(? & ? & ?)|]]; 
    des; clarify; simpl in *; clarify.
  right; left; eexists; split; [try by eexists; vauto|].
  split; simpl; vauto;
  intros tid'; generalize (Mthr tid'); destruct (peq tid' tid);
    [ by subst; rewrite !PTree.gss, ?tupdate_s, GStid; intros _; vauto
    | by rewrite !PTree.gso, ?tupdate_o; clarify].

  Case "step_unbuf".
  by intros; edestruct sim_step_unbuf; try eassumption; vauto.

  Case "step_tau".
  intros; destruct SIM; simpl in *; clarify.
  generalize (Mthr tid); rewrite Gtid.
  destruct (sthr ! tid) as [ss|] _eqn: GStid; clarify;
    intros [(MS & BREL)|(ff & sn & R & BREL & MS)];

  destruct (sim_step ENVR tidSTEP MS); des; clarify; simpl in *; clarify.

  right; left.
    eexists; split.
    - eexists; split; vauto.
  split; simpl; vauto.
  intros tid'; generalize (Mthr tid'); destruct (peq tid' tid);
    [ by subst; rewrite ?PTree.gss, ?tupdate_s, GStid, Gtid; intros _; vauto
    | by rewrite ?PTree.gso, ?tupdate_o; clarify].

  right; right; eexists; repeat first [done|split]; simpl; vauto.
  intros tid'; generalize (Mthr tid'); destruct (peq tid' tid);
    [ subst; rewrite ?PTree.gss, ?tupdate_s, GStid, Gtid; intros _; vauto
    | by rewrite ?PTree.gso, ?tupdate_o; clarify].
  by right; exists nil; eexists; split; [|eby rewrite <- app_nil_end]; vauto.

  right; right; eexists; repeat first [done|split]; simpl; vauto.
  intros tid'; generalize (Mthr tid'); destruct (peq tid' tid);
    [ subst; rewrite ?PTree.gss, ?tupdate_s, GStid, Gtid; intros _; vauto
    | by rewrite ?PTree.gso, ?tupdate_o; clarify].
  right; eexists; eexists; split; [|edone].
  by rewrite (app_nil_end ff); eapply twf_reach_trans; try edone; vauto.

  right; right; eexists; repeat first [done|split]; simpl; vauto.
  intros tid'; generalize (Mthr tid'); destruct (peq tid' tid);
    [ subst; rewrite ?PTree.gss, ?tupdate_s, GStid, Gtid; intros _; vauto
    | by rewrite ?PTree.gso, ?tupdate_o; clarify].
  right; eexists; eexists; split; [|edone].
  by rewrite (app_nil_end ff); eapply twf_reach_trans; try edone; vauto.

  Case "step_start".
  intros; destruct SIM; simpl in *; clarify.
  generalize (Mthr tid); rewrite Gtid.
  destruct (sthr ! tid) as [ss|] _eqn: GStid; clarify;
    intros [(MS & BREL)|(ff & sn & R & BREL & MS)];
    [|by pose proof (MScontra tidSTEP MS)].
  destruct (sim_step ENVR tidSTEP MS); des; clarify; simpl in *; clarify.
  assert (sthr ! newtid = None).
  - by generalize (Mthr newtid); rewrite Gnewtid; clear; destruct (sthr ! newtid).
  exploit sim_init; try edone; []; intro; des; clarify.
  inv tsoSTEP; simpl.
  right; left.
    eexists; split.
    - by eexists; split; vauto.
  split; simpl; vauto.
  intros tid'; generalize (Mthr tid'); destruct (peq tid' tid); 
  destruct (peq tid' newtid); subst; subst; clarify';
     repeat first [ done | by vauto | 
                    match goal with H : _ = _ |- _ => rewrite H end 
                  | rewrite PTree.gss | rewrite tupdate_s
                  | rewrite PTree.gso | rewrite tupdate_o ].
  by left; split; vauto.

  Case "step_start_fail".
  intros; destruct SIM; simpl in *; clarify.
  generalize (Mthr tid); rewrite Gtid.
  destruct (sthr ! tid) as [ss|] _eqn: GStid; clarify;
    intros [(MS & BREL)|(ff & sn & R & BREL & MS)];
    [|by pose proof (MScontra tidSTEP MS)].
  destruct (sim_step ENVR tidSTEP MS); des; clarify; simpl in *; clarify.
  exploit sim_init_none; try edone; []; intro; des; clarify.
  left; eexists; split; [by vauto|].
  by eexists; exists (Evisible Efail); split; try done; vauto.

  Case "step_exit".
  intros; destruct SIM; simpl in *; clarify.
  generalize (Mthr tid); rewrite Gtid.
  destruct (sthr ! tid) as [ss|] _eqn: GStid; clarify;
    intros [(MS & BREL)|(ff & sn & R & BREL & MS)];
    [|by pose proof (MScontra tidSTEP MS)].
  destruct (sim_step ENVR tidSTEP MS); des; clarify; simpl in *; clarify.
  inv tsoSTEP; rewrite BREL in *.
  right; left; eexists; split; [by eexists; split; vauto|].
  split; simpl; vauto.
  intros tid'; generalize (Mthr tid'); destruct (peq tid' tid); subst; clarify';
     repeat first [ done | by vauto | 
                    match goal with H : _ = _ |- _ => rewrite H end 
                  | rewrite PTree.grs | rewrite tupdate_s
                  | rewrite PTree.gro | rewrite tupdate_o ].

  Case "step_read_fail".
  intros; destruct SIM; simpl in *; clarify.
  generalize (Mthr tid); rewrite Gtid.
  destruct (sthr ! tid) as [ss|] _eqn: GStid; clarify;
    intros [(MS & BREL)|(ff & sn & R & BREL & MS)];
    [|by pose proof (MScontra tidSTEP MS)].
  destruct (sim_step ENVR tidSTEP MS); des; clarify; simpl in *; clarify.
  inv tsoSTEP; rewrite BREL in *.
  left; eexists; split; [by vauto|].
  by eexists; exists (Evisible Efail); split; try done; vauto.

  Case "step_write_fail".
  intros; destruct SIM; simpl in *; clarify.
  generalize (Mthr tid); rewrite Gtid.
  destruct (sthr ! tid) as [ss|] _eqn: GStid; clarify;
    intros [(MS & BREL)|(ff & sn & R & BREL & MS)];
  destruct (sim_step ENVR tidSTEP MS); des; clarify; simpl in *; clarify;
  inv tsoSTEP; rewrite BREL in *.
  - left; eexists; split; [by vauto|];
    by eexists; exists (Evisible Efail); split; try done; vauto. 
  - eapply app_eq_nil in Bemp; des; clarify; rewrite <- app_nil_end in *. 
    left; eexists; split; [eby eapply twf_reach_taustar|].
    eexists; exists (Evisible Efail); split; try done.
    by eapply Comp.step_write_fail; eauto using PTree.gss; vauto.

  Case "step_free_fail".
  intros; assert (M := sim_weaken2 SIM); destruct SIM; simpl in *; clarify.
  generalize (Mthr tid); rewrite Gtid.
  destruct (sthr ! tid) as [ss|] _eqn: GStid; clarify;
    intros [(MS & BREL)|(ff & sn & R & BREL & MS)];
    [|by pose proof (MScontra tidSTEP MS)].
  destruct (sim_step ENVR tidSTEP MS); des; clarify; simpl in *; clarify.
  inv tsoSTEP.
  clear Mthr.
  destruct (free_ptr p k (tso_mem tso')) as [] _eqn: FREE.
  2: by left; eexists; split; [by vauto|];
        eexists; exists (Evisible Efail); split; [done|]; 
        eapply Comp.step_free_fail with (tid:=tid); try edone;
        econstructor; simpl; try congruence; rewrite FREE.
  destruct FAIL as (tid' & p' & c & v & b & Beq' & STO).
  specialize (M tid'); generalize (proj1 tCONS tid'); simpl.
  rewrite PTree.gmap.
  destruct (sthr ! tid') as [] _eqn: S'; destruct (st ! tid'); 
    des; clarify; [intros _| by intro X; rewrite X in *].
  destruct (sb tid') as [] _eqn: SB; simpl in *; clarify'.
  2: eby left; eexists; split; [by vauto|];
         eexists; exists (Evisible Efail); split; [done|]; 
         eapply Comp.step_free_fail with (tid:=tid); try edone;
         econstructor; simpl; try congruence; rewrite FREE; repeat eexists.
  assert (load_ptr c m p' = None).
    by generalize (store_chunk_allocated_noneD STO),
         (load_chunk_allocated_spec c m p'); destruct (load_ptr c m p').
  assert (tid <> tid') by congruence.
  rewrite Beq' in H1.
  assert (FS := fin_sup_buffer_insert tid' (BufferedWrite p' c v) _
                                      (TSO.tso_cons_impl_fin_sup _ _ sCONS)).
  destruct (twf_reach_inv H1) as (? & ? & ? & sss & ? & ? & REACH & STEP & ?); clarify.
  assert (TAU:=twf_reach_taustar (mktsostate sb (tso_mem tso')) sthr _ REACH S' SB).
  destruct (unbuffer_safe_dec _ FS) as [US|NS].
  + left; eexists; split.
      eapply taustar_trans, steptau_taustar; try eassumption. 
    eapply (Comp.step_ord ); try edone; try eapply PTree.gss; vauto;
    econstructor; try edone.
    eexists; exists (Evisible Efail); split; [done|].
    eapply Comp.step_free_fail with (tid:=tid); try edone; [|by rewrite !PTree.gso].
    econstructor; simpl; try done.
    - rewrite tupdate_o; congruence.
    eby rewrite FREE, SB; simpl; exists tid';
        repeat eexists; [rewrite tupdate_s|].
  + destruct (tso_step_write_fail (proj2 sCONS) (not_unbuffer_safe FS NS))
      as (? & ? & ? & ?); simpl in *.
    left; eexists; split; [eby eapply taustar_trans, TSO.unbuffer_to_tsopc2|].
    eexists; exists (Evisible Efail); split; [done|]; 
    by eapply (Comp.step_write_fail); try edone; try eapply PTree.gss; vauto.

  Case "step_rmw_fail".
  intros; destruct SIM; simpl in *; clarify.
  generalize (Mthr tid); rewrite Gtid.
  destruct (sthr ! tid) as [ss|] _eqn: GStid; clarify;
    intros [(MS & BREL)|(ff & sn & R & BREL & MS)];
  destruct (sim_step ENVR tidSTEP MS); des; clarify; simpl in *; clarify;
  inv tsoSTEP; rewrite BREL in *.
  - left; eexists; split; [by vauto|];
    by eexists; exists (Evisible Efail); split; try done; vauto. 
  - left; eexists; split; [by vauto|];
    by eexists; exists (Evisible Efail); split; try done; vauto. 
  - eapply app_eq_nil in Bemp; des; clarify; rewrite <- app_nil_end in *. 
    left; eexists; split; [eby eapply twf_reach_taustar|].
    eexists; exists (Evisible Efail); split; try done.
    by eapply Comp.step_rmw_fail; eauto using PTree.gss; vauto.
  - eapply app_eq_nil in Bemp; des; clarify; rewrite <- app_nil_end in *. 
    left; eexists; split; [eby eapply twf_reach_taustar|].
    eexists; exists (Evisible Efail); split; try done.
    by eapply Comp.step_rmw_fail; eauto using PTree.gss; vauto.

  Case "step_thread_stuck".
  intros; destruct SIM; simpl in *; clarify.
  generalize (Mthr tid); rewrite Gtid.
  destruct (sthr ! tid) as [ss|] _eqn: GStid; clarify;
    intros [(MS & BREL)|(ff & sn & R & BREL & MS)];
    pose proof (sim_stuck ENVR NOtidSTEP MS).

  - left; eexists; split; [by vauto|];
    by eexists; exists (Evisible Efail); split; try done; vauto.

  (* Empty the buffer first, then do twf_reach, then stuck *)
  destruct (apply_buffer (sb tid) (tso_mem tso)) as [] _eqn: AB.
  2: by destruct (no_unbuffer_errors _ tid (proj2 tCONS)); 
        simpl; rewrite BREL, apply_buffer_app, AB. 
  assert (taustar (mklts event_labels (Comp.step tso_mm rtl_sem sge))
             (mktsostate sb (tso_mem tso), sthr)
             (mktsostate (tupdate tid nil sb) m, sthr))
    by (apply TSO.unbuffer_to_tsopc; done).
  eapply Comp.taustar_preserves_consistency in sCONS; try eassumption.
  pose proof (twf_reach_taustar2 (sge:=sge) _ _ R GStid (tupdate_s _ _ _) 
                (TSO.tso_cons_impl_fin_sup _ _ sCONS) (proj2 sCONS)). 
  des; [by left; eauto using taustar_trans|].
  left; eexists; split; [eby eapply taustar_trans|].
  eexists; exists (Evisible Efail); split; try done; vauto.
  eapply Comp.step_thread_stuck; eauto using PTree.gss. 
Qed.

Lemma sim_machine_wstep:
 forall (sge tge : SEM_GE rtl_sem) (s t t' : Comp.state tso_mm rtl_sem)
   (REL: fenceelim2_wsim sge tge s t)
   (MY: mystep tge t t')
   (sCONS: Comp.consistent _ _ s)
   (sCONS: Comp.consistent _ _ t),
   (exists s', taustar (mklts event_labels (Comp.step tso_mm rtl_sem sge)) s s'
       /\ can_do_error (mklts event_labels (Comp.step tso_mm rtl_sem sge)) s') \/
   (exists s', taustep (mklts event_labels (Comp.step tso_mm rtl_sem sge)) s Etau s'
       /\ fenceelim2_wsim sge tge s' t').
Proof.
  intros; destruct REL; destruct MY; [destruct ev; clarify; inv tsoSTEP|];
  destruct s as [[sb sm] sthr];
  generalize (Mthr tid); simpl in *; rewrite Gtid;
  destruct (sthr ! tid) as [ss|] _eqn: GStid; clarify;
    intros (ff & sn & R & MS);

  (destruct (apply_buffer (sb tid) sm) as [sm'|] _eqn: AB;
   [|by generalize (no_unbuffer_errors _ tid (proj2 sCONS))]);

  assert (TAUS: taustar (mklts event_labels (Comp.step tso_mm rtl_sem sge))
             (mktsostate sb sm, sthr)
             (mktsostate (tupdate tid nil sb) sm', sthr))
    by (apply TSO.unbuffer_to_tsopc; done);
  eapply Comp.taustar_preserves_consistency in sCONS; try eassumption;

  destruct (sim_step ENVR tidSTEP MS) as [(ss' & STEP & MS')|[(? & ? & ?)|]]; 
    des; clarify; simpl in *; clarify;

  eapply twf_reach_taustar2 with (tb := tupdate tid nil sb) in R;
    try eapply (TSO.tso_cons_impl_fin_sup _ _ sCONS);
    try eapply (proj2 sCONS);
    try eassumption; simpl; eauto using @tupdate_s;
  des; eauto using taustar_trans.

  Case "write".
  eapply Comp.taustar_preserves_consistency in sCONS; try eassumption.

  assert (FS' := fin_sup_buffer_insert tid (BufferedWrite p chunk v) _ 
                      (TSO.tso_cons_impl_fin_sup _ _ sCONS)).
  destruct (unbuffer_safe_dec _ FS') as [US|UNS].
  2: by destruct (tso_step_write_fail (proj2 sCONS) (not_unbuffer_safe FS' UNS))
          as (? & ? & ? & ?);
        left; eexists; split;
        [ eby eapply taustar_trans, taustar_trans; [| |eapply TSO.unbuffer_to_tsopc2]
        | eexists; exists (Evisible Efail); split; [|eapply Comp.step_write_fail]; 
          eauto using PTree.gss; vauto].
 
  right; eexists; split.
  - eexists; split; [eby eapply taustar_trans|]; simpl. 
    by eapply Comp.step_ord; simpl; try edone; vauto; eapply PTree.gss.
  split; simpl; try done.
  intros tid'; generalize (Mthr tid'); destruct (peq tid' tid);
    [ subst; rewrite ?PTree.gss, ?tupdate_s, GStid, Gtid; intros _; vauto
    | by rewrite ?PTree.gso, ?tupdate_o; clarify].
  by exists nil; eexists; vauto.

  Case "tau".
  right; eexists; split.
  - eexists; split; [eby eapply taustar_trans|]; simpl. 
    by eapply Comp.step_tau; simpl; try edone; vauto; eapply PTree.gss.
  split; simpl; try done.
  intros tid'; generalize (Mthr tid'); destruct (peq tid' tid);
    [ subst; rewrite ?PTree.gss, ?tupdate_s, GStid, Gtid; intros _; vauto
    | by rewrite ?PTree.gso, ?tupdate_o; clarify].
  by exists nil; eexists; vauto.

  Case "tau-fence".
  right; eexists; split.
  - eexists; split; [eby eapply taustar_trans|]; simpl. 
    by eapply Comp.step_ord; simpl; try edone; (try econstructor (eapply tupdate_s)); eapply PTree.gss. 
  split; simpl; try done.
  intros tid'; generalize (Mthr tid'); destruct (peq tid' tid);
    [ subst; rewrite ?PTree.gss, ?tupdate_s, GStid, Gtid; intros _; vauto
    | by rewrite ?PTree.gso, ?tupdate_o; clarify].
  exists nil; eexists; split; vauto.
  by inv H1; vauto.
Qed.

Lemma sim_machine_init:
 forall (sprg tprg : SEM_PRG rtl_sem) (tge : SEM_GE rtl_sem)
     (args : list val) (tinit : Comp.state tso_mm rtl_sem),
   fenceelim2_match_prg sprg tprg ->
   valid_args args ->
   Comp.init tso_mm rtl_sem tprg args tge tinit ->
   exists sge : SEM_GE rtl_sem,
     exists sinit : Comp.state tso_mm rtl_sem,
       Comp.init tso_mm rtl_sem sprg args sge sinit /\
       fenceelim2_sim sge tge sinit tinit.
Proof.
  unfold Comp.init; simpl; unfold rtl_ge_init; intros; des; clarify; simpl in *.
  exploit (transform_program_match); try eassumption; intro M.
  eapply Genv.exists_matching_genv_and_mem_rev in M; try eassumption; des.
  unfold fenceelim2_match_prg in *; clarify; simpl in *.
  erewrite symbols_preserved in * |-; try eassumption.
  exploit sim_init; try edone; intro; des.
  repeat first [edone |eexists]; simpl.
  instantiate (1 := maintid).
  intro tid; destruct (peq tid maintid); subst; 
  rewrite ?PTree.gss, ?PTree.gso, ?PTree.gempty; try done; [].
  by left; split; vauto.
Qed.

(** Packaging of the proof into a weaktau simulation. *)

Definition fenceelim2_basic_sim : Bsim.sim tso_mm tso_mm rtl_sem rtl_sem fenceelim2_match_prg.
Proof.
  apply (@Bsim.make tso_mm tso_mm rtl_sem rtl_sem fenceelim2_match_prg 
            fenceelim2_sim (fun _ => mystep)); try done.
  - by destruct 1; intros; eapply PTree.ext; intro tid;
       generalize (Mthr tid); rewrite EMPTY, PTree.gempty; clear; destruct PTree.get.
  - eby intros; eapply sim_machine_init. 
  - eby intros; eapply sim_machine_step.
Defined.

Theorem fenceelim2sim : WTsim.sim tso_mm tso_mm rtl_sem rtl_sem fenceelim2_match_prg.
Proof.
  apply (@WTsim.make _ _ _ _ _ fenceelim2_basic_sim fenceelim2_wsim); try done.
  - destruct 1; split; try done. 
    intro tid; specialize (Mthr tid); 
      destruct ((snd s) ! tid); try done;
      destruct ((snd t) ! tid); try done; des.
    + by exists nil; eexists; split; try edone; vauto.
    + by eexists; eexists; split; try edone; inv H1; vauto. 
  - eby intros; eapply sim_machine_wstep.
Qed.
