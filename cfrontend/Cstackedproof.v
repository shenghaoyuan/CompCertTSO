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
Require Import Floats.
Require Import Values.
Require Import Pointers.
Require Import Events.
Require Import Globalenvs.
Require Import TSOmachine.
Require Import TSOsimulation.
Require Import Relations.Relation_Operators.
Require Cminor.
Require Import Cminorgen.
Require Import Cstacked.
Require Import Csharpminor.
Require Import Simulations.
Require Import Mem.
Require Import Memeq.
Require Import Memcomp Traces.
Require Import Cstackedproofsimdef.
Require Import Cstackedproofunbuffer.
Require Import Cstackedproofalloc.
Require Import Cstackedprooffree.
Require Import Cstackedprooftau.
Require Import Errors.
Require Import Libtactics.

Section SIM.

Variable cst_globenv : genv * gvarenv.
Variable csm_globenv : genv * gvarenv.

Let cshm_lts := (mklts event_labels (Comp.step tso_mm cs_sem csm_globenv)).
Let cst_lts := (mklts event_labels (Comp.step tso_mm cst_sem cst_globenv)).

Hypothesis globenv_same:
  Genv.genv_match (fun a b => a = b) (Cstacked.ge cst_globenv) (ge csm_globenv) /\
  Cstacked.gvare cst_globenv = gvare csm_globenv.

Hypothesis globenv_machine:
  forall id p, Genv.find_symbol (Cstacked.ge cst_globenv) id = Some p -> 
               machine_ptr p.

Hypothesis function_stacksize_limit:
  forall p f cenv, Genv.find_funct (Cstacked.ge cst_globenv) p = 
                     Some (Internal f) ->
                   snd (build_compilenv cenv f) <= Int.max_unsigned.

Notation cont_related := (cont_related cst_globenv). 
Notation expr_cont_related := (expr_cont_related cst_globenv). 
Notation state_related := (state_related cst_globenv).
Notation buffered_states_related := (buffered_states_related cst_globenv).
Notation buffered_ostates_related := (buffered_ostates_related cst_globenv).
Notation tso_pc_related_witt := (tso_pc_related_witt cst_globenv).
Notation tso_pc_related := (tso_pc_related cst_globenv).
Notation tso_pc_unsafe_related := (tso_pc_unsafe_related cst_globenv).
Notation unbuffer_item_preserves_tso_pc_unsafe :=
              (unbuffer_item_preserves_tso_pc_unsafe cst_globenv).
Notation tso_pc_related_to_buff_states :=
              (tso_pc_related_to_buff_states cst_globenv).  

Lemma eval_var_ref_rel:
  forall tp sp sm te se p c id,
    env_related tp sp sm te se ->
    Cstacked.eval_var_ref cst_globenv te id p c ->
    Csharpminor.eval_var_ref csm_globenv se id p c.
Proof.
  intros tp sp sm te se p c id ER EVR.
  
  destruct ER as [n (_ & _ & _ & EIR)].
  
  specialize (EIR id).
  inv EVR; rewrite EG in EIR;
    destruct (se ! id) as [sei|] _eqn : Esei; try done.
    inv EIR.
    apply eval_var_ref_local. rewrite EB in *. clarify.
  apply eval_var_ref_global. edone. by rewrite (proj1 (proj1 globenv_same)).
  by rewrite <- (proj2 globenv_same).
Qed.

Lemma fence_sim:
  forall s s' (st : PTree.t Cstacked.state) t tso csms
    (ST : SEM_step cst_sem cst_globenv s (TEmem MEfence) s')
    (CS : st ! t = Some s)
    (Bemp : tso_buffers tso t = nil)
    (TSOPCREL : tso_pc_related (tso, st) csms),
      can_reach_error csm_globenv csms \/
      (exists shms' : St cshm_lts,
        taustep cshm_lts csms Etau shms' /\ 
        tso_pc_related (tso, st ! t <- s') shms').
Proof.
  intros. destruct csms as [cstso csst].
  generalize TSOPCREL; intros [TC [bp [tp [sp TREL]]]].
  pose proof (tso_pc_related_to_buff_states _ _ _ _ _ _ _ t TREL) as BOR.
  destruct TREL as (_ & _ & (MCRt & _ & LR & MM) & _ & BE & _ & _ & _ & _ & BR).
  destruct (BR t) as (_ & BRt & _).
  simpl in *; rewrite CS in BOR.
  destruct (csst ! t) as [ss'|] _eqn : Ess'; simpl in BOR; try done.
  destruct BOR as [sm' [sp' [tp' (AB' & PUBt & PUBs & SR & SCO)]]].

  simpl in BRt. rewrite Bemp in BRt. inv BRt. specialize (BE t).
  replace (bp t) with (@nil (list buffer_item)) in BE. simpl in BE.

  pose proof (step_consistent_with_env ST SCO) as SCO'.

  inv ST; inv SR; right.
  eexists (_, _); split. 
  apply step_taustep. simpl.
  by eapply Comp.step_ord; try edone; vauto.
  eapply memory_neutral_sim; try edone.
  intros tpt spt smt SR. 
  inv SR; eby econstructor.
Qed.

Lemma read_sim:
  forall s s' p c v (st : PTree.t Cstacked.state) t tso m csms
    (ST : cst_step cst_globenv s (TEmem (MEread p c v)) s')
    (CS : st ! t = Some s)
    (AB : apply_buffer (tso.(tso_buffers) t) tso.(tso_mem) = Some m)
    (LP : load_ptr c m p = Some v)
    (TSOPCREL : tso_pc_related (tso, st) csms),
      can_reach_error csm_globenv csms \/
      (exists shms' : St cshm_lts,
        taustep cshm_lts csms Etau shms' /\ 
        tso_pc_related (tso, st ! t <- s') shms').
Proof.
  intros. destruct csms as [cstso csst].
  generalize TSOPCREL; intros [TC [bp [tp [sp TREL]]]].
  pose proof (tso_pc_related_to_buff_states _ _ _ _ _ _ _ t TREL) as BOR.
  destruct TREL as (_ & _ & (MCRt & _ & _) & _).
  simpl in *; rewrite CS in BOR.
  destruct (csst ! t) as [ss'|] _eqn : Ess'; simpl in BOR; try done.
  destruct BOR as [sm' [sp' [tp' (AB' & PUBt & PUBs & SR & SCO)]]].

  pose proof (step_consistent_with_env ST SCO) as SCO'.

  assert (MP : machine_ptr p).
    pose proof (load_chunk_allocated_spec c m p) as LS.
    rewrite LP in LS. destruct LS as [[[[b' o'] n'] [k [RI RA]]] _].
    apply range_allocated_consistent_with_restr in RA.
    destruct p as [b o]. destruct RI as [-> _].
    by rewrite (mem_consistent_with_restr_apply_buffer _ _ _ AB), MCRt in RA.

  pose proof (tso_pc_rel_load_eq cst_globenv _ _ _ _ _ _ _ _ c MP TSOPCREL AB AB') as LD.
  rewrite LP in LD.

  destruct LD as [[LSUCC MV] | LF].
    (* Load succeeded *)
    inv ST; inv SR; right.
      (* Variable read *)
      eexists (_, _); split. 
      apply step_taustep. simpl.
      eapply Comp.step_ord; try edone.
        econstructor; eby try eapply eval_var_ref_rel. 
        eby econstructor.
      eapply memory_neutral_sim; try edone.
      intros tpt spt smt SR. 
      inv SR; eby econstructor.
    (* Explicit load *)
    inv EKR.
    eexists (_, _).
    split. 
    apply step_taustep. simpl.
    eapply Comp.step_ord; try edone.
        eby econstructor. 
      eby econstructor.
    eapply memory_neutral_sim; try edone.
    intros tpt spt smt SR. 
    inversion SR; inversion EKR.
    econstructor; try edone.
  (* Load fail - unfortunately we have to do almost the same gymnastics 
     as above (and fail). *)
  left. 
  pose proof (TSO.unbuffer_to_tsopc cs_sem csm_globenv _ _ _ csst AB') as TS.
  eexists (_, _). split. edone.
  inv ST; inv SR. 
    eexists (_, _). exists (Evisible Efail).
    split. done. simpl.
    eapply Comp.step_read_fail; try edone. 
      econstructor; eby try eapply eval_var_ref_rel.
    econstructor; try edone; by simpl; rewrite tupdate_s.
  inv EKR.
  eexists (_, _). exists (Evisible Efail).
  split. done. simpl.
  eapply Comp.step_read_fail; try edone.
    eby econstructor.
  econstructor; try edone; by simpl; rewrite tupdate_s.
Qed.

Lemma tso_cons_store:
  forall sem c tso st p v m'
    (S  : store_ptr c (tso_mem tso) p v = Some m')
    (TC : Comp.consistent tso_mm sem (tso, st)),
      (Comp.consistent tso_mm sem (mktsostate (tso_buffers tso) m', st)).
Proof.
  intros. destruct TC as (BC & US).
  split; simpl in *.
    intros t N. simpl in *; auto.
  destruct tso as [bufs m].
  eapply unbuffer_safe_arange; [|edone].
  eby eapply arange_eq_sym, arange_eq_store.
Qed.

Lemma store_both_related:
  forall tso sthr cstso tthr m' sm'' v p c
 (TREL: tso_pc_related (tso, tthr) (cstso, sthr))
 (MP : machine_ptr p)
 (MV : machine_val v)
 (S  : store_ptr c (tso_mem tso)   p v = Some m')
 (S' : store_ptr c (tso_mem cstso) p v = Some sm''),
 tso_pc_related
     (mktsostate (tso_buffers tso) m', tthr)
     (mktsostate (tso_buffers cstso) sm'', sthr).
Proof.
  intros.
  destruct TREL as [[BC US] [bp [tp [sp TREL]]]].
  destruct TREL as (MTB & NSMR & (MCRt & MCRs & LR & MCM) & (BCs & USs) &
    BPD & BNE & SAF & MRPt & MRPs & TREL).

  assert (buffer_item_irrelevant (BufferedWrite p c v)) by done.
  assert (apply_buffer_item (BufferedWrite p c v) (tso_mem tso) = Some m') by done.
  assert (apply_buffer_item (BufferedWrite p c v) (tso_mem cstso) = Some sm'') by done.

  split.
    eby eapply tso_cons_store.
  exists bp. exists tp. exists sp.
  split. done.
  split.
      eby eapply sim_irrelevant_preserves_non_stack_mem_related. 
  split.
    (* mem_content_related preservation *)
    split. eby erewrite mem_consistent_with_restr_apply_item.
    split. eby erewrite mem_consistent_with_restr_apply_item.
    (* Load value related *)
    split. eby eapply sim_irrelevant_preserves_load_rel.
    (* Memory contents are machine values *)
    by eapply apply_machine_item_preserves_machine_memory; try edone. 
  split.
    eby eapply tso_cons_store.
  split. done. (* Buffer partitioning *)
  split. done. (* Buffer partitions not empty *)
  split. done. (* Allocation freshness for scratch items *)
  split. (* Memory related with partitioning in target *)
    eby eapply store_ptr_preserves_mem_partitioning.
  split. (* Memory related with partitioning in source *) 
    eby eapply store_ptr_preserves_mem_partitioning.
  intro t'.
  specialize (TREL t'). destruct TREL as [PI [BREL BSREL]].
  split. done. (* Partition injectivity *)
  (* Per-thread buffered simulation is preserved *)
  split. done.
  simpl in *.
  destruct (sthr ! t') as [sst|]; destruct (tthr ! t') as [tst|]; 
    simpl in BSREL; try done.
  simpl.
  pose proof MRPs as X; destruct X as [PD [RLD RLA]].
(*  destruct (apply_buffer_preserves_mem_partitioning _ _ _ _ _ _ 
    MRPs SAB PUBwithbi) as [PR' [RLD' RLA']]. *)
  apply buffered_states_related_load_inv with (smem := tso_mem cstso);
    try done.
        intros r IN. apply (RLA r). eby eexists.
      intros r IN. apply -> (store_preserves_allocated_ranges S'). 
      by apply -> RLA; eauto.
    eapply tso_consistent_safe_buffer_app; try edone.
      rewrite <- app_nil_end. apply BPD.
    replace sm'' with (tso_mem (mktsostate (tso_buffers cstso) sm'')).
    eapply tso_consistent_safe_buffer_app; try edone.
      eby eapply tso_cons_store.
      rewrite <- app_nil_end. apply BPD. 
      done.
    intros r' p' c' IN RI SCR.
    rewrite (load_store_other S'). done.
    by apply machine_scratch_disjoint.
Qed.

Lemma machine_val_rmw_instr_semantics:
  forall r v' args astmt p 
    (SM: Cminorops.sem_atomic_statement astmt args = Some (p, r))
    (MVA: machine_val_list args)
    (MV : machine_val v'),
      machine_val (rmw_instr_semantics r v').
Proof.
  intros.
  destruct astmt; simpl in SM.
  - destruct args as [|[] args]; try done.
    destruct args as [|? args]; try done.
    destruct args as [|? args]; try done.
    destruct args as [|? args]; try done.
    destruct Val.eq_dec; try done.
    destruct Val.has_type; try done.
    destruct Val.eq_dec; try done.
    destruct Val.has_type; try done.
    inv SM. simpl; repeat destruct Val.eq_dec; try done; simpl.
    by apply MVA; right; left.
  - destruct args as [|[] args]; try done.
    destruct args as [|? args]; try done.
    inv SM. 
    destruct v'; try done.
    by destruct p0. 
Qed.

Lemma machine_ptr_rmw_instr_semantics:
  forall r args astmt p 
    (SM: Cminorops.sem_atomic_statement astmt args = Some (p, r))
    (MV : machine_val_list args),
      machine_ptr p.
Proof.
  intros.
  destruct astmt; simpl in SM.
  - destruct args as [|[] args]; try done.
    destruct args as [|? args]; try done.
    destruct args as [|? args]; try done.
    destruct args as [|? args]; try done.
    destruct Val.eq_dec; try done.
    destruct Val.has_type; try done.
    destruct Val.eq_dec; try done.
    destruct Val.has_type; try done.
    inv SM. by specialize (MV _ (in_eq _ _)).
  - destruct args as [|[] args]; try done.
    destruct args as [|? args]; try done.
    inv SM. by specialize (MV _ (in_eq _ _)).
Qed.

Lemma rmw_sim:
  forall s s' p v (st : PTree.t Cstacked.state) st' t tso tso' c csms r
    (ST : SEM_step cst_sem cst_globenv s (TEmem (MErmw p c v r)) s')
    (TSOST : tso_step tso (MMmem t (MErmw p c v r)) tso')
    (CS : st ! t = Some s)
    (NS : st' = st ! t <- s')
    (TSOPCREL : tso_pc_related (tso, st) csms),
     can_reach_error csm_globenv csms \/
     (exists shms' : St cshm_lts,
        taustep cshm_lts csms Etau shms' /\ tso_pc_related (tso', st') shms').
Proof.
  intros. destruct csms as [cstso csst].
  generalize TSOPCREL; intros [TC [bp [tp [sp TREL]]]].
  pose proof (tso_pc_related_to_buff_states _ _ _ _ _ _ _ t TREL) as BOR.
  destruct TREL as (_ & _ & (MCRt & _ & LR & MM) & _ & BE & _ & _ & _ & _ & BR).
  destruct (BR t) as (_ & BRt & _).
  simpl in *; rewrite CS in BOR.
  destruct (csst ! t) as [ss'|] _eqn : Ess'; simpl in BOR; try done.
  destruct BOR as [sm' [sp' [tp' (AB' & PUBt & PUBs & SR & SCO)]]].
  inv TSOST.

  pose proof (step_consistent_with_env ST SCO) as SCO'.

  assert (MP : machine_ptr p).
    pose proof (load_chunk_allocated_spec c (tso_mem tso) p) as LS.
    rewrite LD in LS. destruct LS as [[[[b' o'] n'] [k [RI RA]]] _].
    apply range_allocated_consistent_with_restr in RA.
    destruct p as [b o]. destruct RI as [-> _]. simpl. by rewrite <- MCRt.

  simpl in BRt. rewrite Bemp in BRt. inv BRt. specialize (BE t).
  replace (bp t) with (@nil (list buffer_item)) in BE. simpl in BE.

  specialize (LR p MP c). rewrite LD in LR.  

  destruct (load_ptr c (tso_mem cstso) p) as [v'|] _eqn : LD'; subst.
    pose proof (load_chunk_allocated_someD LD') as LDS'.
    destruct (store_ptr Mint32 (tso_mem cstso) p (rmw_instr_semantics r v')) as [sm''|] _eqn : S;
      [| by pose proof (store_chunk_allocated_noneD S); inv ST].
    (* Load succeeded *)
    inv ST; inv SR; inv EKR; right.
      (* Atomic without a store of the obtained value. *)
      eexists (_, _); split. 
      apply step_taustep. simpl.
      by eapply Comp.step_ord; try edone; vauto.
      eapply memory_neutral_sim; try edone.
      eapply store_both_related; [done | edone | | edone | edone].
      simpl in SCO.
      eapply machine_val_rmw_instr_semantics; try edone.
        intros x INx. by apply in_app_or in INx; destruct INx as [|[<-|]]; auto. 
      by specialize (MM p Mint32); rewrite LD' in MM.
      intros tpt spt smt SR. 
      eby inv SR; inv EKR; econstructor.
    (* Explicit load *)
    eexists (_, _).
    split. 
    apply step_taustep. simpl.
    by eapply Comp.step_ord; try edone; vauto.
    eapply memory_neutral_sim; try edone.
    eapply store_both_related; [done | edone | | edone | edone].
    eapply machine_val_rmw_instr_semantics; try edone.
      intros x INx. by apply in_app_or in INx; destruct INx as [|[<-|]]; auto. 
    by specialize (MM p Mint32); rewrite LD' in MM.
    intros tpt spt smt SR. 
    inv SR. inv EKR. econstructor; try edone. eby econstructor.
    by specialize (MM p Mint32); rewrite LD' in MM.
  (* Load fail - unfortunately we have to do almost the same gymnastics 
     as above (and fail). *)
  left. 
  eexists (_, _). split. eapply taustar_refl.
  inv ST; inv SR; inv EKR.
    eexists (_, _). exists (Evisible Efail).
    split. done. simpl.
    by eapply Comp.step_rmw_fail; try edone; vauto.
  eexists (_, _). exists (Evisible Efail).
  split. done. simpl.
  eapply Comp.step_rmw_fail; try edone; vauto.
Qed.

Lemma ext_sim:
  forall s ev s' (st : PTree.t Cstacked.state) t tso sst
    (ST : cst_step cst_globenv s (TEext ev) s')
    (CS : st ! t = Some s)
    (TSOPCREL : tso_pc_related (tso, st) sst),
      can_reach_error csm_globenv sst \/
      (exists shms' : St cshm_lts,
        taustep cshm_lts sst (Evisible ev) shms' /\
        tso_pc_related (tso, st ! t <- s') shms').
Proof.
  intros. destruct sst as [cstso csst].
  generalize TSOPCREL; intros [TC [bp [tp [sp TREL]]]].
  pose proof (tso_pc_related_to_buff_states _ _ _ _ _ _ _ t TREL) as BOR.
  destruct TREL as (_ & _ & _ & _ & LE & _). simpl in LE.
  simpl in *; rewrite CS in BOR.
  destruct (csst ! t) as [ss'|] _eqn : Ess'; simpl in BOR; try done.
  destruct BOR as [sm' [sp' [tp' (AB & PUBt & PUBs & SR & SCO)]]].
  pose proof (step_consistent_with_env ST SCO) as SCO'.
  right. inv ST.
    (* Call *)
    inv SR. inv KR.
      eexists (_, _).
      split. 
        by apply step_taustep; simpl; eapply Comp.step_ext; try edone; vauto.
      eapply memory_neutral_sim; try edone.
      intros tpt spt smt SR.
      inv SR. eby inv KR; [eapply st_rel_external_stop |
                           inv KR0].
    eexists (_, _).
    split. 
      by apply step_taustep; simpl; eapply Comp.step_ext; try edone; vauto.
    eapply memory_neutral_sim; try edone.
    intros tpt spt smt SR.
    inv SR; inv KR; [inv KR0 | eby eapply st_rel_external].
  (* Return *)
  inv SR.   
    eexists (_, _).
    split. 
      by apply step_taustep; simpl; eapply Comp.step_ext; try edone; vauto.
    eapply memory_neutral_sim; try edone.
    intros tpt spt smt SR.
    by inv SR; [econstructor; try edone; destruct evres |  inv KR].
  eexists (_, _); split.
    by apply step_taustep; simpl; eapply Comp.step_ext; try edone; vauto.
  eapply memory_neutral_sim; try edone.
  intros tpt spt smt SR.
  by inv SR; [inv KR | econstructor; try edone; destruct evres].
Qed.

Lemma tso_pc_rel_state_none:
  forall {ttso tthr stso sthr} t,
    tso_pc_related (ttso, tthr) (stso, sthr) ->
    (tthr ! t = None <-> sthr ! t = None).
Proof.
  intros ttso tthr stso sthr t [TC [bp [tp [sp TREL]]]].
  pose proof TREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TR).
  pose proof (TR t) as (_ & _ & BSR). simpl in BSR.
  simpl in *.
  split; intro S; rewrite S in BSR.
    by destruct (sthr!t).
  by destruct (tthr!t).
Qed.

Lemma empty_env_related:
  forall m,
    env_related nil nil m (mkcsenv None (PTree.empty env_item)) empty_env.
Proof.
  exists Int.zero; repeat split; try done.
  (* - by unfold env_ranges; rewrite elems_of_empty_nil; constructor. *)
  by intro; unfold empty_env; rewrite !PTree.gempty.
Qed.

Lemma thread_start_sim:
  forall s p v s' tso t newtid tso' (st : PTree.t Cstacked.state) sinit sms
  (ST : cst_step cst_globenv s (TEstart p v) s')
  (TS : tso_step tso (MMstart t newtid) tso')
  (CS : st ! t = Some s)
  (TF : st ! newtid = None)
  (INIT : cst_init cst_globenv p v = Some sinit)
  (TSOPCREL : tso_pc_related (tso, st) sms),
   can_reach_error csm_globenv sms \/
   (exists shms' : St cshm_lts,
      taustep cshm_lts sms Etau shms' /\ 
      tso_pc_related (tso', (st ! t <- s') ! newtid <- sinit) shms').
Proof.
  intros. destruct sms as [cstso csst].

  assert(TSOC: 
    Comp.consistent tso_mm cst_sem (tso', (st ! t <- s') ! newtid <- sinit)).
    eapply Comp.step_preserves_consistency, (proj1 TSOPCREL). 
    eby eapply Comp.step_start.
    
  generalize TSOPCREL; intros [TC [bp [tp [sp TREL]]]].
  pose proof (tso_pc_related_to_buff_states _ _ _ _ _ _ _ t TREL) as BOR.
  destruct TREL as (MTB & NSMR & (MCRt & MCRs & LR) & SC &
    BPD & BNE & SAF & MRPt & MRPs & TREL).
  simpl in *; rewrite CS in BOR.
  pose proof (TREL newtid) as (_ & _ & BORnt).
  destruct (csst ! t) as [ss'|] _eqn : Ess'; simpl in BOR; try done.
  destruct BOR as [sm' [sp' [tp' (AB' & PUBt & PUBs & SR & SCO)]]].
  pose proof (step_consistent_with_env ST SCO) as SCO'.
  inv TS. simpl in BORnt.
  rewrite TF in BORnt. 
  destruct (csst ! newtid) as [csn|] _eqn : Ecsn; try done.
  simpl in BORnt. destruct BORnt as (Etpn & Espn & Etbn & Ebpn).
  pose proof Ebpn as Esbn. rewrite <- BPD in Esbn. simpl in Esbn.
  inv ST. inv SR. inv EKR.

  unfold cst_init in INIT. 
  destruct (Genv.find_funct_ptr (Cstacked.ge cst_globenv) p) 
    as [ifn|] _eqn : Eifn; try done.
  destruct ifn; [|done].
  destruct (beq_nat (length (v0 :: nil)) (length (sig_args (fn_sig f)))) 
    as [] _eqn:BE; [|done].
  inv INIT.
  rewrite <- (find_funct_ptr_eq cst_globenv csm_globenv) in Eifn.
  unfold Cstacked.ge, Cstacked.genv, Cstacked.gvarenv in Eifn.
  assert (STEP: Comp.step tso_mm cs_sem csm_globenv (cstso, csst) Etau
     ({|
      tso_buffers := tupdate newtid nil (tso_buffers cstso);
      tso_mem := tso_mem cstso |},      
      (csst ! t <- (SKstmt Sskip csm_e csm_k)) 
           ! newtid <- (SKcall (Val.conv_list (v0 :: nil) (sig_args (fn_sig f)))
                                (Kcall None (Internal f) empty_env Kstop)))).
    eapply Comp.step_start; try econstructor; try edone. 
    apply (tso_pc_rel_state_none _ TSOPCREL) in TF.
    simpl; unfold cs_init, ge, gvarenv, genv in *.
    by rewrite Eifn, BE.
  right; eexists (_, _); split.
    eby apply step_taustep.
  split. done. (* Target tso-consistency *)
  exists bp. exists tp. exists sp.
  split; simpl. (* Buffers contain only machine values *)
    intros t'. destruct (peq t' newtid) as [-> | N].
      by rewrite tupdate_s.
    rewrite tupdate_o; try done.
  split. done. (* Non-stack memory related *)
  split. done. (* Memory contents related *)
  split. (* Source tso-consistency *)
    eby eapply Comp.step_preserves_consistency.
  split. (* flattened buffer partition correspondes to the buffer *)
    intros t'. destruct (peq t' newtid) as [-> | N].
      by rewrite tupdate_s.
    rewrite tupdate_o. apply BPD. done.
  split. done. (* buffer partitions not empty *)
  split. (* Scratch allocs fresh *)
    split. 
      intros t'.
      destruct (peq t' newtid) as [-> | N].
        rewrite tupdate_s. done.
      rewrite tupdate_o. by apply (proj1 SAF).
      done.
    split.
      intros t1 t2 N.
      destruct (peq t1 newtid) as [-> | N1];
        destruct (peq t2 newtid) as [-> | N2];
          try rewrite !tupdate_s;
            try done; try by apply range_lists_disjoint_comm. 
      rewrite !tupdate_o; try done.
      by apply (proj1 (proj2 SAF)).
    intros t1 t2.
    destruct (peq t2 newtid) as [-> | N2]. by rewrite tupdate_s.
    rewrite tupdate_o. apply (proj2 (proj2 SAF)). done.
  split. done. (* Memory related with partitioning *)
  split. done. (* Memory related with partitioning *)
  intro t'. 
  destruct (TREL t') as (PI & BR & BOR'). 
  split. done. (* partition injectivity *)
  split. (* buffers related *)
    destruct (peq t' newtid) as [-> | N]. 
      rewrite tupdate_s. rewrite <- Etbn. done.
    by rewrite tupdate_o.
  (* Buffered states related *)
  destruct (peq t' newtid) as [-> | Nn].
    (* The states of the newly spawned thread are related *)
    rewrite tupdate_s, !PTree.gss. simpl.
    rewrite (find_funct_ptr_eq cst_globenv) in Eifn.
    eexists. eexists. eexists.
    rewrite Ebpn, Etpn, Espn. unfold part_update_buffer.
    split. edone. split. edone. split. edone.
    split. 
      econstructor. replace (@nil arange) with (@nil arange ++ nil).
      econstructor; try done; try apply empty_env_related.
      by exists (Vptr p).
      done.
      destruct (sig_args (fn_sig f)) as [|s0 [|s1 fs]]; try done; [].
      by destruct s0; destruct v0; simpl; intros v' [<-|].
    simpl. split. done. by intro; rewrite PTree.gempty.
    apply globenv_same.
  rewrite tupdate_o; try done.
  destruct (peq t' t) as [-> | Nt].
    repeat (rewrite PTree.gso; repeat rewrite PTree.gss); try done.
    (* The states of the spawning thread are related *)
    simpl. 
    eexists; eexists; eexists. rewrite <- BPD. 
    repeat split; try edone; vauto. apply stmt_consistent_skip.
  by rewrite !PTree.gso. 
  apply globenv_same.
Qed.

Lemma thread_start_fail_sim:
  forall s p v s' tso t (st : PTree.t Cstacked.state) sms
  (ST : cst_step cst_globenv s (TEstart p v) s')
  (CS : st ! t = Some s)
  (INIT : cst_init cst_globenv p v = None)
  (TSOPCREL : tso_pc_related (tso, st) sms),
   can_reach_error csm_globenv sms \/
   (exists shms' : St cshm_lts,
      taustep cshm_lts sms (Evisible Efail) shms' /\ 
      tso_pc_related (tso, st ! t <- s') shms').
Proof.
  intros. destruct sms as [cstso csst].
  generalize TSOPCREL; intros [TC [bp [tp [sp TREL]]]].
  pose proof (tso_pc_related_to_buff_states _ _ _ _ _ _ _ t TREL) as BOR.
  simpl in *; rewrite CS in BOR.
  destruct (csst ! t) as [ss'|] _eqn : Ess'; simpl in BOR; try done.
  destruct BOR as [sm' [sp' [tp' (AB & PUBt & PUBs & SR & SCO)]]].
  inv ST. inv SR. inv EKR.
  right.
  eexists (_, _).
  split.
    apply step_taustep. simpl.
    eapply Comp.step_start_fail.
    econstructor; try edone. apply Ess'. 
  unfold cst_init in INIT.
  by destruct (Genv.find_funct_ptr (Cstacked.ge cst_globenv) p) 
    as [[]|] _eqn : Eifn; try done; 
      rewrite <- (find_funct_ptr_eq cst_globenv csm_globenv) in Eifn by apply globenv_same;
      unfold Cstacked.ge, Cstacked.genv, Cstacked.gvarenv in Eifn;
      simpl; unfold cs_init, ge, gvarenv, genv in *; rewrite Eifn; try done;
    destruct beq_nat.
  eapply memory_neutral_sim; try edone.
  intros tpt spt smt SR. 
  inv SR. inv EKR. eby econstructor. 
  by split; [apply stmt_consistent_skip|].
Qed.

Lemma tso_pc_rel_buf_nil_rel:
  forall ttso tthr stso sthr t
    (TREL : tso_pc_related (ttso, tthr) (stso, sthr))
    (TBNIL : ttso.(tso_buffers) t = nil),
    stso.(tso_buffers) t = nil.
Proof.
  intros.
  destruct TREL as [TC [bp [tp [sp TREL]]]].
  destruct TREL as (_ & _ & _ & _ & BP & _ & _ & _ & _ & BREL).
  destruct (BREL t) as (_ & BR & _).
  simpl in BR. rewrite TBNIL in BR.
  rewrite BP. by inv BR.
Qed.

Lemma thread_exit_sim:
  forall s s' (st : PTree.t Cstacked.state) t sms tso tso'
  (ST : cst_step cst_globenv s TEexit s')
  (TS : tso_step tso (MMexit t) tso')
  (CS : st ! t = Some s)
  (TSOPCREL : tso_pc_related (tso, st) sms),
   can_reach_error csm_globenv sms \/
   (exists shms' : St cshm_lts,
      taustep cshm_lts sms Etau shms' /\ 
      tso_pc_related (tso', PTree.remove t st) shms').
Proof.
  intros. destruct sms as [cstso csst].
  generalize TSOPCREL; intros [TC [bp [tp [sp TREL]]]].
  pose proof (tso_pc_related_to_buff_states _ _ _ _ _ _ _ t TREL) as BOR.
  destruct TREL as (MTB & NSMR & (MCRt & MCRs & LR) & (BCs & USs) &
    BPD & BNE & SAF & MRPt & MRPs & TREL).
  simpl in *; rewrite CS in BOR.
  destruct (csst ! t) as [ss'|] _eqn : Ess'; simpl in BOR; try done.
  destruct BOR as [sm' [sp' [tp' (AB & PUBt & PUBs & SR & SCO)]]].
  inv TS. inv ST. inv SR. inv EKR.
  right.
  eexists (_, _).
  split.
    apply step_taustep. simpl.
    eapply Comp.step_exit.
    econstructor. econstructor; try edone.
    eby eapply tso_pc_rel_buf_nil_rel. apply Ess'.
  split. (* tso consistency of the target state*)
    split. (* buffer consistency *)
      intros t' X; simpl in *.     
      destruct (peq t' t) as [-> | N]. done.
      rewrite PTree.gmap, PTree.gro in X; try done.
      by apply (proj1 TC); rewrite PTree.gmap.
    by destruct TC. (* unbuffer safety *)
  exists bp. exists tp. exists sp.
  assert (SBnil := tso_pc_rel_buf_nil_rel _ _ _ _ _ TSOPCREL Bemp).
  split; simpl. done. (* machine buffers *)
  split. done. (* non-stack memory related *)
  split. done. (* memory contents related *)
  split. (* tso consistency of the source state *) 
    split. (* buffer consistency *)
      intros t' X; simpl in *.     
      destruct (peq t' t) as [-> | N]. done.
      rewrite PTree.gmap, PTree.gro in X; try done.
      by apply BCs; rewrite PTree.gmap.
    (* unbuffer safety *)
    by destruct cstso.
  repeat (split; [done|]).
  intro t'.  
  destruct (TREL t') as (PI & BR & BSR).
  split. done. (* Injective partitions *)
  split. done. (* Buffers related *)
  destruct (peq t' t) as [-> | N].
    rewrite !PTree.grs in *. simpl.
    rewrite Bemp, SBnil in *.
    unfold part_update_buffer in *. simpl in PUBs, PUBt.  
    injection PUBs; injection PUBt; intros -> ->.
    repeat (split; [done|]).
    rewrite <- BPD. done.
  by rewrite !PTree.gro.
Qed.

Lemma is_call_cont_related_rev:
  forall {tp sp sm tk sk}
    (KR: cont_related tp sp sm tk sk)
    (CC: is_call_cont sk),
      Cstacked.is_call_cont tk.
Proof. intros; destruct tk; try done; by inv KR. Qed.

Lemma read_fail_sim:
  forall s p c v s' tso tso' (st : PTree.t Cstacked.state) sms t
  (ST : cst_step cst_globenv s (TEmem (MEread p c v)) s')
  (TS : tso_step tso (MMreadfail t p c) tso')
  (CS : st ! t = Some s)
  (TSOPCREL : tso_pc_related (tso, st) sms),
   can_reach_error csm_globenv sms \/
   (exists shms' : St cshm_lts,
      taustep cshm_lts sms (Evisible Efail) shms' /\
      tso_pc_related (tso', st ! t <- s') shms').
Proof.
  intros. destruct sms as [cstso csst].
  generalize TSOPCREL; intros [TC [bp [tp [sp TREL]]]].
  pose proof (tso_pc_related_to_buff_states _ _ _ _ _ _ _ t TREL) as BOR.
  destruct TREL as (_ & _ & (MCRt & _ & _) & _ & _ & _ & _ & 
    (_ & _ & PRTt) & _); simpl in *.
  rewrite CS in BOR.
  destruct (csst ! t) as [ss'|] _eqn : Ess'; simpl in BOR; try done.
  destruct BOR as [sm' [sp' [tp' (AB' & PUBt & PUBs & SR & SCO)]]].
  inversion TS as [| | tsox tx px cx BN LN| | | | | | | | |];
    subst; clear TS.
  rewrite BN in PUBt. inv PUBt.
  assert(TPMP: forall p n, In (p, n) (tp t) -> machine_ptr p).
    intros p' n' IN. 
    assert (RA: range_allocated (p', n') MObjStack tso'.(tso_mem)).
      apply -> PRTt. eby eexists.
    apply range_allocated_consistent_with_restr in RA. 
    simpl in MCRt; rewrite MCRt in RA. by destruct p'.
  assert (SBnil : tso_buffers cstso t = nil). eby eapply tso_pc_rel_buf_nil_rel.
  assert (ABt : apply_buffer (tso_buffers tso' t) 
                             (tso_mem tso') = Some (tso_mem tso')).
    by rewrite BN.
  assert (ABs : apply_buffer (tso_buffers cstso t) 
                             (tso_mem cstso) = Some (tso_mem cstso)).
    by rewrite SBnil.
  left. eexists (_, _). split. apply taustar_refl.
  inv ST. inv SR.
    eexists (_, _). exists (Evisible Efail). split. done. simpl.
    eapply Comp.step_read_fail; try edone. 
      econstructor; eby try eapply eval_var_ref_rel.
    econstructor; try edone. 
    assert (MP : machine_ptr p).
      eapply eval_var_ref_machine; try edone.
      intros p' n' IN'.
      eapply TPMP. replace (tp t) with (cst_obs' ++ cst_obs).
      apply in_or_app. eby left.
    pose proof (tso_pc_rel_load_eq _ _ _ _ _ _ _ _ _ 
      c MP TSOPCREL ABt ABs) as LD.
    by rewrite LN in LD.
  inv SR. inv EKR.
  eexists (_, _). exists (Evisible Efail). split. done. simpl.
  eapply Comp.step_read_fail; try edone. 
    econstructor; eby try eapply eval_var_ref_rel.
  econstructor; try edone.
  simpl in MV.
  pose proof (tso_pc_rel_load_eq _ _ _ _ _ _ _ _ _
    c MV TSOPCREL ABt ABs) as LD.
  by rewrite LN in LD. 
Qed.

Definition var_info_local vi :=
    match vi with
      | Var_local _ => True
      | Var_stack_scalar _ _ => True
      | Var_stack_array _ => True
      | Var_global_scalar _ => False
      | Var_global_array => False 
    end.

Lemma assign_vars_other:
  forall {id i vs m cenv fsize}
    (Eav : assign_variables i vs m = (cenv, fsize))
    (NIN : ~ In id (map (@fst _ _) vs)),
      cenv !! id = (fst m) !! id.
Proof.
  intros id i vs.
  induction vs as [|[vid vk] vs IH]; intros; simpl in Eav.

  by subst.
  
  rewrite (IH _ _ _ Eav). destruct m as [m ?]. simpl.
  destruct vk.
  - destruct Identset.mem; simpl; (rewrite PMap.gso; [done|]);
      intro E; elim NIN; by left.
  - simpl; rewrite PMap.gso; [done|]; intro E; elim NIN; by left.
  intro IN. elim NIN. by right.
Qed.

Lemma assign_vars_local:
  forall id i vs m cenv fsize
    (Eav : assign_variables i vs m = (cenv, fsize))
    (IN : In id (map (@fst _ _) vs)),
    var_info_local cenv !! id.
Proof.
  intros id i vs.
  induction vs as [|v vs IH]; intros. done.
  
  simpl in *.
  destruct (In_dec peq id (map (@fst _ _) vs)) as [INid | NIN].
    by specialize (IH _ _ _ Eav INid).
  rewrite (assign_vars_other Eav); [|done].
  destruct v as [vid vk]. destruct m as [m sz].
  destruct IN as [<- | IN]; [|done].
  by destruct vk; simpl; [destruct Identset.mem|]; simpl; rewrite PMap.gss.
Qed.

Lemma build_envmap_succ:
  forall cenv vs env
    (VL: forall id, In id (map (@fst _ _) vs) ->
                    var_info_local cenv !! id),
    build_envmap vs cenv env <> None.
Proof.
  intros cenv vs.
  induction vs as [|[id vk] vs IH]; intros. done.
  simpl.
  assert (VLid := VL id (in_eq _ _)).
  destruct (cenv !! id); try done;
    eapply IH; intros id' IN'; apply VL, in_cons, IN'.
Qed.

Lemma build_env_succ:
  forall f, build_env f <> None.
Proof.
  intros.
  unfold build_env, build_compilenv.
  unfold compilenv, PMap.t.
  destruct (assign_variables (addr_taken_stmt (fn_body f)) 
            (fn_variables f) (PMap.init Var_global_array, 0%Z)) 
    as [cenv fsz] _eqn : Eav.
  destruct (build_envmap (fn_variables f) cenv (PTree.empty env_item))
    as [] _eqn : Ebem.
    done.
  intro.
  eapply build_envmap_succ; [|edone].
  intros id IN. eby eapply assign_vars_local.
Qed.

Lemma thread_stuck_sim:
  forall s (st : PTree.t Cstacked.state) tso csst cstso t
    (STUCK : forall (s' : Cstacked.state) (l' : thread_event),
             ~ cst_step cst_globenv s l' s')
    (CS : st ! t = Some s)
    (TSOPCREL : tso_pc_related (tso, st) (cstso, csst)),
      can_reach_error csm_globenv (cstso, csst).
Proof.
  intros.
  generalize TSOPCREL; intros [TC [bp [tp [sp TREL]]]].
  pose proof (tso_pc_related_to_buff_states _ _ _ _ _ _ _ t TREL) as BOR.
  destruct TREL as (_ & _ & (MCRt & _ & _) & _ & _ & _ & _ & 
    (_ & _ & PRTt) & _); simpl in *.
  rewrite CS in BOR.
  destruct (csst ! t) as [ss'|] _eqn : Ess'; simpl in BOR; try done.
  destruct BOR as [sm' [sp' [tp' (AB' & PUBt & PUBs & SR & SCO)]]].
  

  eexists. split. constructor.
  eexists; exists (Evisible Efail). split. done.
  simpl. 
  apply Comp.step_thread_stuck with (tid := t)(s := ss'); try done.
  intros s' l' SST.

  (*
  assert (NEX: ~ exists l', exists s', cst_step cst_globenv s l' s').
     eby intros (? & ? & ?); eelim STUCK.
  elim NEX; clear STUCK NEX. *)
  
  revert SR SCO. 
  (cs_step_cases (case SST) Case); 
   first [ Case "StepThreadEvt" |
   try (eby intros; inv SR; eapply STUCK; constructor);
   try (eby intros; inv SR; inv EKR; eapply STUCK; constructor edone);
   try (eby intros; inv SR; inv KR; eapply STUCK; constructor)
  ].

  Case "StepVar".
    intros id p c v env k EVR HT SR SCO.
    inv SR.
    destruct ER as [n (_ & _ & _ & EIR)].
    specialize (EIR id).
    inv EVR; destruct (env!id) as [[p' []]|]; clarify.
      destruct ((csenv_env cst_e) ! id) as [] _eqn : En; [|done].
      inv EIR; eapply STUCK.
        apply StepVarLocal. eby econstructor. 
      apply StepVarStack.
      eapply Cstacked.eval_var_ref_local. edone. eby apply sym_eq.
      edone.
    destruct ((csenv_env cst_e) ! id) as [] _eqn : En. done.
    eapply STUCK; apply StepVarStack.
    eapply Cstacked.eval_var_ref_global. done. 
    rewrite <- (proj1 (proj1 globenv_same)). edone.
    rewrite (proj2 globenv_same). edone.
    edone.

  Case "StepAddrOf".
    intros id p env k EVA SR SCO.
    inv SR. destruct SCO as [EC _]. destruct cst_e as [csp cste].
    destruct ER as [n (_ & _ & _ & EIR)].
    specialize (EIR id). specialize (EC id).
    inv EVA; destruct (env!id) as [[p' []]|] _eqn:Eei; clarify; simpl in *.
    - destruct (cste!id) as [] _eqn : En; [|done].
      inv EIR.
        assert (NI: ~ Identset.In id (Identset.add id Identset.empty)).
          intro C. apply Identset.mem_1 in C. rewrite C in EC; clarify.
        by apply NI, Identset.add_1.
      eapply STUCK. econstructor. eby econstructor.
    - destruct (cste!id) as [] _eqn : En; [|done]. inv EIR.
      eapply STUCK. econstructor. eby apply Cstacked.eval_var_addr_array.
    - destruct (cste!id) as [] _eqn : En; [done|]. inv EIR.
      eapply STUCK. econstructor. apply Cstacked.eval_var_addr_global.
      done. eby rewrite <- (proj1 (proj1 globenv_same)). 

  Case "StepAssign".
    intros v id p chunk env k EVR SR SCO. 
    inv SR. inv EKR.
    destruct ER as [n (_ & _ & _ & EIR)].
    specialize (EIR id).
    inv EVR; destruct (env!id) as [[p' []]|]; clarify.
      destruct ((csenv_env cst_e) ! id) as [] _eqn : En; [|done].
      inv EIR; eapply STUCK.
        apply StepAssignLocal; eby econstructor.
      apply StepAssignEnv.
      eapply Cstacked.eval_var_ref_local. edone. eby apply sym_eq.
    destruct ((csenv_env cst_e) ! id) as [] _eqn : En. done.
    eapply STUCK; apply StepAssignEnv.
    eapply Cstacked.eval_var_ref_global. done. 
    rewrite <- (proj1 (proj1 globenv_same)). edone.
    rewrite (proj2 globenv_same). edone.

  Case "StepEmptyCall".
    intros. inv SR. inv EKR.
    destruct vf; try done; [].
    eapply STUCK. econstructor; try edone.
    eby simpl; erewrite <- find_funct_ptr_eq.

  Case "StepCallArgs".
    intros. inv SR. inv EKR.
    destruct vf; try done; [].
    eapply STUCK. econstructor; try edone.
    eby simpl; erewrite <- find_funct_ptr_eq.

  Case "StepGoto".
    intros. inv SR.
    assert (Cstacked.get_fundef (Cstacked.call_cont cst_k) = Some (Internal f)).      
      pose proof (call_cont_related _ EKR) as CC. rewrite H in CC; by inv CC.
    pose proof (find_label_related _ lbl (fn_body f) 
                                   (call_cont_related _ EKR)) as FLM.
    destruct (Cstacked.find_label lbl (fn_body f) (Cstacked.call_cont cst_k)) 
      as [[ns nlbl]|] _eqn : Efl; [|by rewrite FLM in *].
    destruct FLM as [nlbl' [Efl' CR]].
    rewrite Efl' in *. clarify.
    eapply STUCK. econstructor. reflexivity. edone. edone.

  Case "StepReturnNone".
    intros f k e e' k' Ecc SIG SR SCO.
    inv SR.
    assert(CCR := (call_cont_related _ EKR)).
    rewrite Ecc in CCR. inv CCR; 
      by eapply STUCK; econstructor; apply sym_eq; edone; done.

  Case "StepReturnNoneFinish".
    intros e e' k' k fd opt_v Ecc SR SCO.
    inv SR. inv EKR.
      destruct op; eapply STUCK; econstructor.
    assert(CCR := call_cont_related _ KR); rewrite Ecc in CCR.
    inv CCR; eapply STUCK; econstructor; eby apply sym_eq.

  Case "StepReturnSome".
    intros until 0. intros GFD SIG SR SCO. 
    inv SR. 
    assert(CCR := call_cont_related _ EKR).
    destruct (call_cont k) as [] _eqn : CK; inv GFD.
    by inv CCR; eapply STUCK; econstructor; try (eby rewrite <- H3).

  Case "StepReturnSomeFinish".
    intros v c fd p id k k' e env Ecc EVR SR SCO.
    inv SR. inv EKR.
      destruct op; eapply STUCK; econstructor.
    assert(CCR := call_cont_related _ KR); rewrite Ecc in CCR; inv CCR.
    destruct ER as [n (_ & _ & _ & EIR)].
    specialize (EIR id).
    inv EVR; destruct (env!id) as [[p' []]|]; clarify.
      destruct ((csenv_env cst_e) ! id) as [] _eqn : En; [|done].
      inv EIR; eapply STUCK.
        eapply StepReturnFinishLocal. eby apply sym_eq. eby econstructor.
      eapply StepReturnFinishStack. eby apply sym_eq.
      eapply Cstacked.eval_var_ref_local. edone. eby apply sym_eq.
    destruct ((csenv_env cst_e) ! id) as [] _eqn : En. done.
    eapply STUCK; eapply StepReturnFinishStack.
    eby apply sym_eq.
    eapply Cstacked.eval_var_ref_global. done. 
    rewrite <- (proj1 (proj1 globenv_same)). edone.
    rewrite (proj2 globenv_same). edone.

  Case "StepFunctionInternal".
    intros. inv SR. 
    assert (NoDup (List.map (@fst ident var_kind) (fn_variables f))).
      unfold fn_variables, fst. by rewrite map_app, map_map.
    inv KR;
      (destruct (build_env f) as [[? fs]|] _eqn:Ebe; 
        [|eby eapply build_env_succ];
        destruct (zeq fs 0) as [-> | N];
          [eby eapply STUCK; eapply StepFunctionInternalNoStack |
           eby eapply STUCK; eapply StepFunctionInternalWithStack 
            with (sp := Ptr 0 Int.zero)]).

  Case "StepBindArgs".
    intros f id args p env v c vs k Eid SR SCO.
    inv SR.
    destruct ER as [n (_ & _ & _ & EIR)].
    specialize (EIR id). rewrite Eid in EIR.
    destruct ((csenv_env cst_e) ! id) as [] _eqn : En; [|done].
    inv EIR; eapply STUCK.
      eby apply StepBindArgsEnv; econstructor.
    eby apply StepBindArgsStack; try edone; apply sym_eq.

  Case "StepExternalStoreSome".
    intros vres env c p k id EVR SR SCO.
    inv SR.
    destruct ER as [n (_ & _ & _ & EIR)].
    specialize (EIR id).
    inv EVR; destruct (env!id) as [[p' []]|]; clarify.
      destruct ((csenv_env cst_e) ! id) as [] _eqn : En; [|done].
      inv EIR; eapply STUCK.
        eapply StepExternalStoreEnv. eby econstructor.
      eapply StepExternalStoreStack.
      eapply Cstacked.eval_var_ref_local. edone. eby apply sym_eq.
    destruct ((csenv_env cst_e) ! id) as [] _eqn : En. done.
    eapply STUCK; eapply StepExternalStoreStack.
    eapply Cstacked.eval_var_ref_global. done. 
    rewrite <- (proj1 (proj1 globenv_same)). edone.
    rewrite (proj2 globenv_same). edone.

  Case "StepFree".  
    intros. inv SR. inv EKR.
    destruct op; eapply STUCK; econstructor.


  Case "StepStop".
    intros.
    inv SR. inv EKR.
    eapply STUCK. constructor.

  Case "StepThreadEvt".
    intros; inv SR; inv EKR. eapply STUCK.
    apply Cstacked.StepThreadEvt.

Qed.

Definition tso_order := clos_trans _
  (fun (t1 t2 : Comp.state tso_mm cst_sem) =>
    PTree.order (ltof _ measure) (snd t1) (snd t2) /\ fst t1 = fst t2).

Lemma tso_order_wf:
  well_founded tso_order.
Proof.
  eapply Wellfounded.Transitive_Closure.wf_clos_trans.
  intros [tso threads].
  pose proof (PTree.order_wf (well_founded_ltof _ measure)) as PTWF.
  induction threads as [threads IH] using (well_founded_ind PTWF).
  apply Acc_intro.
  intros [tso' x']; simpl; intros [H1 ->].
  by apply IH. 
Qed.

Lemma tso_order_update:
  forall (st : PTree.t Cstacked.state) t s s' tso
    (CS : st ! t = Some s)
    (LESS : (measure s' < measure s) % nat),
      tso_order (tso, st ! t <- s') (tso, st).  
Proof.
  intros. unfold tso_order; apply t_step; simpl.
  split; [|done].
  eby eapply PTree.order_set_lt.
Qed.

Lemma rmw_fail_sim:
  forall s p c v s' tso tso' (st : PTree.t Cstacked.state) sms t instr
  (ST : cst_step cst_globenv s (TEmem (MErmw p c v instr)) s')
  (TS : tso_step tso (MMreadfail t p c) tso')
  (CS : st ! t = Some s)
  (TSOPCREL : tso_pc_related (tso, st) sms),
   can_reach_error csm_globenv sms.
Proof.
  intros. destruct sms as [cstso csst].
  generalize TSOPCREL; intros [TC [bp [tp [sp TREL]]]].
  pose proof (tso_pc_related_to_buff_states _ _ _ _ _ _ _ t TREL) as BOR.
  destruct TREL as (_ & _ & (MCRt & _ & _) & _ & _ & _ & _ & 
    (_ & _ & PRTt) & _); simpl in *.
  rewrite CS in BOR.
  destruct (csst ! t) as [ss'|] _eqn : Ess'; simpl in BOR; try done.
  destruct BOR as [sm' [sp' [tp' (AB' & PUBt & PUBs & SR & SCO)]]].
  inversion TS as [| | tsox tx px cx BN LN| | | | | | | | |];
    subst; clear TS.
  rewrite BN in PUBt. inv PUBt.
  assert(TPMP: forall p n, In (p, n) (tp t) -> machine_ptr p).
    intros p' n' IN. 
    assert (RA: range_allocated (p', n') MObjStack tso'.(tso_mem)).
      apply -> PRTt. eby eexists.
    apply range_allocated_consistent_with_restr in RA. 
    simpl in MCRt; rewrite MCRt in RA. by destruct p'.
  assert (SBnil : tso_buffers cstso t = nil). eby eapply tso_pc_rel_buf_nil_rel.
  assert (ABt : apply_buffer (tso_buffers tso' t) 
                             (tso_mem tso') = Some (tso_mem tso')).
    by rewrite BN.
  assert (ABs : apply_buffer (tso_buffers cstso t) 
                             (tso_mem cstso) = Some (tso_mem cstso)).
    by rewrite SBnil.
  assert (MP : machine_ptr p).
    by inv ST; inv SR; inv EKR;
      (eapply machine_ptr_rmw_instr_semantics; [edone |
        intros v' IN; destruct (in_app_or _ _ _ IN) as [|IN']; 
            [auto|destruct IN' as [<- |]]]).
  eexists (_, _). split. apply taustar_refl.
  inv ST; inv SR; inv EKR.
    eexists (_, _). exists (Evisible Efail). split. done. simpl.
    eapply Comp.step_rmw_fail; try edone; vauto.
    econstructor; try edone. 
    pose proof (tso_pc_rel_load_eq _ _ _ _ _ _ _ _ _ 
      Mint32 MP TSOPCREL ABt ABs) as LD.
    by rewrite LN in LD.
  eexists (_, _). exists (Evisible Efail). split. done. simpl.
  eapply Comp.step_rmw_fail; try edone. 
    eby econstructor. 
  econstructor; try edone.
  pose proof (tso_pc_rel_load_eq _ _ _ _ _ _ _ _ _
    Mint32 MP TSOPCREL ABt ABs) as LD.
  by rewrite LN in LD. 
Qed.

(** Main simulation theorem *) 
Lemma chm_cst_bsim:
  forall sts shms sts' e
    (PCREL: tso_pc_related sts shms)
    (NOOM: e <> Eoutofmemory)
    (TSOST: cst_lts.(stepr) sts e sts'),
  can_reach_error csm_globenv shms \/
  (exists shms', taustep cshm_lts shms e shms' /\ tso_pc_related sts' shms') \/
  e = Etau /\ tso_pc_related sts' shms /\ tso_order sts' sts.
Proof.
  intros; revert shms NOOM PCREL.
  (comp_step_cases (case TSOST) Case); clear TSOST sts sts' e; try done;
    try (by intros; inv tidSTEP).

  Case "step_ord".
    intros s s' ev t tso tso' st st' ST TSOST CS NS csms _ TREL.

    mem_event_cases (destruct ev) SCase.
    
    SCase "MEfence".
      eby inv TSOST; exploit fence_sim; try edone; intros [ERR | WS]; vauto.

    SCase "MEwrite".
      eby inv TSOST; exploit write_sim; try edone; intros [ERR | WS]; vauto.

    SCase "MEread".
      eby inv TSOST; exploit read_sim; try edone; intros [ERR | WS]; vauto.

    SCase "MErmw".
      eby exploit rmw_sim; try edone; intros [ERR | WS]; vauto.

    SCase "MEalloc".
      eby inv TSOST; exploit alloc_sim; try edone; intros [ERR | WS]; vauto.
 
    SCase "MEfree". 
      eby inv TSOST; exploit free_sim; try edone; intros [ERR | WS]; vauto.

  Case "step_ext".
    eby intros; subst; exploit ext_sim; try edone; intros [ERR | WS]; vauto.

  Case "step_unbuf".
    eby right; exploit unbuffer_item_preserves_tso_pc; vauto.

  Case "step_tau".    
    eby intros; subst; exploit thread_tau_sim; try edone; 
      intros [ERR | [WS | [TR M]]]; vauto;
      right; right; repeat (split; [done|]); eapply tso_order_update.

  Case "step_start".
    intros; subst.
    eby exploit thread_start_sim; try edone; intros [ERR | WS]; vauto.

  Case "step_start_fail".
    eby intros; exploit thread_start_fail_sim; try edone; intros [ERR | WS]; vauto.

  Case "step_exit".
    eby intros; exploit thread_exit_sim; try edone; intros [ERR | WS]; vauto.

  Case "step_read_fail".
    eby intros; subst; exploit read_fail_sim; try edone; intros [ERR | WS]; vauto.

  Case "step_write_fail".
    eby intros; subst; exploit write_fail_sim; try edone; vauto.

  Case "step_free_fail". 
    eby intros; subst; exploit free_fail_sim; try edone; vauto.

  Case "step_rmw_fail".
    eby left; intros; subst; exploit rmw_fail_sim.

  Case "step_thread_stuck".
    intros s tid tso st STUCK CS [csst cstso] TSOPCREL.
    eby left; eapply thread_stuck_sim.
Qed.

End SIM.

Definition full_cshm_cstk_rel
  (csm_globenv cst_globenv : genv * gvarenv)
  cst_st csm_st :=
  Genv.genv_match (fun a b => a = b) (Cstacked.ge cst_globenv) (ge csm_globenv) /\
  Cstacked.gvare cst_globenv = gvare csm_globenv /\
  (forall id p, Genv.find_symbol (Cstacked.ge cst_globenv) id = Some p -> 
               machine_ptr p) /\
  (forall p f cenv, Genv.find_funct (Cstacked.ge cst_globenv) p = 
                      Some (Internal f) ->
                    snd (build_compilenv cenv f) <= Int.max_unsigned) /\
  tso_pc_related cst_globenv cst_st csm_st.

Definition program_stackframes_small (prg : program) := 
  forall id f cenv, In (id, Internal f) prg.(prog_funct) ->
                    snd (build_compilenv cenv f) <= Int.max_unsigned.

Lemma list_forall2_in1:
  forall {A B} {f : A -> B -> Prop} {a b x}
    (LF : list_forall2 f a b)
    (IN : In x a),
    exists y, In y b /\ f x y.
Proof.
  intros.
  induction LF. done.
  simpl in IN; destruct IN as [<- | IN].
    eexists. split. apply in_eq. done.
  destruct (IHLF IN) as [y (IN' & F)].
  eexists. split. apply in_cons. edone. done.
Qed.

Lemma build_compilenv_indep:
  forall {f c1 c2 n1 n2 c1' c2'}
    (BC1 : build_compilenv c1 f = (c1', n1))
    (BC2 : build_compilenv c2 f = (c2', n2)),
    n1 = n2.
Proof.
  unfold build_compilenv.
  intro f.
  remember 0 as n. clear Heqn. revert n.
  induction (fn_variables f) as [|v vs IH]; intros; simpl in *.
  by inv BC1; inv BC2.

  eby destruct v as [id []]; [destruct Identset.mem|]; eapply IH.
Qed.

Lemma transl_program_program_stackframes_small:
  forall p p',
    transl_program p = OK p' -> program_stackframes_small p.
Proof.
  intros p p' TP.
  intros id f cenv IN.
  unfold transl_program in TP.
  monadInv TP.
  apply map_partial_forall2 in EQ.
  destruct (list_forall2_in1 EQ IN)
    as [[id' f'] (IN' & Eidf & TF)].
  simpl in TF. monadInv TF.
  unfold transl_function in EQ0.
  destruct (build_compilenv (build_global_compilenv p) f) 
    as [cenv' stacksize] _eqn : BCE.
  destruct (build_compilenv cenv f) 
    as [xcenv xstacksize] _eqn : BCEx.
  destruct zle as [LE|]; [|done].
  rewrite (build_compilenv_indep BCE BCEx) in *.
  eapply Zle_trans. apply LE. by compute.
Qed.

Lemma less_restr_no_mem_low_mem:
  Genv.less_restr no_mem_restr low_mem_restr.
Proof. done. Qed.

Lemma match_program_id:
  forall (prg : program),
    match_program (fun f1 f2 => f1 = f2)
                  (fun v1 v2 => v1 = v2)
                  prg prg.
Proof.
  split.
  induction (prog_funct prg) as [|[id fd] l IH]; by constructor.
  split; [done|].
  induction (prog_vars prg) as [|[[id init] fd] l IH]; by constructor.
Qed.

Lemma tso_init_safe:
  forall m, unbuffer_safe (tso_init m).
Proof. by constructor. Qed.

Lemma machine_val_list_conv:
  forall t l
    (MVL: machine_val_list l),
      machine_val_list (Val.conv_list l t).
Proof.
  induction t; intros. by induction l.
  simpl. destruct l. by intros v' [<- |]; [|apply IHt].
  pose proof (MVL _ (in_eq _ _)).
  pose proof (fun v' IN' => MVL _ (in_cons _ v' _ IN')).
  intros v' [<- |]. by destruct a; destruct v.
  by apply IHt. 
Qed.

Theorem initsim_cshm_cstk:
  forall prg prg' args cstk_ge cstk_st,
    transl_program prg = OK prg' ->
    machine_val_list args ->
    Comp.init _ cst_sem prg args cstk_ge cstk_st ->
    exists cshm_ge, exists cshm_st,
      Comp.init _ cs_sem prg args cshm_ge cshm_st /\
      full_cshm_cstk_rel cshm_ge cstk_ge cstk_st cshm_st.
Proof.
  intros prg prg' args tge ts TS MVL [mst [mtid [tm [mptr (GI & FM & IM & ->)]]]].
  simpl in *. 
  apply transl_program_program_stackframes_small in TS.
  exploit Genv.exists_matching_genv_and_mem_rev_lessdef.
  - apply less_restr_no_mem_low_mem. 
  - apply match_program_id.
  - apply GI.
  intros [sge [sm (SGI & GM & MEQ)]].
  destruct tge as [tge tve].
  unfold cst_init in IM.
  pose proof (proj2 GM mptr) as MAINM.
  simpl in *.
  destruct (Genv.find_funct_ptr tge mptr)
    as [[]|] _eqn : Emfn; try done.
  destruct ( beq_nat (length args) (length (sig_args (fn_sig f))))
    as [] _eqn : BE; [|done].
  destruct (Genv.find_funct_ptr sge mptr) 
    as [mfn'|] _eqn:Emfn'; [|done]. subst.
  inv IM.
  exists (sge, tve).
  set (nst := (SKcall (Val.conv_list args (sig_args (fn_sig f))) 
                      (Kcall None (Internal f) empty_env Kstop))).
  exists (tso_init sm, (PTree.empty Csharpminor.state) ! mtid <- nst).
  split. (* establish Comp.init *)
    exists nst. exists mtid. exists sm. exists mptr.
    split. by destruct GI; split.
    split. simpl. by rewrite (proj1 GM).
    split. by simpl; unfold nst, cs_init; simpl; rewrite Emfn', BE.
    done.
  (* Establish the properties of the global environment *)
  unfold cst_ge_init in GI. simpl in GI.
  split. apply GM.
  split. done.
  split.
    intros id p FS. simpl in FS.
    destruct p; apply (Genv.find_symbol_mem_restr (proj1 GI) FS).
  split.
    intros p f0 cenv FF. simpl in FF.
    set (P f := exists id, In (id, f) prg.(prog_funct)).
    destruct p as [ | | | p]; try done; []. simpl in FF.
    exploit (@Genv.find_funct_ptr_prop _ _ P _ _ _ _ p (Internal f0) (proj1 GI)).
    - intros id' f' IN'. eby eexists.
    - done.
    - unfold P. intros [id' IN']. eby eapply TS.
  (* And finally the simulation relation on states *)
  split. (* tso consistency of target *)
    split. 
      intro t'. simpl. done.
    apply tso_init_safe.
  exists (fun t => nil).
  exists (fun t => nil).
  exists (fun t => nil).
  split; simpl. (* machine thread buffers *)
    intro t'. done.
  split. (* Non-stack memory related *)
    intros r k. pose proof (proj1 MEQ r k) as RAR.
    destruct k. done. done.
    split; intro RA. by elim (proj1 RAR). by elim (proj2 RAR).
  split. (* Memory contents are related *)
    split. by rewrite (Genv.initmem_mem_restr (proj1 GI)).
    split. by rewrite (Genv.initmem_mem_restr SGI).
    split. 
      intros p MP c.
      by rewrite (proj1 (proj2 MEQ)); destruct load_ptr.
    intros p c.
    destruct (load_ptr c sm p) as [v|] _eqn : LD; [|done].
    pose proof (proj2 (proj2 MEQ) p c) as MV.
    rewrite (proj1 (proj2 MEQ)), LD, (Genv.initmem_mem_restr (proj1 GI)) in MV.
    by destruct v as [| | | []]; try destruct MV.
  split. (* Source tso consistency *)
    split. intro t'. simpl. done.
    apply tso_init_safe.
  repeat (split; [done|]).
  split. (* Scratch allocations fresh *)
    split. done.
    split. intros. done.
    intros. done.
  split. (* Memory related in partitioning in target *)
    split. intros t1 t2 N. done.
    split. done.
    intros r. split. by intros [t IP].
    intro RA. by destruct (proj1 (proj1 MEQ r MObjStack) RA).
  split. (* Memory related in partitioning in source *)
    split. intros t1 t2 N. done.
    split. done.
    intros r. split. by intros [t IP].
    intro RA. by destruct (proj2 (proj1 MEQ r MObjStack) RA).
  intro t'. 
  split. done. (* Partitions injective *)
  split. constructor. (* Buffers related *)
  simpl in *.
  destruct (peq t' mtid) as [-> | N].
    rewrite !@PTree.gss. simpl.
    eexists. eexists. eexists.
    repeat (split; [edone|]).
    split.
      unfold nst.
      constructor. by constructor; exists (Vptr mptr).
      by apply machine_val_list_conv.
    simpl. split. done. by intro; rewrite PTree.gempty.
  by rewrite !@PTree.gso, !@PTree.gempty. 
Qed.

Definition cs_cst_match_prg (p : cs_sem.(SEM_PRG)) (p' : cst_sem.(SEM_PRG)) := 
  p = p' /\ 
  exists cm_p, transl_program p = OK cm_p.

(* Instantiate the simulation *)
Definition cshm_cst_basic_sim : Bsim.sim tso_mm tso_mm cs_sem cst_sem cs_cst_match_prg.
Proof.
  apply (Bsim.make cs_cst_match_prg
     (fun sge tge s t => full_cshm_cstk_rel sge tge t s) (fun _ _ t t' => tso_order t' t)).
  - intros; destruct REL as (_ & _ & _ & _ & ? & ? & ? & ? & A). 
    repeat apply proj2 in A. 
    by eapply PTree.ext; intro tid; 
       generalize (proj2 (proj2 (A tid))); rewrite EMPTY, !PTree.gempty;
       destruct ((snd s) ! tid); try done;
       destruct ((snd t) ! tid).
  - intros sprg tprg tge args tinit [Eprg [cm_p OKtrans]] Vargs INIT. subst.
    exploit initsim_cshm_cstk; eauto; []. 
    by intros v IN; specialize (Vargs v IN); destruct v.
  intros; destruct REL; edestruct chm_cst_bsim; des; eauto.
  - by right; left; eexists; vauto. 
  - by right; right; vauto.
Defined.

Lemma cshm_cst_sim : Sim.sim tso_mm tso_mm cs_sem cst_sem cs_cst_match_prg.
Proof.
  apply (Sim.make cshm_cst_basic_sim). 
  intros; simpl.
  intros i; induction i as [i IH] using (well_founded_ind tso_order_wf).
  vauto. 
Qed.
