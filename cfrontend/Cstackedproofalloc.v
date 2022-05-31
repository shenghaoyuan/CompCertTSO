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
Require Import Libtactics.
Require Import TSOmachine.
Require Import TSOsimulation.
Require Cminor.
Require Import Cminorgen.
Require Import Cstacked.
Require Import Csharpminor.
Require Import Simulations.
Require Import Mem.
Require Import Memeq.
Require Import Memcomp.
Require Import Cstackedproofsimdef.
Require Import Cstackedproofunbuffer.
Require Import Permutation.

Section ALLOC_SIMS.

Variable cst_globenv : genv * gvarenv.
Variable csm_globenv : genv * gvarenv.

Let cshm_lts := (mklts event_labels (Comp.step tso_mm cs_sem csm_globenv)).
Let cst_lts := (mklts event_labels (Comp.step tso_mm cst_sem cst_globenv)).

Hypothesis function_stacksize_limit:
  forall p f cenv, Genv.find_funct (Cstacked.ge cst_globenv) p = Some (Internal f) ->
                   snd (build_compilenv cenv f) <= Int.max_unsigned.

Notation cont_related := (cont_related cst_globenv). 
Notation expr_cont_related := (expr_cont_related cst_globenv). 
Notation state_related := (state_related cst_globenv).
Notation buffered_states_related := (buffered_states_related cst_globenv).
Notation buffered_ostates_related := (buffered_ostates_related cst_globenv).
Notation tso_pc_related_witt := (tso_pc_related_witt cst_globenv).
Notation tso_pc_related := (tso_pc_related cst_globenv).
Notation tso_pc_unsafe_related := (tso_pc_unsafe_related cst_globenv).
 
Inductive unbuffer_reachable : tso_state -> tso_state -> Prop :=
| unbuffer_reachable_refl:
  forall tso,
    unbuffer_reachable tso tso
| unbuffer_reachable_step:
  forall tso t bi b m' tso' tso'',
    tso.(tso_buffers) t = bi :: b ->
    apply_buffer_item bi tso.(tso_mem) = Some m' ->
    tso' = mktsostate (tupdate t b tso.(tso_buffers))
                      m' ->
    unbuffer_reachable tso' tso'' ->
    unbuffer_reachable tso tso''.

Lemma unbuffer_safe_reachable_safe:
  forall tso,
    unbuffer_safe tso ->
    (forall tso' t bi b, 
      unbuffer_reachable tso tso' ->
      tso'.(tso_buffers) t = bi :: b ->
      apply_buffer_item bi tso'.(tso_mem) <> None).
Proof.
  intros tso US.
  induction US as [tso ABI US IH].

  intros tso' t bi b R BD.
  destruct R as [tso' | tso' t' bi' b' m' tso'' tso''' BD' ABI' Etso''].
    by destruct (ABI t bi b BD) as [m' ->].
  eapply IH; try edone. by rewrite <- Etso''.
Qed.  


(*============================================================================*)
(* Unbuffering safety for allocations                                         *)
(*============================================================================*)

(* Small stepping the buffer relation for source unbufferings *)
Inductive buffers_ss_rel:
  list buffer_item ->      (* Cstacked buffer *)
  list arange ->           (* Cstacked partition *)
  list (list buffer_item) -> (* C#minor (partitioned) buffer *)
  list arange ->           (* C#minor partition *)
  Prop :=
| buffers_ss_rel_coarse:
  forall tb tp sb sp
    (BSR : buffers_related tb tp sb sp),
    buffers_ss_rel tb tp sb sp
| buffers_ss_rel_scratch:
  forall tb tp sb sbr sp sp' 
    (SCR: forall bi, In bi sb -> is_item_scratch_update bi) 
    (PUB: part_update_buffer sb sp = Some sp')
    (BSR: buffers_related tb tp sbr sp'),
    buffers_ss_rel tb tp (sb :: sbr) sp
| buffers_ss_rel_alloc: 
  forall p n tb tp sb sbr sp sp'
    (AR:  allocs_related p n sb)
    (PUB: part_update_buffer sb sp = Some sp')
    (BSR: buffers_related tb ((p, n) :: tp) sbr sp'),
    buffers_ss_rel tb ((p, n) :: tp) (sb :: sbr) sp.


Tactic Notation "buffers_ss_rel_cases" tactic(first) tactic(c) :=
    first; [
      c "buffers_ss_rel_coarse" |
      c "buffers_ss_rel_scratch" |
      c "buffers_ss_rel_alloc"].

Inductive  tso_pc_ss_rel_witt  (ts : tso_state)
                               (ss : tso_state) 
                               (bp : thread_id -> list (list buffer_item))
                               (tp : partitioning)
                               (sp : partitioning) : Prop :=
| tso_pc_ss_rel_witt_intro: forall
  (* Only machine values in buffers *)
  (MB: machine_thread_buffers ss.(tso_buffers))
  (* Non-stack allocations are the same *)
  (NSMR: non_stack_mem_related ts.(tso_mem) ss.(tso_mem))
  (* Memory contents are related *)
  (* mem_content_related (fst csts).(tso_mem) (fst csms).(tso_mem) /\ *)
  (MCWRt: mrestr ts.(tso_mem) = low_mem_restr)
  (MCWRs: mrestr ss.(tso_mem) = no_mem_restr)
  (* finite support for buffers *)
  (TFS: tso_fin_sup ts) 
  (SFS: tso_fin_sup ss)
  (* all unbufferings are successful *)
  (TUS: unbuffer_safe ts)
  (* bp is C#minor buffer partitioning *)
  (BPART: forall t, ss.(tso_buffers) t = flatten (bp t))
  (* Scratch allocations in buffers are globally fresh *)
  (SAF: scratch_allocs_fresh ss.(tso_buffers) sp)
  (* cstm and csmmp are partitionings consistent with the memory *)
  (MRWPt: mem_related_with_partitioning ts.(tso_mem) tp)
  (MRWPs: mem_related_with_partitioning ss.(tso_mem) sp)
  (TREL: forall t,
  (* Partitions must be injective *)
  partition_injective (tp t) (sp t) /\
  (* Buffers must be related *)
  buffers_ss_rel (ts.(tso_buffers) t) (tp t) 
                 (bp t) (sp t)),
  tso_pc_ss_rel_witt ts ss bp tp sp.

Definition tso_pc_ss_rel  (ts : tso_state)
                          (ss : tso_state) : Prop :=
  exists bp, exists tp, exists sp,
    tso_pc_ss_rel_witt ts ss bp tp sp.

Lemma buffered_states_related_length_eq:
  forall tb tp sb sp,
    buffers_related tb tp sb sp ->
    length tb = length sb.
Proof.
  intros tb tp sb sp BREL.
  induction BREL; try done; by simpl; rewrite IHBREL.
Qed.

Lemma ss_rel_preservation_free_nil:
  forall ttso stso bp tb tp tpr bsr smp p n t tm',
     tso_pc_ss_rel_witt ttso stso bp tp smp ->
     tso_buffers ttso t = BufferedFree p MObjStack :: tb ->
     bp t = nil :: bsr ->
     tp t = (p, n) :: tpr ->
     length tb = length bsr ->
     apply_buffer_item (BufferedFree p MObjStack) (tso_mem ttso) = Some tm' ->
     tso_pc_ss_rel_witt
            (mktsostate
               (tupdate t tb (tso_buffers ttso)) tm') 
            stso
            (fun t' => if peq t' t then bsr else bp t')
            (update_partitioning t tpr tp) smp.
Proof.
  intros ttso stso bp tb tp tpr bsr smp p n t tm'
    TWREL TB BP TP El ABIt.
  destruct TWREL.

  split; try done. 
  - eby eapply non_stack_mem_rel_preserved_by_stack_or_write_tgt.
  - eby erewrite mem_consistent_with_restr_apply_item. 
  - eby eapply tso_fin_sup_tupdate.
  - eby destruct ttso; eapply apply_item_unbuffer_safe. 
  - intro t'. specialize (BPART t'). destruct (peq t' t) as [-> | N]. 
      rewrite BP in BPART. by simpl in BPART.
    done.
  - replace tpr with (range_remove p (tp t)).
    eapply free_ptr_preserves_mem_partitioning; try edone. 
    eexists; rewrite TP; apply in_eq.
    rewrite TP. simpl. by destruct MPtr.eq_dec.
  - intros t'.
    destruct (TREL t') as [PI BREL].
    split.
    unfold update_partitioning.
    destruct (peq t' t) as [-> | N].
      eapply (remove_disj_preserves_partition_injectivity _ _ p n). 
        inv BREL. inv BSR. by rewrite BP in *. by rewrite TB in *.
            rewrite TP, BP in *. clarify.
            unfold part_update_buffer in PUB. by inv PUB.
          rewrite TB in *; clarify.
        apply buffered_states_related_length_eq in BSR.
        simpl in BSR. rewrite BP, TB in *; clarify.
        replace (length bsr) with (S (length tb)) in *.
        by apply n_Sn in H1. 
        apply buffered_states_related_length_eq in BSR.
        simpl in BSR. rewrite BP, TB in *; clarify.
        replace (length bsr) with (S (length tb)) in *.
        by apply n_Sn in H2. 
        intros r IN. apply valid_alloc_range_non_empty.
        eapply allocated_range_valid. eapply (proj2 (proj2 MRWPs)).
        exists t. done.
        by rewrite <- TP.
    done.
  simpl in BREL.
  destruct (peq t' t) as [-> | N]; simpl.
    (* same thread as the unbuffering one *)
    rewrite !update_partitioning_s, tupdate_s.
    rewrite TB in BREL.
    inv BREL; try (
      rewrite BP in *;
        apply buffered_states_related_length_eq in BSR; simpl in BSR;
          rewrite El in BSR; clarify; by apply sym_eq, n_Sn in BSR).
    inv BSR; try done.
    econstructor. rewrite BP, TP in *; clarify. 
    unfold part_update_buffer in PUB. by inv PUB.
  (* Other threads - use the memory "sameness" *)
  rewrite ! update_partitioning_o, tupdate_o; try done.
Qed.

Lemma ss_rel_preservation_free_cons:
  forall ttso stso bp bi bis tb tp bsr sp spt' p t sm',
     tso_pc_ss_rel_witt ttso stso bp tp sp ->
     tso_buffers ttso t = BufferedFree p MObjStack :: tb ->
     bp t = (bi :: bis) :: bsr ->
     (* tp t = (p, n) :: tpr -> *)
     length tb = length bsr -> 
     apply_buffer_item bi (tso_mem stso) = Some sm' ->
     part_update bi (sp t)  = Some spt' ->
     tso_pc_ss_rel_witt
            ttso
            (mktsostate
               (tupdate t (bis ++ flatten bsr) (tso_buffers stso)) sm') 
            (fun t' => if peq t' t then (bis :: bsr) else bp t')
            tp (update_partitioning t spt' sp).
Proof.
  intros until 0; intros [] TP BP LB ABIs PU.

  destruct (TREL t) as (_ & BTREL). simpl in BTREL.

  split; simpl; try done.
  - intros t'. pose proof (MB t') as MBt.
    unfold tupdate; destruct (peq t' t) as [-> | N].
      rewrite (BPART t), BP in MBt. simpl in MBt.
      intros bi' IN'. by apply MBt, in_cons.
    done.
  - eapply non_stack_mem_rel_preserved_by_stack_or_write; try edone.
    destruct BTREL. inv BSR; try done. clarify.
      eapply frees_related_impl_stack_or_write; try edone. apply in_eq.
      clarify. apply scratch_impl_stack_or_write, SCR. inv BP. apply in_eq.
    apply buffered_states_related_length_eq in BSR. inv BP. 
    rewrite <- LB in BSR. by apply sym_eq, n_Sn in BSR. 
  - eby erewrite mem_consistent_with_restr_apply_item.
  - eby eapply tso_fin_sup_tupdate.
  - intro t'. unfold tupdate. destruct (peq t' t) as [_ | N]. done.
    apply BPART.
  - eapply unbuffer_preserves_scratch_allocs_fresh; try edone. 
    by rewrite BPART, BP.
  - eby eapply apply_buffer_item_preserves_mem_partitioning.
  - intro t'.
  destruct (TREL t') as [PI BREL].
  destruct (peq t' t) as [-> | N].
    split.    
      destruct BTREL;
        try (subst; inv BP; apply buffered_states_related_length_eq in BSR;
          by rewrite <- LB in BSR; apply sym_eq, n_Sn in BSR).
      inv BSR; try done.
        rewrite update_partitioning_s.
        eapply frees_related_item_preserves_partition_injectivity; try edone.
        inv H1; apply in_eq. 
      clarify.
    rewrite update_partitioning_s. simpl in BREL. 
    rewrite BP, TP in *.
    inv BREL; try (subst; inv BP; apply buffered_states_related_length_eq in BSR;
      by rewrite <- LB in BSR; apply sym_eq, n_Sn in BSR).
    inv BSR; try done.
    eapply buffers_ss_rel_coarse. eapply buffers_related_free.
    intros bi' IN'; apply FR. by apply in_cons. edone.
    unfold part_update_buffer in *. simpl in PUB. rewrite PU in PUB.
    by simpl in PUB. done.
  (* Other threads *)
  by rewrite update_partitioning_o; try split.
Qed.

Lemma ss_rel_preservation_alloc_tgt:
  forall ttso stso bp tb tp smp p n t tm',
     tso_pc_ss_rel_witt ttso stso bp tp smp ->
     tso_buffers ttso t = BufferedAlloc p n MObjStack :: tb ->
     length(bp t) = S(length tb) ->
     apply_buffer_item (BufferedAlloc p n MObjStack) (tso_mem ttso) = Some tm' ->
     tso_pc_ss_rel_witt
            (mktsostate (tupdate t tb (tso_buffers ttso)) tm') 
            stso
            bp
            (update_partitioning t ((p, n) :: tp t) tp) smp.
Proof.
  intros until 0; intros [] TB BPL ABIt.

  split; simpl; try done.
  - eby eapply non_stack_mem_rel_preserved_by_stack_or_write_tgt.
  - eby erewrite mem_consistent_with_restr_apply_item. 
  - eby eapply tso_fin_sup_tupdate.
  - eby destruct ttso; eapply apply_item_unbuffer_safe. 
  - eby eapply alloc_ptr_stack_preserves_mem_partitioning.
  - intros t'.
    destruct (TREL t') as [PI BREL].
    split.
    unfold update_partitioning.
    destruct (peq t' t) as [-> | N].
      intros p' n' MP IN. destruct (PI p' n' MP IN) as [r' [RI RA]].
      eexists. split. edone. by apply in_cons.
    done.
  simpl in BREL.
  destruct (peq t' t) as [-> | N].
    (* same thread as the unbuffering one *)
    rewrite !update_partitioning_s, tupdate_s.
    rewrite TB in BREL.
    inv BREL;
      try (inv BSR; try done; eby eapply buffers_ss_rel_alloc);
        apply buffered_states_related_length_eq in BSR; simpl in BSR;
        match goal with H : _ = bp t |- _ => rewrite <- H in BPL end;
        rewrite BSR in BPL; by apply sym_eq, n_Sn in BPL.      
  (* Other threads - use the memory "sameness" *)
  rewrite ! update_partitioning_o, tupdate_o; try done.
Qed.

Lemma ss_rel_preservation_src_nil:
  forall ttso stso bsr bp tp smp t,
     tso_pc_ss_rel_witt ttso stso bp tp smp ->
     bp t = nil :: bsr ->
     length bsr = length (tso_buffers ttso t) ->
     tso_pc_ss_rel_witt
            ttso
            stso
            (fun t' => if peq t' t then bsr else bp t')
            tp smp.
Proof.
  intros until 0; intros [] BP BPL.
  split; try done. 
  - intro t'. 
    destruct (peq t' t) as [-> | N]; [by rewrite BPART, BP | by rewrite BPART].
  - intro t'.
    destruct (TREL t') as [PI BREL].
    split. done.
  simpl in BREL.
  destruct (peq t' t) as [-> | N].
    (* same thread as the unbuffering one *)
    simpl. 
      
    inv BREL;
      try (apply buffered_states_related_length_eq in BSR; rewrite BSR, BP in *;
        by apply n_Sn in BPL);
      by econstructor; rewrite BP in *; clarify; inv PUB. 
  (* Other threads *)
  done.
Qed.

Lemma ss_rel_preservation_alloc_src_cons:
  forall ttso stso bi bis bsr m' bp tp spt smp t,
     tso_pc_ss_rel_witt ttso stso bp tp smp ->
     bp t = (bi :: bis) :: bsr ->
     apply_buffer_item bi stso.(tso_mem) = Some m' ->
     part_update bi (smp t) = Some spt ->
     length bsr = length (tso_buffers ttso t) ->
     tso_pc_ss_rel_witt
            ttso
            (mktsostate
              (tupdate t (bis ++ flatten bsr) stso.(tso_buffers)) m')
            (fun t' => if peq t' t then bis :: bsr else bp t')
            tp 
            (update_partitioning t spt smp).
Proof.
  intros until 0; intros [] BP ABIs PU LB.

  destruct (TREL t) as (_ & BTREL). simpl in BTREL.

  split; simpl; try done.
  - intros t'. pose proof (MB t') as MBt.
    unfold tupdate; destruct (peq t' t) as [-> | N].
      rewrite (BPART t), BP in MBt. simpl in MBt.
      intros bi' IN'. by apply MBt, in_cons.
    done.
  - eapply non_stack_mem_rel_preserved_by_stack_or_write; try edone.
    destruct BTREL. 
    apply buffered_states_related_length_eq in BSR. rewrite BSR, BP in LB.
      by apply n_Sn in LB. 
    apply scratch_impl_stack_or_write, SCR. inv BP. apply in_eq.
    apply (allocs_related_impl_stack_or_write _ _ _ AR). inv BP. apply in_eq.
  - eby erewrite mem_consistent_with_restr_apply_item.
  - eby eapply tso_fin_sup_tupdate.
  - by intro t'; unfold tupdate; destruct peq; clarify.
  - eapply unbuffer_preserves_scratch_allocs_fresh; try edone. 
    by rewrite BPART, BP.
  - eby eapply apply_buffer_item_preserves_mem_partitioning.
  - intro t'.
  destruct (TREL t') as [PI BREL].
  destruct (peq t' t) as [-> | N].
  split.    
    destruct BTREL.
    apply buffered_states_related_length_eq in BSR. 
      rewrite BSR, BP in LB. by apply n_Sn in LB. 
      eapply update_part_scratch_preserves_partition_injectivity. apply SCR.
      inv BP. apply in_eq. 2 : apply PI. by rewrite update_partitioning_s. 
      rewrite update_partitioning_s. 
      eapply allocs_related_item_preserves_partition_injectivity; try edone.
      inv BP. apply in_eq.
      rewrite update_partitioning_s.
      inv BTREL. 
        apply buffered_states_related_length_eq in BSR. 
          rewrite BSR, BP in LB. by apply n_Sn in LB.
        rewrite BP in *; clarify.
        unfold part_update_buffer in PUB; simpl in PUB; rewrite PU in PUB;
          simpl in PUB.
        eapply buffers_ss_rel_scratch.
          intros bi' IN'. apply SCR, in_cons, IN'. edone. edone. 
        rewrite BP in *; clarify.
        unfold part_update_buffer in PUB; simpl in PUB; rewrite PU in PUB;
          simpl in PUB.
        eapply buffers_ss_rel_alloc.
          intros bi' IN'. apply AR, in_cons, IN'. edone. edone.
  (* Other threads *)
  by rewrite update_partitioning_o; try split.
Qed.

Lemma ss_rel_preservation_other:
  forall ttso stso bi bis bsr sm' tm' bp tp tb sp t,
     tso_pc_ss_rel_witt ttso stso bp tp sp ->
     buffer_item_irrelevant bi ->
     bp t = (bi :: bis) :: bsr ->
     tso_buffers ttso t = bi :: tb ->
     apply_buffer_item bi stso.(tso_mem) = Some sm' ->
     apply_buffer_item bi ttso.(tso_mem) = Some tm' ->
     tso_pc_ss_rel_witt
            (mktsostate (tupdate t tb (tso_buffers ttso)) tm') 
            (mktsostate (tupdate t (bis ++ flatten bsr) stso.(tso_buffers)) sm')
            (fun t' => if peq t' t then bis :: bsr else bp t')
            tp sp.
Proof.
  intros until 0; intros [] BIIR BP TB ABIs ABIt.
  destruct (TREL t) as (_ & BTREL). simpl in BTREL.

  split; simpl; try done.
  - intros t'. pose proof (MB t') as MBt.
    unfold tupdate; destruct (peq t' t) as [-> | N].
      rewrite (BPART t), BP in MBt. simpl in MBt.
      intros bi' IN'. by apply MBt, in_cons.
    done.
  - eby eapply sim_irrelevant_preserves_non_stack_mem_related.
  - eby erewrite mem_consistent_with_restr_apply_item.
  - eby erewrite mem_consistent_with_restr_apply_item.
  - eby eapply tso_fin_sup_tupdate.
  - eby eapply tso_fin_sup_tupdate.
  - eby destruct ttso; eapply apply_item_unbuffer_safe. 
  - by intro; unfold tupdate; destruct peq; clarify.
  - eapply scratch_allocs_fresh_ext.
    eapply unbuffer_preserves_scratch_allocs_fresh. 
    apply buffer_item_irrelevant_part_update. apply BIIR. 
    specialize (BPART t); rewrite BP in BPART; simpl in BPART. apply BPART.
    edone. 
    intros t'. by unfold update_partitioning; destruct (peq t' t) as [-> | ?].
    done.
  - eapply (mem_related_with_partitioning_ext _
             (update_partitioning t (tp t) tp)).
    eapply apply_buffer_item_preserves_mem_partitioning. apply MRWPt.
    edone. by apply buffer_item_irrelevant_part_update.
    intros t'. unfold update_partitioning. by destruct (peq t' t) as [-> | ?].
  - eapply (mem_related_with_partitioning_ext _
             (update_partitioning t (sp t) sp)).
    eapply apply_buffer_item_preserves_mem_partitioning. apply MRWPs.
    edone. by apply buffer_item_irrelevant_part_update.
    intros t'. unfold update_partitioning. by destruct (peq t' t) as [-> | ?].
  - intro t'.
  destruct (TREL t') as [PI BREL].
  split. done.
  destruct (peq t' t) as [-> | N].
    inv BTREL. 
      inv BSR; rewrite TB, BP in *; clarify.
      eapply buffers_ss_rel_scratch. done. edone. by rewrite tupdate_s.
      rewrite TB, BP in *; clarify.
      specialize (SCR bi (in_eq _ _)).
      destruct bi as [? ? ?| ? ? [] | ? []]; simpl in *; try done.
      destruct BIIR as [M _].  destruct p; simpl in *; by rewrite M in SCR.
    rewrite TB, BP in *; clarify.
    specialize (AR bi (in_eq _ _)).
    destruct bi as [? ? ?| ? ? [] | ? []]; simpl in *; 
      destruct AR as [SCR | ?]; try done.
    destruct BIIR as [M _].  destruct p0; simpl in *. by rewrite M in SCR.
  (* Other threads *)
  by rewrite tupdate_o.
Qed.

(* If I unbuffer in source then I am still related with the target or
   I can do a step in target and stay related *)
Lemma ss_rel_sim:
  forall ttso t stso bi b m',
  tso_pc_ss_rel ttso stso ->
  stso.(tso_buffers) t = bi :: b ->
  apply_buffer_item bi stso.(tso_mem) = Some m' ->
  exists ttso',
    unbuffer_reachable ttso ttso' /\
    tso_pc_ss_rel ttso' (mktsostate (tupdate t b stso.(tso_buffers)) m').
Proof.
  intros ttso t stso bi b m' [bp [tp [sp TWREL]]] SB SABI.
  remember (bp t) as bpt.
  revert bp Heqbpt ttso tp TWREL.
  
  induction bpt as [|bph bpt IH]; intros bp E ttso tp TWREL;
    generalize TWREL;
      intros X; destruct X;
      destruct (TREL t) as [PI BREL]; simpl in *; apply sym_eq in E.

  inv BREL; [inv BSR | | ]; 
    try (by specialize (BPART t); rewrite SB, E in BPART).

  (* Induction step *)
  specialize (IH (fun t' => if peq t' t then bpt else bp t')).
  simpl in IH. destruct (peq t t); try done.
  specialize (IH (refl_equal _)).
  inv BREL.
    inv BSR. 
    (* End of buffer *)
    by rewrite E in *.
    (* Allocation *)
    rewrite E in *. clarify.
    destruct (unbuffer_unbuffer_safe TUS (sym_eq H0))
      as [tm' [ABIt US']]. simpl in ABIt, US'.
    destruct bph as [|bphi bphr].
      inv PUB.
      specialize (IH (mktsostate
        (tupdate t tb (tso_buffers ttso)) tm')
        (update_partitioning t ((p, n) :: tp t) tp)). 
      apply modusponens in IH. 
      destruct IH as [ttso' [UR REL]].
      exists ttso'. split. 
        econstructor. eby apply sym_eq. edone. edone. done.
      edone.
      apply buffered_states_related_length_eq in BSR0. 
      eapply (ss_rel_preservation_src_nil _ _ _ _ _ _ t).
      eapply ss_rel_preservation_alloc_tgt; try edone.
      by rewrite E, BSR0. done. simpl. by rewrite tupdate_s.
    exists (mktsostate (tupdate t tb (tso_buffers ttso)) tm').
    split. econstructor. eby apply sym_eq. edone. edone. constructor.
    rewrite (BPART t), E in SB. inv SB. 
    unfold part_update_buffer in PUB; simpl in PUB.
    destruct (part_update bi (sp t)) as [spt|] _eqn : PU; try done.
    eexists; eexists; eexists.
    apply buffered_states_related_length_eq in BSR0. 
    eapply (ss_rel_preservation_alloc_src_cons _ _ _ _ _ _ _ _ _ _ t);
      try edone.
    eapply ss_rel_preservation_alloc_tgt; try edone. done.
    by rewrite BSR0, E. simpl. by rewrite tupdate_s.
    (* Free *)
    destruct (unbuffer_unbuffer_safe TUS (sym_eq H0))
      as [tm' [ABIt US']]. simpl in ABIt, US'.
    destruct sb as [|sbi sbir].
      specialize (IH (mktsostate
        (tupdate t tb (tso_buffers ttso)) tm')
        (update_partitioning t tp0 tp)). 
      apply modusponens in IH.
        destruct IH as [ttsox [URx TRWx]].
        exists ttsox.
        split. econstructor; try edone. eby apply sym_eq. edone. done.
      rewrite E in *. clarify.
      eapply (ss_rel_preservation_free_nil _ _ _ _ _ _ _ _ _ _ t); try edone.
      eby apply sym_eq. eby apply sym_eq. 
      by apply buffered_states_related_length_eq in BSR0.  
    exists ttso. split. constructor.
    exists (fun t' : thread_id => if peq t' t then sbir :: sbr else bp t').
    exists tp.
    unfold part_update_buffer in PUB. simpl in PUB.
    destruct (part_update sbi (sp t)) as [spt'|] _eqn : PU; try done.
    exists (update_partitioning t spt' sp).
    rewrite BPART in SB. 
    replace (bp t) with ((sbi :: sbir) :: sbr) in SB.
    simpl in SB. inv SB.
    eapply ss_rel_preservation_free_cons; try edone.
      eby apply sym_eq. eby apply sym_eq. 
    by apply buffered_states_related_length_eq in BSR0.
    (* Other actions *)
    rewrite BPART in SB. replace (bp t) with ((bi0 :: sb) :: sbr) in SB.
    simpl in SB. inv SB.
    destruct (unbuffer_unbuffer_safe TUS (sym_eq H0))
      as [tm' [ABIt US']]. simpl in ABIt, US'.
    exists (mktsostate (tupdate t tb (tso_buffers ttso)) tm').
    split. econstructor. apply sym_eq. edone. edone. reflexivity. constructor.
    eexists; eexists; eexists.
    eapply (ss_rel_preservation_other _ _ _ _ _ _ _ _ _ _ _ t); try edone.
  (* Alloc in progress *)  
  rewrite E in *. clarify.
  destruct bph as [|bphi bphr].
    inv PUB.
    specialize (IH ttso tp).
    apply modusponens in IH. 
      destruct IH as [ttso' [UR REL]].
      exists ttso'. by split. 
    apply buffered_states_related_length_eq in BSR.
    eapply (ss_rel_preservation_src_nil _ _ _ _ _ _ t); try done.
  exists ttso. split. constructor.
  rewrite (BPART t), E in SB. inv SB. 
  unfold part_update_buffer in PUB; simpl in PUB.
  destruct (part_update bi (sp t)) as [spt|] _eqn : PU; try done.
  eexists; eexists; eexists.
  apply buffered_states_related_length_eq in BSR. 
  eapply (ss_rel_preservation_alloc_src_cons _ _ _ _ _ _ _ _ _ _ t);
      try edone.
  (* Scratch in progress *)
  rewrite E in *. clarify.
  destruct bph as [|bphi bphr].
    inv PUB.
    specialize (IH ttso tp).
    apply modusponens in IH. 
      destruct IH as [ttso' [UR REL]].
      exists ttso'. by split. 
    apply buffered_states_related_length_eq in BSR.
    eapply (ss_rel_preservation_src_nil _ _ _ _ _ _ t); try done.
  exists ttso. split. constructor.
  rewrite (BPART t), E in SB. inv SB. 
  unfold part_update_buffer in PUB; simpl in PUB.
  destruct (part_update bi (sp t)) as [spt|] _eqn : PU; try done.
  eexists; eexists; eexists.
  apply buffered_states_related_length_eq in BSR. 
  eapply (ss_rel_preservation_alloc_src_cons _ _ _ _ _ _ _ _ _ _ t);
      try edone.
Qed.

Definition disjoint_item (r : arange) (bi : buffer_item) :=
  match bi with 
    | BufferedAlloc p' n' _ => ranges_disjoint (p', n') r 
    | _ => True
  end.

Fixpoint disjoint_allocs (b : list buffer_item) :=
  match b with 
    | BufferedAlloc p n _ :: br => 
        disjoint_allocs br /\
        forall bi, In bi br -> disjoint_item (p, n) bi
    | nil => True
    | _ => False
  end.  

Ltac mach_scr_elim :=
  match goal with
    H : machine_ptr ?p, H' : scratch_ptr ?p |- _ =>
      by destruct (machine_not_scratch _ H H')
  end.

Definition non_stack_kind (k : mobject_kind) :=
  match k with
    |  MObjStack => False
    | _ => True
  end.

Definition non_stack_item (bi : buffer_item) :=
  match bi with 
    | BufferedAlloc pi ni ki => non_stack_kind ki
    | BufferedFree pi ki => non_stack_kind ki
    | _ => False
  end.

Lemma irrelevant_src_buff_impl_tgt_success:
  forall ts ss t bi sbr,
    tso_pc_ss_rel ts ss ->
    ss.(tso_buffers) t = bi :: sbr ->
    non_stack_item bi ->
    exists ts', exists tbr,
      tso_pc_ss_rel ts' ss /\
      ts'.(tso_buffers) t = bi :: tbr.
Proof.
  intros ts ss t bi sbr TREL SB NS.
  destruct TREL as [bp [tp [sp TWREL]]].
  remember (bp t) as bpt.
  revert bp Heqbpt ts tp TWREL.

  induction bpt as [|bph bpt IH];
    intros bp E ts tp TWREL; apply sym_eq in E;
      generalize TWREL; destruct 1.

  (* Base case *)
  specialize (BPART t). rewrite E, SB in BPART. done. 

  (* Step case *)
  specialize (IH (fun t' => if peq t' t then bpt else bp t')).
  simpl in IH. destruct (peq t t); try done.
  specialize (IH (refl_equal _)).
  destruct (TREL t) as [PIt BRELt].
  inv BRELt. 
    inv BSR; rewrite E in *; clarify.
    (* Allocs *)
    destruct (unbuffer_unbuffer_safe TUS (sym_eq H0))
      as [tm' [ABIt US']]. simpl in ABIt, US'.
    destruct bph as [|bphi bphs].
      (* Go to IH *)
      inv PUB.
      specialize (IH (mktsostate 
        (tupdate t tb (tso_buffers ts)) tm')
        (update_partitioning t ((p, n) :: tp t) tp)). 
      apply modusponens in IH. done. 
      apply buffered_states_related_length_eq in BSR0. 
      eapply (ss_rel_preservation_src_nil _ _ _ _ _ _ t).
      eapply ss_rel_preservation_alloc_tgt; try edone.
      by rewrite E, BSR0. done. simpl. by rewrite tupdate_s.
    (* Non-empty is not possible *)
    specialize (BPART t). rewrite E, SB in BPART.
    simpl in BPART. inv BPART.
    specialize (AR _ (in_eq _ _)). unfold is_item_scratch_update in AR.  
    destruct AR; destruct bphi as [ | ? ? [] | ? []]; try done;
      destruct NS; by mach_scr_elim.
    (* Frees *)
    destruct (unbuffer_unbuffer_safe TUS (sym_eq H0))
      as [tm' [ABIt US']]. simpl in ABIt, US'.
    destruct bph as [|bphi bphs].
      (* Go to IH *)
      inv PUB.
      specialize (IH (mktsostate
        (tupdate t tb (tso_buffers ts)) tm')
        (update_partitioning t tp0 tp)). 
      apply modusponens in IH. done. 
      apply buffered_states_related_length_eq in BSR0.
      eapply (ss_rel_preservation_free_nil _ _ _ _ _ _ _ _ _ _ t); try edone;
        eby apply sym_eq.
    (* Non-empty is not possible *)
    specialize (BPART t). rewrite E, SB in BPART.
    simpl in BPART. inv BPART.
    specialize (FR _ (in_eq _ _)). unfold is_item_scratch_update in FR.  
    destruct FR; destruct bphi as [ | ? ? [] | ? []]; try done;
      destruct NS; by mach_scr_elim.
    (* Buffer irrelevant item *)
    specialize (BPART t). rewrite E, SB in BPART.
    simpl in BPART. inv BPART.
    exists ts. eexists. split. eexists; eexists; eexists; edone.
    eby apply sym_eq. 
  (* Scratch unbuffering in progress *)
  rewrite E in *; clarify.
  destruct bph as [|bphi bphs].
    (* Go to IH *)  
    inv PUB.
    specialize (IH ts tp). 
    apply modusponens in IH. done. 
    apply buffered_states_related_length_eq in BSR. 
    by eapply (ss_rel_preservation_src_nil _ _ _ _ _ _ t).
  (* Non-empty is not possible *)
  specialize (BPART t). rewrite E, SB in BPART.
  simpl in BPART. inv BPART.
  specialize (SCR _ (in_eq _ _)). unfold is_item_scratch_update in SCR.  
  destruct bphi as [ | ? ? [] | ? []]; try done;
      destruct NS; by mach_scr_elim.
  (* Allocation unbuffering in progress *)
  rewrite E in *; clarify.
  destruct bph as [|bphi bphs].
    (* Go to IH *)  
    inv PUB.
    specialize (IH ts tp). 
    apply modusponens in IH. done. 
    apply buffered_states_related_length_eq in BSR. 
    by eapply (ss_rel_preservation_src_nil _ _ _ _ _ _ t).
  (* Non-empty is not possible *)
  specialize (BPART t). rewrite E, SB in BPART.
  simpl in BPART. inv BPART.
  specialize (AR _ (in_eq _ _)). unfold is_item_scratch_update in AR.  
  destruct AR; destruct bphi as [ | ? ? [] | ? []]; try done;
      destruct NS; by mach_scr_elim.
Qed.

Lemma alloc_stack_src_buff_impl_tgt_partition:
  forall ts ss t p n sbr,
    tso_pc_ss_rel ts ss ->
    ss.(tso_buffers) t = BufferedAlloc p n MObjStack :: sbr ->
    machine_ptr p ->
    exists ts', exists r, exists tpr, exists bp, exists tp, exists sp,
      tso_pc_ss_rel_witt ts' ss bp tp sp /\
      range_inside (p, n) r /\
      tp t = r :: tpr /\
      range_not_in (p, n) (sp t).
Proof.
  intros ts ss t p n sbr TREL SB MP.
  destruct TREL as [bp [tp [sp TWREL]]].
  remember (bp t) as bpt.
  revert bp Heqbpt ts tp TWREL.

  induction bpt as [|bph bpt IH];
    intros bp E ts tp TWREL; apply sym_eq in E;
      generalize TWREL; destruct 1.

  (* Base case *)
  specialize (BPART t). rewrite E, SB in BPART. done. 

  (* Step case *)
  specialize (IH (fun t' => if peq t' t then bpt else bp t')).
  simpl in IH. destruct (peq t t); try done.
  specialize (IH (refl_equal _)).
  destruct (TREL t) as [PIt BRELt].
  inv BRELt. 
    inv BSR; rewrite E in *; clarify.
    (* Allocs *)
    destruct (unbuffer_unbuffer_safe TUS (sym_eq H0))
      as [tm' [ABIt US']]. simpl in ABIt, US'.
    destruct bph as [|bphi bphs].
      (* Go to IH *)
      inv PUB.
      specialize (IH (mktsostate
        (tupdate t tb (tso_buffers ts)) tm')
        (update_partitioning t ((p0, n0) :: tp t) tp)). 
      apply modusponens in IH. done. 
      apply buffered_states_related_length_eq in BSR0. 
      eapply (ss_rel_preservation_src_nil _ _ _ _ _ _ t).
      eapply ss_rel_preservation_alloc_tgt; try edone.
      by rewrite E, BSR0. done. simpl. by rewrite tupdate_s.
    (* Do a step in target to allocate the range *)
    specialize (BPART t). rewrite E, SB in BPART.
    simpl in BPART. inv BPART.
    exists (mktsostate (tupdate t tb ts.(tso_buffers)) tm').
    exists (p0, n0). exists (tp t). exists bp.
    exists (update_partitioning t ((p0, n0) :: tp t) tp). exists sp.
    apply buffered_states_related_length_eq in BSR0. 
    split. 
      eapply ss_rel_preservation_alloc_tgt; try edone; by rewrite E, BSR0.
    split.
      specialize (AR _ (in_eq _ _)). simpl in AR.
      by destruct AR as [SCR | RI]; [mach_scr_elim | ].
    split.
      by rewrite update_partitioning_s.
    unfold part_update_buffer in PUB; simpl in PUB.
    by destruct valid_alloc_range_dec; try destruct range_in_dec.

    (* Frees *)
    destruct (unbuffer_unbuffer_safe TUS (sym_eq H0))
      as [tm' [ABIt US']]. simpl in ABIt, US'.
    destruct bph as [|bphi bphs].
      (* Go to IH *)
      inv PUB.
      specialize (IH (mktsostate
        (tupdate t tb (tso_buffers ts)) tm')
        (update_partitioning t tp0 tp)). 
      apply modusponens in IH. done. 
      apply buffered_states_related_length_eq in BSR0.
      eapply (ss_rel_preservation_free_nil _ _ _ _ _ _ _ _ _ _ t); try edone;
        eby apply sym_eq.
    (* Non-empty is not possible *)
    specialize (BPART t). rewrite E, SB in BPART.
    simpl in BPART. inv BPART.
    specialize (FR _ (in_eq _ _)). unfold is_item_scratch_update in FR.  
    by destruct FR; [mach_scr_elim | ].

    (* Other *)
    specialize (BPART t). rewrite E, SB in BPART.
    simpl in BPART. inv BPART. by simpl in BIIR.
  (* Scratch unbuffering in progress *)
  rewrite E in *; clarify.
  destruct bph as [|bphi bphs].
    (* Go to IH *)  
    inv PUB.
    specialize (IH ts tp). 
    apply modusponens in IH. done. 
    apply buffered_states_related_length_eq in BSR. 
    by eapply (ss_rel_preservation_src_nil _ _ _ _ _ _ t).
  (* Non-empty is not possible *)
  specialize (BPART t). rewrite E, SB in BPART.
  simpl in BPART. inv BPART.
  specialize (SCR _ (in_eq _ _)). unfold is_item_scratch_update in SCR.  
  mach_scr_elim.
  (* Allocation unbuffering in progress *)
  rewrite E in *; clarify.
  destruct bph as [|bphi bphs].
    (* Go to IH *)  
    inv PUB.
    specialize (IH ts tp). 
    apply modusponens in IH. done. 
    apply buffered_states_related_length_eq in BSR. 
    by eapply (ss_rel_preservation_src_nil _ _ _ _ _ _ t).
  (* We are done *)
  specialize (BPART t). rewrite E, SB in BPART.
  simpl in BPART. inv BPART.
  specialize (AR _ (in_eq _ _)). unfold is_item_scratch_update in AR.  
  destruct AR. mach_scr_elim.
  eexists; eexists; eexists; eexists; eexists; eexists.
  split. edone. split. edone. split. eby apply sym_eq.
  unfold part_update_buffer in PUB; simpl in PUB.
  by destruct valid_alloc_range_dec; try destruct range_in_dec.
Qed.

Lemma alloc_stack_src_buff_impl_part_update_succ:
  forall ts ss bp tp sp t bi sbr,
    tso_pc_ss_rel_witt ts ss bp tp sp ->
    ss.(tso_buffers) t = bi :: sbr ->
    part_update bi (sp t) <> None.
Proof.
  intros ts ss bp tp sp t bi sbr TWREL SB.
  remember (bp t) as bpt.
  revert bp Heqbpt ts tp TWREL.

  induction bpt as [|bph bpt IH];
    intros bp E ts tp TWREL; apply sym_eq in E;
      generalize TWREL; destruct 1.

  (* Base case *)
  specialize (BPART t). rewrite E, SB in BPART. done. 

  (* Step case *)
  specialize (IH (fun t' => if peq t' t then bpt else bp t')).
  simpl in IH. destruct (peq t t); try done.
  specialize (IH (refl_equal _)).
  destruct (TREL t) as [PIt BRELt].
  inv BRELt. 
    inv BSR; rewrite E in *; clarify.
    (* Allocs *)
    destruct (unbuffer_unbuffer_safe TUS (sym_eq H0))
      as [tm' [ABIt US']]. simpl in ABIt, US'.
    destruct bph as [|bphi bphs].
      (* Go to IH *)
      inv PUB.
      specialize (IH (mktsostate 
        (tupdate t tb (tso_buffers ts)) tm')
        (update_partitioning t ((p, n) :: tp t) tp)). 
      apply modusponens in IH. done. 
      apply buffered_states_related_length_eq in BSR0. 
      eapply (ss_rel_preservation_src_nil _ _ _ _ _ _ t).
      eapply ss_rel_preservation_alloc_tgt; try edone.
      by rewrite E, BSR0. done. simpl. by rewrite tupdate_s.
    (* Do a step in target to allocate the range *)
    specialize (BPART t). rewrite E, SB in BPART.
    simpl in BPART. inv BPART.
    unfold part_update_buffer in PUB. simpl in PUB.
    by destruct (part_update bphi (sp t)).

    (* Frees *)
    destruct (unbuffer_unbuffer_safe TUS (sym_eq H0))
      as [tm' [ABIt US']]. simpl in ABIt, US'.
    destruct bph as [|bphi bphs].
      (* Go to IH *)
      inv PUB.
      specialize (IH (mktsostate 
        (tupdate t tb (tso_buffers ts)) tm')
        (update_partitioning t tp0 tp)). 
      apply modusponens in IH. done. 
      apply buffered_states_related_length_eq in BSR0.
      eapply (ss_rel_preservation_free_nil _ _ _ _ _ _ _ _ _ _ t); try edone;
        eby apply sym_eq.
    (* Non-empty is not possible *)
    specialize (BPART t). rewrite E, SB in BPART.
    simpl in BPART. inv BPART.
    specialize (FR _ (in_eq _ _)). unfold is_item_scratch_update in FR.  
    unfold part_update_buffer in PUB. simpl in PUB.
    by destruct (part_update bphi (sp t)).

    (* Other *)
    specialize (BPART t). rewrite E, SB in BPART.
    simpl in BPART. inv BPART.
    by rewrite buffer_item_irrelevant_part_update.

  (* Scratch unbuffering in progress *)
  rewrite E in *; clarify.
  destruct bph as [|bphi bphs].
    (* Go to IH *)  
    inv PUB.
    specialize (IH ts tp). 
    apply modusponens in IH. done. 
    apply buffered_states_related_length_eq in BSR. 
    by eapply (ss_rel_preservation_src_nil _ _ _ _ _ _ t).
  (* Non-empty is not possible *)
  specialize (BPART t). rewrite E, SB in BPART.
  simpl in BPART. inv BPART.
  unfold part_update_buffer in PUB. simpl in PUB.
  by destruct (part_update bphi (sp t)).
  (* Allocation unbuffering in progress *)
  rewrite E in *; clarify.
  destruct bph as [|bphi bphs].
    (* Go to IH *)  
    inv PUB.
    specialize (IH ts tp). 
    apply modusponens in IH. done. 
    apply buffered_states_related_length_eq in BSR. 
    by eapply (ss_rel_preservation_src_nil _ _ _ _ _ _ t).
  (* We are done *)
  specialize (BPART t). rewrite E, SB in BPART.
  simpl in BPART. inv BPART.
  unfold part_update_buffer in PUB. simpl in PUB.
  by destruct (part_update bphi (sp t)).
Qed.

Lemma tso_ss_rel_range_allocated:
  forall ts ss p n k,
    tso_pc_ss_rel ts ss ->
    range_allocated (p, n) k ss.(tso_mem) ->
    machine_ptr p ->
    exists r',
      range_inside (p, n) r' /\
      range_allocated r' k ts.(tso_mem). 
Proof.
  intros ts ss p n k [bp [tp [sp []]]] RA MP.
  destruct k;
    try (by exists (p, n); split; 
      [apply range_inside_refl | ];
      try apply (NSMR (p, n) MObjGlobal); 
        try apply (NSMR (p, n) MObjHeap)).
  destruct (proj2 (proj2 (proj2 MRWPs) (p, n)) RA) as [t INPs].
  destruct (proj1 (TREL t) _ _ MP INPs) as [r [RIN INPt]].
  exists r. split. done. apply (proj1 (proj2 (proj2 MRWPt) r)).
  eby eexists.
Qed.

Lemma tso_ss_rel_non_stack_alloc_contr:
  forall ts ss r k pi ni ki b t,
  tso_pc_ss_rel ts ss ->
  range_allocated r k (tso_mem ss) ->
  ranges_overlap (pi, ni) r ->
  tso_buffers ss t = BufferedAlloc pi ni ki :: b ->
  non_stack_kind ki ->
  False.
Proof.
  intros ts ss r k pi ni ki b t TREL RA RO Bs NS.
  destruct (irrelevant_src_buff_impl_tgt_success _ _ _ _ _
    TREL Bs NS) as [ts' [tsr [TREL' BD']]].
  generalize TREL'. 
  intros [_ [_ [_ [_ _ MCRt _ _ _ UST' _ _ _ _ _]]]].
  destruct (unbuffer_unbuffer_safe UST' BD') as [tm' [ABIT _]].
  unfold apply_buffer_item in ABIT. 
  pose proof (alloc_cond_spec (pi, ni) ki (tso_mem ts')) as AST'.
  rewrite ABIT in AST'. destruct AST' as (_ & _ & RP' & RNA') .
  assert (MPi: machine_ptr pi).
    by apply (restricted_low_pointer_machine _ _ MCRt).
  destruct r as [p n].
  assert (MP: machine_ptr p).
    by destruct p; destruct pi; destruct (ranges_overlapD RO); subst.
  destruct (tso_ss_rel_range_allocated _ _ _ _ _ TREL' RA MP) 
    as [rt [RIt RAt]].
  eapply RNA'. 2 : apply RAt.
  eapply ranges_overlap_comm, overlap_inside_overlap.
  apply ranges_overlap_comm, RO. done.
Qed.

(* TODO: prove this using alloc_stack_src_buff_impl_part_update_succ!!! *)
Lemma tso_pc_rel_valid_alloc_range_src_buff:
  forall ts ss t p n k br,
    tso_pc_ss_rel ts ss ->
    ss.(tso_buffers) t = BufferedAlloc p n k :: br ->
    valid_alloc_range (p, n).
Proof.
  intros ts ss t p n k br [bp [tp [sp TWREL]]] SB.
  remember (bp t) as bpt.
  revert bp Heqbpt ts tp TWREL.

  induction bpt as [|bph bpt IH];
    intros bp E ts tp TWREL; apply sym_eq in E;
      generalize TWREL; destruct 1.

  specialize (BPART t). rewrite E, SB in BPART. done. 

  (* Step case *)
  specialize (IH (fun t' => if peq t' t then bpt else bp t')).
  simpl in IH. destruct (peq t t); try done.
  specialize (IH (refl_equal _)).
  destruct (TREL t) as [PIt BRELt].
  inv BRELt. 
    inv BSR; rewrite E in *; clarify.
    (* Allocs *)
    destruct (unbuffer_unbuffer_safe TUS (sym_eq H0))
      as [tm' [ABIt US']]. simpl in ABIt, US'.
    destruct bph as [|bphi bphs].
      (* Go to IH *)
      inv PUB.
      specialize (IH (mktsostate
        (tupdate t tb (tso_buffers ts)) tm')
        (update_partitioning t ((p0, n0) :: tp t) tp)). 
      apply modusponens in IH. done. 
      apply buffered_states_related_length_eq in BSR0. 
      eapply (ss_rel_preservation_src_nil _ _ _ _ _ _ t).
      eapply ss_rel_preservation_alloc_tgt; try edone.
      by rewrite E, BSR0. done. simpl. by rewrite tupdate_s.
    (* Do a step in target to allocate the range *)
    specialize (BPART t). rewrite E, SB in BPART.
    simpl in BPART. inv BPART.
    unfold part_update_buffer in PUB. simpl in PUB. 
    by destruct k; destruct valid_alloc_range_dec.

    (* Frees *)
    destruct (unbuffer_unbuffer_safe TUS (sym_eq H0))
      as [tm' [ABIt US']]. simpl in ABIt, US'.
    destruct bph as [|bphi bphs].
      (* Go to IH *)
      inv PUB.
      specialize (IH (mktsostate
        (tupdate t tb (tso_buffers ts)) tm')
        (update_partitioning t tp0 tp)). 
      apply modusponens in IH. done. 
      apply buffered_states_related_length_eq in BSR0.
      eapply (ss_rel_preservation_free_nil _ _ _ _ _ _ _ _ _ _ t); try edone;
        eby apply sym_eq.
    (* Non-empty is not possible *)
    specialize (BPART t). rewrite E, SB in BPART.
    simpl in BPART. inv BPART.
    unfold part_update_buffer in PUB. simpl in PUB. 
    by destruct k; destruct valid_alloc_range_dec.

    (* Other *)
    specialize (BPART t). rewrite E, SB in BPART.
    simpl in BPART. inv BPART. simpl in BIIR. by destruct k; destruct BIIR.
  (* Scratch unbuffering in progress *)
  rewrite E in *; clarify.
  destruct bph as [|bphi bphs].
    (* Go to IH *)  
    inv PUB.
    specialize (IH ts tp). 
    apply modusponens in IH. done. 
    apply buffered_states_related_length_eq in BSR. 
    by eapply (ss_rel_preservation_src_nil _ _ _ _ _ _ t).
  (* Non-empty is not possible *)
  specialize (BPART t). rewrite E, SB in BPART.
  simpl in BPART. inv BPART.
  unfold part_update_buffer in PUB; simpl in PUB.
  by destruct k; destruct valid_alloc_range_dec; try destruct range_in_dec.
  (* Allocation unbuffering in progress *)
  rewrite E in *; clarify.
  destruct bph as [|bphi bphs].
    (* Go to IH *)  
    inv PUB.
    specialize (IH ts tp). 
    apply modusponens in IH. done. 
    apply buffered_states_related_length_eq in BSR. 
    by eapply (ss_rel_preservation_src_nil _ _ _ _ _ _ t).
  (* We are done *)
  specialize (BPART t). rewrite E, SB in BPART.
  simpl in BPART. inv BPART.
  specialize (AR _ (in_eq _ _)). unfold is_item_scratch_update in AR.  
  unfold part_update_buffer in PUB; simpl in PUB.
  by destruct k; destruct valid_alloc_range_dec; try destruct range_in_dec.
Qed.

Lemma range_allocated_restr:
  forall p n k m,
    range_allocated (p, n) k m ->
    restricted_pointer p m.
Proof.
  intros [b ofs] n k m RA.
  by apply range_allocated_consistent_with_restr in RA.
Qed.

Lemma machine_overlap_machine:
  forall p1 n1 p2 n2,
    ranges_overlap (p1, n1) (p2, n2) ->
    machine_ptr p1 ->
    machine_ptr p2.
Proof. 
  by intros [b1 o1] n1 [b2 o2] n2 O; destruct (ranges_overlapD O) as [-> _].
Qed.

Lemma alloc_unbuffer_safe:
  forall t ss ts ss' ab,
  tso_pc_ss_rel ts ss ->
  unbuffer_safe ss' ->
  disjoint_allocs ab ->
  ss.(tso_buffers) t = ss'.(tso_buffers) t ++ ab ->
  (forall t', t' <> t -> ss.(tso_buffers) t' = ss'.(tso_buffers) t') ->
  (forall r k, range_allocated r k ss'.(tso_mem) -> 
               range_allocated r k ss.(tso_mem)) ->
  unbuffer_safe ss.
Proof.
  intros t ss ts ss' ab TREL.
  generalize TREL.
  intros (_ & _ & _ & [_ _ _ _ _ [l [NDUP DOM]] _ _ _ _ _ _]).

  remember (buffers_measure l ss.(tso_buffers)) as bsize.
  revert ss ts ss' ab TREL DOM NDUP Heqbsize.
  induction bsize as [|bsize IH];
    intros ss ts ss' ab TREL DOM NDUP BM US DAL SBT SBO RAS.

  (* Base case *)
  constructor; [intros t' bi b Bs | intros t' bi b m' Bs];
    destruct (In_dec peq t' l) as [IN | NIN]; 
      try (by rewrite (buffer_measure_zero _ _ _ BM IN) in Bs);
        by rewrite DOM in Bs.

  (* Step case *)
  constructor.
  intros t' bi b Bs.
  destruct US as [ss' MABI US].
  destruct (apply_buffer_item bi (tso_mem ss)) as [m|] _eqn : FAIL. eby eexists.
  byContradiction.
  destruct bi as [pi ci vi | pi ni ki | pi ki].
      (* Write succeeds because we have more stuff allocated *)
      assert (Bs' : exists br, tso_buffers ss' t' = BufferedWrite pi ci vi :: br).
        destruct (peq t' t) as [-> | N].
          rewrite Bs in SBT. 
          destruct (tso_buffers ss' t) as [| bi' br'].
             by simpl in SBT; rewrite <- SBT in DAL.
          rewrite <- app_comm_cons in SBT. inv SBT.
          eby eexists.
        rewrite (SBO _ N) in Bs.
        eby eexists.
      destruct Bs' as [br Bs'].
      destruct (MABI _ _ _ Bs') as [m' ABI].
      simpl in ABI. 
      pose proof (store_chunk_allocated_spec ci (tso_mem ss') pi vi) as SS'. 
      pose proof (store_chunk_allocated_spec ci (tso_mem ss) pi vi) as SS.
      rewrite ABI in SS'. destruct SS' as [[r' [k' [RI' RA']]] CA].
      apply RAS in RA'.
      simpl in FAIL; rewrite FAIL in SS. apply SS.
      split. eexists; eexists; eby split. done.
    (* Allocation *)
    pose proof (alloc_cond_spec (pi, ni) ki (tso_mem ss)) as AS.
    unfold apply_buffer_item in FAIL.
    rewrite FAIL in AS.
    destruct AS as [NVAR | [NRES | [r' [k' (RO' & RA')]]]].
      elim NVAR. eby eapply tso_pc_rel_valid_alloc_range_src_buff.
      destruct TREL as [x [_ [_ [_ _ _ R _ _ _ _ _ _ _ _]]]]. clear x.
      destruct pi as [bli ?]. 
      elim NRES; unfold restricted_pointer; simpl; rewrite R; by cbv. 
    destruct ki; try eby eapply tso_ss_rel_non_stack_alloc_contr.
    destruct (machine_or_scratch pi) as [MP | SP].
      (* Use the partitioning for machine pointers *)
      destruct (alloc_stack_src_buff_impl_tgt_partition _ _ _ _ _ _ TREL Bs MP) 
        as [ts' [rt [tpr' [bp' [tp' [sp' [TREL' [RI' [BD' NIP']]]]]]]]].
      destruct TREL'.
      assert (RAt: range_allocated rt MObjStack ts'.(tso_mem)).
        apply (proj1 (proj2 (proj2 MRWPt) _)). 
        exists t'; rewrite BD'; apply in_eq.
      destruct k' as [] _eqn : Ek;
        try by specialize (NSMR r' k'); rewrite Ek in NSMR; apply NSMR in RA';
          destruct (ranges_are_disjoint RAt RA') as [[_ ?] | DISJ];
             try done; eapply ranges_disjoint_dont_overlap; 
               [apply DISJ | eby eapply overlap_inside_overlap].
      destruct (proj2 (proj2 (proj2 MRWPs) r') RA') as [tr INtr].
      destruct (peq tr t') as [-> | N].
        specialize (NIP' r' INtr).
        by pose proof (ranges_disjoint_dont_overlap _ _ NIP' RO').
      destruct r' as [p' n'].
      assert (MP': machine_ptr p'). eby eapply machine_overlap_machine.
      destruct (proj1 (TREL0 tr) _ _ MP' INtr) as [rt' [RIrt' INrt']].
      pose proof (proj1 MRWPt _ _ N _ INrt') as DISJ.
      rewrite BD' in DISJ. specialize (DISJ _ (in_eq _ _)).
      eapply ranges_disjoint_dont_overlap.
      apply DISJ.
      eapply overlap_inside_overlap, RIrt'.
      by eapply ranges_overlap_comm, overlap_inside_overlap, RI'.        
    (* Use scratch safety for scratch pointers *)
    destruct TREL as [bp [tp [sp TWREL]]].
    generalize TWREL; destruct 1.
    destruct k' as [] _eqn : Ek;
      try by specialize (NSMR r' k'); rewrite Ek in NSMR; apply NSMR in RA';
        destruct r' as [p' n'];
          apply range_allocated_restr, 
            (restricted_low_pointer_machine _ _ MCWRt) in RA';
            apply ranges_overlap_comm in RO';
              eapply machine_not_scratch, SP; eby eapply machine_overlap_machine.
    subst. 
    pose proof (alloc_stack_src_buff_impl_part_update_succ _ _ _ _ _ _ 
      _ _ TWREL Bs) as PUn. simpl in PUn.
    destruct valid_alloc_range_dec as [VAR | NVAR];
      try destruct range_in_dec as [RI | NRI]; try done.
    destruct (proj2 (proj2 (proj2 MRWPs) _) RA') as [tr INPs].
    pose proof (proj2 (proj2 SAF) tr t') as DISJ.
    rewrite Bs in DISJ. simpl in DISJ.
    destruct (low_mem_restr (MPtr.block pi)) as [] _eqn : LMR.
      destruct pi; simpl in *; rewrite LMR in *; done.
    specialize (DISJ _ (in_eq _ _) _ INPs).
    eby eapply ranges_disjoint_dont_overlap.
  (* Free *)    
  pose proof (free_cond_spec pi ki (tso_mem ss)) as FS.
  unfold apply_buffer_item in FAIL. rewrite FAIL in FS.
  destruct ki as [] _eqn : Eki;
   try( by pose proof (irrelevant_src_buff_impl_tgt_success _ _ _ _ _ 
        TREL Bs) as TGSUCC;
      destruct (TGSUCC I) as [ts' [tbr [TREL' BD']]];
        generalize TREL';
          intros [x [_ [_ [_ NSMR MCRt _ _ _ UST' _ _ _ _ _]]]];
            destruct (unbuffer_unbuffer_safe UST' BD') 
              as [tm' [ABIT _]];
                unfold apply_buffer_item in ABIT;
                  pose proof (free_cond_spec pi ki (tso_mem ts')) as FS';
                    rewrite Eki, ABIT in FS'; destruct FS' as [n' RA'];
                      specialize (NSMR (pi, n') ki); rewrite Eki in NSMR; 
                        apply NSMR in RA'; specialize (FS _ RA')).
  destruct TREL as [bp [tp [sp TWREL]]].
  pose proof (alloc_stack_src_buff_impl_part_update_succ _ _ _ _ _ _ _ _ 
    TWREL Bs) as PU.
  simpl in PU.
  destruct (pointer_in_range_list pi (sp t')) as [] _eqn : PIRL; try done.
  apply pointer_in_range_list_in in PIRL.
  destruct PIRL as [n INPs].
  apply (FS n).
  destruct TWREL.
  eapply MRWPs. eby eexists. 

  (* Proof of preservation of the induction hypothesis *)
  intros t' bi sbr sm' BD ABIs.
  destruct (ss_rel_sim _ _ _ _ _ _ TREL BD ABIs) as [ts' [UR TREL']].
  destruct (In_dec peq t' l) as [INR | NINR].
    2: by rewrite DOM in BD.
  pose proof (preserve_dom_unbuffer _ _ _ _ _ BD DOM) as NDOM.
  destruct (measure_down_unbuffer _ _ _ _ _ NDUP BD INR) 
    as [s [BS SBS]].
  rewrite <- BM in SBS. inv SBS.
  destruct (peq t' t) as [-> | N].
    rewrite SBT in BD. 
    destruct (tso_buffers ss' t) as [|bssh' bsst'] _eqn : Ebss'.
      (* Unbuffering the newly buffered allocs *)
      simpl in BD. subst. simpl in DAL.
      destruct bi as [| p n k |] _eqn : Ebi; try done. 
      destruct DAL as [NDAL DISJ].
      eapply (IH _ _ ss' sbr); try edone. 
      simpl. rewrite tupdate_s. by rewrite Ebss'.
      intros tx Nx. simpl. by rewrite tupdate_o; [rewrite SBO|]. 
      intros r' k' RA'. apply RAS in RA'. simpl.
      unfold apply_buffer_item in ABIs.
      eby eapply alloc_preserves_allocated.
    (* Unbuffering old stuff *)
    rewrite <- app_comm_cons in BD. inv BD.
    destruct (unbuffer_unbuffer_safe US Ebss') as [ssm' [ABIss' US']].
    eapply (IH _ _ (mktsostate
      (tupdate t bsst' ss'.(tso_buffers)) ssm') ab); try edone.
    simpl. by rewrite ! tupdate_s.
    intros t' Nt'. simpl. by rewrite ! tupdate_o; [apply SBO | | ].
    simpl. eby eapply sim_apply_item_preserves_alloc_impl.
  (* Unbuffering another thread *)
  pose proof BD as BD'. rewrite SBO in BD'; [|done].
  destruct (unbuffer_unbuffer_safe US BD') as [ssm' [ABIss' US']].
  eapply (IH _ _ (mktsostate 
    (tupdate t' sbr ss'.(tso_buffers)) ssm') ab); try edone.
  simpl. rewrite ! tupdate_o; try done; intro E; by rewrite E in N.
  intros t'' N''. simpl. 
    unfold tupdate. by destruct (peq t'' t'); try rewrite SBO. 
  simpl. eby eapply sim_apply_item_preserves_alloc_impl.
Qed.

(*============================================================================*)
(* Actually connecting all the above to the state                             *)
(*============================================================================*)

Inductive alloc_steps : Csharpminor.state -> 
                        list arange -> 
                        Csharpminor.state -> Prop :=
| alloc_steps_refl: forall s,
  alloc_steps s nil s
| alloc_steps_step: forall s s' s'' p n b
  (STEP : cs_step csm_globenv s (TEmem (MEalloc p n MObjStack)) s')
  (AS : alloc_steps s' b s''),
  alloc_steps s ((p, n) :: b) s''.

Tactic Notation "alloc_steps_cases" tactic(first) tactic(c) :=
    first; [
      c "alloc_steps_refl" |
      c "alloc_steps_step"].

Definition base_offset := Int.repr 8.

Fixpoint ranges_of_vars (vars: list (ident * var_kind))
                        (cenv: compilenv) 
                        (scratch_block : Z)
                        (bp : pointer)
                        : option (list arange) :=
  match vars with
    | (vid, Vscalar c) :: r =>
        match PMap.get vid cenv with
          | Var_local c' => 
            match ranges_of_vars r cenv (scratch_block + 1) bp with
              | Some rb => Some ((Ptr scratch_block base_offset, 
                                  Int.repr (size_chunk c)) :: rb)
              | None => None
            end
          | Var_stack_scalar c' offs => 
            match ranges_of_vars r cenv scratch_block bp with
              | Some rb => Some ((MPtr.add bp (Int.repr offs),
                                  Int.repr (size_chunk c)) :: rb)
              | None => None
            end
          | _ => None
        end
    | (vid, Varray sz) :: r =>
        match PMap.get vid cenv with
          | Var_stack_array offs => 
            match ranges_of_vars r cenv scratch_block bp with
              | Some rb => Some ((MPtr.add bp (Int.repr offs), 
                                  Int.repr (Zmax 1 sz)) :: rb)
              | None => None
            end
          | _ => None
        end
    | nil => Some nil
  end.

Definition get_name (v : ident * var_kind) :=
  let (n, _) := v in n.

Definition get_vkind (v : ident * var_kind) :=
  let (_, k) := v in k.

Lemma assign_variables_not_in: 
  forall vr v ids ce s ce' s',
  ~ In v (map get_name  vr) ->
  assign_variables ids vr (ce, s) = (ce', s') ->
  ce !! v = ce' !! v.
Proof.
  intro vr.

  induction vr as [|vh vt IH].
  intros; simpl in *; clarify.

  intros v ids ce s ce' s' NIN AV.
  destruct vh as [vid []]; simpl in AV;
    (assert (NINv : ~ In v (map get_name vt));
      [intro; elim NIN; simpl; by right |]);
    destruct (Identset.mem vid ids);
      specialize (IH _ _ _ _ _ _ NINv AV) ;
        rewrite PMap.gso in IH; try done; 
          intro; subst; apply NIN; left; done.
Qed.

Lemma align_size_chunk_le:
  forall n c, n <= align n (size_chunk c).
Proof. intros; apply align_le, size_chunk_pos. Qed.

Lemma array_alignment_pos:
  forall sz, array_alignment sz > 0.
Proof. 
  intro. unfold array_alignment. repeat destruct zlt; omega.
Qed.

Lemma assign_variables_mono:
  forall ids vars ge n ce sz,
    assign_variables ids vars (ge, n) = (ce, sz) ->
    n <= sz.
Proof.
  intros ids vars.
  induction vars as [|[vid [c | asz]] vt IH]; 
    intros ge n ce sz AV; simpl in *.
  (* Base case *)
  clarify; omega.
  (* Step case *)
    destruct Identset.mem; apply IH in AV;
      pose proof (align_size_chunk_le n c);
        pose proof (size_chunk_pos c); omega.
  apply IH in AV.
  pose proof (align_le n (array_alignment asz) 
    (array_alignment_pos asz)).
  pose proof (Zle_max_l 1 asz).
  omega.
Qed.

Lemma assign_variables_in:
  forall ids vars ge n ce sz,
  NoDup (map get_name vars) ->
  assign_variables ids vars (ge, n) = (ce, sz) ->
  forall v, In v vars -> 
    match ce !! (get_name v) with
      | Var_stack_scalar c ofs => n <= ofs /\ 
                                  ofs + size_chunk c <= sz /\
                                  get_vkind v = Vscalar c /\
                                  Identset.mem (get_name v) ids = true
      | Var_local c => get_vkind v = Vscalar c /\
                       Identset.mem (get_name v) ids = false
      | Var_stack_array ofs => 
                       n <= ofs /\
                       exists asz, get_vkind v = Varray asz /\
                       ofs + Zmax 1 asz <= sz
      | _ => False
    end.
Proof.
  intros ids vars.
  
  induction vars as [|vh vt IH]; intros ge n ce sz ND AV [vid vk] IN.
  
  (* Base case *)
  done.

  (* Step case *)
  simpl in IN; inversion ND as [ | vids vir NIN NDvt]; subst.                   
  destruct vh as [vhid []]; simpl in AV.
    destruct (Identset.mem vhid ids) as [] _eqn : IS.
      (* Head is an on-stack scalar *)
      destruct IN as [E | IN].
        inv E. rewrite <- (assign_variables_not_in _ _ _ _ _ _ _ NIN AV).
        simpl. rewrite PMap.gss.
        split. apply align_size_chunk_le.
        split. eby eapply assign_variables_mono.
        done.
      specialize (IH _ _ _ _ NDvt AV _ IN).
      simpl in *.
      destruct (ce !! vid); try done; split;
        pose proof (align_size_chunk_le n m); pose proof (size_chunk_pos m);
        try omega; by destruct IH.
    (* Head is a local scalar *)  
    destruct IN as [E | IN].
      inv E. rewrite <- (assign_variables_not_in _ _ _ _ _ _ _ NIN AV).
      simpl. rewrite PMap.gss. by split.
    specialize (IH _ _ _ _ NDvt AV _ IN).
    simpl in *.
    destruct (ce !! vid); try done; split;
      pose proof (align_size_chunk_le n m); pose proof (size_chunk_pos m);
        try omega; by destruct IH.
  (* Head is an array *)
  destruct IN as [E | IN].
    inv E. rewrite <- (assign_variables_not_in _ _ _ _ _ _ _ NIN AV).
    simpl. rewrite PMap.gss. 
    split. apply align_le, array_alignment_pos.
    eexists. split. reflexivity.
    eby eapply assign_variables_mono.
  specialize (IH _ _ _ _ NDvt AV _ IN).
  simpl in *.
  destruct (ce !! vid); destruct IH; split; try done;
    pose proof (align_le n _ (array_alignment_pos z));
      pose proof (Zle_max_l 1 z); omega.
Qed.  

Lemma align_size_le_divides:
  forall s s'
    (LT : s <= s'),
    (align_size s | align_size s').
Proof.
  intros.
  unfold align_size.
  repeat destruct zlt; try omegaContradiction; 
    by apply Zmod_divide. 
Qed.

Lemma align_add:
  forall s' s n ofs
    (ALn : (align_size s' | n))
    (ALo : (align_size s  | ofs))
    (Szlt: s' <= s),
      (align_size s' | ofs + n).
Proof.
  intros.
  apply Zdivide_plus_r.
    eapply Zdivide_trans, ALo.
    by apply align_size_le_divides.
  done.
Qed.

Lemma align_size_chunk:
  forall c,
    (align_size (size_chunk c) | size_chunk c).
Proof.
  intros []; simpl; compute; apply Zdivide_refl.
Qed.  

Lemma align_size_array:
  forall sz,
    (align_size (Zmax 1 sz) | array_alignment sz).
Proof.
  intro sz.
  unfold align_size, array_alignment.
  assert (Zmax 1 sz = sz \/ sz < 1 /\ Zmax 1 sz = 1).
    pose proof (Zmax_spec 1 sz).
    by destruct zlt; vauto. 
  repeat destruct zlt; try omegaContradiction; try (by apply Zmod_divide).
Qed.

(* First, we show that ranges_of_vars always succeeds for
   a correctly constructed compilenv. We also show disjointness
   and containment in the frame. *)
Lemma ranges_of_vars_succ:
  forall ids vars ge n sbp bp cenv fsize,
  NoDup (map get_name vars) ->
  MPtr.block bp < sbp ->
  assign_variables ids vars (ge, n) = (cenv, fsize) ->
  0 <= n ->
  fsize <= Int.max_unsigned ->
  valid_alloc_range (bp, Int.repr fsize) \/ fsize = 0 ->
  exists rs,
    ranges_of_vars vars cenv sbp bp = Some rs /\
    range_list_disjoint rs /\
    (forall r, In r rs -> valid_alloc_range r) /\
    forall r, In r rs -> range_inside r (bp, Int.repr fsize) /\
                          (Int.unsigned (MPtr.offset bp) + n <= 
                           Int.unsigned (MPtr.offset (fst r))) \/
                          MPtr.block (fst r) >= sbp.
Proof.
  intros ids vars.
  induction vars as [|v vr IH]; 
    intros ge n sbp bp cenv fsize ND BIEQ AV NPOS MU VAR.
  
  (* Base case *)
  eby eexists.
  
  (* Step case *)
  inversion ND as [ | vids vir NIN NDvr]; subst.
  simpl in AV.
  destruct v as [vid [c | sz]].
    destruct (Identset.mem vid ids).
      (* Stack scalar *)
      pose proof (size_chunk_pos c) as SCPOS.
      pose proof (align_size_chunk_le n c) as ASCPOS.
      assert (NPOS': 0 <= align n (size_chunk c) + size_chunk c).
        omega.
      specialize (IH _ _ sbp bp _ _ NDvr BIEQ AV NPOS' MU VAR).
      destruct IH as [rs' (ROV & RLD & VARS & RINOS)].
      eexists. split.
        pose proof (assign_variables_not_in _ _ _ _ _ _ _ NIN AV) as E.
        simpl in *. rewrite <- E, PMap.gss, ROV. reflexivity.
      pose proof (assign_variables_mono _ _ _ _ _ _ AV) as ALFS.
      unfold valid_alloc_range in VAR. 
      rewrite !Int.unsigned_repr in VAR. 2 : omega.
      split. (* Disjointness *)
        split. done.
        intros [[b' o'] n'] IN'. destruct bp as [bpb bpo].
        destruct (RINOS _ IN') as [[RIN SEP] | SCR].
          right. left. simpl in SEP.
          destruct RIN as [-> RIN]. eapply Zle_trans, SEP.
          rewrite !Int.add_unsigned, !size_chunk_repr; 
            repeat rewrite Int.unsigned_repr; try omega.
          unfold Int.max_unsigned. omega.
        left. intro E. rewrite E in *. simpl in *. omega.
      split. intros r IN. destruct IN as [<- | IN].
        unfold MPtr.add. destruct bp. unfold valid_alloc_range.
          rewrite !Int.add_unsigned; 
            repeat rewrite Int.unsigned_repr; try omega;
              unfold Int.max_unsigned; repeat split; try omega.
        destruct VAR as [(L & SZ & H & ALG) | E0]; [|omegaContradiction].
        eapply align_add.
        - eapply Zdivide_trans, align_divides, size_chunk_pos.
          apply align_size_chunk. 
        - apply ALG.
        - omega.
        by apply VARS.
      intros r IN.
      simpl in IN. destruct IN as [<- | IN].
        left. destruct bp as [bpb bpo].
        split. 
          split. done. 
          right; split;
            rewrite !Int.add_unsigned; 
              repeat rewrite Int.unsigned_repr; try omega;
                unfold Int.max_unsigned; omega.
        unfold MPtr.offset, MPtr.add, fst.
        rewrite !Int.add_unsigned; 
          repeat rewrite Int.unsigned_repr; try omega;
            unfold Int.max_unsigned; omega.
      destruct (RINOS _ IN) as [[RIN SEP] | SCR].
        left. split. done. omega. 
      by right. 
    (* Local scalar *)
    assert (BIEQ': MPtr.block bp < sbp + 1). omega.
    specialize (IH _ _ (sbp + 1) bp _ _ NDvr BIEQ' AV NPOS MU VAR).
    destruct IH as [rs' (ROV & RLD & VARS & RINOS)].
    eexists.
    split. 
      pose proof (assign_variables_not_in _ _ _ _ _ _ _ NIN AV) as E.
      simpl in *. rewrite <- E, PMap.gss, ROV. reflexivity.
    split.
      split. done.
      intros [[b' o'] n'] IN'. 
      destruct (RINOS _ IN') as [[RIN SEP] | SCR].
        left. intro E. subst. destruct bp. destruct RIN as [-> _].
        simpl in *. omega.
      left. intro E. subst. simpl in *. omega.
    split. intros r IN. destruct IN as [<- | IN].
      by destruct c; repeat split; try compute; try done;
        apply Zmod_divide.
      by apply VARS.
    intros r IN.
    simpl in IN. destruct IN as [<- | IN].
      right. simpl. omega.
    destruct (RINOS _ IN) as [[RIN SEP] | SCR].
      left. split. done. omega. 
    right. omega.
  (* On-stack array *)
  pose proof (Zle_max_l 1 sz) as SCPOS.
  pose proof (array_alignment_pos sz) as AAPOS.
  pose proof (align_le n _ AAPOS) as ASCPOS.
  assert (NPOS': 0 <= align n (array_alignment sz) + Zmax 1 sz).
    omega.
  specialize (IH _ _ sbp bp _ _ NDvr BIEQ AV NPOS' MU VAR).
  destruct IH as [rs' (ROV & RLD & VARS & RINOS)].
  eexists. split.
    pose proof (assign_variables_not_in _ _ _ _ _ _ _ NIN AV) as E.
    simpl in *. rewrite <- E, PMap.gss, ROV. reflexivity.
  pose proof (assign_variables_mono _ _ _ _ _ _ AV) as ALFS.
  unfold valid_alloc_range in VAR. 
  rewrite !Int.unsigned_repr in VAR. 2 : omega.
  split. (* Disjointness *)
    split. done.
    intros [[b' o'] n'] IN'. destruct bp as [bpb bpo].
    destruct (RINOS _ IN') as [[RIN SEP] | SCR].
      right. left. simpl in SEP.
      destruct RIN as [-> RIN]. eapply Zle_trans, SEP.
      rewrite !Int.add_unsigned; 
        repeat rewrite Int.unsigned_repr; try omega.
      unfold Int.max_unsigned. omega.
    left. intro E. rewrite E in *. simpl in *. omega.
  split. intros r IN. destruct IN as [<- | IN].
    destruct bp; unfold MPtr.add, valid_alloc_range.
    destruct VAR as [(L & SZ & H & ALG) | E0]; [|omegaContradiction].
      rewrite !Int.add_unsigned; 
        repeat rewrite Int.unsigned_repr; try omega;
          unfold Int.max_unsigned; repeat split; try omega; [].
      eapply align_add.
      - eapply Zdivide_trans. 2 : apply align_divides.
        apply align_size_array.
        apply array_alignment_pos.
      - apply ALG.
      - omega.
    by apply VARS.
  intros r IN.
  simpl in IN. destruct IN as [<- | IN].
    left. destruct bp as [bpb bpo].
    split. 
      split. done.
      right; split;
        rewrite !Int.add_unsigned; 
          repeat rewrite Int.unsigned_repr; try omega;
            unfold Int.max_unsigned; omega.
    unfold MPtr.offset, MPtr.add, fst.
    rewrite !Int.add_unsigned; 
      repeat rewrite Int.unsigned_repr; try omega;
        unfold Int.max_unsigned; omega.
  destruct (RINOS _ IN) as [[RIN SEP] | SCR].
    left. split. done. omega. 
  by right. 
Qed.


Definition alloc_item_of_range (r : arange) := 
  let (p, n) := r in BufferedAlloc p n MObjStack.

Definition alloc_items_of_ranges (rs : list arange) :=
  List.map alloc_item_of_range rs.

Lemma apply_buffer_cons_decomp:
  forall bi b m m',
  apply_buffer (bi :: b) m = Some m' ->
  exists m'', 
    apply_buffer_item bi m = Some m'' /\
    apply_buffer b m'' = Some m'.
Proof.
  intros bi b m m' AB. 
  simpl in AB.
  destruct (apply_buffer_item bi m) as [m''|] _eqn : ABI; try done.
  exists m''. by split.
Qed.

Definition cst_range_list (p : pointer) (n : Z) :=
  if zeq n 0 
    then (p, Int.repr n) :: nil
    else nil.


(* Witness environment in C#minor, given a base pointer,
   base block and frame layout. *)
Fixpoint build_csm_env (vars : list (ident * var_kind))
                       (cenv : compilenv)
                       (sbp : Z)
                       (bp : pointer) 
                       (acc : env) : env :=
  match vars with 
    | (vid, vk) :: vt =>
        match cenv !! vid with
          | Var_local c => 
              build_csm_env vt cenv (sbp + 1) bp
                            (acc ! vid <- (Ptr sbp base_offset, vk)) 
          | Var_stack_scalar c ofs =>
              build_csm_env vt cenv sbp bp
                            (acc ! vid <- (MPtr.add bp (Int.repr ofs), vk)) 
          | Var_stack_array ofs =>
              build_csm_env vt cenv sbp bp
                            (acc ! vid <- (MPtr.add bp (Int.repr ofs), vk))
          | _ => acc (* Should never get here *)
        end
    | nil => acc
  end.

Definition renv : Type := PTree.t arange.

Lemma elems_of_empty_nil:
  forall A, PTree.elements (PTree.empty A) = nil.
Proof.
  intro A.
  destruct (PTree.elements (PTree.empty A)) as [|[hk he] t] _eqn : Ee.
    done.
  assert (IN := in_eq  (hk, he) t). rewrite <- Ee in IN.
  assert (EL := PTree.elements_complete _ _ _ IN).
  by rewrite PTree.gempty in EL.
Qed.

Lemma permutation_1_eq:
  forall A l (e : A),
    Permutation l (e :: nil) ->
    l = (e :: nil).
Proof.
  intros A l e P.
  remember (e :: nil) as enil.
  induction P; subst; try done. 
    clarify. apply Permutation_sym, Permutation_nil in P. by rewrite P.
  rewrite <- IHP2 in IHP1 |- *; try done.
  by rewrite IHP1.
Qed.

Lemma nodup_map:
  forall A B (f : A -> B) (l : list A), 
    NoDup (map f l) -> NoDup l.
Proof.
  intros A B f l.
  induction l as [|h t IH]; simpl; intro ND; constructor; 
    inversion ND as [ | h' t' NIN NDvr]; subst.
    intro IN; apply NIN, in_map, IN.
  apply IH, NDvr.
Qed.

Lemma ptree_elems_1_eq:
  forall A id (x : A),
    PTree.elements (PTree.empty A) ! id <- x = (id, x) :: nil.
Proof.
  intros A id x.
  assert (P: Permutation (PTree.elements ((PTree.empty A) ! id <- x))
                         ((id, x) :: nil)).
    apply NoDup_Permutation.
        eapply nodup_map, PTree.elements_keys_norepet.
      by repeat constructor.
    intros [id' x']; split; intro IN.
      apply PTree.elements_complete in IN.
      destruct (peq id' id) as [-> | N]. 
        rewrite PTree.gss in IN; clarify. apply in_eq.
      by rewrite PTree.gso, PTree.gempty in IN. 
    simpl in IN. destruct IN as [E | ]; try done.
    inv E. apply PTree.elements_correct, PTree.gss. 
  eby eapply permutation_1_eq.
Qed.

Lemma ptree_elems_insert:
  forall A e v (x : A),
    e ! v = None ->
    Permutation ((v, x) :: (PTree.elements e))
                (PTree.elements (e ! v <- x)).
Proof.
  intros A e v x NIN.
  apply NoDup_Permutation.
      constructor. intro IN. apply PTree.elements_complete in IN.
      rewrite IN in NIN. done.
      eapply nodup_map, PTree.elements_keys_norepet.
    eapply nodup_map, PTree.elements_keys_norepet.
  intros [id' x']; split; intro IN.
    simpl in IN. destruct IN as [E | IN]; apply PTree.elements_correct.
      inv E. apply PTree.gss. 
    apply PTree.elements_complete in IN.
    destruct (peq id' v) as [-> | N]. rewrite PTree.gss. by rewrite IN in NIN.
    by rewrite PTree.gso.
  simpl.
  apply PTree.elements_complete in IN.
  destruct (peq id' v) as [-> | N]. 
    rewrite PTree.gss in IN; clarify. by left. 
  rewrite PTree.gso in IN. right. by apply PTree.elements_correct.
  done.
Qed.  

Lemma ptree_insert_2_comm:
  forall A x y (a : A) b e,
    x <> y ->
    e ! x <- a ! y <- b = e ! y <- b ! x <- a.
Proof.
  intros A x y a b e NE.
  apply PTree.ext.
  intro k.
  destruct (peq k x) as [<- | Nx];
    destruct (peq k y) as [<- | Ny];
      by repeat (try rewrite PTree.gss; try rewrite PTree.gso).
Qed.

Lemma build_env_ranges_cons_perm:
  forall v vr cenv sbp bp p vk e,
  ~ In v (map get_name vr) ->
  e ! v = None ->
  Permutation ((p, Int.repr (sizeof(vk))) :: 
                   env_ranges (build_csm_env vr cenv sbp bp e))
    (env_ranges (build_csm_env vr cenv sbp bp (e ! v <- (p, vk)))).
Proof.
  intros v vr.
  induction vr as [|vrh vrt IH]; intros cenv sbp bp p vk e NIN NENONE.
  
  (* Base case *)
  unfold env_ranges. simpl. 
  apply ptree_elems_insert with (x := (p, vk)) in NENONE.
  by apply Permutation_map 
    with (f := fun ei => csm_env_item_range (snd ei)) in NENONE.

  (* Step case *)
  simpl. 
  destruct vrh as [vid' vk']. 
  assert (NINr: ~ In v (map get_name vrt)).
    intro IN. elim NIN. simpl. by right.
  assert (NE: v <> vid'). intro E; subst. elim NIN. by left.
  destruct (cenv !! vid') as [c | c ofs | ofs | |];
    try (rewrite ptree_insert_2_comm; try done; apply IH; try done;
      rewrite PTree.gso; done);
      unfold env_ranges;
        apply ptree_elems_insert with (x := (p, vk)) in NENONE;
          by apply Permutation_map 
            with (f := fun ei => csm_env_item_range (snd ei)) in NENONE.
Qed.

Lemma env_ranges_permut_range_of_vars:
  forall vars cenv sbp bp rs er,
    NoDup (map get_name vars) ->
    ranges_of_vars vars cenv sbp bp = Some rs ->
    env_ranges (build_csm_env vars cenv sbp bp empty_env) = er ->
    Permutation rs er.
Proof.
  intros vars.
  induction vars as [|[v vk] vr IH];
    intros cenv sbp bp rs er ND ROV ER.

  (* Base case *)
  unfold env_ranges in ER.
  simpl in *.  inv ROV. by constructor. 
  
  (* Step case *)
  simpl in ER, ROV.
  simpl in ND. inversion ND as [ | vids vir NIN NDvr]; subst.
  destruct (cenv !! v) as [c | c ofs | ofs | |]; 
    destruct vk as [c' | asz]; try done. 
      destruct (ranges_of_vars vr cenv (sbp + 1) bp) as [rs'|] _eqn : Erov;
        try done; clarify.
      apply perm_trans 
        with (l' := (Ptr sbp base_offset, Int.repr (size_chunk c')) ::
          (env_ranges (build_csm_env vr cenv (sbp + 1) bp empty_env))).
        apply perm_skip. eby eapply IH.
      apply (build_env_ranges_cons_perm _ _ _ _ _ _ 
        (Vscalar c') _ NIN (PTree.gempty _ _)).
    destruct (ranges_of_vars vr cenv sbp bp) as [rs'|] _eqn : Erov;
      try done; clarify.
    apply perm_trans 
      with (l' := ((bp + Int.repr ofs)%pointer, Int.repr (size_chunk c')) ::
        (env_ranges (build_csm_env vr cenv sbp bp empty_env))).
    apply perm_skip. eby eapply IH.
      apply (build_env_ranges_cons_perm _ _ _ _ _ _ 
        (Vscalar c') _ NIN (PTree.gempty _ _)).
  destruct (ranges_of_vars vr cenv sbp bp) as [rs'|] _eqn : Erov;
    try done; clarify.
  apply perm_trans 
    with (l' := ((bp + Int.repr ofs)%pointer, Int.repr (Zmax 1 asz)) ::
      (env_ranges (build_csm_env vr cenv sbp bp empty_env))).
  apply perm_skip. eby eapply IH.
    apply (build_env_ranges_cons_perm _ _ _ _ _ _ 
      (Varray asz) _ NIN (PTree.gempty _ _)).
Qed.

Lemma range_list_disjoint_app:
  forall l1 l2,
    range_list_disjoint (l1 ++ l2) <->
    range_list_disjoint l1 /\
    range_list_disjoint l2 /\
    range_lists_disjoint l1 l2.
Proof.
  intros l1 l2. 
  
  induction l1 as [|h t IH].

  simpl. repeat (split; try done). 
  by intros (_ & RLD & _). 
  
  rewrite <- app_comm_cons. simpl.
  split.
    intros (RLD & RNI).
    apply IH in RLD. destruct RLD as (RLDt & RLDl2 & RLSD).
    split. split. done. 
      intros r IN. apply RNI, in_or_app. by left.
    split. done. 
    intros r1 IN1 r2 IN2. simpl in IN1. 
    destruct IN1 as [-> | IN1].
      apply RNI, in_or_app. by right.
    by apply RLSD.
  intros ((RLDt & RNI) & RLDl2 & RLSD).
  split. 
    apply IH.
    split. done.
    split. done.
    intros r1 IN1 r2 IN2. apply RLSD. by apply in_cons. done.
  intros r IN.
  apply in_app_or in IN. destruct IN as [IN | IN].
    by apply RNI.
  apply RLSD. apply in_eq. done.
Qed.

Lemma range_list_disjoint_perm:
  forall l l',
    Permutation l l' ->
    range_list_disjoint l ->
    range_list_disjoint l'.
Proof.
  intro l.
  
  induction l as [|h t IH]; intros l' P RLD.
  by rewrite Permutation_nil.

  pose proof (Permutation_in _ P (in_eq _ _)) as IN.
  destruct (In_split _ _ IN) as [l1 [l2 ->]].
  simpl in RLD; destruct RLD as [RLD RNI].
  apply Permutation_cons_app_inv in P. 
  specialize (IH _ P RLD).
  destruct (proj1 (range_list_disjoint_app _ _) IH) as (RLDl1 & RLD2 & RLSD).
  apply (proj2 (range_list_disjoint_app _ _)).
  split. done.
  split. split. done.
    intros r' IN'. apply RNI. apply Permutation_sym in P.
    apply (Permutation_in _ P). apply in_or_app. by right.
  intros r1 IN1 r2 IN2.
  simpl in IN2. destruct IN2 as [-> | IN2].
    apply ranges_disjoint_comm, RNI. apply Permutation_sym in P.
    apply (Permutation_in _ P). apply in_or_app. by left.
  by apply RLSD.
Qed.

Definition mkcstenv (p : pointer) (n : Z) 
                    (e : PTree.t Cstacked.env_item) : Cstacked.env :=
  mkcsenv (if zeq n 0 then None else (Some p)) e.

Lemma env_item_related_mem_alloc:
  forall m sz bp ei1 ei2 p n k m',
    env_item_related m sz bp ei1 ei2 ->
    alloc_ptr (p, n) k m = Some m' ->
    env_item_related m' sz bp ei1 ei2.
Proof.
  intros m sz bp ei1 ei2 p n k m' EIR AP.
  inv EIR; econstructor; try edone.
  eby eapply load_some_alloc.
Qed.

Definition scratch_min_block := 1.

Lemma scratch_less_block:
  forall b,
    scratch_min_block <= b ->
    low_mem_restr b = false.
Proof.
  intros b.
  unfold low_mem_restr.
  destruct (zeq b 0) as [-> | N]; try done. 
  unfold scratch_min_block. intro; omegaContradiction.
Qed.

Definition local_cons_with_ids (te : PTree.t Cstacked.env_item)
                               (ids : Identset.t) : Prop :=
  forall id,
    match te ! id with
      | Some (Env_local _ _) => Identset.mem id ids = false 
      | _ => True
    end.

Lemma buffer_alloc_env_related:
  forall env' f opt ids vars cenv sbp bp rs vs k te te' se se' m m' ge n fsize,
    ranges_of_vars vars cenv sbp bp = Some rs ->
    apply_buffer (alloc_items_of_ranges rs) m = Some m' ->
    build_envmap vars cenv te = Some te' ->
    NoDup (map get_name vars) ->
    MPtr.block bp < sbp ->
    scratch_min_block <= sbp ->
    assign_variables ids vars (ge, n) = (cenv, fsize) ->
    0 <= n ->
    fsize <= Int.max_unsigned ->
    valid_alloc_range (bp, Int.repr fsize) \/ fsize = 0 ->
    build_csm_env vars cenv sbp bp se = se' ->
    env_items_related (Int.repr fsize) m
                      (mkcstenv bp fsize te) se ->
    local_cons_with_ids te ids ->
    alloc_steps (SKalloc vs vars se (Kcall opt (Internal f) env' k))
                rs
                (SKalloc vs nil se' (Kcall opt (Internal f) env' k)) /\
    env_items_related (Int.repr fsize) m'
                      (mkcstenv bp fsize te') se' /\
    local_cons_with_ids te' ids.
Proof.
  intros env' f opt ids vars.
  
  induction vars as [|v vr IH]; 
    intros cenv sbp bp rs vs k te te' se se' m m' ge n fsize
      ROV AB BEM ND UM SBPSCR AV NPOS FSIZEL VAR BE ER LCI.
  
  (* Base case *)
  simpl in ROV. clarify. simpl in AB, BEM. clarify.
  split. econstructor. done.

  (* Step case *)
  inversion ND as [ | vids vir NIN NDvr [E1 E2]].
  simpl in ROV. simpl in AV.
  destruct v as [vid [c | sz]].
    destruct (Identset.mem vid ids) as [] _eqn : ISM.
      (* Stack scalar *)
      pose proof (size_chunk_pos c) as SCPOS.
      pose proof (align_size_chunk_le n c) as ASCPOS.
      assert (NPOS': 0 <= align n (size_chunk c) + size_chunk c).
        omega.
      pose proof (assign_variables_not_in _ _ _ _ _ _ _ NIN AV) as E. simpl in E.
      simpl in BEM, BE. 
      rewrite <- E, PMap.gss in ROV, BEM, BE. 
      destruct (ranges_of_vars vr cenv sbp bp) as [|rs'] _eqn : Erov; [| done].
      injection ROV as Er; rewrite <- Er in *; clear Er.
      unfold alloc_items_of_ranges in AB. simpl map in AB.
      apply apply_buffer_cons_decomp in AB. destruct AB as [mi (ABI & AB)].
      specialize (IH _ _ _ _ vs k _ _ _ se' _ _ _ _ _ 
        Erov AB BEM NDvr UM SBPSCR AV NPOS' FSIZEL VAR BE).
      exploit IH.
          intro id. simpl.
          destruct (peq id vid) as [-> | N]. 
            rewrite ! PTree.gss.
            apply assign_variables_mono in AV.
            destruct (zeq fsize 0) as [-> | Nf0]. omegaContradiction.
            eapply env_item_related_scalar. omega.
            rewrite Zmod_small. done. unfold Int.max_unsigned in FSIZEL. omega.
          rewrite ! PTree.gso; try done.
          pose proof (ER id) as ERid. simpl in ERid.
          destruct (te ! id); destruct (se ! id); try done.        
          eby eapply env_item_related_mem_alloc.
        intro id. destruct (peq id vid) as [-> | N].
          by rewrite PTree.gss. 
        rewrite PTree.gso. apply (LCI id). done.
      intros [AS EIR].
      split; [|done].
      eapply alloc_steps_step. 2 : apply AS.
      by eapply StepAllocLocal.
    (* Local variable *)
    assert (BIEQ': MPtr.block bp < sbp + 1). omega.
    pose proof (assign_variables_not_in _ _ _ _ _ _ _ NIN AV) as E. simpl in E.
    simpl in BEM, BE.
    rewrite <- E, PMap.gss in ROV, BEM, BE. 
    destruct (ranges_of_vars vr cenv (sbp+1) bp) as [|rs'] _eqn : Erov; [| done].
    injection ROV as Er; rewrite <- Er in *; clear Er.
    unfold alloc_items_of_ranges in AB. simpl map in AB.
    apply apply_buffer_cons_decomp in AB. destruct AB as [mi (ABI & AB)].
    assert (SBPSCR' : scratch_min_block <= sbp + 1). omega.
    specialize (IH _ (sbp + 1) bp _ vs k _ _ _ se' _ _ _ _ _ 
      Erov AB BEM NDvr BIEQ' SBPSCR' AV NPOS FSIZEL VAR BE).
    exploit IH.
        intro id. simpl.
        destruct (peq id vid) as [-> | N]. 
          rewrite ! PTree.gss.
          eapply env_item_related_local.
          eapply load_alloc_inside. 
              unfold apply_buffer_item in ABI. apply ABI.
            apply range_inside_refl.
          unfold pointer_chunk_aligned, base_offset, align_chunk. 
          by destruct c; compute; apply Zmod_divide; try compute.
          by apply scratch_less_block.
          done. 
          split. by compute.
          repeat (split; [by by destruct c; simpl; compute|]). 
          by destruct c; compute; apply Zmod_divide.
          by destruct c. 
        rewrite ! PTree.gso; try done.
        pose proof (ER id) as ERid. simpl in ERid.
        destruct (te ! id); destruct (se ! id); try done.        
        eapply env_item_related_mem_alloc. edone.
        unfold apply_buffer_item in ABI. apply ABI.
      intro id. destruct (peq id vid) as [-> | N].
        by rewrite PTree.gss. 
      rewrite PTree.gso. apply (LCI id). done.
    intros [AS EIR].
    split; [|done].
    eapply alloc_steps_step. 2 : apply AS.
    by econstructor. 
  (* Array variable *)
  pose proof (array_alignment_pos sz) as SCPOS.
  pose proof (align_le n (array_alignment sz) 
    (array_alignment_pos sz)) as ASCPOS.
  pose proof (Zle_max_l 1 sz).
  assert (NPOS': 0 <= align n (array_alignment sz) + Zmax 1 sz).
    omega.
  pose proof (assign_variables_not_in _ _ _ _ _ _ _ NIN AV) as E. simpl in E.
  simpl in BEM, BE. 
  rewrite <- E, PMap.gss in ROV, BEM, BE. 
  destruct (ranges_of_vars vr cenv sbp bp) as [|rs'] _eqn : Erov; [| done].
  injection ROV as Er; rewrite <- Er in *; clear Er.
  unfold alloc_items_of_ranges in AB. simpl map in AB.
  apply apply_buffer_cons_decomp in AB. destruct AB as [mi (ABI & AB)].
  specialize (IH _ _ _ _ vs k _ _ _ se' _ _ _ _ _ 
    Erov AB BEM NDvr UM SBPSCR AV NPOS' FSIZEL VAR BE).
  exploit IH.
      intro id. simpl.
      destruct (peq id vid) as [-> | N]. 
        rewrite ! PTree.gss.
        apply assign_variables_mono in AV.
        destruct (zeq fsize 0) as [-> | Nf0]. omegaContradiction.
        eapply env_item_related_array. omega.
        rewrite Zmod_small. done. unfold Int.max_unsigned in FSIZEL. omega.
      rewrite ! PTree.gso; try done.
      pose proof (ER id) as ERid. simpl in ERid.
      destruct (te ! id); destruct (se ! id); try done.        
      eby eapply env_item_related_mem_alloc.
    intro id. destruct (peq id vid) as [-> | N].
      by rewrite PTree.gss. 
    rewrite PTree.gso. apply (LCI id). done.
  intros [AS EIR].
  split; [|done].
  eapply alloc_steps_step. 2 : apply AS.
  by eapply StepAllocLocal.
Qed.

Lemma update_buffer_allocs:
  forall als sp,
    (forall r, In r als -> valid_alloc_range r) ->
    range_list_disjoint als ->
    range_lists_disjoint als sp ->
    part_update_buffer (alloc_items_of_ranges als) sp =
      Some (rev als ++ sp).
Proof.
  intros als.
  induction als as [|h t IH].

  intros. unfold part_update_buffer. done.

  intros sp VARS RLD RLSD.
  specialize (IH (h :: sp)).
  exploit IH.
        intros r IN. by apply VARS, in_cons. 
      by destruct RLD.
    intros r1 IN1 r2 IN2.
    simpl in IN2. destruct IN2 as [<- | IN2]. 
      by apply ranges_disjoint_comm, (proj2 RLD).
    apply RLSD. by apply in_cons. done.
  unfold part_update_buffer. simpl.
  intros PUB.
  destruct (part_update (alloc_item_of_range h) sp) as [spi|] _eqn : PU;
    destruct h as [p n]; simpl in PU;
      destruct valid_alloc_range_dec as [|NVAR]; try done;
        try destruct range_in_dec as [[r' [IN OVER]] |]; try done. 
      inv PU. rewrite app_ass. done.
    byContradiction.
    eapply ranges_disjoint_dont_overlap, OVER. 
    apply RLSD. apply in_eq. done.
  elim NVAR. apply VARS, in_eq.
Qed.
    
Lemma buffers_related_part_update:
  forall {tb tp bp sp},
    buffers_related tb tp bp sp ->
    (exists tp',
      part_update_buffer tb tp = Some tp') /\
    (exists sp',
      part_update_buffer (flatten bp) sp = Some sp').
Proof.
  intros tb tp bp sp BR.
  (buffers_related_cases (induction BR) Case); 
    unfold part_update_buffer in *.

  Case "buffers_related_empty".
    eby split; eexists; simpl.

  Case "buffers_related_alloc".
    destruct IHBR as [[tp' PUB'] [spx PUBsx]].
    split.
      exists tp'; simpl; destruct valid_alloc_range_dec;
        try destruct range_in_dec as [[r' [IN OVER]]|];
          try destruct (ranges_disjoint_dont_overlap _ _ (RIN _ IN) OVER); done.
    exists spx. simpl. rewrite fold_left_opt_app. by rewrite PUB.    
    
  Case "buffers_related_free".
    destruct IHBR as [[tp' PUB'] [spx PUBsx]].
    split.
      exists tp'; simpl; by destruct MPtr.eq_dec.
    exists spx; simpl; rewrite fold_left_opt_app; by rewrite PUB.
    
  Case "buffers_related_other".
    destruct IHBR as [[tp' PUB'] [spx PUBsx]].
    split.
      exists tp'; simpl; 
        by rewrite (buffer_item_irrelevant_part_update _ _ BIIR).
    exists spx. simpl. 
    rewrite (buffer_item_irrelevant_part_update _ _ BIIR). simpl.
    rewrite fold_left_opt_app; by rewrite PUB.
Qed.

Lemma unbuffer_safe_partition_alloc:
  forall tso tb tp t p n tp', 
  unbuffer_safe tso ->
  mem_related_with_partitioning tso.(tso_mem) tp ->
  (tso_buffers tso t) = tb ++ BufferedAlloc p n MObjStack :: nil ->
  part_update_buffer tb (tp t) = Some tp' ->
  range_not_in (p, n) tp'.
Proof.
  intros [bufs m] tb tp t p n tp' US MRWP TB PUB.
  destruct (unbuffer_unbuffer_safe_app _ _ _ _ US TB) as [m' AB].
  assert (US' := apply_buffer_unbuffer_safe _ _ _ _ _ _ US TB AB).
  assert (MRWP' := apply_buffer_preserves_mem_partitioning _ _ _ _ _ _ 
    MRWP AB PUB).
  inversion US' as [tso' ABI' _]. subst.
  specialize (ABI' t (BufferedAlloc p n MObjStack) nil).
  exploit ABI'. simpl. by rewrite tupdate_s. 
  intros [m'' ABI'']. unfold apply_buffer_item in ABI''. 
  simpl tso_mem in ABI''.
  intros r' IN'.
  assert (AS := alloc_cond_spec (p, n) MObjStack m').
  rewrite ABI'' in AS. destruct AS as (_ & _ & _ & OV).
  destruct (ranges_disjoint_dec (p, n) r') as [DISJ | OVER].
    done.
  eelim OV. edone.
  eapply (proj2 (proj2 MRWP') r'). exists t. by rewrite update_partitioning_s.
Qed.

Lemma unbuffer_safe_partition_alloc_pub:
  forall tso tb tp t p n tp', 
  unbuffer_safe tso ->
  mem_related_with_partitioning tso.(tso_mem) tp ->
  (tso_buffers tso t) = tb ++ BufferedAlloc p n MObjStack :: nil ->
  part_update_buffer tb (tp t) = Some tp' ->
  part_update_buffer (tb ++ BufferedAlloc p n MObjStack :: nil) (tp t) =
    Some ((p, n) :: tp').
Proof.
  intros tso tb tp t p n tp' US MRWP BD PUB.
  unfold part_update_buffer in *.

  pose proof (unbuffer_safe_partition_alloc _ _ _ _ _ _ _ US MRWP BD PUB) 
    as RNI.
  pose proof (no_unbuffer_errors _ t US) as ABN. rewrite BD in ABN.
  rewrite apply_buffer_app in ABN. 
  destruct (apply_buffer tb (tso_mem tso)) as [m'|] _eqn : AB'; try done.
  unfold apply_buffer, apply_buffer_item, optbind in ABN.
  pose proof (alloc_cond_spec (p, n) MObjStack m') as AS.
  destruct (alloc_ptr (p, n) MObjStack m') as [m''|]; try done.
  destruct AS as (_ & VAR & RP & _). 

  rewrite fold_left_opt_app, PUB. simpl.
  destruct valid_alloc_range_dec; try done.
  destruct (range_in_dec (p, n) tp') as [[r' [IN OVER]] | _].
    elim OVER. by apply RNI.
  done.
Qed.

Lemma states_related_suffix:
  forall sb tb tp sp sm ts ss tp' sp' sm' ts' ss' sb' tb',
  (state_related tp sp sm ts ss ->
   buffered_states_related tb tp ts' sb sp sm ss') ->
  buffered_states_related tb' tp' ts sb' sp' sm' ss ->
  apply_buffer sb' sm' = Some sm ->
  part_update_buffer sb' sp' = Some sp ->
  part_update_buffer tb' tp' = Some tp ->
  buffered_states_related (tb' ++ tb) tp' ts' (sb' ++ sb) sp' sm' ss'.
Proof.
  intros sb tb tp sp sm ts ss tp' sp' sm' ts' ss' sb' tb' SIMPL
    BSR' AB PUBs PUBt.
  destruct BSR' as [smi [spi [tpi (ABi & PUBti & PUBsi & SR' & SCO')]]].
  rewrite PUBt in PUBti. inv PUBti.
  rewrite PUBs in PUBsi. inv PUBsi.
  rewrite AB in ABi. inv ABi.
  destruct (SIMPL SR') as [sm [sp [tp (AB' & PUBt' & PUBs' & SR & SCO)]]].
  exists sm. exists sp. exists tp.
  unfold part_update_buffer in *.
  split.
    by rewrite apply_buffer_app, AB.
  split.
    by rewrite fold_left_opt_app, PUBt.
  split.
    by rewrite fold_left_opt_app, PUBs.
  done.
Qed.

(** There is always an upper bound on all blocks appearing in memory and 
    buffers *)
Definition block_bound_buff (bnd : Z) (b : list buffer_item) : Prop :=
  forall blk ofs n, 
    In (BufferedAlloc (Ptr blk ofs) n MObjStack) b -> blk < bnd.

Definition block_bound_buffers (bnd : Z) (tso : tso_state) : Prop :=
  forall t, block_bound_buff bnd (tso_buffers tso t).

Lemma block_bound_buff_exists:
  forall b, exists bb, block_bound_buff bb b.
Proof.
  induction b as [|h t IH].
  
  by exists 0.
  
  destruct IH as [bb BB].
  buffer_item_cases (destruct h as [p c v|p n k|p k]) Case.

  Case "BufferedWrite".
    exists bb; intros blk ofs n IN; simpl in IN;
    destruct IN as [E | IN]; [done|exact (BB _ _ _ IN)].

  Case "BufferedAlloc".
    destruct k;
      try (exists bb; intros blk ofs n' IN; simpl in IN;
        destruct IN as [E | IN]; [done|exact (BB _ _ _ IN)]).
    destruct p as [b ofs].
    destruct (Zle_or_lt bb b).
      exists (b + 1). 
      intros blk' ofs' n' IN; simpl in IN. 
      destruct IN as [E | IN]. inv E. omega.
      specialize (BB _ _ _ IN). omega.
    exists bb. 
      intros blk' ofs' n' IN; simpl in IN. 
      destruct IN as [E | IN]. by inv E. 
      exact (BB _ _ _ IN).
    
  Case "BufferedFree".
    exists bb; intros blk ofs n IN; simpl in IN;
    destruct IN as [E | IN]; [done|exact (BB _ _ _ IN)].
Qed.

Lemma block_bound_from_fin_sup:
  forall tso,
    tso_fin_sup tso ->
    exists bb, block_bound_buffers bb tso.
Proof.
  intros tso [l [ND NEN]]; revert tso NEN.

  induction l as [|h l IH]; intros tso NEN.
  
  exists 0.
  intros t b ofs n. by rewrite (NEN t). 

  inversion ND as [|? ? NI' ND']; subst. 
  specialize (IH ND' (mktsostate
                                 (tupdate h nil tso.(tso_buffers))
                                 tso.(tso_mem)) ).
  exploit IH. 
    intros t' NIN; simpl.
    destruct (peq t' h) as [-> | N].
      by rewrite tupdate_s.
    rewrite tupdate_o; [|done].
    apply NEN. intro IN. simpl in IN. destruct IN as [-> | IN]; done.
  intros [bb BB]. unfold block_bound_buffers in BB. simpl in BB.
  destruct (block_bound_buff_exists (tso_buffers tso h)) as [bbb BBB].
  destruct (Zle_or_lt bb bbb).
    exists bbb.
    intros t b ofs n IN. specialize (BB t).
    destruct (peq t h) as [-> | N].
      apply (BBB _ _ _ IN).
    rewrite tupdate_o in BB; [|done].
    specialize (BB _ _ _ IN). omega.
  exists bb.
  intros t b ofs n IN. specialize (BB t).
  destruct (peq t h) as [-> | N].
    specialize (BBB _ _ _ IN). omega.
  rewrite tupdate_o in BB; [|done].
  apply (BB _ _ _ IN). 
Qed.

Definition is_mem_block_bound (bnd : Z) (m : mem) : Prop :=
  forall b ofs n k,
    range_allocated ((Ptr b ofs), n) k m -> b < bnd.

Lemma mem_bound_exists:
  forall m, exists bnd, is_mem_block_bound bnd m.
Proof.
  intros m.
  destruct (proj1 (mvalid m)) as [bnd B].
  exists (bnd + 1). intros b ofs n k RA.
  simpl in RA.
  destruct (Zle_or_lt (bnd + 1) b); [|done].
  exploit (B b). omega.
  intro G; rewrite G in RA. simpl in RA. done. 
Qed.

Definition tso_memory_upper_bound (bnd : Z) (tso : tso_state) : Prop :=
  block_bound_buffers bnd tso /\
  is_mem_block_bound bnd tso.(tso_mem) /\
  scratch_min_block <= bnd.

Lemma block_bound_buffers_mono:
  forall bnd bs bnd',
    block_bound_buffers bnd bs ->
    bnd <= bnd' ->
    block_bound_buffers bnd' bs.
Proof.
  intros bnd bs bnd' BB LE.
  intros t blk ofs n IN.
  pose proof (BB t blk ofs n IN). omega.
Qed.

Lemma mem_block_bound_mono:
  forall bnd m bnd',
    is_mem_block_bound bnd m ->
    bnd <= bnd' ->
    is_mem_block_bound bnd' m.
Proof.
  intros bnd m bnd' MB LE b ofs n k RA.
  pose proof (MB b ofs n k RA). omega.
Qed.

Lemma tso_memory_upper_bound_exists:
  forall tso,
    tso_fin_sup tso ->
    exists bb, tso_memory_upper_bound bb tso.
Proof.
  intros tso FS.
  destruct (mem_bound_exists tso.(tso_mem)) as [mb MB].
  destruct (block_bound_from_fin_sup _ FS) as [bb BB].
  exists (Zmax 1 (Zmax bb mb)).
  split.
    eapply block_bound_buffers_mono. apply BB.
    eapply Zle_trans. 2: apply Zmax2. apply Zmax1.
  split.
    eapply mem_block_bound_mono. apply MB.
    eapply Zle_trans. 2: apply Zmax2. apply Zmax2.
  apply Zmax1.
Qed.

Record is_buffer_ins (t : thread_id)
                     (b : list buffer_item)
                     (tso tso' : tso_state) : Prop :=
  mk_is_buffer_ins {
    is_buffer_ins_s : tso'.(tso_buffers) t = tso.(tso_buffers) t ++ b;
    is_buffer_ins_o : forall t', t' <> t -> tso'.(tso_buffers) t' = 
                                            tso.(tso_buffers) t';
    is_buffer_ins_m : tso'.(tso_mem) = tso.(tso_mem)}.

(*Definition is_buffer_ins (t : thread_id)
                         (b : list buffer_item)
                         (tso tso' : tso_state) : Prop :=
  tso'.(tso_buffers) t = tso.(tso_buffers) t ++ b /\
  (forall t', t' <> t -> tso'.(tso_buffers) t' = tso.(tso_buffers) t') /\
  tso'.(tso_locked) = tso.(tso_locked) /\
  tso'.(tso_mem) = tso.(tso_mem). *)

Lemma buffer_scratch_ranges_app:
  forall b1 b2,
    buffer_scratch_ranges b1 ++ buffer_scratch_ranges b2 =
    buffer_scratch_ranges (b1 ++ b2).
Proof.
  intros b1 b2.
  induction b1 as [|h b1 IH]. done.
  destruct h as [p c v|p n []|p []]; try done.
  simpl. destruct low_mem_restr. done.
  rewrite <- app_comm_cons. by rewrite <- IH.
Qed.

Lemma buffer_scratch_ranges_in:
  forall r rs,
    In r (buffer_scratch_ranges (alloc_items_of_ranges rs)) ->
    In r rs.
Proof.
  intros r rs.
  induction rs as [|[p n] rs IH]. done.
  simpl. 
  unfold alloc_item_of_range.
  destruct low_mem_restr. intro. right. by apply IH.
  simpl. 
  intros [<- | IN]. by left.
  right. apply IH, IN.
Qed.

Lemma range_list_disjoint_buffer_scratch_ranges:
  forall rs,
    range_list_disjoint rs ->
    range_list_disjoint (buffer_scratch_ranges (alloc_items_of_ranges rs)).
Proof.
  induction rs as [|h rs IH]. done.
  simpl.
  intros [RLD RNI].
  specialize (IH RLD).
  destruct (alloc_item_of_range h) as [p c v|p n []|p []] _eqn : E; try done.
  destruct low_mem_restr. done.
  unfold alloc_item_of_range in E. destruct h. inv E.
  simpl. split. done.
  intros r IN. apply buffer_scratch_ranges_in in IN.
  exact (RNI r IN).
Qed.

Lemma block_bound_scratch_range_bound:
  forall bnd b buff ofs n,
    block_bound_buff bnd buff ->
    In ((Ptr b ofs), n) (buffer_scratch_ranges buff) ->
    b < bnd.
Proof.
  intros bnd b buff ofs n.
  induction buff as [|h buff IH]. done.

  unfold block_bound_buff in *.
  simpl. intros BBB IN.
  apply modusponens in IH.
    destruct h as [p c v|p n' []|p k]; try by apply IH.
    destruct low_mem_restr. by apply IH.
    simpl in IN.
    destruct IN as [E | IN]. 
      inv E; eapply BBB; eby left.
    by apply IH.

  intros blk' ofs' n' IN'. 
  eapply BBB. eby right.
Qed.

Lemma scratch_allocs_fresh_app:
  forall tso sp t rs tso' bnd,
  mem_related_with_partitioning tso.(tso_mem) sp ->
  scratch_allocs_fresh tso.(tso_buffers) sp ->
  is_buffer_ins t (alloc_items_of_ranges rs) tso tso' ->
  (forall p n, In (p, n) rs -> machine_ptr p \/
                               bnd <= MPtr.block p) ->
  range_list_disjoint rs ->
  tso_memory_upper_bound bnd tso ->
  scratch_allocs_fresh tso'.(tso_buffers) sp.
Proof.
  intros tso sp t rs tso' bnd 
    MRWP SAF [BA OB ME] LBND RLD (BBND & MBND & SMB).
  split. (* Disjointness within buffer of one thread *)
    intros t'.
    destruct (peq t' t) as [-> | N].
      rewrite BA. rewrite <- buffer_scratch_ranges_app.
      apply <- range_list_disjoint_app.
      split. exact (proj1 SAF t).
      split. by apply range_list_disjoint_buffer_scratch_ranges. 
      intros [[b ofs] n] IN [[b' ofs'] n'] IN'.
      pose proof (buffer_scratch_ranges_are_scratch _ _ _ IN') as SCR.
      apply buffer_scratch_ranges_in in IN'.
      specialize (LBND _ _ IN').
      destruct LBND as [MP | HB]. 
        byContradiction. eby eapply machine_not_scratch.
      pose proof (block_bound_scratch_range_bound _ _ _ _ _ (BBND t) IN) as LB.
      left. simpl in HB. omega.
    rewrite OB. apply (proj1 SAF t'). done.
  split. (* Disjoints between different threads' buffers, very similar 
            to the previous case, but hard to factor out... *)
    intros t1 t2 N12 [[b1 o1] n1] IN1 [[b2 o2] n2] IN2.
    destruct (peq t1 t) as [-> | N].
      rewrite OB in IN1; [|intro E; by rewrite E in N12].
      rewrite BA, <- buffer_scratch_ranges_app in IN2.
      apply in_app_or in IN2.
      destruct IN2 as [IN2 | IN2]. 
      exact (proj1 (proj2 SAF) t t2 N12 _ IN1 _ IN2).
      pose proof (buffer_scratch_ranges_are_scratch _ _ _ IN2) as SCR.
      apply buffer_scratch_ranges_in in IN2.
      specialize (LBND _ _ IN2).
      destruct LBND as [MP | HB]. 
        byContradiction. eby eapply machine_not_scratch.
      assert (LB := block_bound_scratch_range_bound _ _ _ _ _ (BBND t2) IN1).
      left. simpl in HB. omega.
    rewrite OB in IN2; [|done].
    destruct (peq t2 t) as [-> | N2].
      rewrite BA, <- buffer_scratch_ranges_app in IN1.
      apply in_app_or in IN1.
      destruct IN1 as [IN1 | IN1]. 
      exact (proj1 (proj2 SAF) t1 t N12 _ IN1 _ IN2).
      pose proof (buffer_scratch_ranges_are_scratch _ _ _ IN1) as SCR.
      apply buffer_scratch_ranges_in in IN1.
      specialize (LBND _ _ IN1).
      destruct LBND as [MP | HB]. 
        byContradiction. eby eapply machine_not_scratch.
      assert (LB := block_bound_scratch_range_bound _ _ _ _ _ (BBND t1) IN2).
      left. simpl in HB. omega.
    rewrite OB in IN1; [|done].
    exact (proj1 (proj2 SAF) t1 t2 N12 _ IN1 _ IN2).
  (* Disjointness from partitions *)
  intros t1 t2 [[b1 o1] n1] IN1 [[b2 o2] n2] IN2.
  destruct (peq t2 t) as [-> | N2].
    rewrite BA, <- buffer_scratch_ranges_app in IN1.
    apply in_app_or in IN1.
    destruct IN1 as [IN1 | IN1]. exact (proj2 (proj2 SAF) t1 t _ IN1 _ IN2).
    pose proof (buffer_scratch_ranges_are_scratch _ _ _ IN1) as SCR.
    apply buffer_scratch_ranges_in in IN1.
    specialize (LBND _ _ IN1).
    destruct LBND as [MP | HB]. 
      byContradiction. eby eapply machine_not_scratch.
    assert (RA : range_allocated (Ptr b2 o2, n2) MObjStack tso.(tso_mem)).
      apply -> (proj2 (proj2 MRWP)). eby eexists.
    apply MBND in RA.
    left. simpl in HB. omega.
  rewrite OB in IN1; [|done].    
  exact (proj2 (proj2 SAF) t1 t2 _ IN1 _ IN2).
Qed.  

Lemma in_buffer_scratch_ranges:
  forall rs p1 n1
    (SC : scratch_ptr p1)
    (IN : In (p1, n1) rs),
      In (p1, n1) (buffer_scratch_ranges (alloc_items_of_ranges rs)).
Proof.
  induction rs as [|h rs IH]. done.

  intros.
  simpl in IN. destruct IN as [-> | IN].
    simpl. destruct (low_mem_restr (MPtr.block p1)) as [] _eqn : E.
    destruct p1; simpl in *; by rewrite SC in *.
    apply in_eq.
  simpl. 
  destruct (alloc_item_of_range h) as [| n k [] |]; try eby eapply IH.
  destruct low_mem_restr. eby eapply IH.
  simpl. right.  eby eapply IH.
Qed.

Lemma new_alloc_disjoint:
  forall p n tp rs sp 
    (RNI : range_not_in (p, n) tp)
    (MP : machine_ptr p)
    (INS : forall (p' : pointer) (n' : int),
             In (p', n') rs -> range_inside (p', n') (p, n) \/ scratch_ptr p')
    (RLD : range_lists_disjoint
              (buffer_scratch_ranges (alloc_items_of_ranges rs)) sp)
    (PI : partition_injective tp sp),
      range_lists_disjoint rs sp.
Proof.
  intros.
  intros [p1 n1] IN1 [p2 n2] IN2.
  destruct (machine_or_scratch p1) as [MP1 | SC1].
    (* p1 is machine pointer *)
    destruct (INS _ _ IN1) as [RNIN | SP]. 
      2 : byContradiction; eby eapply machine_not_scratch.
    eapply disjoint_inside_disjoint, RNIN.
    destruct (machine_or_scratch p2) as [MP2 | SC2].
      2 : eby eapply machine_scratch_disjoint.
    destruct (PI _ _ MP2 IN2) as [r [RIr INr]].
    specialize (RNI _ INr). apply ranges_disjoint_comm in RNI.
    eapply ranges_disjoint_comm, disjoint_inside_disjoint.
    apply RNI. done.
  (* p1 is scratch pointer *)
  destruct (machine_or_scratch p2) as [MP2 | SC2].
    eby eapply ranges_disjoint_comm, machine_scratch_disjoint.
  pose proof (in_buffer_scratch_ranges _ _ _ SC1 IN1) as IN1a.
  exact (RLD _ IN1a _ IN2).
Qed.

Lemma parts_disjoint_to_buffers_related:
  forall p n tp rs sp
  (RLD:  range_lists_disjoint rs sp)
  (RNI : range_not_in (p, n) tp)
  (VAR : valid_alloc_range (p, n))
  (DISJ: range_list_disjoint rs)
  (VARs : forall r, In r rs -> valid_alloc_range r)
  (INS : forall p' n', In (p', n') rs -> range_inside (p', n') (p, n) \/
                                         scratch_ptr p'),
    buffers_related (BufferedAlloc p n MObjStack :: nil) tp
                    (alloc_items_of_ranges rs :: nil) sp.
Proof.
  intros.
  econstructor; try done. 3 : econstructor.
    intros bi IN. 
    unfold alloc_items_of_ranges in IN. apply in_map_iff in IN.
    destruct IN as [r [<- IN]].
    destruct r; destruct (INS _ _ IN); [by right | by left].
  by apply update_buffer_allocs.
Qed.

Lemma allocs_disjoint_to_buffers_related:
  forall p n tp rs sp
  (RNI : range_not_in (p, n) tp)
  (VAR : valid_alloc_range (p, n))
  (DISJ: range_list_disjoint rs)
  (MP : machine_ptr p)
  (VARs : forall r, In r rs -> valid_alloc_range r)
  (INS : forall p' n', In (p', n') rs -> range_inside (p', n') (p, n) \/
                                         scratch_ptr p')
  (RLD : range_lists_disjoint (buffer_scratch_ranges (alloc_items_of_ranges rs))
                              sp)
  (PI : partition_injective tp sp),
    buffers_related (BufferedAlloc p n MObjStack :: nil) tp
                    (alloc_items_of_ranges rs :: nil) sp.
Proof.
  intros.
  apply parts_disjoint_to_buffers_related; try done;
    eby eapply new_alloc_disjoint.
Qed.

Lemma machine_buffer_alloc_items_of_ranges:
  forall rs, 
    machine_buffer (alloc_items_of_ranges rs).
Proof.
  induction rs as [|h rs IH]. done.
  intros bi IN.
  simpl in IN. destruct IN as [<- | IN].
    by destruct h.
  by apply IH.
Qed.  

Lemma fin_sup_buffer_ins:
  forall t b tso tso',
    tso_fin_sup tso ->
    is_buffer_ins t b tso tso' ->
    tso_fin_sup tso'.
Proof.
  intros t b tso tso' [l [ND FS]] IBI.
  destruct (In_dec peq t l) as [IN | NIN].
    exists l. split. done.
    intros t' NIN'. 
    destruct (peq t' t) as [-> | N]. done. 
    rewrite (is_buffer_ins_o _ _ _ _ IBI); [by apply FS | done].
  exists (t :: l).
  split. by constructor.
  intros t' NIN'. 
  destruct (peq t' t) as [-> | N]. elim NIN'. by left.
  rewrite (is_buffer_ins_o _ _ _ _ IBI); [|done].
  destruct (In_dec peq t' l) as [IN2 | NIN2].
    elim NIN'. by right.
  by apply FS.
Qed.

Lemma disjoint_allocs_from_alloc_items_of_ranges:
  forall rs
    (DISJ: range_list_disjoint rs)
    (VARs : forall r, In r rs -> valid_alloc_range r),
      disjoint_allocs (alloc_items_of_ranges rs).
Proof.
  induction rs as [|[p n] rs IH]. done.

  intros. simpl in DISJ. destruct DISJ as [DISJ RNI].
  split.
    apply IH. done.
    intros r IN. apply VARs, in_cons, IN.
  intros bi IN. unfold alloc_items_of_ranges in IN.
  apply in_map_iff in IN. destruct IN as [[p' n'] [<- IN]]. simpl.
  apply ranges_disjoint_comm, RNI, IN.
Qed.  

Definition ranges_valid (rl : list arange) :=
  forall r, In r rl -> valid_alloc_range r.

Lemma ranges_valid_part_update:
  forall sp bi sp'
    (RV : ranges_valid sp)
    (PU : part_update bi sp = Some sp'),
      ranges_valid sp'.
Proof.
  intros.
  destruct bi as [p c v | p n k | p k]; 
    simpl in PU.

  destruct low_mem_restr; [|destruct chunk_inside_range_list]; by inv PU.
  
  destruct k; destruct valid_alloc_range_dec; 
    try (destruct (low_mem_restr (MPtr.block p)); by inv PU).
  destruct range_in_dec. done. 
  inv PU. intros r' IN'. simpl in IN'. 
  destruct IN' as [<- | IN']; [|apply RV]; done.
  
  destruct k; try by destruct low_mem_restr; inv PU.
  destruct (pointer_in_range_list p sp); [|done].
  inv PU.
  intros (p', n') IN'. apply in_range_remove in IN'.
  by apply RV.
Qed.

Lemma ranges_valid_part_update_buffer:
  forall b sp sp'
    (RV : ranges_valid sp)
    (PUB: part_update_buffer b sp = Some sp'),
      ranges_valid sp'.
Proof.
  induction b as [|bi b IH].

  intros. by inv PUB.

  intros. unfold part_update_buffer in *. simpl in PUB.
  destruct (part_update bi sp) as [spi|] _eqn : PU; try done.
  simpl in PUB. eapply IH, PUB. eby eapply ranges_valid_part_update.
Qed.

Lemma partition_injective_buffers_related:
  forall tb tp tp' bp sp sp'
    (BR   : buffers_related tb tp bp sp)
    (RV   : ranges_valid sp)
    (PUBt : part_update_buffer tb tp = Some tp')
    (PUBs : part_update_buffer (flatten bp) sp = Some sp')
    (PI   : partition_injective tp sp),
       partition_injective tp' sp'.
Proof.
  intros.
  
  buffers_related_cases (induction BR) Case.

  Case "buffers_related_empty".
    by inv PUBt; inv PUBs.
    
  Case "buffers_related_alloc".
    apply IHBR; unfold part_update_buffer in *.
          eby eapply ranges_valid_part_update_buffer.
        simpl in PUBt.
        destruct valid_alloc_range_dec; [|done].
        by destruct range_in_dec.
      simpl in PUBs. rewrite fold_left_opt_app in PUBs.
      by rewrite PUB in PUBs.
    eapply allocs_related_preserves_partition_injectivity.
    edone. edone.
    intros p' n' MP IN. destruct (PI p' n' MP IN) as [r' [RI RA]].
    eexists. split. edone. by apply in_cons.

  Case "buffers_related_free".
    assert (RV0 : ranges_valid sp'0).
      eby eapply ranges_valid_part_update_buffer.
    apply IHBR; unfold part_update_buffer in *. edone.
        simpl in PUBt.
        by destruct MPtr.eq_dec. 
      simpl in PUBs. rewrite fold_left_opt_app in PUBs.
      by rewrite PUB in PUBs.
    eapply remove_disj_preserves_partition_injectivity. edone.
      intros r IN. apply valid_alloc_range_non_empty. by apply RV0.
    eby eapply frees_related_preserves_partition_injectivity.

  Case "buffers_related_other".
    assert (RV0 : ranges_valid sp'0).
      eby eapply ranges_valid_part_update_buffer.
    apply IHBR; unfold part_update_buffer in *. edone.
        simpl in PUBt. by rewrite buffer_item_irrelevant_part_update in PUBt.
      simpl in PUBs. 
      rewrite buffer_item_irrelevant_part_update in PUBs. simpl in PUBs.
      rewrite fold_left_opt_app in PUBs. by rewrite PUB in PUBs.
    done.
    eby eapply update_part_buffer_scratch_preserves_partition_injectivity.
Qed.  

Lemma scratch_min_block_mptr:
  forall tso p bnd,
    machine_ptr p ->
    tso_memory_upper_bound bnd tso ->
    MPtr.block p < bnd.
Proof.
  intros tso p bnd MP (_ & _ & SMB).
  destruct p as [b o].
  unfold machine_ptr, low_mem_restr, scratch_min_block in *.
  destruct (zeq b 0) as [-> | N]. 
    simpl. omega.
  done.
Qed.

Lemma allocs_disjoint_to_unbuffer_safe:
  forall ttso tthr stso sthr bp sp tp t ttso' stso' p n rs bnd tp'
    (TC  : Comp.consistent tso_mm cst_sem (ttso, tthr))
    (USt : unbuffer_safe ttso')
    (TREL: tso_pc_related_witt (ttso, tthr) (stso, sthr) bp tp sp)
    (PUt : part_update_buffer (tso_buffers ttso t ++ 
                               BufferedAlloc p n MObjStack :: nil) 
                              (tp t) = Some ((p, n) :: tp'))
    (VAR : valid_alloc_range (p, n))
    (DISJ: range_list_disjoint rs)
    (MP  : machine_ptr p)
    (VARs: forall r, In r rs -> valid_alloc_range r)
    (TSOBND: tso_memory_upper_bound bnd stso)
    (INS : forall p' n', In (p', n') rs -> range_inside (p', n') (p, n) \/
                                           bnd <= MPtr.block p')
    (BAt : is_buffer_ins t (BufferedAlloc p n MObjStack :: nil) ttso ttso')
    (BAs : is_buffer_ins t (alloc_items_of_ranges rs) stso stso'),
      unbuffer_safe stso'.
Proof.
  intros.
  destruct TREL as (MTB & NSMR & (MCRt & MCRs & LR) & SC &
    BPD & BNE & SAF & MRPt & MRPs & TREL).
  simpl in *.

  assert(SSREL: tso_pc_ss_rel ttso' stso').
    exists (tupdate t (bp t ++ (alloc_items_of_ranges rs :: nil)) bp).
    exists tp. exists sp.

    assert (SAF' : scratch_allocs_fresh (tso_buffers stso') sp).
      eapply scratch_allocs_fresh_app; try edone.
      intros p' n' IN'. 
      destruct (INS p' n' IN') as [RI | BND].
        left. by destruct p'; destruct p; destruct RI as [-> _].
      by right. 

    assert (SPV : ranges_valid (sp t)).
      intros r IN.
      assert (range_allocated r MObjStack stso.(tso_mem)).
        apply -> (proj2 (proj2 MRPs)). eby eexists.
      eby eapply allocated_range_valid.

    split; try done. (* machine buffers *)
    - intro t'.
      destruct (peq t' t) as [-> | N].
        rewrite (is_buffer_ins_s _ _ _ _ BAs).
        intros bi IN. apply in_app_or in IN.
        destruct IN. eby eapply MTB.
        eby eapply machine_buffer_alloc_items_of_ranges.
      rewrite (is_buffer_ins_o _ _ _ _ BAs); [apply MTB | ]; done.
    - (* non-stack memory consistent *)
      by rewrite (is_buffer_ins_m _ _ _ _ BAs); 
        rewrite (is_buffer_ins_m _ _ _ _ BAt).
    - (* target mem is machine *)
      by rewrite (is_buffer_ins_m _ _ _ _ BAt).
    - (* source mem is machine *)
      by rewrite (is_buffer_ins_m _ _ _ _ BAs).
    - (* Finite support for ttso *)
      eapply fin_sup_buffer_ins. eby eapply (TSO.tso_cons_impl_fin_sup cst_sem).
      edone.
    - (* Finite support for stso *)
      eapply fin_sup_buffer_ins. eby eapply (TSO.tso_cons_impl_fin_sup cs_sem).
      edone.
    - (* Flattened buffer partitions correspond to buffers *)
      intro t'.
      destruct (peq t' t) as [-> | N].
        rewrite (is_buffer_ins_s _ _ _ _ BAs), tupdate_s.
        rewrite flatten_app. simpl. rewrite <- app_nil_end, BPD.
        done.
      rewrite tupdate_o. by rewrite (is_buffer_ins_o _ _ _ _ BAs), BPD.
      done.
    - (* Target memory consistent with partitioning *)
      by rewrite (is_buffer_ins_m _ _ _ _ BAt).
    - (* Source memory consistent with partitioning *)
      by rewrite (is_buffer_ins_m _ _ _ _ BAs).
    - intros t'.
    destruct (TREL t') as (PI & BR & BSR).
    split. done. (* Partitions injective *)
    destruct (peq t' t) as [-> | N].
      rewrite tupdate_s, (is_buffer_ins_s _ _ _ _ BAt).
      destruct (buffers_related_part_update BR) as [[tps PUBt] [sps PUBs]].
      econstructor.
      eapply buffers_related_suffix; try edone.
      eapply allocs_disjoint_to_buffers_related; try done.
      unfold part_update_buffer in *.
      rewrite fold_left_opt_app in PUt. rewrite PUBt in PUt.
      simpl in PUt. destruct valid_alloc_range_dec; [|done].
      by destruct (range_in_dec (p, n) tps).
      intros p' n' IN'. destruct (INS _ _ IN'). by left.
      destruct (machine_or_scratch p') as [MP'|SC'].
        pose proof (scratch_min_block_mptr _ _ _ MP' TSOBND). omegaContradiction.
      by right.
      exploit (scratch_allocs_fresh_apply_buffer _ _ _ stso'.(tso_buffers) 
        (tupdate t (alloc_items_of_ranges rs) stso'.(tso_buffers)) _ PUBs).
        by rewrite (is_buffer_ins_s _ _ _ _ BAs), BPD, tupdate_s.
        intros t' N. by rewrite tupdate_o. 
        done.
      intros (_ & _ & RLDP).
      specialize (RLDP t t).
      by rewrite tupdate_s, update_partitioning_s in RLDP.
      eby eapply partition_injective_buffers_related.
    by rewrite tupdate_o; [|done];
      rewrite (is_buffer_ins_o _ _ _ _ BAt); [constructor|].

  eapply alloc_unbuffer_safe; 
    try apply (is_buffer_ins_s _ _ _ _ BAs); try edone.
  - by destruct SC.
  - by apply (disjoint_allocs_from_alloc_items_of_ranges _ DISJ VARs).
  apply (is_buffer_ins_o _ _ _ _ BAs).
  by intros; rewrite (is_buffer_ins_m _ _ _ _ BAs).
Qed.

Lemma memory_neutral_sim:
  forall ttso tthr stso sthr ts ss ts' ss' t,
    tso_pc_related (ttso, tthr) (stso, sthr) ->
    tthr ! t = Some ts ->
    sthr ! t = Some ss ->
    (forall tp sp sm,
      state_related tp sp sm ts  ss ->
      state_related tp sp sm ts' ss') ->
    state_consistent_with_env ts' ->
    tso_pc_related (ttso, tthr ! t <- ts')
                   (stso, sthr ! t <- ss').
Proof.
  intros ttso tthr stso sthr ts ss ts' ss' t 
    [[BCt USt] [bp [tp [sp TSOREL]]]] TS SS THRR SCE.
  destruct TSOREL as (MTB & NSMR & MCR & SC &
    BPD & BNE & SAF & MRPt & MRPs & TREL).
  split. 
    eby eapply Comp.thread_update_preserves_consistency.
  exists bp; exists tp; exists sp.
  repeat (split; [done|]).
  split. 
    eby eapply Comp.thread_update_preserves_consistency.
  repeat (split; [done|]).
  intro t'.
  destruct (TREL t') as (PI & BR & BOR).
  repeat (split; [done|]).
  simpl in *.
  destruct (peq t' t) as [-> | N].
    rewrite !PTree.gss. rewrite TS, SS in BOR. simpl in *.
    destruct BOR as [smt [spt [tpt (AB & PUBt & PUBs & SR & SCO)]]].
    exists smt. exists spt. exists tpt.
    do 3 (split; [done|]). 
    split. by apply THRR. done.
  by rewrite !PTree.gso.
Qed.

Lemma alloc_steps_appD:
  forall {l1 l2 s s'}
    (AS : alloc_steps s (l1 ++ l2) s'),
    exists si,
      alloc_steps s l1 si /\
      alloc_steps si l2 s'.
Proof.
  induction l1 as [|h l1 IH]; simpl; intros.

  by eexists; vauto. 
  
  inv AS.
  destruct (IH _ _ _ AS0) as [s'' [AS1 AS2]].
  eby eexists; split; [eapply alloc_steps_step|].
Qed.

Lemma alloc_steps_buffer:
  forall ss thrs tso t rs ss'
    (AS  : alloc_steps ss rs ss')
    (STt : thrs ! t = Some ss)
    (USi : unbuffer_safe (buffer_insert_list t (alloc_items_of_ranges rs) tso)),
      exists thrs', 
        taustar cshm_lts (tso, thrs) 
                         (buffer_insert_list t (alloc_items_of_ranges rs) tso, 
                          thrs') /\
        thrs' ! t = Some ss' /\
        (forall t', t' <> t -> thrs' ! t' = thrs ! t').
Proof.
  intros ss thrs tso t rs ss' AS STt.
  revert ss' AS. 
  induction rs as [|r rs IH] using rev_ind; intros.

  (* Base case *)
  by inv AS; exists thrs; split; [apply taustar_refl|].

  (* Inductive case *)
  destruct (alloc_steps_appD AS) as [si [ASrrs ASr]].
  inv ASr. inv AS0.
  specialize (IH _ ASrrs). 
  exploit IH.
    destruct (buffer_insert_list t (alloc_items_of_ranges rs) tso)
      as [b' m'] _eqn : Ebil. 
    apply unbuffer_safe_on_buffer_prefixes 
      with (b := tupdate t (b' t ++ BufferedAlloc p n MObjStack :: nil) b').
    unfold alloc_items_of_ranges in *.
    by rewrite map_app, buffer_insert_list_app, Ebil in USi.
    intros t'. simpl in *.
    destruct (peq t' t) as [-> | N].
      exists (BufferedAlloc p n MObjStack :: nil). by rewrite tupdate_s.
    exists nil. by rewrite tupdate_o, <-app_nil_end.
  clear IH; intros [thrs' (TAU & CS' & OS')].
  eexists.
  split.
    eapply taustar_trans. apply TAU. 
    apply steptau_taustar. simpl.
    eapply Comp.step_ord with (tid := t). apply STEP.
    apply tso_step_alloc; try edone.
      unfold alloc_items_of_ranges.
      by rewrite map_app, buffer_insert_list_app. 
    done.
    edone.
  split.
    by rewrite PTree.gss.
  by intros; rewrite PTree.gso, OS'.
Qed.

Lemma unbuffer_safe_buffer_insert_low_mp:
  forall tso t p n k 
  (M  : mrestr tso.(tso_mem) = low_mem_restr)
  (US : unbuffer_safe (buffer_insert tso t (BufferedAlloc p n k))),
  machine_ptr p /\ valid_alloc_range (p, n).
Proof.
  intros.
  pose proof (no_unbuffer_errors _ t US) as AB.
  simpl in AB. rewrite tupdate_s, apply_buffer_app in AB.
  destruct (apply_buffer (tso_buffers tso t) (tso_mem tso)) as [|m] _eqn : ABi; 
    [|done].
  unfold apply_buffer, apply_buffer_item, optbind in AB.
  pose proof (alloc_cond_spec (p, n) k m) as AS.
  destruct (alloc_ptr (p, n) k m); [|done].
  destruct AS as (_ & VAR & RP & _). simpl in RP.
  eapply restricted_low_pointer_machine in RP.
    by split.
  eby erewrite mem_consistent_with_restr_apply_buffer.
Qed.

Lemma is_buffer_ins_buffer_insert_list:
  forall t b tso,
    is_buffer_ins t b tso (buffer_insert_list t b tso).
Proof.
  intros t b tso.
  split.
  by apply buffer_insert_list_s.
  by apply buffer_insert_list_o.
  by apply buffer_insert_list_m.
Qed.

Lemma is_buffer_ins_buffer_insert:
  forall t bi tso,
    is_buffer_ins t (bi :: nil) tso (buffer_insert tso t bi).
Proof.
  intros t bi tso.
  by apply is_buffer_ins_buffer_insert_list.
Qed.

Lemma empty_envs_items_rel:
  forall fsize sm p,
    env_items_related (Int.repr fsize) sm
          (mkcstenv p fsize (PTree.empty env_item)) empty_env.
Proof.
  by red; intros; simpl; rewrite !PTree.gempty.
Qed.

Lemma empty_env_local_cons_with_ids:
  forall ids,
    local_cons_with_ids (PTree.empty env_item) ids.
Proof.
  by red; intros; rewrite PTree.gempty.
Qed.

Lemma part_update_buffer_alloc_items_of_ranges:
  forall {rs sp sp'}
    (PUB : part_update_buffer (alloc_items_of_ranges rs) sp = Some sp'),
    sp' = rev rs ++ sp.
Proof.
  unfold part_update_buffer.
  induction rs as [|(p, n) rs IH]; intros; simpl in *.
  
  by inv PUB.

  destruct valid_alloc_range_dec; [|done].
  destruct range_in_dec. done.
  simpl in PUB. rewrite (IH _ _ PUB).
  by rewrite app_ass. 
Qed.

Lemma cons_to_app:
  forall {A} {e:A} l,
    e :: l = (e :: nil) ++ l.
Proof. done. Qed.

Lemma allocs_mem_agrees_on_scratch:
  forall rs m m' sp
    (AB  : apply_buffer (alloc_items_of_ranges rs) m = Some m')
    (SPAL: forall r, In r sp -> range_allocated r MObjStack m),
      mem_agrees_on_scratch m m' sp.
Proof.
  induction rs as [|[p n] rs IH].
  
  by intros; inv AB.

  intros. simpl in AB.
  destruct (alloc_ptr (p, n) MObjStack m) as [mi|] _eqn : ABI;
    [|done]; simpl in AB.
  assert(SPALi: forall r : arange, In r sp -> range_allocated r MObjStack mi).
    intros [pi ni] IN.
    by apply (alloc_preserves_allocated ABI), SPAL.
  intros r' p' c' IN RIN SP.
  specialize (IH mi m' sp AB SPALi r' p' c' IN RIN SP).
  rewrite <- IH, (load_alloc_other ABI). done.
  destruct (alloc_someD ABI) as (_ & _ & _ & NA).
  specialize (NA r' MObjStack).
  destruct (ranges_disjoint_dec (p, n) r') as [DISJ | OVER].
    eapply disjoint_inside_disjoint, RIN. 
    by apply ranges_disjoint_comm.
  elim (NA OVER). eby eapply SPAL.
Qed.

Lemma allocs_mem_agrees_on_scratch_mrwp:
  forall part part' part'' m m' m'' b rs t
    (MRWP: mem_related_with_partitioning m part)
    (AB  : apply_buffer b m = Some m')
    (PUB : part_update_buffer b (part t) = Some part')
    (SUB : forall r, In r part'' -> In r part') 
    (AB' : apply_buffer (alloc_items_of_ranges rs) m' = Some m''),
      mem_agrees_on_scratch m' m'' part''.
Proof.
  intros.
  assert(SPAL: forall r, In r part'' -> range_allocated r MObjStack m').
    pose proof (apply_buffer_preserves_mem_partitioning _ _ _ _ _ _ MRWP AB PUB)
      as (_ & _ & AA).
    intros r IN. apply SUB in IN.
    apply -> AA. exists t. by rewrite update_partitioning_s.
  eapply (allocs_mem_agrees_on_scratch _ _ _ _ AB' SPAL).
Qed.

Lemma alloc_sim:
  forall s s' p n k (st : PTree.t Cstacked.state) t tso csms
    (ST : cst_step cst_globenv s (TEmem (MEalloc p n k)) s')
    (CS : st ! t = Some s)
    (USt : unbuffer_safe (buffer_insert tso t (BufferedAlloc p n k)))
    (TSOPCREL : tso_pc_related (tso, st) csms),
      can_reach_error csm_globenv csms \/
      (exists shms',
        taustep cshm_lts csms Etau shms' /\ 
        tso_pc_related (buffer_insert tso t (BufferedAlloc p n k), 
                        st ! t <- s') 
                       shms').
Proof.
  intros. destruct csms as [cstso csst].
  generalize TSOPCREL; intros [TC [bp [tp [sp TRELW]]]].
  pose proof (tso_pc_related_to_buff_states _ _ _ _ _ _ _ _ t TRELW) as BOR.
  pose proof TRELW as (MTB & NSMR & (MCRt & MCRs & LR) & SC &
    BPD & BNE & SAF & MRPt & MRPs & TREL). simpl in *.
  rewrite CS in BOR.
  destruct (csst ! t) as [ss'|] _eqn : Ess'; simpl in BOR; try done.
  destruct BOR as [sm' [sp' [tp' (AB' & PUBt & PUBs & SR & SCO)]]].
  
  assert (SCO' := step_consistent_with_env ST SCO).
  
  assert (TC' : Comp.consistent tso_mm cst_sem
                   (buffer_insert tso t (BufferedAlloc p n k), 
                    st ! t <- s')).
    eapply Comp.step_preserves_consistency.
    econstructor; try edone; eby econstructor. 
    done.

  inv ST. inv SR.

  exploit (unbuffer_safe_partition_alloc_pub _ (tso_buffers tso t) _ t p 
                                             (Int.repr fsize) tp' USt MRPt).
      by simpl; rewrite tupdate_s.
    done.
  intro PUBtn.

  assert (RNIt: range_not_in (p, (Int.repr fsize)) tp').
    eapply unbuffer_safe_partition_alloc. 
    apply USt. apply MRPt. 2 : apply PUBt.
    simpl. rewrite tupdate_s. done.
  assert (FINP : exists p, Genv.find_funct (Cstacked.ge cst_globenv) p =
                           Some (Internal f)).
    by inv KR.
  assert (KS : exists csm_e, exists csm_k0, 
    csm_k = Kcall optid (Internal f) csm_e csm_k0).
    eby inv KR; eexists; eexists.
  destruct KS as [csm_e [csm_k0 KS]].
  assert (FS := TSO.tso_cons_impl_fin_sup _ _ SC).
  destruct (tso_memory_upper_bound_exists _ FS) as [bnd TSOUB].
  unfold build_env in BE. 
  destruct FINP as [fp FINP].
  assert (LIM := function_stacksize_limit _ _ 
                   (PMap.init Var_global_array) FINP).
  destruct (build_compilenv (PMap.init Var_global_array) f) 
    as [cenv fsz] _eqn : Ebce.
  destruct (build_envmap (fn_variables f) cenv (PTree.empty env_item))
    as [e|] _eqn : Ee; [|done]. inv BE.
  pose proof (unbuffer_safe_buffer_insert_low_mp _ _ _ _ _ MCRt USt) 
    as [MP VAR].
  assert (PBND := scratch_min_block_mptr _ _ _ MP TSOUB).
  unfold build_compilenv in Ebce.
  simpl in LIM.

  (* Get the ranges of variables... *)  
  destruct (ranges_of_vars_succ _ _ _ 0 _ _ _ _ ND PBND Ebce 
                                (Zle_refl _) LIM (or_introl _ VAR))
    as [rs (ROV & RLD & VARs & INOSCR)].

  (* Get the unbuffer safety for source... *)
  assert(USsi: unbuffer_safe (buffer_insert_list t (alloc_items_of_ranges rs)
                                                 cstso)).
    apply(allocs_disjoint_to_unbuffer_safe _ _ _ _ _ _ _ _ _ _  _ _ _ _ _
            TC USt TRELW PUBtn VAR RLD MP VARs TSOUB).
        intros p' n' IN'. 
        destruct (INOSCR _ IN') as [[RI _] | O].
          by left.
        right. simpl in O. omega.
      apply is_buffer_ins_buffer_insert.
    apply is_buffer_ins_buffer_insert_list.
  
  assert (ABs := no_unbuffer_errors _ t USsi).
  rewrite buffer_insert_list_s, buffer_insert_list_m, apply_buffer_app, AB' 
    in ABs. simpl in ABs.
  destruct (apply_buffer (alloc_items_of_ranges rs) sm') as [sm''|] _eqn:ABs'';
    [|done].

  (* Get allocation step and relation on environment items *)
  destruct (buffer_alloc_env_related csm_e f optid
    _ _ _ _ _ _ vs csm_k0 _ _ empty_env 
    _ _ _ _ _ _ ROV ABs'' Ee ND PBND (proj2 (proj2 TSOUB)) Ebce (Zle_refl _)
    LIM (or_introl _ VAR) (refl_equal _) (empty_envs_items_rel _ _ _) 
    (empty_env_local_cons_with_ids _)) as (ASTEPS & ITSREL & LC).
  unfold mkcstenv in ITSREL.
  destruct (zeq fsize 0); [done|].

  (* And transform to taustars *)
  destruct (alloc_steps_buffer _ _ _ _ _ _ ASTEPS (PTree.gss _ _ csst) USsi) 
    as [sthrs' (TAUa & NSa & OSa)].

  set (ntso := buffer_insert_list t (alloc_items_of_ranges rs) cstso).

  set (nthr := sthrs' ! t <-
     (SKbind f vs (map (@fst _ _) (fn_params f))
        (build_csm_env (fn_variables f) cenv bnd p empty_env)
        (Kcall optid (Internal f) csm_e csm_k0))).
  
  (* Prove the taustep *)
  assert(WS : taustep cshm_lts (cstso, csst) Etau (ntso, nthr)).
    eapply (@steptau_taustar_taustep _ cshm_lts _ (_, _)).
    simpl.
    (* Step from SKcall to SKalloc *)
    eapply Comp.step_tau; try edone; vauto; [].
    eapply StepFunctionInternal; try edone; [].
    unfold fn_variables in ND. unfold fst in ND.
    rewrite !@map_app, map_map in ND. apply ND.
    eapply taustar_trans. (* Alloc steps *) apply TAUa.
    (* Step from SKalloc to SKbind *)
    apply steptau_taustar. simpl.
    by eapply Comp.step_tau; try edone; vauto.

  (* Build some auxiliary statements *)
  assert (SAF' : scratch_allocs_fresh (tso_buffers ntso) sp).
    eapply scratch_allocs_fresh_app; try edone.
    apply is_buffer_ins_buffer_insert_list.
    intros p' n' IN'. 
    destruct (INOSCR (p', n') IN') as [[RI _] | BND].
      left. by destruct p'; destruct p; destruct RI as [-> _].
    right. simpl in *. omega.

  assert (RLDrssp : range_lists_disjoint rs sp').
    destruct (TREL t) as (PIt' & BRt' & _).
    eapply new_alloc_disjoint; try edone.
    intros p' n' IN'. destruct (INOSCR _ IN'). by left; tauto.
    destruct (machine_or_scratch p') as [MP'|SC'].
      pose proof (scratch_min_block_mptr _ _ _ MP' TSOUB). 
      simpl in *. omegaContradiction.
      by right.
    exploit (scratch_allocs_fresh_apply_buffer _ _ _ ntso.(tso_buffers) 
      (tupdate t (alloc_items_of_ranges rs) ntso.(tso_buffers)) _ PUBs);
      unfold ntso.
      by rewrite buffer_insert_list_s, BPD, tupdate_s.
      intros t' N. by rewrite tupdate_o. 
      done.
    intros (_ & _ & RLDP).
    specialize (RLDP t t).
    eby rewrite tupdate_s, update_partitioning_s in RLDP.
    eapply partition_injective_buffers_related; try edone.
    intros r IN.
    assert (range_allocated r MObjStack cstso.(tso_mem)).
      apply -> (proj2 (proj2 MRPs)). eby eexists.
    eby eapply allocated_range_valid. eby rewrite <- BPD.

  assert (BRt : buffers_related
     (tso_buffers tso t ++ BufferedAlloc p (Int.repr fsize) MObjStack :: nil)
     (tp t) (bp t ++ alloc_items_of_ranges rs :: nil) 
     (sp t)).
      destruct (TREL t) as (PIt' & BRt' & _).
      eapply buffers_related_suffix; try edone.
      eapply parts_disjoint_to_buffers_related; try edone.
      intros p' n' IN'. destruct (INOSCR _ IN'). by left; tauto.
      destruct (machine_or_scratch p') as [MP'|SC'].
        pose proof (scratch_min_block_mptr _ _ _ MP' TSOUB). 
        simpl in *. omegaContradiction.
      by right.      
      eby rewrite <- BPD.

  assert (NErsnil : rs <> nil).
    destruct (fn_variables f). simpl in *. inv Ebce. done.
    destruct p0 as [? []]; simpl in ROV; destruct (cenv !! i); 
      try done; destruct ranges_of_vars; try done;
        injection ROV; by intros <-.
  end_assert NErsnil.
                             
  right. eexists (_, _).
  split. apply WS.
  (* Finally, establish the simulation relation *)
  split. done. (* tso consistency of target *)
  exists (tupdate t (bp t ++ (alloc_items_of_ranges rs :: nil)) bp).
  exists tp. exists sp.
  unfold ntso, nthr.
  split; simpl. (* machine buffers *)
    intro t'.
    destruct (peq t' t) as [-> | N].
      rewrite buffer_insert_list_s.
      intros bi IN. apply in_app_or in IN.
      destruct IN. eby eapply MTB.
      eby eapply machine_buffer_alloc_items_of_ranges.
    rewrite buffer_insert_list_o; [apply MTB | ]; done.
  split. (* non-stack memory consistent *)
    by rewrite buffer_insert_list_m. 
  split. (* memory contents related *)
    by rewrite buffer_insert_list_m. 
  split. (* tso consistency for source *)
    eapply Comp.taustep_preserves_consistency.
    apply WS. done. 
  split. (* buffer partitioning *)
    intro t'.
    destruct (peq t' t) as [-> | N].
      rewrite buffer_insert_list_s, tupdate_s.
      rewrite flatten_app. simpl. rewrite <- app_nil_end, BPD.
      done.
    by rewrite buffer_insert_list_o, tupdate_o, BPD.
  split. (* buffer partitions non-empty *)
    intros t' bi IN.
    destruct (peq t' t) as [-> | N].
      rewrite tupdate_s in IN.
      apply in_app_or in IN. 
      destruct IN as [IN | [<- | IM]]. eby eapply BNE.
      by destruct rs.
      done.
    rewrite tupdate_o in IN. eby eapply BNE. done.
  split. done. (* Scratch allocation freshness *)
  split. done. (* Target memory consistent with partitioning *)
  split. (* Source memory consistent with partitioning *)
    by rewrite buffer_insert_list_m.
  intros t'.
  destruct (TREL t') as (PI & BR & BSR).
  split. done. (* Partitions injective *)
  split. (* Buffers related *)
    destruct (peq t' t) as [-> | N].
      rewrite !@tupdate_s. done.
    by rewrite !@tupdate_o. 
  (* Buffered states related *)
  destruct (peq t' t) as [-> | N].
    rewrite !@tupdate_s, !@PTree.gss.
    simpl. rewrite buffer_insert_list_m.
    destruct (buffers_related_part_update BRt) as [_ [sps PUBs']].
    unfold part_update_buffer in *.
    rewrite flatten_app, fold_left_opt_app, <- BPD, PUBs in PUBs'. 
    simpl in PUBs'. rewrite <- app_nil_end in PUBs'.
    rewrite (part_update_buffer_alloc_items_of_ranges PUBs') in PUBs'.
    eexists. eexists. eexists.
    split.
      rewrite flatten_app, <- BPD, apply_buffer_app, AB'. 
      simpl. rewrite <- app_nil_end. edone.
    split. edone.
    split. unfold part_update_buffer.
      rewrite flatten_app, fold_left_opt_app, <- BPD, PUBs.
      simpl. rewrite <- app_nil_end. edone.
    rewrite cons_to_app. 
    split; [|done].
    eapply st_rel_bind.
      eapply cont_related_load_inv.
        edone. 
        eapply allocs_mem_agrees_on_scratch_mrwp; try edone;
          intros r IN; apply in_or_app; by right.
    (* Environments related *)
    exists (Int.repr fsize).
    split. 
      repeat (split; [done|]).
      destruct rs. done. simpl.
      intro E. eby eapply app_cons_not_nil, sym_eq.
    split. 
      apply range_list_disjoint_perm with (l := rs).
      apply Permutation_rev.
      done.
    split.
      eapply Permutation_trans.
        apply Permutation_sym, Permutation_rev.
      eapply env_ranges_permut_range_of_vars.
      edone. edone. done. done. done.
      intros r1 IN1 r2 IN2. destruct IN2 as [<- | ?]; [|done].
      by apply ranges_disjoint_comm, RNIt.
    intros r1 IN1 r2 IN2. apply In_rev in IN2. 
    apply ranges_disjoint_comm. eby eapply RLDrssp.
  rewrite !@tupdate_o, buffer_insert_list_m, !@PTree.gso; try done.
  by rewrite OSa, PTree.gso.
Qed.

End ALLOC_SIMS.

