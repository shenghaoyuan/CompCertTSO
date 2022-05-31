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
Require Import Permutation.

Section UNBUFFER_SIMS.

Variable cst_globenv : genv * gvarenv.
Variable csm_globenv : genv * gvarenv.

Let cshm_lts := (mklts event_labels (Comp.step tso_mm cs_sem csm_globenv)).
Let cst_lts := (mklts event_labels (Comp.step tso_mm cst_sem cst_globenv)).

Notation cont_related := (cont_related cst_globenv). 
Notation expr_cont_related := (expr_cont_related cst_globenv). 
Notation state_related := (state_related cst_globenv).
Notation buffered_states_related := (buffered_states_related cst_globenv).
Notation tso_pc_related_witt := (tso_pc_related_witt cst_globenv).
Notation tso_pc_related := (tso_pc_related cst_globenv).
Notation tso_pc_unsafe_related := (tso_pc_unsafe_related cst_globenv).

(* The state relation only depends on the values of its 
   scratch partition *)

Definition mem_agrees_on_scratch (m : mem)
                                 (m' : mem)
                                 (rs : list arange) : Prop :=
  forall r p c,
    In r rs ->
    range_inside (range_of_chunk p c) r ->
    scratch_ptr p ->
    load_ptr c m p = load_ptr c m' p.

Lemma env_related_load_inv:
  forall tp sp smem smem' te se,
    env_related tp sp smem te se ->
    mem_agrees_on_scratch smem smem' sp ->
    env_related tp sp smem' te se.
Proof.
  intros tp sp smem smem' te se ER MAS.
  destruct ER as [n [FR [DISJ [PERM EIR]]]].
  exists n.
  split. done.
  split. done.
  split. done.
  intro id. specialize (EIR id).
  destruct ((csenv_env te)!id) as [ei|]; [|done].
  destruct (se!id) as [p|] _eqn : Eseid; [|done].
  inv EIR; try (by constructor); [].
  (* Local variable *)
  apply env_item_related_local; try done.
  rewrite <- LV. apply sym_eq.
  specialize (MAS  (csm_env_item_range (snd (id, (p0, Vscalar c))))).
  apply MAS; try done. unfold env_ranges.
    apply PTree.elements_correct in Eseid.
    apply (Permutation_in _ (Permutation_sym PERM)).
    apply (in_map (fun ei => csm_env_item_range (snd ei))
      (PTree.elements se) _ Eseid).
  unfold csm_env_item_range. simpl. unfold range_of_chunk. 
  apply range_inside_refl.
Qed.  

Lemma mem_agrees_on_scratch_app1:
  forall m m' s1 s2,
    mem_agrees_on_scratch m m' (s1 ++ s2) ->
    mem_agrees_on_scratch m m' s1.
Proof.
  intros m m' s1 s2 MAS r p c IN RI PS.
  eapply MAS; try edone. apply in_or_app. by left.
Qed.

Lemma mem_agrees_on_scratch_app2:
  forall m m' s1 s2,
    mem_agrees_on_scratch m m' (s1 ++ s2) ->
    mem_agrees_on_scratch m m' s2.
Proof.
  intros m m' s1 s2 MAS r p c IN RI PS.
  eapply MAS; try edone. apply in_or_app. by right.
Qed.

Lemma cont_related_load_inv:
  forall tp sp smem smem' te se,
    cont_related tp sp smem te se ->
    mem_agrees_on_scratch smem smem' sp ->
    cont_related tp sp smem' te se.
Proof.
  intros tp sp smem smem' te se C. revert smem'.
  (cont_related_cases (induction C) Case);
    try (by intros; constructor; try apply IHC).

  Case "k_rel_call".
    intros smem' MAS. 
    constructor; try done.
    apply IHC. eby eapply mem_agrees_on_scratch_app2.
    eapply env_related_load_inv. edone.
    eby eapply mem_agrees_on_scratch_app1.
Qed.

Lemma expr_cont_related_load_inv:
  forall tp sp smem smem' tps sps te se,
    expr_cont_related tp sp smem tps sps te se ->
    mem_agrees_on_scratch smem smem' sp ->
    expr_cont_related tp sp smem' tps sps te se.
Proof.
  intros tp sp smem smem' tps sps te se C. revert smem'.
  (expr_cont_related_cases (induction C) Case);
    try (eby intros; econstructor; try (apply IHC);
           try (eapply cont_related_load_inv)).
Qed.

Lemma state_related_load_inv:
  forall tp sp smem smem' te se,
    state_related tp sp smem te se ->
    mem_agrees_on_scratch smem smem' sp ->
    state_related tp sp smem' te se.
Proof.
  intros tp sp smem smem' te se S. revert smem'.
  (state_related_cases (induction S) Case);

  intros; try (by constructor; try done; 
    try eapply expr_cont_related_load_inv; 
      try eapply cont_related_load_inv;
        try edone; try (eby eapply mem_agrees_on_scratch_app2);
          try eapply env_related_load_inv; try edone;
            try eby eapply mem_agrees_on_scratch_app1).
Qed.

Lemma mem_agrees_on_scratch_perm:
  forall m m' p p',
    mem_agrees_on_scratch m m' p ->
    Permutation p p' ->
    mem_agrees_on_scratch m m' p'.
Proof.
  intros m m' p p' MAS P r ptr c IN RI SC.
  eapply MAS; try edone.
  eby eapply Permutation_in; try apply Permutation_sym.
Qed.

(* Tools for proving non-interference of buffer applications with
   other threads' invariants. *) 

Definition range_list_allocated (p : list arange)
                                (m : mem) : Prop := 
  forall r : arange, In r p -> range_allocated r MObjStack m.

Lemma range_disjoint_remove:
  forall p l,
    range_list_disjoint l ->
    range_list_disjoint (range_remove p l).
Proof.
  induction l as [|[ph nh]  l IH].
  done.

  simpl. 
  intros [DISJ RNI].
  destruct (MPtr.eq_dec ph p) as [-> | N]. done.
  simpl. split. by apply IH. 
  intros [] IN'. eby eapply RNI, in_range_remove.
Qed.  

Lemma range_list_disjoint_remove_not_in:
  forall p l,
    (forall r, In r l -> range_non_empty r) ->
    range_list_disjoint l ->
    forall n, ~ In (p, n) (range_remove p l).
Proof.
  induction l as [|[ph nh] l IH]; simpl.
    by intros.
  intros RNE [RD RNI] n IN.
  destruct (MPtr.eq_dec ph p) as [-> | N].
    assert (PNE: range_non_empty (p, n)). 
    apply RNE. right. done.
    assert (PHNE: range_non_empty (p, nh)) by (apply RNE; left; done).
    apply RNI in IN.
    by eapply non_empty_same_ptr_overlap in IN. 
  simpl in IN. destruct IN as [E | IN]. by inv E. 
  by eapply IH; try edone; intros; apply RNE; right.
Qed.

Lemma part_update_range_list_disjoint_allocated:
  forall bi sp smem sp' smem',
    apply_buffer_item bi smem = Some smem' ->
    part_update bi sp = Some sp' ->
    range_list_allocated sp smem ->
    range_list_disjoint sp ->
    range_list_allocated sp' smem' /\
    range_list_disjoint sp'.
Proof.
  intros bi sp smem sp' smem' ABI PU RLA RLD.

  (buffer_item_cases (destruct bi as [p c v | p n k | p k]) Case); 
    simpl in PU |- *; unfold apply_buffer_item in ABI.

  Case "BufferedWrite".
    replace sp with sp' in *;
      [| destruct (low_mem_restr (MPtr.block p)); 
         destruct (chunk_inside_range_list p c sp); try inv PU; done].
    split. 
      intros r IN. 
      apply (proj1 (store_preserves_allocated_ranges ABI _ _)).
      apply RLA. done.
    done.

  Case "BufferedAlloc".
    destruct k;
      destruct (valid_alloc_range_dec (p, n)) as [VAR |];
        try destruct range_in_dec as [|RNI];
          try (by destruct (low_mem_restr (MPtr.block p));
            try done; inv PU;
              try (by split; [intros r IN; 
                apply (alloc_preserves_allocated ABI), RLA|])).
    inv PU.
    split.
      intros r IN.
      simpl in IN. destruct IN as [<- | IN].
        apply (proj1 (alloc_someD ABI)).
      by apply (alloc_preserves_allocated ABI), RLA.
    split. done.
    intros r IN. apply RLA in IN.
    pose proof (alloc_cond_spec (p, n) MObjStack smem) as Aspec.
    rewrite ABI in Aspec. destruct Aspec as [_ [_ [_ NA]]].
    destruct (ranges_disjoint_dec (p, n) r) as [DISJ | OVER]. done.
    specialize (NA _ MObjStack OVER). done.
    
  Case "BufferedFree".
    destruct k; 
      try (destruct (low_mem_restr (MPtr.block p)); try done; inv PU; 
        split; [intros r IN;
        destruct (free_preserves_allocated ABI _ _ (RLA _ IN)) 
          as [? | [? ?]] | ]; done).
    destruct (pointer_in_range_list p sp) as [] _eqn : PIR; try done. inv PU.
    split. 
      intros [p' n'] IN.
      destruct (free_preserves_allocated ABI _ _ 
        (RLA _ (in_range_remove _ _ _ _ IN))) as [RA | [E _]]. done.
      simpl in E. subst.
      byContradiction.
      eapply range_list_disjoint_remove_not_in; [|apply RLD|apply IN].
      intros r INr.
      eapply valid_alloc_range_non_empty, allocated_range_valid, RLA, INr.
    by apply range_disjoint_remove.
Qed.

Lemma pointer_in_range_list_in:
  forall p l,
    pointer_in_range_list p l = true ->
    exists n, In (p, n) l.
Proof.
  intros p. induction l as [|[p' n'] l IH]. done.
  simpl; destruct (MPtr.eq_dec p p') as [-> | N].
    intro. eexists. left; reflexivity.
  intro H. destruct (IH H). eexists; right; eassumption.
Qed.

Lemma mem_agrees_on_scratch_preserved_by_pv_update:
  forall bi smem smem' sp sp' smemx smemx',
    part_update bi sp = Some sp' ->
    range_list_disjoint sp ->
    range_list_allocated sp smem ->
    range_list_allocated sp smem' ->
    apply_buffer_item bi smem = Some smemx ->
    apply_buffer_item bi smem' = Some smemx' ->
    mem_agrees_on_scratch smem smem' sp ->
    mem_agrees_on_scratch smemx smemx' sp'.
Proof.
  intros bi smem smem' sp sp' smemx smemx' PVU RLD RLA RLA' ABI ABI' MAS.
  unfold part_update in PVU.
  unfold apply_buffer_item in ABI, ABI'.

  (buffer_item_cases (destruct bi as [p c v | p n k | p k]) Case);
  simpl; intros r' p' c' IN RI SP.
  
  Case "BufferedWrite".
    replace sp with sp' in *;
      [| destruct (low_mem_restr (MPtr.block p)); 
         destruct (chunk_inside_range_list p c sp); try inv PVU; done].
    specialize (MAS r' p' c' IN RI SP).
    eby eapply load_eq_preserved_by_store.

  Case "BufferedAlloc".
    destruct k; 
      destruct (valid_alloc_range_dec (p, n)) as [VAR |];
        try destruct range_in_dec as [|RNI];
          try (destruct (low_mem_restr (MPtr.block p)); try done; inv PVU;
            specialize (MAS r' p' c' IN RI SP); 
              eby eapply load_eq_preserved_by_alloc).
    inv PVU.
    simpl in IN. 
    destruct IN as [<- | IN].
      destruct (pointer_chunk_aligned_dec p' c') as [CA | CNA].
      eby erewrite !@load_alloc_inside. 
      pose proof (load_chunk_allocated_spec c' smemx p') as LDALX.
      pose proof (load_chunk_allocated_spec c' smemx' p') as LDALX'.
      destruct (load_ptr c' smemx p'); destruct (load_ptr c' smemx' p'); 
        try done; destruct LDALX; destruct LDALX'; done.
    specialize (MAS r' p' c' IN RI SP); eby eapply load_eq_preserved_by_alloc.

  Case "BufferedFree".
    assert (INsp: In r' sp).
      destruct k; try (by destruct (low_mem_restr (MPtr.block p)); 
        try done; inv PVU; done). 
      destruct (pointer_in_range_list p sp); try done; inv PVU.
      eby destruct r'; eapply in_range_remove.
    specialize (MAS r' p' c' INsp RI SP).
    destruct k; try (by
      destruct (low_mem_restr (MPtr.block p)) as [] _eqn : MP; try done; inv PVU;
        eapply load_eq_preserved_by_free_diff_block; try edone;
          intro E; simpl in *; unfold range_inside, 
            range_of_chunk in *; destruct p; destruct p'; destruct r' as [[]]; 
              destruct RI; simpl in *; rewrite E, SP in *).
    
    destruct (pointer_in_range_list p sp) as [] _eqn : E; try done; inv PVU.
    destruct (pointer_in_range_list_in _ _ E)  as [n INspn].
    pose proof (RLA _ INspn). pose proof (RLA' _ INspn).
    eapply load_eq_preserved_by_free_same_size; try edone.
Qed.  

Lemma mem_agrees_on_scratch_preserved_by_pv_buffer_update:
  forall b smem smem' sp sp' smemx smemx',
    part_update_buffer b sp = Some sp' ->
    range_list_disjoint sp ->
    range_list_allocated sp smem ->
    range_list_allocated sp smemx ->
    apply_buffer b smem = Some smem' ->
    apply_buffer b smemx = Some smemx' ->
    mem_agrees_on_scratch smem smemx sp ->
    mem_agrees_on_scratch smem' smemx' sp'.
Proof.
  induction b as [|bi br IH];
    intros smem smem' sp sp' smemx smemx' PVBU RLD RLA RLAx AB ABx MAS.
  by simpl in *; inv ABx; inv AB; inv PVBU.

  unfold part_update_buffer in PVBU; simpl in *.
  destruct (apply_buffer_item bi smem) as [smem2|] _eqn : ABI; try done.
  destruct (apply_buffer_item bi smemx) as [smemx2|] _eqn : ABIx; try done.
  destruct (part_update bi sp) as [sp2|] _eqn : PU; try done.
  simpl in AB, ABx, PVBU.
  destruct (part_update_range_list_disjoint_allocated _ _ _ _ _ 
    ABI PU RLA RLD)  as [RLAu RLDu].
  destruct (part_update_range_list_disjoint_allocated _ _ _ _ _ 
    ABIx PU RLAx RLD) as [RLAxu _].
  apply (IH _ _ _ _ _ _ PVBU RLDu RLAu RLAxu AB ABx).
  eapply mem_agrees_on_scratch_preserved_by_pv_update;
    [ | | apply RLA | apply RLAx | | | ]; eassumption.
Qed.

Lemma buffered_states_related_prepend_tgt:
  forall bi tb tp ts sb sp sm ss tp',
    part_update bi tp' = Some tp ->
    (buffered_states_related tb tp ts sb sp sm ss <->
     buffered_states_related (bi :: tb) tp' ts sb sp sm ss).
Proof.
  intros bi tb tp ts sb sp sm ss tp' PU.
  split.
    intros [sm' [sp' [tpx [ABI [PUBt [PUBs SR]]]]]].
    exists sm'; exists sp'; exists tpx.
    split. done.
    split. by unfold part_update_buffer; simpl; rewrite PU.
    by repeat (split; try done). 
  intros [sm' [sp' [tpx [ABI [PUBt [PUBs SR]]]]]].
  exists sm'; exists sp'; exists tpx.
  split. done.
  split. by unfold part_update_buffer in *; simpl in *; rewrite PU in *.
  by repeat (split; try done).
Qed.    

Lemma buffered_states_related_prepend_src:
  forall b tb tp ts sb sp sm ss sm' sp',
    part_update_buffer b sp' = Some sp ->
    apply_buffer b sm' = Some sm ->
    (buffered_states_related tb tp ts sb sp sm ss <->
     buffered_states_related tb tp ts (b ++ sb) sp' sm' ss).
Proof.
  intros b tb tp ts sb sp sm ss sm' sp' PUB ABI.
  split.
    intros [smx [spx [tpx [ABIx [PUBtx [PUBsx SRx]]]]]].
    exists smx; exists spx; exists tpx.
    split. by rewrite apply_buffer_app, ABI. 
    split. done. 
    split. unfold part_update_buffer in *. by rewrite fold_left_opt_app, PUB.
    done.
  intros [smx [spx [tpx [ABIx [PUBtx [PUBsx SRx]]]]]].
  exists smx; exists spx; exists tpx.
  split. by rewrite apply_buffer_app, ABI in ABIx. 
  split. done. 
  split. unfold part_update_buffer in *. 
  by rewrite fold_left_opt_app, PUB in PUBsx.
  done.
Qed.    
  
(* General version of the unbuffering non-interference 
   (it is generalised to make the induction work) *)
Lemma buffered_states_related_load_inv_gen:
  forall tb tp ts b sb sp smem ss smem' spx smemx smemx',
    range_list_disjoint sp ->
    range_list_allocated sp smem ->
    range_list_allocated sp smem' ->
    buffer_safe_for_mem (b ++ flatten sb) smem ->
    buffer_safe_for_mem (b ++ flatten sb)  smem' ->
    mem_agrees_on_scratch smem smem' sp ->
    apply_buffer b smem = Some smemx ->
    apply_buffer b smem' = Some smemx' ->
    part_update_buffer b sp = Some spx ->
    buffers_related tb tp sb spx ->
    buffered_states_related tb tp ts (flatten sb) spx smemx ss ->
    buffered_states_related tb tp ts (flatten sb) spx smemx' ss.
Proof.
  intros tb tp ts b sb sp smem ss smem' spx smemx smemx'.
  intros RLD RLA RLA' BS BS' MAS AB AB' PVU BR BSR.
  
  revert smemx smemx' b BS BS' AB AB' PVU BSR. 
  (buffers_related_cases (induction BR) Case); 
    intros smemx smemx' b BS BS' SMAB SMAB' PVU BSR.
 
  Case "buffers_related_empty".
    destruct BSR as [sm' [sp' [tp' [ABI [PUBt [PUBs [SR SCO]]]]]]].
    (* eapply buffered_states_related_empty. apply PAL. *)
    simpl in BS, BS'. rewrite <- app_nil_end in *.
    
    eexists; eexists; eexists; unfold part_update_buffer in *; 
      simpl in *; inv PUBs.
    do 3 (split; [edone|]).
    split; [|done].
    eapply state_related_load_inv. edone.
    (* eapply mem_agrees_on_scratch_perm. 2: apply PERM. *)
    eapply mem_agrees_on_scratch_preserved_by_pv_buffer_update. 
    edone. done. apply RLA. apply RLA'. inv ABI; done. done. done.

  Case "buffers_related_alloc".
    simpl in BS, BS'. rewrite <- app_ass in BS, BS'.
    destruct (buffer_safe_for_mem_app1 _ _ _ BS) as [mx ABx].
    destruct (buffer_safe_for_mem_app1 _ _ _ BS') as [mx' ABx']. simpl.
    apply -> buffered_states_related_prepend_src.
    apply -> buffered_states_related_prepend_tgt.
    
    eapply IHBR. edone. edone. edone. edone.
    unfold part_update_buffer in *. rewrite fold_left_opt_app, PVU. done.
    apply <- buffered_states_related_prepend_src.
    apply <- buffered_states_related_prepend_tgt. 
    edone. simpl.
      destruct valid_alloc_range_dec; try done. 
      destruct range_in_dec as [[r' [INr RO]] | RNI]; try done.
      specialize (RIN _ INr). done.
    unfold range_not_in in RIN.
    by rewrite apply_buffer_app, SMAB in ABx.
    unfold part_update_buffer in *. done. simpl. 
      destruct valid_alloc_range_dec; try done. 
      destruct range_in_dec as [[r' [INr RO]] | RNI]; try done.
      specialize (RIN _ INr). done.
    by rewrite apply_buffer_app, SMAB' in ABx'. done.

  Case "buffers_related_free".    
    simpl in BS, BS'. rewrite <- app_ass in BS, BS'.
    destruct (buffer_safe_for_mem_app1 _ _ _ BS) as [mx ABx].
    destruct (buffer_safe_for_mem_app1 _ _ _ BS') as [mx' ABx'].
    apply -> buffered_states_related_prepend_src.
    apply -> buffered_states_related_prepend_tgt.
    eapply IHBR. edone. edone. edone. edone.
    unfold part_update_buffer in *. rewrite fold_left_opt_app, PVU. done.
    apply <- buffered_states_related_prepend_src.
    apply <- buffered_states_related_prepend_tgt. 
    edone. simpl. by destruct (MPtr.eq_dec p p).
    by rewrite apply_buffer_app, SMAB in ABx.
    unfold part_update_buffer in *. done. simpl. by destruct MPtr.eq_dec. 
    by rewrite apply_buffer_app, SMAB' in ABx'. done.

  Case "buffers_related_other".
    simpl in BS, BS'. 
    rewrite app_comm_cons, <- app_ass in BS, BS'.
    destruct (buffer_safe_for_mem_app1 _ _ _ BS) as [mx ABx].
    destruct (buffer_safe_for_mem_app1 _ _ _ BS') as [mx' ABx'].
    apply -> buffered_states_related_prepend_src.
    apply -> buffered_states_related_prepend_tgt.
    eapply IHBR. edone. edone. edone. edone.
    unfold part_update_buffer in *. rewrite fold_left_opt_app, PVU. simpl.
    rewrite (buffer_item_irrelevant_part_update _ _ BIIR). done.
    apply <- buffered_states_related_prepend_src.
    apply <- buffered_states_related_prepend_tgt. 
    edone. simpl. by rewrite (buffer_item_irrelevant_part_update _ _ BIIR).
    by rewrite apply_buffer_app, SMAB in ABx.
    unfold part_update_buffer in *. simpl. 
    rewrite (buffer_item_irrelevant_part_update _ _ BIIR). done.
    rewrite (buffer_item_irrelevant_part_update _ _ BIIR). done.
    by rewrite apply_buffer_app, SMAB' in ABx'.
    unfold part_update_buffer. simpl. 
    rewrite (buffer_item_irrelevant_part_update _ _ BIIR). done.
Qed.

Lemma buffered_states_related_load_inv:
  forall tb tp ts sb sp smem ss smem',
    buffers_related tb tp sb sp ->
    buffered_states_related tb tp ts (flatten sb) sp smem ss ->
    range_list_disjoint sp ->
    range_list_allocated sp smem ->
    range_list_allocated sp smem' ->
    buffer_safe_for_mem (flatten sb) smem ->
    buffer_safe_for_mem (flatten sb)  smem' ->
    mem_agrees_on_scratch smem smem' sp ->
    buffered_states_related tb tp ts (flatten sb) sp smem' ss.
Proof.
  intros tb tp ts sb sp smem ss smem' BR BSR RLD RLA RLA' BS BS' MAS.
  by eapply (buffered_states_related_load_inv_gen _ _ _ nil 
    _ _ _ _ _ _ _ _ RLD RLA RLA').
Qed.  

Lemma tso_consistent_safe_buffer_app:
  forall stso sthr t bis rb,
    Comp.consistent tso_mm cs_sem (stso, sthr) ->
    stso.(tso_buffers) t = bis ++ rb ->
    buffer_safe_for_mem bis stso.(tso_mem).
Proof. 
  intros stso sthr t bis rb [_ UBS]; 
    eby eapply unbuffer_safe_to_buffer_safe_for_mem.
Qed.

Lemma alloc_ptr_tgt_preserves_load_rel:
  forall cstm csmm cstm' r k,
    load_values_related cstm csmm ->
    alloc_ptr r k cstm = Some cstm' -> 
    load_values_related cstm' csmm.
Proof.
  intros cstm csmm cstm' r k LVR AP.
  intros p MP c.
  specialize (LVR p MP c).
  destruct (load_ptr c cstm p) as [csv|] _eqn : CSLD;
    destruct (load_ptr c csmm p) as [cmv|] _eqn : CMLD; try done;
      try by rewrite (load_some_alloc CSLD AP). 
  by destruct (load_ptr c cstm' p).
Qed.

Lemma alloc_ptr_stack_preserves_mem_partitioning:
  forall m m' p n part t,
    mem_related_with_partitioning m part ->
    alloc_ptr (p, n) MObjStack m = Some m' ->
    mem_related_with_partitioning m'
      (update_partitioning t ((p, n) :: (part t)) part).
Proof.
  intros m m' p n part t [PD [LD MR]] AP. unfold update_partitioning.
  split.
    (* Partitions are pairwise disjoint *)
    intros t1 t2 N r IN r' IN'.
    destruct (peq t1 t) as [-> | Nt1]; 
      destruct (peq t2 t) as [-> | Nt2]; try done; 
          try (eapply PD; [apply N | apply IN | apply IN']).
    
    simpl in IN. 
    destruct IN as [<- | IN]; 
      [|eapply PD; [apply N | apply IN | apply IN']].
    destruct (ranges_disjoint_dec (p, n) r') as [DISJ | OVER]. done.
    byContradiction.
    apply (proj2 (proj2 (proj2 (alloc_someD AP))) _ MObjStack OVER).
    apply (proj1 (MR _)); eexists; eassumption.
    (* The symmetric case *)
    simpl in IN'. 
    destruct IN' as [<- | IN']; 
      [|eapply PD; [apply N | apply IN | apply IN']].
    destruct (ranges_disjoint_dec (p, n) r) as [DISJ | OVER]. 
      by apply ranges_disjoint_comm.
    byContradiction.
    apply (proj2 (proj2 (proj2 (alloc_someD AP))) _ MObjStack OVER).
    apply (proj1 (MR _)); eexists; eassumption.
  split.
    (* Each partition is still disjoint *)
    intros t'.
    destruct (peq t' t) as [_ | N].
      split. apply LD.
      intros r IN.
      destruct (ranges_disjoint_dec (p, n) r) as [DISJ | OVER]. done.
      byContradiction.
      apply (proj2 (proj2 (proj2 (alloc_someD AP))) _ MObjStack OVER).
      apply (proj1 (MR _)); eexists; eassumption.
    apply LD.
  (* All partitions are allocated *)
  intro r.
  split.
    intros [t' IN].
    (* Allocation *)
    destruct (peq t' t) as [_ | N];
      try (apply (alloc_preserves_allocated AP); 
          apply (proj1 (MR _)); eexists; eassumption).
      simpl in IN; destruct IN as [<- | IN].
        apply (proj1 (alloc_someD AP)).
    apply (alloc_preserves_allocated AP); 
      apply (proj1 (MR _)); eexists; eassumption. 
  intro RA. 
  destruct (alloc_preserves_allocated_back AP _ _ RA)
    as [[-> _] | RAo].
    exists t. destruct (peq t t); try apply in_eq; done.
  destruct (proj2 (MR _) RAo) as [t' IN'].
  exists t'. 
  destruct (peq t' t) as [-> | N]; try apply in_cons; done.
Qed.

Lemma alloc_ptr_non_stack_preserves_mem_partitioning:
  forall m m' p n k part t,
    mem_related_with_partitioning m part ->
    match k with MObjStack => False | _ => True end ->
    alloc_ptr (p, n) k m = Some m' ->
    mem_related_with_partitioning m'
      (update_partitioning t (part t) part).
Proof.
  intros m m' p n k part t [PD [LD MR]] NS AP. unfold update_partitioning.
  split. 
    intros t1 t2 N r IN r' IN'.
    destruct (peq t1 t) as [-> | Nt1]; 
      destruct (peq t2 t) as [-> | Nt2]; eby eapply (PD _ _ N r IN r' IN').
  split.
    intros t'. destruct (peq t' t); apply LD.
  intro r.
  split.
    intros [t' IN].
    (* Allocation *)
    destruct (peq t' t) as [_ | N];
      try (apply (alloc_preserves_allocated AP); 
          apply (proj1 (MR _)); eexists; eassumption).
  intro RA. 
  destruct (alloc_preserves_allocated_back AP _ _ RA)
    as [[-> <-] | RAo]; try done.
  destruct (proj2 (MR _) RAo) as [t' IN'].
  exists t'. 
  destruct (peq t' t) as [-> | N]; try apply in_cons; done.
Qed.

Lemma store_ptr_preserves_mem_partitioning:
  forall m m' c p v part,
    mem_related_with_partitioning m part ->
    store_ptr c m p v = Some m' ->
    mem_related_with_partitioning m' part.
Proof.
  intros m m' c p v part [PD [LD MR]] ST.
  split. done.
  split. done.
  (* All partitions are allocated *)
  intro r.
  split.
    intros [t' IN]. 
    apply (proj1 (store_preserves_allocated_ranges ST _ _)).
    apply (proj1 (MR _)). eby eexists.
  intro RA.
  apply (proj2 (store_preserves_allocated_ranges ST _ _)) in RA.
  apply (proj2 (MR _) RA).
Qed.

Lemma store_ptr_preserves_mem_partitioning2:
  forall m m' c p v part t,
    mem_related_with_partitioning m part ->
    store_ptr c m p v = Some m' ->
    mem_related_with_partitioning m'
      (update_partitioning t (part t) part).
Proof.
  intros m m' c p v part t [PD [LD MR]] ST. unfold update_partitioning.
  split. intros x y NE. 
    destruct (peq x t) as [-> | Nx]; destruct (peq y t) as [-> | Ny];
      apply (PD _ _ NE).
  split. intro t'. destruct (peq t' t); apply LD.
  (* All partitions are allocated *)
  intro r.
  split.
    intros [t' IN]. 
    apply (proj1 (store_preserves_allocated_ranges ST _ _)).
    apply (proj1 (MR _)). destruct (peq t' t); eby eexists.
  intro RA.
  apply (proj2 (store_preserves_allocated_ranges ST _ _)) in RA.
  destruct (proj2 (MR _) RA) as [t' IN].
  exists t'. by destruct (peq t' t) as [-> | _].
Qed.

Lemma ranges_disjoint_dont_overlap:
  forall r r',
    ranges_disjoint r r' ->
    ranges_overlap r r' ->
    False.
Proof. intros r r' D O. apply O, D. Qed.

Lemma free_ptr_preserves_mem_partitioning:
  forall m m' p k part t,
    mem_related_with_partitioning m part ->
    free_ptr p k m = Some m' ->
    (exists n, In (p, n) (part t)) ->
    mem_related_with_partitioning m'
      (update_partitioning t (range_remove p (part t)) part).
Proof.
  intros m m' p k part t [PD [LD MR]] FP [n INP]. unfold update_partitioning.
  pose proof (free_cond_spec p k m) as Fspec.
  rewrite FP in Fspec. destruct Fspec as [n' Fspec].
  assert (INpe: exists t, In (p, n) (part t)). eby eexists.
  destruct (alloc_ranges_same Fspec (proj1 (MR _) INpe)) as [-> ->].
  split.
    (* Partitions are pairwise disjoint *)
    intros t1 t2 N r IN r' IN'.
    destruct (peq t1 t) as [-> | Nt1]; 
      destruct (peq t2 t) as [-> | Nt2]; try done; 
        try (eapply PD; [apply N | apply IN | apply IN']).
      destruct r as [rp rn].
      apply in_range_remove in IN. 
      eapply PD; [apply N | apply IN | apply IN'].
    (* The symmetric case *)
    destruct r'. apply in_range_remove in IN'. 
    eapply PD; [apply N | apply IN | apply IN'].
  split.
    (* Each partition is still disjoint *)
    intros t'.
    destruct (peq t' t) as [_ | N]; try apply range_disjoint_remove; apply LD.
  (* All partitions are allocated *)
  intro r.
  split.
    intros [t' IN].
    (* Free *)
    destruct (peq t' t) as [<- | N].
      destruct r as [pr nr]; 
      pose proof (in_range_remove _ _ _ _ IN) as IN2.
      assert (IN': exists t, In (pr, nr) (part t)). eexists; eassumption.
      apply (proj1 (MR _)) in IN'.
      destruct (free_preserves_allocated FP _ _ IN') as [|[E _]]. done.
      simpl in E. rewrite E in *.
      byContradiction.
      eapply (range_list_disjoint_remove_not_in p (part t')).
        intros rp INp. 
        assert (INrpe : exists t, In rp (part t)). eexists; eassumption.
        by apply (proj1 (MR _)), allocated_range_valid, 
          valid_alloc_range_non_empty in INrpe.
        apply LD.
      simpl in E. subst. eassumption.
    assert (IN': exists t, In r (part t)). eexists; eassumption.
    apply (proj1 (MR _)) in IN'. 
    destruct r as [pr nr].
    destruct (free_preserves_allocated FP _ _ IN') as [|[E _]]. done.
    simpl in E. subst.
    byContradiction.
    eapply ranges_disjoint_dont_overlap.
      apply (PD _ _ N _ IN _ INP).
    eapply non_empty_same_ptr_overlap;
      eapply valid_alloc_range_non_empty, allocated_range_valid, (proj1 (MR _));
        eexists; eassumption.
  intro RA. 
  (* Free *)
  pose proof (free_preserves_allocated_back FP _ _ RA) as RAo.
  destruct (proj2 (MR _) RAo) as [t' IN'].
  exists t'. 
  destruct (peq t' t) as [-> | N]; try done.
  destruct r as [pr nr].
  destruct (in_range_remove_back p _ _ _ IN') as [<- | RR].
    destruct (free_not_allocated FP _ _ RA).
  done.
Qed.

Lemma free_ptr_non_stack_preserves_mem_partitioning:
  forall m m' p k part t,
    mem_related_with_partitioning m part ->
    match k with MObjStack => False | _ => True end ->
    free_ptr p k m = Some m' ->
    mem_related_with_partitioning m'
      (update_partitioning t (part t) part).
Proof.
  intros m m' p k part t [PD [LD MR]] NS FP. unfold update_partitioning.
  split. 
    intros t1 t2 N r IN r' IN'.
    destruct (peq t1 t) as [-> | Nt1]; 
      destruct (peq t2 t) as [-> | Nt2]; eby eapply (PD _ _ N r IN r' IN').
  split.
    intros t'. destruct (peq t' t); apply LD.
  intro r.
  split.
    intros [t' IN].
    destruct (peq t' t) as [<- | N];
      (assert (RA : range_allocated r MObjStack m);
        [apply (proj1 (MR _)); eby eexists |
          by destruct (free_preserves_allocated FP _ _ RA)
            as [RA' | [<- <-]]]).
  intro RA. 
  apply (free_preserves_allocated_back FP) in RA.
  destruct (proj2 (MR _) RA) as [t' IN'].
  exists t'. 
  destruct (peq t' t) as [-> | N]; try apply in_cons; done.
Qed.

Lemma apply_buffer_item_preserves_mem_partitioning:
  forall m m' bi part part' t,
    mem_related_with_partitioning m part ->
    apply_buffer_item bi m = Some m' ->
    part_update bi (part t) = Some part' ->
    mem_related_with_partitioning m' (update_partitioning t part' part).
Proof.
  intros m m' bi part part' t MRP ABI PU.
  buffer_item_cases (destruct bi as [p c v|p n k|p k]) Case.
  
  Case "BufferedWrite".
    simpl in ABI, PU.
    replace part' with (part t) in *.
      eby eapply store_ptr_preserves_mem_partitioning2.
    destruct low_mem_restr; [|destruct chunk_inside_range_list]; try inv PU; try done.
  
  Case "BufferedAlloc".
    unfold part_update, apply_buffer_item in *.
    destruct k;
    destruct (valid_alloc_range_dec (p, n)); try destruct range_in_dec;
      destruct (low_mem_restr (MPtr.block p)); try done; inv PU;
        try (by refine (alloc_ptr_non_stack_preserves_mem_partitioning 
          _ _ _ _ _ _ _ MRP _ ABI)); 
        try apply (alloc_ptr_stack_preserves_mem_partitioning 
          _ _ _ _ _ _ MRP ABI). 

  Case "BufferedFree".
    unfold part_update, apply_buffer_item in *.
    destruct k;
      try (destruct (low_mem_restr (MPtr.block p)); inv PU; try done;
        by refine (free_ptr_non_stack_preserves_mem_partitioning 
          _ _ _ _ _ _ MRP _ ABI)).
    destruct (pointer_in_range_list p (part t)) as [] _eqn : PIR; [|done].
    inv PU.
    eby eapply free_ptr_preserves_mem_partitioning, pointer_in_range_list_in.
Qed.

Lemma mem_related_with_partitioning_ext:
  forall m part part',
    mem_related_with_partitioning m part ->
    (forall t, part t = part' t) ->
    mem_related_with_partitioning m part'.
Proof.
  intros m part part' (PD & RLD & MRWP) E.
  split.
    intros t t'. rewrite <- ! E. apply PD.
  split.
    intro t; rewrite <- ! E; apply RLD.
  intro r; split.
    intros [t IN]. rewrite <- E in IN.
    apply (proj1 (MRWP r)).
    eby eexists.
  intro RA. 
  destruct (proj2 (MRWP r) RA) as [t' IN]. exists t'.
  by rewrite <- E.
Qed.

Lemma update_partitioning_s:
  forall t p part,
    update_partitioning t p part t = p.
Proof. by intros; unfold update_partitioning; destruct peq. Qed.

Lemma update_partitioning_o:
  forall t' t p part,
    t' <> t ->
    update_partitioning t p part t' = part t'.
Proof. by intros; unfold update_partitioning; destruct peq. Qed.

Lemma apply_buffer_preserves_mem_partitioning:
  forall b m m' part part' t,
    mem_related_with_partitioning m part ->
    apply_buffer b m = Some m' ->
    part_update_buffer b (part t) = Some part' ->
    mem_related_with_partitioning m' (update_partitioning t part' part).
Proof.
  induction b as [|bi br IH];
    intros m m' part part' t MRWP AB PUB; 
      unfold part_update_buffer in PUB; simpl in AB, PUB.

  inv AB. inv PUB.
  eapply mem_related_with_partitioning_ext. edone.
  intro t'.
  unfold update_partitioning. 
  by destruct peq; subst.

  destruct (apply_buffer_item bi m) as [mi|] _eqn : ABI;
    destruct (part_update bi (part t)) as [pi|] _eqn : PU; 
      try done; unfold optbind in *.
  eapply mem_related_with_partitioning_ext.
  eapply IH. 
      eapply apply_buffer_item_preserves_mem_partitioning. 
      eapply MRWP. apply ABI. apply PU.
    apply AB.
  rewrite update_partitioning_s. edone.
  intro t'.
  unfold update_partitioning; by destruct peq.
Qed.

Lemma store_ptr_mem_consistent:
  forall m c p v m',
    store_ptr c m p v = Some m' ->
    mrestr m (MPtr.block p) = true.
Proof.
  intros m c p v m' ST.

  pose proof (store_chunk_allocated_spec c m p v) as SSP.
  rewrite ST in SSP. destruct SSP as [[r' [k' [RI RA]]] _].
  destruct r'.
  pose proof (range_allocated_consistent_with_restr _ _ _ _ RA).
  destruct p; destruct p0. unfold range_inside, range_of_chunk in RI.
  by destruct RI as [-> _].
Qed.

Lemma apply_scratch_preserve_machine_allocs:
  forall bi m m' p n k,
    apply_buffer_item bi m = Some m' ->
    is_item_scratch_update bi ->
    machine_ptr p ->
    (range_allocated (p, n) k m <-> range_allocated (p, n) k m').
Proof.
  intros bi m m' p n k ABI ISU MP.
  unfold apply_buffer_item in ABI.
  buffer_item_cases (destruct bi as [p' c' v' | p' n' k' | p' k']) Case.
      
  Case "BufferedWrite".
    eby eapply store_preserves_allocated_ranges.

  Case "BufferedAlloc".
    split. intro RA; eby eapply alloc_preserves_allocated.
    intro RA. 
    destruct (alloc_preserves_allocated_back ABI _ _ RA) 
      as [[E <-] | RA'].
      inv E. simpl in ISU. destruct k; try done. 
      by destruct p'; simpl in *; rewrite MP in ISU.
    done.
  
  Case "BufferedFree".
    split; intro RA.
      destruct (free_preserves_allocated ABI _ _ RA)
        as [RA' | [<- <-]]. done.
      destruct k; simpl in ISU; try done;
        by destruct p; simpl in *; rewrite MP in ISU.
    eby eapply free_preserves_allocated_back.
Qed.

Lemma apply_scratch_preserves_load_rel:
  forall tmem bi m m',
    apply_buffer_item bi m = Some m' ->
    is_item_scratch_update bi ->
    load_values_related tmem m ->
    load_values_related tmem m'.
Proof.
  intros tmem bi m m' ABI ISU LR p MP c.
  replace (load_ptr c m' p) with (load_ptr c m p).
    apply (LR p MP c).
  unfold apply_buffer_item in ABI.
  buffer_item_cases (destruct bi as [p' c' v' | p' n' k' | p' k']) Case.
      
  Case "BufferedWrite".
    eapply load_store_other. apply ABI. 
    destruct p; destruct p'; left. intros ->. simpl in *. by rewrite MP in ISU.
  
  Case "BufferedAlloc".
    eapply sym_eq, load_alloc_other. apply ABI.
    destruct p; destruct p'; left. intros ->. simpl in *. destruct k'; try done.
    by rewrite MP in ISU.

  Case "BufferedFree".
    pose proof (free_cond_spec p' k' m) as Fspec. rewrite ABI in Fspec.
    destruct Fspec as [n RA].
    eapply sym_eq, load_free_other. apply ABI. edone.
    destruct p; destruct p'; left. intros ->. simpl in *. destruct k'; try done.
    by rewrite MP in ISU.
Qed.

Lemma apply_scratch_buffer_preserves_load_rel:
  forall b tmem m m',
    apply_buffer b m = Some m' ->
    (forall bi, In bi b -> is_item_scratch_update bi) ->
    load_values_related tmem m ->
    load_values_related tmem m'.
Proof.
  induction b as [|bi br IH]; intros tmem m m' AB SCR LR.

  inv AB. done.

  simpl in AB; destruct (apply_buffer_item bi m) as [mi|] _eqn : ABI; 
    try done; simpl in AB.
  eapply IH; try edone. 
    intros bi' IN'. apply SCR, in_cons, IN'.
  eapply apply_scratch_preserves_load_rel; try edone.
  apply SCR, in_eq.
Qed.

Lemma allocs_related_buff_disjoint:
  forall b p' n' k' p n pi ni ki m m',
  allocs_related p n b ->
  apply_buffer b m = Some m' ->
  range_allocated (p', n') k' m ->
  machine_ptr p' ->
  In (BufferedAlloc pi ni ki) b ->
  ranges_disjoint (p', n') (pi, ni).
Proof.
  induction b as [|bi b IH]. done.

  intros p' n' k' p n pi ni ki m m' AR AB RA MP IN.
  simpl in IN, AB. 
  destruct (apply_buffer_item bi m) as [mi|] _eqn : ABI; 
    simpl in AB; [|done].
  pose proof ABI as AP; unfold apply_buffer_item in AP.

  destruct IN as [-> | IN]. 
    (* First see wether (pi, ni) is bi. If yes, we have a contradiction *)
    pose proof (alloc_cond_spec (pi, ni) ki m) as Aspec. rewrite AP in Aspec.
    destruct Aspec as (_ & _ & _ & OA).
    destruct (ranges_disjoint_dec (p', n') (pi, ni)) as [? | OVER]. 
      done.
    apply ranges_overlap_comm in OVER.
    destruct (OA _ _ OVER RA).
  (* If no, use the induction hypothesis *)
  eapply IH; try edone. intros bi' IN'. apply (AR bi' (in_cons _ _ _ IN')).
  (* range allocated in the intermediate memory, this part is different
     for scratch items and genuine on-stack allocation. *)
  destruct (AR _ (in_eq bi b)) as [SCRATCH | STACK].
    eby eapply (apply_scratch_preserve_machine_allocs _ _ _ _ _ _ ABI SCRATCH MP).
  destruct bi as [| px nx []|]; try done.
  eby eapply alloc_preserves_allocated.
Qed.

Definition non_conflicting_allocs_buffer (b : list buffer_item)
                                         (m : mem) : Prop :=
  forall bi, In bi b ->
      match bi with 
        | BufferedAlloc p' n' k' =>
            scratch_ptr p' \/
              k' = MObjStack /\
              forall r'' k'', ranges_overlap r'' (p', n') ->
                ~ range_allocated r'' k'' m
        | BufferedFree p' _ => scratch_ptr p'
        | BufferedWrite p' _ _ => scratch_ptr p'
      end.

Lemma non_conflicting_allocs_buffer_from_relation:
  forall b smem tp sp p n k tmem tmem',
    non_stack_mem_related tmem smem ->
    mem_related_with_partitioning tmem tp ->
    mem_related_with_partitioning smem sp ->
    (forall t, partition_injective (tp t) (sp t)) ->
    allocs_related p n b ->
    alloc_ptr (p, n) k tmem = Some tmem' ->
    non_conflicting_allocs_buffer b smem.
Proof.
  intros b smem tp sp p n k tmem tmem' 
    NSMR [_ [_ MRt]] [_ [_ MRs]] PIS AR AP.
  intros bi IN.
  destruct (AR _ IN) as [SCRATCH | INSIDE].
    unfold is_item_scratch_update in SCRATCH.
    destruct bi as [pi ci vi|pi ni []|pi []]; try left; done.
  destruct bi as [| pi ni []|]; try done.
  destruct (low_mem_restr (MPtr.block pi)) as [] _eqn : LMR;
    [|by left; destruct pi; simpl in *].
  right. split. done.
  intros [p'' n''] k'' ROVER RA.
  assert (MP : machine_ptr pi). by destruct pi; simpl in *.
  pose proof (alloc_cond_spec (p, n) k tmem) as TAspec; rewrite AP in TAspec.
  destruct TAspec as (_ & _ & _ & UNAL).
  assert (ALI: exists r', exists k', 
    range_inside (p'', n'') r' /\ range_allocated r' k' tmem).
    pose proof (NSMR (p'', n'') k'') as NSAL.
    destruct k''; try (by apply NSAL in RA; eexists; eexists; split; 
        [apply range_inside_refl| apply RA]).
    destruct (proj2 (MRs (p'', n'')) RA) as [t INt].
    assert (MPp'' : machine_ptr p''). 
      by destruct p''; destruct pi; 
        destruct (ranges_overlapD ROVER) as [-> _]; simpl in *.
    destruct (PIS _ _ _ MPp'' INt) as [rt [RI INtp]].
    eexists; eexists; split. apply RI. eapply MRt. eexists; apply INtp.
  destruct ALI as (r' & k' & RI' & RA').
  eapply UNAL. 2: apply RA'. eapply overlap_inside_overlap. 
    2 : apply INSIDE.
  eapply ranges_overlap_comm, overlap_inside_overlap.
  apply ROVER. done.
Qed.

(* Now we show that unbuffering preserves mem_content_related *)
Lemma allocs_related_preserves_alloc_load_rels:
  forall b tmem smem smem' sp sp' p n,
    allocs_related p n b ->
    part_update_buffer b sp = Some sp' ->
    apply_buffer b smem = Some smem' ->
    mrestr smem = no_mem_restr ->
    (forall p' c', 
      range_inside (range_of_chunk p' c') (p, n) ->
      chunk_allocated_and_aligned p' c' tmem ->
      load_ptr c' tmem p' = Some Vundef) ->
    non_conflicting_allocs_buffer b smem ->
    load_values_related tmem smem ->
    range_allocated (p, n) MObjStack tmem ->
    load_values_related tmem smem'.
Proof.
  induction b as [|bi sb IH];
    intros tmem smem smem' sp sp' p n AR PUB AB MC LUN BUNAL LREL RA;
      pose proof AB as ABwithbi;
      simpl in AB.

  (* Base case is trivial because smem = smem' *)
  by inv AB.

  (* Induction step: *)
  (* - extract the intermediate memory and partitioning (but make a copy
       before disassembling it). *)
  destruct (apply_buffer_item bi smem) as [m'|] _eqn : ABI; [simpl in AB|done].
  unfold part_update_buffer in *; simpl in PUB. 
  destruct (part_update bi sp) as [spi|] _eqn : PU; [simpl in PUB|done].
  assert (ARsb: allocs_related p n sb).
    intros bi' IN'. apply (AR bi' (in_cons _ _ _ IN')).
  
  (* - and apply the induction hypothesis *)
  eapply IH; try edone.

  (* consistency of memory with restriction *)
  eby erewrite mem_consistent_with_restr_apply_item.
  
  (* things in the buffer are not allocated in smem *)
  intros bi' IN. 
  specialize (BUNAL bi' (in_cons bi _ _ IN)).
  destruct bi' as [| p' n' k' |]; try done.
  destruct (low_mem_restr (MPtr.block p')) as [] _eqn : LMR. 
    destruct BUNAL as [? | [K NRA]]. 
      by destruct p'; simpl in *; rewrite LMR in *.
    right. split. done.
    intros [p'' n''] k'' OVER RA''.
    specialize (NRA (p'', n'') k'' OVER).
    elim NRA.
    destruct (AR _ (in_eq bi sb)) as [SCRATCH | STACK].
      (* bi is scratch *)
      eapply (apply_scratch_preserve_machine_allocs _ _ _ _ _ _ ABI SCRATCH).
      by destruct p''; destruct p'; 
        destruct (ranges_overlapD OVER) as [-> _]; simpl in *.
      edone.
    (* bi is stack *)
    destruct bi as [|pi ni []|]; try done.
    unfold apply_buffer_item in ABI.
    destruct (alloc_preserves_allocated_back ABI _ _ RA'') 
      as [[-> ->] | RACM].
      byContradiction.
      eapply ranges_disjoint_dont_overlap. 2: apply OVER.
      eapply allocs_related_buff_disjoint; try edone. 
      by destruct p'; destruct p''; 
        destruct (ranges_overlapD OVER) as [-> _]; simpl in *.
    done.
  by left; destruct p'; simpl in LMR |- *.
  
  (* load_values_related *)
  destruct (AR _ (in_eq bi sb)) as [SCRATCH | RI].
    eby eapply apply_scratch_preserves_load_rel.
  destruct bi as [|pi ni []|]; try done.
  intros px MPx cx.
  pose proof ABI as AP; unfold apply_buffer_item in AP.
  specialize (LREL px MPx cx).
  pose proof (load_chunk_allocated_spec cx smem px) as LDCAS.
  destruct (load_ptr cx smem px) as [sv|] _eqn : LDS.
    destruct (load_ptr cx tmem px) as [tv|] _eqn : LDT.
      by rewrite (load_some_alloc LDS AP).
    done.
  destruct (pointer_chunk_aligned_dec px cx) as [ALG | NALG].
    destruct (ranges_disjoint_dec (range_of_chunk px cx) (pi, ni))
      as [DISJx | OVERx].
      rewrite (load_alloc_other AP DISJx), LDS.
      destruct (load_ptr cx tmem px); done.
    destruct (range_inside_dec (range_of_chunk px cx) (pi, ni))
      as [RIx | NRIx].
      rewrite (load_alloc_inside AP), LUN; try done.
      eapply range_inside_trans. apply RIx. done.
      split. eexists. eexists. split. 
        eapply range_inside_trans. apply RIx. apply RI. apply RA.
      done. 
    by rewrite (load_alloc_overlap AP).
  pose proof (load_chunk_allocated_spec cx m' px) as LDM'.
  destruct (load_ptr cx m' px). destruct LDM' as [? ?]; done.
  destruct (load_ptr cx tmem px); done.
Qed.

Lemma free_preserves_load_fail:
  forall p k m m' p' c,
    free_ptr p k m = Some m' ->
    load_ptr c m p' = None ->
    load_ptr c m' p' = None.
Proof.
  intros p k m m' p' c FR LD.
  pose proof (free_cond_spec p k m) as FPS. rewrite FR in FPS.
  destruct FPS as [n RA].
  pose proof (load_chunk_allocated_spec c m' p') as LDS'.
  destruct (load_ptr c m' p') as [v|] _eqn : LD'; try done.
  destruct LDS' as [[rx [kx [RIx RAx]]] ALGx].
  pose proof (load_chunk_allocated_spec c m p') as LDS. rewrite LD in LDS. 
  elim LDS.
  split. eexists; eexists; split. 
    apply RIx. 
    apply (free_preserves_allocated_back FR), RAx.
  done.
Qed.

Lemma free_src_preserves_load_rel:
  forall p k sm sm' tm,
    free_ptr p k sm = Some sm' ->
    load_values_related tm sm ->
    load_values_related tm sm'.
Proof.
  intros p k sm sm' tm FP LR p' MP c'.
  specialize (LR p' MP c').
  
  pose proof (free_cond_spec p k sm) as Fspec; 
    rewrite FP in Fspec; destruct Fspec as [n RA].

  destruct (load_ptr c' sm p') as [sv|] _eqn : SLD.
    destruct (load_ptr c' tm p') as [tv|]; try done.
    destruct LR as [-> MV].
    destruct (ranges_disjoint_dec (range_of_chunk p' c') (p, n)) 
        as [DISJ | OVER].
      rewrite (load_free_other FP RA DISJ), SLD. by split.
    by rewrite (load_free_overlap FP RA OVER).
  by rewrite (free_preserves_load_fail _ _ _ _ _ _ FP SLD).
Qed.

Lemma frees_related_preserves_load_rel_src:
  forall  p n tm sm' b sm,
    frees_related p n b ->
    apply_buffer b sm = Some sm' ->
    load_values_related tm sm ->
    load_values_related tm sm'.
Proof.
  intros p n tm sm' b.
  induction b as [|bi br IH];
    intros sm FR AB LREL;
      simpl in AB.

  by inv AB.

  destruct (apply_buffer_item bi sm) as [mi|] _eqn : ABI; try done.
  simpl in AB.
  
  eapply IH; [exact (fun bi' IN => FR bi' (in_cons bi _ _ IN)) | edone |].
  destruct (FR _ (in_eq _ _)) as [SCRATCH | STACK].
    eby eapply apply_scratch_preserves_load_rel.
  destruct bi as [| | p' []]; try done.
  eby eapply free_src_preserves_load_rel.
Qed.

Lemma free_preserves_load_back:
  forall p k m m' p' c v,
    free_ptr p k m = Some m' ->
    load_ptr c m' p' = Some v ->
    load_ptr c m p' = Some v.
Proof.
  intros p k m m' p' c v FR LD.
  pose proof (free_cond_spec p k m) as FPS. rewrite FR in FPS.
  destruct FPS as [n RA].
  pose proof (load_chunk_allocated_spec c m' p') as LDS'. rewrite LD in LDS'.
  destruct LDS' as [[rx [kx [RIx RAx]]] ALGx].
  pose proof (free_preserves_allocated_back FR _ _ RAx) as RAm.
  destruct (ranges_are_disjoint RA RAm) as [[<- <-] | DISJ].
    destruct (free_not_allocated FR _ _ RAx).
  erewrite <- (load_free_other FR); try eassumption.
  eapply disjoint_inside_disjoint. apply ranges_disjoint_comm.
  edone. done.
Qed.

Lemma range_of_chunk_not_empty:
  forall p c,
    range_non_empty (range_of_chunk p c).
Proof.
  intros p c.
  unfold range_non_empty, range_of_chunk, snd.
  rewrite size_chunk_repr. by pose proof (size_chunk_pos c); omega.
Qed.  

Lemma free_preserves_load_rel_tgt:
  forall p n t tm tm' sm sp tp,
    free_ptr p MObjStack tm = Some tm' ->
    non_stack_mem_related tm sm ->
    mem_related_with_partitioning sm sp ->
    mem_related_with_partitioning tm tp ->
    In (p, n) (tp t) ->
    (forall t', partition_injective  (tp t') (sp t')) ->
    (forall r, In r (sp t) -> ranges_disjoint r (p, n)) ->
    load_values_related tm sm ->
    load_values_related tm' sm.
Proof.
  intros p n t tm tm' sm sp tp FP NSR [PDs [RLDs INAs]] [PDt [RLDt INAt]] 
    INpn PI RD LR.
  intros p' MP c'.
  specialize (LR p' MP c').
  pose proof (load_chunk_allocated_spec c' tm p') as LDStm.
  pose proof (load_chunk_allocated_spec c' tm' p') as LDStm'.
  pose proof (load_chunk_allocated_spec c' sm p') as LDSsm.
  destruct (load_ptr c' tm p') as [tv|] _eqn : LDtm;
    destruct (load_ptr c' tm' p') as [tv'|] _eqn : LDtm';
      destruct (load_ptr c' sm p') as [sv|] _eqn : LDsm; try done.
    rewrite (free_preserves_load_back _ _ _ _ _ _ _ FP LDtm') in LDtm.
    by inv LDtm.
  (* The only case that requires any work is the one where
     load succeeds in tm but fails in tm': *)
  destruct LDSsm as [[[ps ns] [ks [RIs RAs]]] ALs].
  destruct LDStm as [[[pt nt] [kt [RIt RAt]]] ALt].
  destruct (free_preserves_allocated FP _ _ RAt) as 
    [RAt' | [<- ->]].
    apply LDStm'. split. eexists. eexists. split. apply RIt. edone. edone.
  (* the load in tm is within the region being freed *)
  
  assert (DISJ : ranges_disjoint (pt, nt) (ps, ns)).
    specialize (NSR (ps, ns) ks).
    destruct ks; try (by apply NSR in RAs;
      destruct (ranges_are_disjoint RAt RAs) as [[_ ?] | DISJ]).
    assert (RAtn: range_allocated (pt, n) MObjStack tm).
      eapply INAt. eby eexists.
    destruct (alloc_ranges_same RAtn RAt) as [-> _].
    apply INAs in RAs. destruct RAs as [ts INs].
    destruct (peq t ts) as [<- | N].
      apply ranges_disjoint_comm, RD, INs.
    apply PI in INs. destruct INs as [rts [RIts INts]].
    eapply ranges_disjoint_comm, disjoint_inside_disjoint.
    2 : apply RIts. apply ranges_disjoint_comm.
    apply (PDt _ _ N _ INpn _ INts).
    by destruct p'; destruct ps; simpl in *; destruct RIs; subst.
  eapply ranges_disjoint_dont_overlap. edone.
  eapply overlap_inside_overlap. 2 : apply RIt.
  eapply ranges_overlap_comm, overlap_inside_overlap. 2 : apply RIs.
  apply ranges_overlap_refl. apply range_of_chunk_not_empty.
Qed.

Lemma update_part_scratch_preserves_partition_injectivity:
  forall bi sp sp' tp,
    is_item_scratch_update bi ->
    part_update bi sp = Some sp' ->
    partition_injective tp sp ->
    partition_injective tp sp'.
Proof.
  intros bi sp sp' tp ISU PU PI p n MP IN.
  unfold is_item_scratch_update, part_update in ISU, PU.
  buffer_item_cases (destruct bi as [p' c' v'|p' n' k'|p' k']) Case.
 
  Case "BufferedWrite".
    destruct (low_mem_restr (MPtr.block p')) as [] _eqn : LMR;
      destruct (chunk_inside_range_list p' c' sp); try done;
        inv PU; apply (PI p n MP IN).

  Case "BufferedAlloc".
    destruct k'; try done.
    destruct (valid_alloc_range_dec (p', n')); [|done].
    destruct range_in_dec; [done|].
    inv PU. simpl in IN. destruct IN as [E | IN].
      inv E. by destruct p; simpl in *; rewrite MP in ISU.
    apply (PI p n MP IN).

  Case "BufferedFree".
    destruct k'; try done.
    destruct (pointer_in_range_list p' sp); try done.
    inv PU.
    apply in_range_remove in IN.
    apply (PI p n MP IN).
Qed.

Lemma update_part_buffer_scratch_preserves_partition_injectivity:
  forall b sp sp' tp,
    (forall bi, In bi b -> is_item_scratch_update bi) ->
    part_update_buffer b sp = Some sp' ->
    partition_injective tp sp ->
    partition_injective tp sp'.
Proof.
  induction b as [|bi rb IH]; intros sp sp' tp SCR PUB PI; 
    unfold part_update_buffer in PUB; simpl in PUB.
  
  by inv PUB.

  destruct (part_update bi sp) as [spi|] _eqn:PU; try done; simpl in PUB.
  eapply IH; try done.
      intros bi' IN'. by eapply SCR, in_cons.
    apply PUB.
  eapply update_part_scratch_preserves_partition_injectivity; try edone.
  apply (SCR _ (in_eq _ _)).
Qed.

Lemma allocs_related_item_preserves_partition_injectivity:
  forall bi b p n sp sp' tp,
    allocs_related p n b ->
    In bi b ->
    part_update bi sp = Some sp' ->
    partition_injective ((p, n) :: tp) sp ->
    partition_injective ((p, n) :: tp) sp'.
Proof.
  intros bi b p n sp sp' tp AR IN PU PI.

  destruct (AR _ IN) as [SCRATCH | INSIDE].
    eby eapply update_part_scratch_preserves_partition_injectivity.
  destruct bi as [|pi ni []|]; try done.
  simpl in PU. 
  destruct valid_alloc_range_dec; try destruct range_in_dec; try done.
  inv PU.
  intros pui nui MPui INui.
    simpl in INui. destruct INui as [E | INui].
      inv E. eexists. split. edone. apply in_eq.
    eby eapply PI.
Qed.

Lemma allocs_related_preserves_partition_injectivity:
  forall b p n sp sp' tp,
    allocs_related p n b ->
    part_update_buffer b sp = Some sp' ->
    partition_injective ((p, n) :: tp) sp ->
    partition_injective ((p, n) :: tp) sp'.
Proof.
  induction b as [|bi b IH];
    intros p n sp sp' tp AR PUB PI.

  (* Base case *)
  unfold part_update_buffer in PUB. simpl in PUB.
  inv PUB; done.

  (* Step case *)
  unfold part_update_buffer in *; simpl in PUB. 
  destruct (part_update bi sp) as [spi|] _eqn : PU; [simpl in PUB|done].
  eapply IH.
      intros bi' IN'. apply (AR bi' (in_cons _ _ _ IN')).
    eassumption.  
  eapply allocs_related_item_preserves_partition_injectivity; try edone.
  apply in_eq.
Qed.

Lemma frees_related_item_preserves_partition_injectivity:
  forall bi b p n sp sp' tp,
    frees_related p n b ->
    In bi b ->
    part_update bi sp = Some sp' ->
    partition_injective tp sp ->
    partition_injective tp sp'.
Proof.
  intros bi b p n sp sp' tp FR IN PU PI.

  destruct (FR _ IN) as [SCRATCH | INSIDE].
    eby eapply update_part_scratch_preserves_partition_injectivity.
  destruct bi as [| | pi []]; try done.
  simpl in PU. destruct pointer_in_range_list; try done.
  inv PU.
  intros pui nui MPui INui. apply in_range_remove in INui.
  eby eapply PI.
Qed.

Lemma frees_related_preserves_partition_injectivity:
  forall b p n sp sp' tp,
    frees_related p n b ->
    part_update_buffer b sp = Some sp' ->
    partition_injective tp sp ->
    partition_injective tp sp'.
Proof.
  induction b as [|bi b IH];
    intros p n sp sp' tp FR PUB PI.

  (* Base case *)
  unfold part_update_buffer in PUB. simpl in PUB.
  inv PUB; done.

  (* Step case *)
  unfold part_update_buffer in *; simpl in PUB. 
  destruct (part_update bi sp) as [spi|] _eqn : PU; [simpl in PUB|done].
  eapply IH.
      intros bi' IN'. apply (FR bi' (in_cons _ _ _ IN')).
    eassumption.
  eapply frees_related_item_preserves_partition_injectivity; try edone.
  apply in_eq.
Qed.

Lemma remove_disj_preserves_partition_injectivity:
  forall tp sp p n,
    (forall r, In r sp -> ranges_disjoint r (p, n)) ->
    (forall r, In r sp -> range_non_empty r) ->
    partition_injective ((p, n) :: tp) sp ->
    partition_injective tp sp.
Proof.
  intros tp sp p n DISJ RNE PI pui nui MPui INui.
  destruct (PI pui nui MPui INui) as [r (RI & IN)].
  simpl in IN; destruct IN as [<- | IN].
    byContradiction.
    eapply ranges_disjoint_dont_overlap.
      apply (DISJ (pui, nui) INui).
    eapply ranges_overlap_comm, overlap_inside_overlap. 2 : apply RI. 
    eapply ranges_overlap_refl. by apply RNE.
  eexists; eby split. 
Qed.

Lemma mem_consistent_with_part_valid_alloc:
  forall m p r t,
    mem_related_with_partitioning m p ->
    In r (p t) ->
    valid_alloc_range r.
Proof.
  intros m p r t (_ & _ & AR) IN.
  assert (RA: range_allocated r MObjStack m).
    apply (AR r). eby eexists.
  eby eapply allocated_range_valid.
Qed.

Lemma non_stack_mem_related_sym:
  forall m m',
    non_stack_mem_related m m' -> non_stack_mem_related m' m.
Proof.
  intros m m' NSR r k. 
  specialize (NSR r k).
  destruct k; try done; by apply iff_sym.
Qed.

(* Machinery for proving preservation for non_stack_mem_related *)
Definition stack_or_write_item (bi : buffer_item) : Prop :=
  match bi with
    | BufferedAlloc _ _ MObjStack => True
    | BufferedFree _ MObjStack => True
    | BufferedWrite _ _ _ => True
    | _ => False
  end.

Lemma non_stack_mem_rel_preserved_by_stack_or_write:
  forall tm sm bi sm',
    non_stack_mem_related tm sm ->
    apply_buffer_item bi sm = Some sm' ->
    stack_or_write_item bi ->
    non_stack_mem_related tm sm'.
Proof.
  intros tm sm bi sm' NSMR ABI SOW r k.
  unfold apply_buffer_item, stack_or_write_item in *.
  specialize (NSMR r k).
  destruct k; try done; (
    split;
    [intro RA; apply NSMR in RA; destruct bi as [? ? ? | ? ? [] | ? []]; try done;
      [apply (store_preserves_allocated_ranges ABI r _) |
       eapply alloc_preserves_allocated |
       destruct (free_preserves_allocated ABI _ _ RA)as [ | []]] |
     intro RA; apply NSMR; destruct bi as [? ? ? | ? ? [] | ? []]; try done;
      [apply (store_preserves_allocated_ranges ABI r _) |
       destruct (alloc_preserves_allocated_back ABI _ _ RA) as [[]|] |
       eapply free_preserves_allocated_back]]); 
        edone.
Qed.

Lemma non_stack_mem_rel_preserved_by_stack_or_write_buffer:
  forall b tm sm sm',
    non_stack_mem_related tm sm ->
    apply_buffer b sm = Some sm' ->
    (forall bi, In bi b -> stack_or_write_item bi) ->
    non_stack_mem_related tm sm'.
Proof.
  induction b as [|bi br IH];
    intros tm sm sm' NSMR AB SOW.

  by inv AB.

  simpl in AB. destruct (apply_buffer_item bi sm) as [smi|] _eqn : ABI; try done.
  simpl in AB.
  eapply (IH tm smi); try edone.
  specialize (SOW bi (in_eq bi _)).
  eapply non_stack_mem_rel_preserved_by_stack_or_write; try edone.
  intros bi' IN. apply (SOW bi' (in_cons _ _ _ IN)).
Qed.

Lemma non_stack_mem_rel_preserved_by_stack_or_write_tgt:
  forall tm sm bi tm',
    non_stack_mem_related tm sm ->
    apply_buffer_item bi tm = Some tm' ->
    stack_or_write_item bi ->
    non_stack_mem_related tm' sm.
Proof.
  intros tm sm bi tm' NSMR ABI SOW.
  apply non_stack_mem_related_sym in NSMR.
  eby eapply non_stack_mem_related_sym, 
    non_stack_mem_rel_preserved_by_stack_or_write.
Qed.

(* Here is how to get the assumptions for presevation of non_stack_mem_related: *)
Lemma allocs_related_impl_stack_or_write:
  forall n p b,
    allocs_related p n b ->
    forall bi, In bi b -> stack_or_write_item bi.
Proof.
  by intros n p b AR bi IN; destruct (AR bi IN); 
    destruct bi as [? ? ? | ? ? [] | ? []].
Qed.

Lemma frees_related_impl_stack_or_write:
  forall n p b,
    frees_related p n b ->
    forall bi, In bi b -> stack_or_write_item bi.
Proof.
  by intros n p b FR bi IN; destruct (FR bi IN); 
    destruct bi as [? ? ? | ? ? [] | ? []].
Qed.

Lemma scratch_impl_stack_or_write:
  forall bi, is_item_scratch_update bi -> stack_or_write_item bi.
Proof. by intros [? ? ? | ? ? [] | ? []]. Qed.


Lemma chunk_inside_range_list_spec:
  forall p c l,
    chunk_inside_range_list p c l = true ->
    exists r, In r l /\ range_inside (range_of_chunk p c) r.
Proof.
  intros p c l CIL.
  
  induction l as [|h l IH]; simpl in CIL. done.

  destruct (range_inside_dec (range_of_chunk p c) h) as [RI | NRI].
    exists h. split. apply in_eq. done.
  destruct (IH CIL) as [r [IN RI]].
  exists r. split. apply in_cons. done. done.
Qed.

Lemma unbuffering_other_item_agrees_on_scratch:
  forall bi m m' part part' t t',
    t' <> t ->
    mem_related_with_partitioning m part ->
    apply_buffer_item bi m = Some m' ->
    part_update bi (part t) = Some part' ->
    mem_agrees_on_scratch m m' (part t').
Proof.
  intros bi m m' part part' t t' Nt [PD [RLD MR]] ABI PU.
  intros r p c IN RI SCR.
  unfold part_update in PU.
  unfold apply_buffer_item in ABI.
  buffer_item_cases (destruct bi as [pi ci vi | pi ni ki | pi ki]) Case.

  Case "BufferedWrite".
    rewrite (load_store_other ABI). done.
    destruct (low_mem_restr (MPtr.block pi)) as [] _eqn : LMR.
      destruct p; destruct pi; left; intro; subst;
        simpl in *; by rewrite LMR in SCR.
    destruct (chunk_inside_range_list pi ci (part t)) as [] _eqn:CIL;
      try done.
    apply chunk_inside_range_list_spec in CIL.
    destruct CIL as [r' [INP' RI']].
    eapply disjoint_inside_disjoint. 2 : apply RI'.
    eapply ranges_disjoint_comm, disjoint_inside_disjoint, RI.
    apply (PD _ _ Nt _ IN _ INP').
  Case "BufferedAlloc".
    rewrite (load_alloc_other ABI). done.
    destruct ki; destruct valid_alloc_range_dec; try done; try (
      destruct (low_mem_restr (MPtr.block pi)) as [] _eqn : LMR; try done;
        by destruct p; destruct pi; left; intro; subst; simpl in *; 
          rewrite LMR in SCR).
    inv PU.
    assert (RA: range_allocated r MObjStack m). 
      apply (MR r). eby eexists.
    pose proof (alloc_cond_spec (pi, ni) MObjStack m) as Aspec.
    rewrite ABI in Aspec.
    destruct Aspec as (_ & _ & _ & OVERNA).
    destruct (ranges_disjoint_dec (range_of_chunk p c) (pi, ni)) 
      as [DISJ | OVER]; try done.
    byContradiction; eapply OVERNA.
    2 : apply RA. 
    eby eapply ranges_overlap_comm, overlap_inside_overlap.
  Case "BufferedFree".
    pose proof (free_cond_spec pi ki m) as Fspec. rewrite ABI in Fspec.
    destruct Fspec as [ni RA].
    rewrite (load_free_other ABI RA). done.
    destruct ki; try (
      destruct (low_mem_restr (MPtr.block pi)) as [] _eqn : LMR; try done;
        by destruct p; destruct pi; left; intro; subst; simpl in *; 
          rewrite LMR in SCR).
    destruct (pointer_in_range_list pi (part t)) as [] _eqn : PIR; try done.
    destruct (pointer_in_range_list_in _ _ PIR) as [sz INpi].
    assert (RAsz: range_allocated (pi, sz) MObjStack m).
      apply (MR (pi, sz)). eby eexists.
    destruct (alloc_ranges_same RAsz RA) as [-> _].
    eapply disjoint_inside_disjoint.
    apply (PD _ _ Nt _ IN _ INpi). done.
Qed.

Lemma unbuffering_other_buffer_agrees_on_scratch:
  forall b part t' t m part' m',
    t' <> t ->
    mem_related_with_partitioning m part ->
    apply_buffer b m = Some m' ->
    part_update_buffer b (part t) = Some part' ->
    mem_agrees_on_scratch m m' (part t').
Proof.
  intros b part t'. remember (part t') as pt. revert part Heqpt.
  induction b as [|bi br IH];
    intros part E t m part' m' NE MRWP AB PUB;
      unfold part_update_buffer in *;
        simpl in AB, PUB.

  by inv AB; inv PUB.

  destruct (apply_buffer_item bi m) as [mi|] _eqn : ABI; try done.
  destruct (part_update bi (part t)) as [pi|] _eqn : PU; try done.
  simpl in AB, PUB.
  intros r p c IN RI SCR.
  eapply trans_eq.
    eapply unbuffering_other_item_agrees_on_scratch; try edone.
    by rewrite <- E.
  eapply IH.
  3: eby eapply apply_buffer_item_preserves_mem_partitioning. 
  eby rewrite update_partitioning_o. apply NE. done. 
  rewrite update_partitioning_s. edone. edone. edone. edone.
Qed.

Lemma range_lists_disjoint_tail1:
  forall h t l,
    range_lists_disjoint (h :: t) l ->
    range_lists_disjoint t l.
Proof.
  intros h t l RLD r IN r' IN'.
  eapply RLD; try done. by apply in_cons.
Qed.

Lemma range_lists_disjoint_tail2:
  forall h t l,
    range_lists_disjoint l (h :: t) ->
    range_lists_disjoint l t.
Proof.
  intros h t l RLD r IN r' IN'.
  eapply RLD; try done. by apply in_cons.
Qed.

Lemma buffer_scratch_ranges_are_scratch:
  forall p n b,
    In (p, n) (buffer_scratch_ranges b) ->
    scratch_ptr p.
Proof.
  intros p n b IN.
  induction b as [|bi br IH]. done.
  
  simpl in IN. 
  destruct bi as [? ? ? | p' ? [] | ? []]; try (by apply IH).
  destruct (low_mem_restr (MPtr.block p')) as [] _eqn : LMR.
    by apply IH.
  simpl in IN. destruct IN as [E | IN].
    inv E. by destruct p.
  by apply IH.
Qed.

Lemma unbuffer_preserves_scratch_allocs_fresh:
  forall bi sp spt' bs t br,
  part_update bi (sp t) = Some spt' ->
  bs t = bi :: br ->
  scratch_allocs_fresh bs sp ->
  scratch_allocs_fresh 
    (tupdate t br bs)
    (update_partitioning t spt' sp).
Proof.
  intros bi sp spt' bs t br PU BS (BDISJ & BSDISJ & BDISJP).
  
  split.
    (* Buffers are still disjoint *)
    intro t'. specialize (BDISJ t'). 
    unfold tupdate. destruct (peq t' t) as [-> | _]; [|done].
    rewrite BS in BDISJ. simpl in BDISJ.
    destruct bi as [p c v | p n [] | p []]; try done.
    destruct (low_mem_restr (MPtr.block p)); try done.
    by destruct BDISJ.
  split.
    (* Buffers are still pairwise disjoint *)
    intros t' t'' NE. specialize (BSDISJ t' t'' NE).
    unfold tupdate. 
    destruct (peq t'' t) as [-> | N1]; destruct (peq t' t) as [-> | N2]; 
      try done; rewrite BS in BSDISJ; simpl in BSDISJ;
        destruct bi as [p c v | p n [] | p []]; try done;
          destruct (low_mem_restr (MPtr.block p)); try done.
      eby eapply range_lists_disjoint_tail1.
    eby eapply range_lists_disjoint_tail2.
  (* Buffers are disjoint from all partitions *)
  intros t' t''.
  specialize (BDISJP t' t'').
  specialize (BDISJ t').
  specialize (BSDISJ t'' t').
  unfold tupdate, update_partitioning. 
  destruct (peq t'' t) as [-> | N1]; destruct (peq t' t) as [-> | N2]; 
    try done; try rewrite BS in *; simpl in BDISJP.
      (* Buffer and partition in the same thread where 
         the unbuffering took place *)
      destruct bi as [p c v | p n [] | p []]; try done; simpl in PU;
        simpl in BDISJ;
        try destruct (low_mem_restr (MPtr.block p)) as [] _eqn : LMR;
          clarify; try destruct (chunk_inside_range_list p c (sp t));
            clarify; try destruct valid_alloc_range_dec; clarify;
              try destruct range_in_dec as [RIx | RNIx]; clarify;
        try (destruct pointer_in_range_list;  [|done]; inv PU;
          intros r IN r' IN'; destruct r'; apply in_range_remove in IN';
            eby eapply BDISJP). 
      (* Allocation in machine *)
      intros r IN r' IN'. simpl in IN'. destruct IN' as [<- | IN'].
        destruct r as [pr nr].
        apply buffer_scratch_ranges_are_scratch in IN. 
        destruct p; destruct pr; left; intro E; rewrite E in *; simpl in *;
          by rewrite LMR in IN.
      by eapply BDISJP.
      (* Allocation in scratch *)
      simpl in *. destruct BDISJ as [BDISJ NIN].
      intros r IN r' IN'. simpl in IN'. destruct IN' as [<- | IN'].
      by apply NIN, ranges_disjoint_comm in IN.
      eapply BDISJP; try edone; by apply in_cons.
    (* Buffer in the same thread, but partition different *)
    destruct bi as [p c v | p n [] | p []]; try done.
    destruct low_mem_restr; try done.
    eby eapply range_lists_disjoint_tail1.
  (* Buffer in other thread, partition same *)
  destruct bi as [p c v | p n [] | p []]; try done; simpl in PU;
    simpl in BDISJ; simpl in BSDISJ;
      try destruct (low_mem_restr (MPtr.block p)) as [] _eqn : LMR;
        clarify; try destruct (chunk_inside_range_list p c (sp t));
          clarify; try destruct valid_alloc_range_dec; clarify;
              try destruct range_in_dec as [RIx | RNIx]; clarify;
        try (destruct pointer_in_range_list;  [|done]; inv PU;
          intros r IN r' IN'; destruct r'; apply in_range_remove in IN';
            eby eapply BDISJP). 
  (* Allocation in machine *)
  intros r IN r' IN'. simpl in IN'. destruct IN' as [<- | IN'].
  destruct r as [pr nr].
  apply buffer_scratch_ranges_are_scratch in IN. 
  destruct p; destruct pr; left; intro E; rewrite E in *; simpl in *;
    by rewrite LMR in IN.
  by eapply BDISJP.
  (* Allocation in scratch *)
  simpl in *. specialize (BSDISJ N1).
  intros r IN r' IN'. simpl in IN'. destruct IN' as [<- | IN'].
  eapply ranges_disjoint_comm, BSDISJ. apply in_eq. done.
  eapply BDISJP; try edone; by apply in_cons.
Qed.

Lemma scratch_allocs_fresh_ext: 
  forall b b' sp sp',
    scratch_allocs_fresh b sp ->
    (forall t, sp t = sp' t) ->
    (forall t, b t = b' t) ->
    scratch_allocs_fresh b' sp'.
Proof.
  intros b b' sp sp' (BDISJ & BSDISJ & BDISJP) SPE BE.
  split. intro t; rewrite <- BE; apply BDISJ.
  split. intros t' t; rewrite <- ! BE; apply BSDISJ.
  intros t' t. rewrite <- BE, <- SPE; apply BDISJP.
Qed.

Lemma scratch_allocs_fresh_apply_buffer:
  forall b sp spt' bs bs' t,
    part_update_buffer b (sp t) = Some spt' ->
    bs t = b ++ (bs' t) ->
    (forall t', t' <> t -> bs t' = bs' t') ->
    scratch_allocs_fresh bs sp ->
    scratch_allocs_fresh bs' (update_partitioning t spt' sp).
Proof.
  induction b as [|bi br IH]; intros sp spt' bs bs' t PUB DC OB SAF.

  unfold part_update_buffer in PUB; inv PUB.
  eapply scratch_allocs_fresh_ext; try edone.
  intro t'. unfold update_partitioning. by destruct (peq t' t) as [-> | ?].
  intro t'. destruct (peq t' t) as [-> | ?]. by rewrite DC.
  by apply OB.

  unfold part_update_buffer in *. simpl in PUB. 
  destruct (part_update bi (sp t)) as [spi|] _eqn : PU; [|done].
  rewrite <- app_comm_cons in DC. simpl in PUB.
  pose proof (unbuffer_preserves_scratch_allocs_fresh _ _ _ _ _ _ PU DC SAF) 
    as SAFI.
  eapply scratch_allocs_fresh_ext. eapply IH.
      4: apply SAFI. rewrite update_partitioning_s. apply PUB. 
      eby rewrite tupdate_s. 
      intros t' N'.  rewrite tupdate_o. by apply OB. done.
    intros t'. destruct (peq t' t) as [-> | N].
      by rewrite !update_partitioning_s.
    by rewrite !update_partitioning_o.
  done.
Qed.

Lemma load_result_machine:
  forall v c,
    machine_val v ->
    machine_val (Val.load_result c v).
Proof. by intros [] []. Qed.

Lemma apply_machine_item_preserves_machine_memory:
  forall bi m m'
    (MBI: machine_buffer_item bi)
    (ABI: apply_buffer_item bi m = Some m')
    (MCM: mem_content_machine m),
      mem_content_machine m'.
Proof.
  intros. intros p' c'.
  specialize (MCM p' c').
  
  buffer_item_cases (destruct bi as [p c v|p n k|p k]) Case.
  
  Case "BufferedWrite".
    destruct (range_eq_dec (range_of_chunk p c) (range_of_chunk p' c'))
      as [RCeq | RCneq].
    (* Reading exactly the memory written by the unbuffered store *)
      injection RCeq. 
      intro SCeqm.
      assert (SCeq: size_chunk c = size_chunk c').
      destruct c; destruct c'; simpl in *; compute in SCeqm; done.
      intro Peq; subst.
      rewrite (load_store_similar ABI SCeq).
      destruct compatible_chunks.
        apply load_result_machine. apply MBI.
      done.
    (* Reading from different memory; two cases: *)
    destruct (ranges_disjoint_dec (range_of_chunk p c) 
                                  (range_of_chunk p' c')) 
      as [RDISJ | ROVER].
      (* Ranges completely disjoint *)
      by rewrite <- (load_store_other ABI RDISJ).
    (* Ranges overlap *)
    pose proof (load_chunk_allocated_spec c' m p') as LDAL.
    destruct (load_ptr c' m p') as [v'|] _eqn : LD.
      apply (store_preserves_chunk_allocation ABI _ _) in LDAL.
      rewrite (load_store_overlap ABI ROVER RCneq LDAL). done.
    pose proof (load_chunk_allocated_spec c' m' p') as LDAL'.
    destruct (load_ptr c' m' p') as [v''|] _eqn : LD'; [|done].
    by apply (store_preserves_chunk_allocation ABI _ _) in LDAL'. 

  Case "BufferedAlloc".
    unfold apply_buffer_item in ABI.
    destruct (ranges_disjoint_dec (range_of_chunk p' c') (p, n))
      as [DISJ | OVER].
      by rewrite (load_alloc_other ABI DISJ).
    destruct (range_inside_dec (range_of_chunk p' c') (p, n))
      as [RI | NRI].
      destruct (pointer_chunk_aligned_dec p' c') as [ALG | NALG].
        by rewrite (load_alloc_inside ABI RI ALG).
      pose proof (load_chunk_allocated_spec c' m' p') as LD'.
      destruct (load_ptr c' m' p'). elim NALG. by destruct LD'. 
      done.
    by rewrite (load_alloc_overlap ABI NRI OVER).

  Case "BufferedFree".
    unfold apply_buffer_item in ABI.
    pose proof (free_cond_spec p k m) as Fspec; 
      rewrite ABI in Fspec; destruct Fspec as [n RA].

    destruct (ranges_disjoint_dec (range_of_chunk p' c') (p, n)) 
        as [DISJ | OVER].
      by rewrite (load_free_other ABI RA DISJ). 
    by rewrite (load_free_overlap ABI RA OVER).
Qed.

Lemma apply_machine_buffer_preserves_machine_memory:
  forall b m m'
    (MBI: machine_buffer b)
    (AB:  apply_buffer b m = Some m')
    (MCM: mem_content_machine m),
      mem_content_machine m'.
Proof.
  induction b as [|bi b IH]; intros.
  
  by inv AB.
  
  simpl in AB.
  destruct (apply_buffer_item bi m) as [mi|] _eqn : Emi; [|done].
  simpl in AB.
  eapply IH. 
      intros bi' IN'. apply MBI. by right.
    edone.
  eapply apply_machine_item_preserves_machine_memory. 
      apply (MBI bi). by left.
    edone.
  done.
Qed.

(* Summary for unbuffering allocation *)
(* This is mostly a plumbing lemma that connects all the stuff above *)
Lemma unbuffer_alloc_preserves_tso_pc_witt:
  forall p n smp smpt' ttso tthr sbis tm' t stso sm' tbr sthr sbr bp tmp,
    apply_buffer_item (BufferedAlloc p n MObjStack) ttso.(tso_mem) = Some tm' ->
    allocs_related p n sbis ->
    part_update_buffer sbis (smp t) = Some smpt' ->
    apply_buffer sbis stso.(tso_mem) = Some sm' ->
    ttso.(tso_buffers) t = BufferedAlloc p n MObjStack :: tbr ->
    bp t = sbis :: sbr ->
    tso_pc_related_witt (ttso, tthr) (stso, sthr) bp tmp smp ->
    exists bp', exists tmp', exists smp', exists stso',
      apply_buffer_reachable t stso sbis stso' /\
      stso'.(tso_mem) = sm' /\ (* might want to constrain buffers as well *)
      stso'.(tso_buffers) t = flatten sbr /\
      tso_pc_related_witt (mktsostate (tupdate t tbr ttso.(tso_buffers))
                                      tm', tthr)
                           (stso', sthr)
                           bp' tmp' smp'.
Proof.
  intros p n smp smpt' ttso tthr sbis tm' t stso sm' tbr sthr sbr bp tmp.
  intros TABI AR PUB SAB TBUFF BP TSOREL; simpl in tthr, sthr.
  pose proof TABI as TAP. unfold apply_buffer_item in TAP.
  destruct TSOREL as (MTB & NSMR & (MCRt & MCRs & LR & MCM) & SC & 
    BPD & BNE & SAF & MRPt & MRPs & TREL).

  pose proof (BPD t) as BPFL. rewrite BP in BPFL. simpl in BPFL. 

  destruct (TSO.unbuffer_to_tso_state _ _ _ _ _ BPFL SAB) 
    as [stso' (ABR & BUFtstso & BUFother & MEMstso)].

  exists (fun t' => if peq t' t then sbr else bp t').
  exists (update_partitioning t ((p, n) :: (tmp t)) tmp).
  exists (update_partitioning t smpt' smp).
  exists stso'.
  split. apply ABR.
  split. apply MEMstso.
  split. done.
  split; subst. (* thread buffers only refer to machine values *)
    intros t' bi IN. apply (MTB t' bi).
    simpl in IN|-*.
    destruct (peq t' t) as [-> | N].
      rewrite BUFtstso in IN.
      rewrite BPFL. apply in_or_app. by right.
    by rewrite <- BUFother.
  split.
    (* non_stack_mem_related preservation *)
    eapply non_stack_mem_rel_preserved_by_stack_or_write_tgt; try edone.
    eapply non_stack_mem_rel_preserved_by_stack_or_write_buffer; try edone.
    eby eapply allocs_related_impl_stack_or_write.
  split.
    (* mem_content_related preservation *)
    split. eby erewrite mem_consistent_with_restr_apply_item.
    split. eby erewrite mem_consistent_with_restr_apply_buffer.
    (* Load value relation requires some more work: *)
    split.
      eapply allocs_related_preserves_alloc_load_rels; try edone.
              eby intros p' c' RIC [_ PCA]; eapply load_alloc_inside.
            eapply non_conflicting_allocs_buffer_from_relation; try edone.
          apply (fun t' => proj1 (TREL t')).
       eby eapply alloc_ptr_tgt_preserves_load_rel.
       by destruct (alloc_someD TAP).
    (* Memory contents are machine values *)
    eapply apply_machine_buffer_preserves_machine_memory; [|apply SAB|done].
    intros bi IN. apply (MTB t). simpl.
    rewrite BPD, BP. simpl. rewrite in_app. by left.
  split.
    eby eapply TSO.apply_buffer_reachable_preserves_tso_consistency.
  split. (* Buffer partitioning *)
    intro t'.
    destruct (peq t' t) as [-> | N]. done.
    rewrite BUFother. apply BPD. done.
  split. (* Buffer partitions not empty *)
    intros t' b IN. apply (BNE t').
    destruct (peq t' t) as [-> | N]. rewrite BP. by right.
    done.
  split; simpl. (* Allocation freshness for scratch items *)
    eapply scratch_allocs_fresh_apply_buffer. edone. 3 : edone. 
    by rewrite BUFtstso, BPD, BP. intros ? ?; by rewrite BUFother.
  split. (* Memory related with partitioning in target *)
    eby eapply alloc_ptr_stack_preserves_mem_partitioning.
  split. (* Memory related with partitioning in source *) 
    eby eapply apply_buffer_preserves_mem_partitioning. 
  intro t'.
  specialize (TREL t'). destruct TREL as [PI [BREL BSREL]].
  split.
    unfold update_partitioning.
    destruct (peq t' t) as [-> | N].
      eapply allocs_related_preserves_partition_injectivity.
      edone. edone. 
      intros p' n' MP IN. destruct (PI p' n' MP IN) as [r' [RI RA]].
      eexists. split. edone. by apply in_cons.
    done.
  (* Per-thread buffered simulation is preserved *)
  simpl in BREL, BSREL.
  destruct (peq t' t) as [-> | N].
    rewrite !update_partitioning_s, tupdate_s.
    split. rewrite TBUFF in BREL. inv BREL. 
    by rewrite BP in *; clarify; rewrite PUB in *; clarify.
    by simpl in BIIR.
    (* same thread as the unbuffering one *)
    destruct (sthr ! t) as [sst|]; destruct (tthr ! t) as [tst|];
      simpl in BSREL; try done.
      simpl. rewrite TBUFF in BSREL.
      rewrite BP in BSREL.  simpl in BSREL.
      apply <- buffered_states_related_prepend_tgt.
      apply <- buffered_states_related_prepend_src; try edone.
      simpl. destruct valid_alloc_range_dec. 
      destruct range_in_dec as [[r' [IN' RO']] | ]; [|done].
        inv BREL; rewrite TBUFF in *; clarify;
        by destruct (ranges_disjoint_dont_overlap _ _ (RIN _ IN') RO').
      inv BREL; rewrite TBUFF in *; clarify.
    destruct BSREL as (_ & _ & E & _). by rewrite E in TBUFF.
  (* Other threads - use the memory "sameness" *)
  rewrite ! update_partitioning_o, tupdate_o; try done.
  split. done.
  destruct (sthr ! t') as [sst|]; destruct (tthr ! t') as [tst|]; 
    simpl in BSREL; try done.
  simpl.
  pose proof MRPs as X; destruct X as [PD [RLD RLA]].
  destruct (apply_buffer_preserves_mem_partitioning _ _ _ _ _ _ 
    MRPs SAB PUB) as [PR' [RLD' RLA']].
  apply buffered_states_related_load_inv with (smem := tso_mem stso);
    try done.
        intros r IN. apply (RLA r). eby eexists.
      intros r IN. apply (RLA' r). exists t'.
      rewrite update_partitioning_o. done. done.
    eapply tso_consistent_safe_buffer_app; try edone.
      rewrite <- app_nil_end. apply BPD.
    eapply tso_consistent_safe_buffer_app; try edone.
      eby eapply TSO.apply_buffer_reachable_preserves_tso_consistency.
    rewrite <- app_nil_end, BUFother. 
    apply BPD. done.  
  eby eapply unbuffering_other_buffer_agrees_on_scratch.
Qed.

(* Summary for unbuffering free *)
(* This is mostly a plumbing lemma that connects all the stuff above *)
Lemma unbuffer_free_preserves_tso_pc_witt:
  forall p n smp smpt' ttso tthr sbis tm' t stso sm' tbr sthr sbr bp tmp tr,
    apply_buffer_item (BufferedFree p MObjStack) ttso.(tso_mem) = Some tm' ->
    frees_related p n sbis ->
    (forall r, In r smpt' -> ranges_disjoint r (p, n)) ->
    part_update_buffer sbis (smp t) = Some smpt' ->
    apply_buffer sbis stso.(tso_mem) = Some sm' ->
    ttso.(tso_buffers) t = BufferedFree p MObjStack :: tbr ->
    tmp t = (p, n) :: tr ->
    bp t = sbis :: sbr ->
    tso_pc_related_witt (ttso, tthr) (stso, sthr) bp tmp smp ->
    exists bp', exists tmp', exists smp', exists stso',
      apply_buffer_reachable t stso sbis stso' /\
      stso'.(tso_mem) = sm' /\ (* might want to constrain buffers as well *)
      stso'.(tso_buffers) t = flatten sbr /\
      tso_pc_related_witt (mktsostate (tupdate t tbr ttso.(tso_buffers))
                                      tm', tthr)
                           (stso', sthr)
                           bp' tmp' smp'.
Proof.
  intros p n smp smpt' ttso tthr sbis tm' t stso sm' tbr sthr sbr bp tmp tr.
  intros TABI FR RDnp PUB SAB TPART TBUFF BP TSOREL.
  pose proof TABI as TFP. unfold apply_buffer_item in TFP.
  destruct TSOREL as (MTB & NSMR & (MCRt & MCRs & LR & MCM) & SC & 
    BPD & BNE & SAF & MRPt & MRPs & TREL).

  pose proof (BPD t) as BPFL. rewrite BP in BPFL. simpl in BPFL. 

  destruct (TSO.unbuffer_to_tso_state _ _ _ _ _ BPFL SAB) 
    as [stso' (TAU & BUFtstso & BUFother & MEMstso)].

  assert (PINJ : forall t',
    partition_injective (tmp t') (update_partitioning t smpt' smp t')).
    intro t'.
    unfold update_partitioning.
    destruct (peq t' t) as [-> | N].
      eapply frees_related_preserves_partition_injectivity. edone.
      edone. apply (proj1 (TREL t)).
    apply (proj1 (TREL t')).

  assert (MRWPs': mem_related_with_partitioning sm'
    (update_partitioning t smpt' smp)).
    eby eapply apply_buffer_preserves_mem_partitioning. 

  exists (fun t' => if peq t' t then sbr else bp t').
  exists (update_partitioning t tr tmp).
  exists (update_partitioning t smpt' smp).
  exists stso'.
  split. apply TAU.
  split. apply MEMstso.
  split. done.
  split; simpl; subst. (* thread buffers only refer to machine values *)
    intros t' bi IN. apply (MTB t' bi).
    simpl in IN|-*.
    destruct (peq t' t) as [-> | N].
      rewrite BUFtstso in IN.
      rewrite BPFL. apply in_or_app. by right.
    by rewrite <- BUFother.
  split.
    (* non_stack_mem_related preservation *)
    eapply non_stack_mem_rel_preserved_by_stack_or_write_tgt; try edone.
    eapply non_stack_mem_rel_preserved_by_stack_or_write_buffer; try edone.
    eby eapply frees_related_impl_stack_or_write.
  split.
    (* mem_content_related preservation *)
    split. eby erewrite mem_consistent_with_restr_apply_item.
    split. eby erewrite mem_consistent_with_restr_apply_buffer.
    (* Load value relation requires some more work: *)
    split.
    apply (free_preserves_load_rel_tgt p n t (tso_mem ttso) _ _ 
      (update_partitioning t smpt' smp) tmp); try done; simpl.
        eapply non_stack_mem_rel_preserved_by_stack_or_write_buffer; try edone.
        eby eapply frees_related_impl_stack_or_write.
       rewrite TBUFF. apply in_eq.
      rewrite update_partitioning_s. done.
    eby eapply frees_related_preserves_load_rel_src.
    (* Memory contents are machine values *)
    eapply apply_machine_buffer_preserves_machine_memory; [|apply SAB|done].
    intros bi IN. apply (MTB t). simpl.
    rewrite BPD, BP. simpl. rewrite in_app. by left.
  split.
    eby eapply TSO.apply_buffer_reachable_preserves_tso_consistency.
  split. (* Buffer partitioning *)
    intro t'.
    destruct (peq t' t) as [-> | N]. done.
    rewrite BUFother. apply BPD. done.
  split. (* Buffer partitions not empty *)
    intros t' b IN. apply (BNE t').
    destruct (peq t' t) as [-> | N]. rewrite BP. by right.
    done.
  split. (* Allocation freshness for scratch items *)
    eapply scratch_allocs_fresh_apply_buffer. edone. 3 : edone. 
    by rewrite BUFtstso, BPD, BP. intros ? ?; by rewrite BUFother.
  split. (* Memory related with partitioning in target *)
    replace tr with (range_remove p (tmp t)).
      eapply free_ptr_preserves_mem_partitioning. edone. edone.
      exists n. rewrite TBUFF; apply in_eq.
    rewrite TBUFF. simpl. eby destruct (MPtr.eq_dec p p).
  split. (* Memory related with partitioning in source *) 
    eby eapply apply_buffer_preserves_mem_partitioning. 
  intro t'.
  specialize (TREL t'). destruct TREL as [PI [BREL BSREL]].
  split.
    destruct (peq t' t) as [-> | N].
      rewrite ! update_partitioning_s.
      eapply remove_disj_preserves_partition_injectivity. edone.
        intros r IN. apply valid_alloc_range_non_empty.
        eapply allocated_range_valid. eapply (proj2 (proj2 MRWPs')).
        exists t. rewrite update_partitioning_s. done.
        pose proof (proj1 (proj2 (MRWPs'))).
      eapply frees_related_preserves_partition_injectivity.
      edone. edone. rewrite <- TBUFF. done.
    rewrite ! update_partitioning_o. apply PI. done. done.
  (* Per-thread buffered simulation is preserved *)
  simpl in *.
  destruct (peq t' t) as [-> | N].
    rewrite !update_partitioning_s, tupdate_s.
    split. rewrite TPART in BREL. inv BREL. 
    by rewrite BP in *; clarify; rewrite PUB, TBUFF in *; clarify.
    by simpl in BIIR.
    (* same thread as the unbuffering one *)
    destruct (sthr ! t) as [sst|]; destruct (tthr ! t) as [tst|]; 
      simpl in BSREL; try done.
      simpl. rewrite TBUFF in BSREL.
      rewrite BP in BSREL. 
      apply <- buffered_states_related_prepend_tgt.
      apply <- buffered_states_related_prepend_src; try edone.
      rewrite TPART in BSREL. edone.
      simpl. by destruct (MPtr.eq_dec p p).
    destruct BSREL as (_ & _ & E & _). by rewrite E in TPART.
  (* Other threads - use the memory "sameness" *)
  rewrite ! update_partitioning_o, tupdate_o; try done.
  split. done.
  destruct (sthr ! t') as [sst|]; destruct (tthr ! t') as [tst|]; 
    simpl in BSREL; try done.
  simpl.
  pose proof MRPs as X; destruct X as [PD [RLD RLA]].
  destruct (apply_buffer_preserves_mem_partitioning _ _ _ _ _ _ 
    MRPs SAB PUB) as [PR' [RLD' RLA']].
  apply buffered_states_related_load_inv with (smem := tso_mem stso);
    try done.
        intros r IN. apply (RLA r). eby eexists.
      intros r IN. apply (RLA' r). exists t'.
      rewrite update_partitioning_o. done. done.
    eapply tso_consistent_safe_buffer_app; try edone.
      rewrite <- app_nil_end. apply BPD.
    eapply tso_consistent_safe_buffer_app; try edone.
      eby eapply TSO.apply_buffer_reachable_preserves_tso_consistency.
    rewrite <- app_nil_end.
    rewrite BUFother. apply BPD. done.
  eby eapply unbuffering_other_buffer_agrees_on_scratch.
Qed.

Lemma sim_non_stack_alloc_preserves_load_rel:
  forall tm sm tm' sm' p n k,
    load_values_related tm sm ->
    alloc_ptr (p, n) k tm = Some tm' ->
    alloc_ptr (p, n) k sm = Some sm' -> 
    match k with MObjStack => False | _ => True end ->
    load_values_related tm' sm'.
Proof.
  intros tm sm tm' sm' p n k LREL ACT ACS NOST.
  intros p' MP' c'.
  specialize (LREL p' MP' c').
  destruct (ranges_disjoint_dec (range_of_chunk p' c') (p, n))
    as [DISJ | OVER].
    by rewrite (load_alloc_other ACT DISJ);
       rewrite (load_alloc_other ACS DISJ).
  destruct (range_inside_dec (range_of_chunk p' c') (p, n))
    as [RI | NRI].
    destruct (pointer_chunk_aligned_dec p' c') as [ALG | NALG].
      rewrite (load_alloc_inside ACT RI ALG).
      rewrite (load_alloc_inside ACS RI ALG).
      done.
    pose proof (load_chunk_allocated_spec c' tm' p') as LDT.
    pose proof (load_chunk_allocated_spec c' sm' p') as LDS.
    destruct (load_ptr c' tm' p'). elim NALG. by destruct LDT.
    destruct (load_ptr c' sm' p'). elim NALG. by destruct LDS.
    done.
  rewrite (load_alloc_overlap ACT NRI OVER).
  rewrite (load_alloc_overlap ACS NRI OVER).
  done.
Qed.

Lemma sim_non_stack_free_preserves_load_rel:
  forall tm sm tm' sm' p k,
    mrestr tm = low_mem_restr ->
    non_stack_mem_related tm sm ->
    load_values_related tm sm ->
    free_ptr p k tm = Some tm' ->
    free_ptr p k sm = Some sm' -> 
    match k with MObjStack => False | _ => True end ->
    load_values_related tm' sm'.
Proof.
  intros cstm csmm cstm' csmm' p k MC NSR LREL FCST FCSM NOST.
  intros p' MP' c'.
  specialize (LREL p' MP' c').
  pose proof (free_cond_spec p k cstm) as FCS. rewrite FCST in FCS.
  pose proof (free_cond_spec p k csmm) as FCM. rewrite FCSM in FCM.
  destruct FCS as [n FCSA]. destruct FCM as [n' FCNA].
  assert (E : n = n').
    assert (MP: machine_ptr p). unfold machine_ptr. 
      pose proof (range_allocated_consistent_with_restr _ _ _ _ FCSA).
      by rewrite <- MC; destruct p.
    specialize (NSR (p, n') k).
    destruct k; try done; apply NSR in FCNA;
      by destruct (alloc_ranges_same FCNA FCSA).
  rewrite <- E in *; clear E n'.
  destruct (ranges_disjoint_dec (range_of_chunk p' c') (p, n))
    as [DISJ | OVER].
    by rewrite (load_free_other FCST FCSA DISJ);
       rewrite (load_free_other FCSM FCNA DISJ).
  by rewrite (load_free_overlap FCST FCSA OVER);
     rewrite (load_free_overlap FCSM FCNA OVER).
Qed.

Lemma sim_write_preserves_load_rel:
  forall tm sm tm' sm' c p v,
    mrestr tm = low_mem_restr ->
    load_values_related tm sm ->
    store_ptr c tm p v = Some tm' ->
    store_ptr c sm p v = Some sm' ->
    machine_val v ->
    load_values_related tm' sm'.
Proof.
  intros cstm csmm cstm' csmm' c p v MC LDREL STCS STCM MVAL p' MPTR' c'.

  assert (MP : machine_ptr p).
    pose proof (store_ptr_mem_consistent _ _ _ _ _ STCS).
    by destruct p; simpl in *; rewrite <- MC.

  specialize (LDREL p' MPTR' c').
  pose proof (load_chunk_allocated_spec c' cstm p') as LDAL.
  pose proof (load_chunk_allocated_spec c' cstm' p') as LDAL'.
  pose proof (load_chunk_allocated_spec c' csmm p') as LDALCM.
  pose proof (load_chunk_allocated_spec c' csmm' p') as LDALCM'.
  destruct (load_ptr c' cstm p') as [v'|] _eqn : CSLD.
    (* Load SUCCESS *)
    destruct (range_eq_dec (range_of_chunk p c) (range_of_chunk p' c'))
      as [RCeq | RCneq].
    (* Reading exactly the memory written by the unbuffered store *)
      injection RCeq. 
      intro SCeqm.
      assert (SCeq: size_chunk c = size_chunk c').
      destruct c; destruct c'; simpl in *; compute in SCeqm; done.
      intro Peq; subst.
      rewrite (load_store_similar STCS SCeq).
      rewrite (load_store_similar STCM SCeq).
      done.
    (* Reading from different memory; two cases: *)
    destruct (ranges_disjoint_dec (range_of_chunk p c) 
                                         (range_of_chunk p' c')) 
      as [RDISJ | ROVER].
      (* Ranges completely disjoint *)
      rewrite <- (load_store_other STCS RDISJ). rewrite CSLD.
      rewrite <- (load_store_other STCM RDISJ). done.
    (* Ranges overlap *)
    apply (store_preserves_chunk_allocation STCS _ _) in LDAL.
    rewrite (load_store_overlap STCS ROVER RCneq LDAL).
    destruct (load_ptr c' csmm p') as [v''|] _eqn : CMLD.
    apply (store_preserves_chunk_allocation STCM _ _) in LDALCM.
    rewrite (load_store_overlap STCM ROVER RCneq LDALCM).
    done.
    destruct (load_ptr c' csmm' p'); 
      [apply (store_preserves_chunk_allocation STCM _ _) 
        in LDALCM'|]; done.
  (* Load FAIL *)
  destruct (load_ptr c' cstm' p') as [v'|] _eqn : CSLD';
    destruct (load_ptr c' csmm p') as [cmv|] _eqn : CMLD;
      destruct (load_ptr c' csmm' p') as [cmv'|] _eqn : CMLD'; 
        try apply (store_preserves_chunk_allocation STCM _ _) in LDALCM';
          try done.
Qed.

Lemma sim_irrelevant_preserves_load_rel:
  forall tm sm tm' sm' bi,
    mrestr tm = low_mem_restr ->
    non_stack_mem_related tm sm ->
    load_values_related tm sm ->
    buffer_item_irrelevant bi ->
    apply_buffer_item bi tm = Some tm' ->
    apply_buffer_item bi sm = Some sm' ->
    load_values_related tm' sm'.
Proof.
  intros tm sm tm' sm' bi MC NSR LR BIIR ABt ABs.
  unfold buffer_item_irrelevant in BIIR.
  unfold apply_buffer_item in ABt, ABs.
  destruct bi as [p c v | p n [] | p []]; try done;
    try (destruct BIIR; eby eapply sim_write_preserves_load_rel);
      try (eby eapply sim_non_stack_alloc_preserves_load_rel);
        eby eapply sim_non_stack_free_preserves_load_rel.
Qed.

Lemma sim_alloc_preserves_non_stack_mem_related:
  forall tm sm tm' sm' p n k,
    non_stack_mem_related tm sm ->
    alloc_ptr (p, n) k tm = Some tm' ->
    alloc_ptr (p, n) k sm = Some sm' -> 
    non_stack_mem_related tm' sm'.
Proof.
  intros tm sm tm' sm' p n k NSR APt APs.
  intros r' k'; specialize (NSR r' k'); destruct k'; try done;
    (split; intro RA; [
    destruct (alloc_preserves_allocated_back APt _ _ RA) 
      as [[-> <-] | RA2]; try done; [
      by apply (proj1 (alloc_someD APs)) |
      by apply (alloc_preserves_allocated APs), NSR] |
    destruct (alloc_preserves_allocated_back APs _ _ RA) 
      as [[-> <-] | RA2]; try done; [
      by apply (proj1 (alloc_someD APt)) |
      by apply (alloc_preserves_allocated APt), NSR]]). 
Qed.

Lemma sim_free_preserves_non_stack_mem_related:
  forall tm sm tm' sm' p k,
    non_stack_mem_related tm sm ->
    free_ptr p k tm = Some tm' ->
    free_ptr p k sm = Some sm' -> 
    non_stack_mem_related tm' sm'.
Proof.
  intros tm sm tm' sm' p k NSR FPt FPs.
  
  intros [p' n'] k'; specialize (NSR (p', n') k'); destruct k'; try done;
    (split; intro RA; [
    pose proof (free_preserves_allocated_back FPt _ _ RA) as RA';
    apply NSR in RA'; destruct (free_preserves_allocated FPs _ _ RA') 
      as [? | [<- <-]]; try done; 
        destruct (free_not_allocated FPt _ _ RA) |
    pose proof (free_preserves_allocated_back FPs _ _ RA) as RA';
    apply NSR in RA'; destruct (free_preserves_allocated FPt _ _ RA') 
      as [? | [<- <-]]; try done; 
        destruct (free_not_allocated FPs _ _ RA)]).
Qed.

Lemma sim_irrelevant_preserves_non_stack_mem_related:
  forall tm sm tm' sm' bi,
    non_stack_mem_related tm sm ->
    buffer_item_irrelevant bi ->
    apply_buffer_item bi tm = Some tm' ->
    apply_buffer_item bi sm = Some sm' -> 
    non_stack_mem_related tm' sm'.
Proof.
  intros tm sm tm' sm' bi NSR BIIR ABIt ABIs.
  unfold apply_buffer_item, buffer_item_irrelevant in *.
  destruct bi as [p c v | p n k | p k].
  
  (* Write *)
  intros r' k'. specialize (NSR r' k'). 
  destruct k'; try done;
    (eapply iff_trans; 
      [eapply iff_sym; 
        apply (store_preserves_allocated_ranges ABIt) |
       eapply iff_trans; 
         [edone | 
          apply (store_preserves_allocated_ranges ABIs)]]).
  eby eapply sim_alloc_preserves_non_stack_mem_related.
  eby eapply sim_free_preserves_non_stack_mem_related.
Qed.  

(* Summary for unbuffering other actions (writes and non-stack alloc/free *)
(* This is mostly a plumbing lemma that connects all the stuff above *)
Lemma unbuffer_other_preserves_tso_pc_witt:
  forall smp smpt' ttso tthr bi sbis tm' t stso sm' tbr sthr sbr bp tmp,
    apply_buffer_item bi ttso.(tso_mem) = Some tm' ->
    buffer_item_irrelevant bi ->
    (forall bi', In bi' sbis -> is_item_scratch_update bi') -> 
    part_update_buffer sbis (smp t) = Some smpt' ->
    apply_buffer (bi :: sbis) stso.(tso_mem) = Some sm' ->
    ttso.(tso_buffers) t = bi :: tbr ->
    bp t = (bi :: sbis) :: sbr ->
    tso_pc_related_witt (ttso, tthr) (stso, sthr) bp tmp smp ->
    exists bp', exists tmp', exists smp', exists stso',
      apply_buffer_reachable t stso (bi :: sbis) stso' /\
      stso'.(tso_mem) = sm' /\ (* might want to constrain buffers as well *)
      stso'.(tso_buffers) t = flatten sbr /\
      tso_pc_related_witt (mktsostate (tupdate t tbr ttso.(tso_buffers))
                                      tm', tthr)
                           (stso', sthr)
                           bp' tmp' smp'.
Proof.
  intros smp smpt' ttso tthr bi sbis tm' t stso sm' tbr sthr sbr bp tmp.
  intros TABI BIIR SCR PUB SAB TBUFF BP TSOREL.

  pose proof TABI as TAP. unfold apply_buffer_item in TAP.
  destruct TSOREL as (MTB & NSMR & (MCRt & MCRs & LR & MCM) & SC &
    BPD & BNE & SAF & MRPt & MRPs & TREL).

  pose proof (BPD t) as BPFL. rewrite BP in BPFL. simpl in BPFL. 

  rewrite app_comm_cons in BPFL.
  destruct (TSO.unbuffer_to_tso_state _ _ _ _ _ BPFL SAB) 
    as [stso' (TAU & BUFtstso & BUFother & MEMstso)].

  pose proof SAB as SABsbis; simpl in SABsbis.
  destruct (apply_buffer_item bi (tso_mem stso)) as [smx|] _eqn : SABI; 
    try done; simpl in SABsbis.
  
  pose proof (buffer_item_irrelevant_part_update _ (smp t) BIIR) as PU.
  assert (PUBwithbi: part_update_buffer (bi :: sbis) (smp t) = Some smpt').
    unfold part_update_buffer; simpl. rewrite PU. apply PUB.

  exists (fun t' => if peq t' t then sbr else bp t').
  exists tmp.
  exists (update_partitioning t smpt' smp).
  exists stso'.
  split. apply TAU.
  split. apply MEMstso.
  split. done.
  split; simpl; subst. (* thread buffers only refer to machine values *)
    intros t' bi' IN. apply (MTB t' bi').
    simpl in IN|-*.
    destruct (peq t' t) as [-> | N].
      rewrite BUFtstso in IN.
      rewrite BPFL. apply in_or_app. by right.
    by rewrite <- BUFother.
  split. simpl.
    (* non_stack_mem_related preservation *)
    eapply non_stack_mem_rel_preserved_by_stack_or_write_buffer.
        eby eapply sim_irrelevant_preserves_non_stack_mem_related.
      edone. 
    intros bi' IN'. by apply scratch_impl_stack_or_write, SCR.
  split.
    (* mem_content_related preservation *)
    split. eby erewrite mem_consistent_with_restr_apply_item.
    split. eby erewrite mem_consistent_with_restr_apply_buffer.
    (* Load value related *)
    split.
    eapply apply_scratch_buffer_preserves_load_rel.
      apply SABsbis. edone.
    eby eapply sim_irrelevant_preserves_load_rel; try edone.
    (* Memory contents are machine values *)
    eapply apply_machine_buffer_preserves_machine_memory; [|apply SAB|done].
    intros bi' IN'. apply (MTB t). simpl.
    rewrite BPD, BP. simpl in *. destruct IN'. 
      by left. 
    by right; rewrite in_app; left.
  split.
    eby eapply TSO.apply_buffer_reachable_preserves_tso_consistency.
  split. (* Buffer partitioning *)
    intro t'.
    destruct (peq t' t) as [-> | N]. done.
    rewrite BUFother. apply BPD. done.
  split. (* Buffer partitions not empty *)
    intros t' b IN. apply (BNE t').
    destruct (peq t' t) as [-> | N]. rewrite BP. by right.
    done.
  split. (* Allocation freshness for scratch items *)
    eapply scratch_allocs_fresh_apply_buffer. edone. 3 : edone. 
    by rewrite BUFtstso, BPD, BP. intros ? ?; by rewrite BUFother.
  split. (* Memory related with partitioning in target *)
    eapply mem_related_with_partitioning_ext.
    eapply (apply_buffer_item_preserves_mem_partitioning _ _ bi _ _ t). 
      apply MRPt. apply TABI. apply buffer_item_irrelevant_part_update. done.
    intros t'.
      by unfold update_partitioning; destruct (peq t' t) as [-> | N].  
  split. (* Memory related with partitioning in source *) 
    eby eapply apply_buffer_preserves_mem_partitioning. 
  intro t'.
  specialize (TREL t'). destruct TREL as [PI [BREL BSREL]].
  split.
    unfold update_partitioning.
    destruct (peq t' t) as [-> | N].
      eby eapply update_part_buffer_scratch_preserves_partition_injectivity.
    done.
  (* Per-thread buffered simulation is preserved *)
  simpl in BREL, BSREL, sthr, tthr.
  destruct (peq t' t) as [-> | N].
    rewrite !update_partitioning_s, tupdate_s.
    split. rewrite TBUFF in BREL. inv BREL; try by simpl in BIIR.
    by rewrite BP in *; clarify; rewrite PUB, TBUFF in *; clarify. 
    (* same thread as the unbuffering one *)
    destruct (sthr ! t) as [sst|]; destruct (tthr ! t) as [tst|]; 
      simpl in BSREL; try done.
      simpl. rewrite TBUFF in BSREL.
      rewrite BP in BSREL. 
      apply <- buffered_states_related_prepend_tgt.
      apply <- buffered_states_related_prepend_src; try edone.
      by rewrite buffer_item_irrelevant_part_update.
    destruct BSREL as (_ & _ & E & _). by rewrite E in TBUFF.
  (* Other threads - use the memory "sameness" *)
  rewrite ! update_partitioning_o, tupdate_o; try done.
  split. done.
  destruct (sthr ! t') as [sst|]; destruct (tthr ! t') as [tst|]; 
    simpl in BSREL; try done.
  simpl.
  pose proof MRPs as X; destruct X as [PD [RLD RLA]].
  destruct (apply_buffer_preserves_mem_partitioning _ _ _ _ _ _ 
    MRPs SAB PUBwithbi) as [PR' [RLD' RLA']].
  apply buffered_states_related_load_inv with (smem := tso_mem stso);
    try done.
        intros r IN. apply (RLA r). eby eexists.
      intros r IN. apply (RLA' r). exists t'.
      rewrite update_partitioning_o. done. done.
    eapply tso_consistent_safe_buffer_app; try edone.
      rewrite <- app_nil_end. apply BPD.
    eapply tso_consistent_safe_buffer_app; try edone.
      eby eapply TSO.apply_buffer_reachable_preserves_tso_consistency.
    rewrite <- app_nil_end.
    rewrite BUFother. apply BPD. done.
  eby eapply unbuffering_other_buffer_agrees_on_scratch.
Qed.

Lemma unbuffer_item_preserves_tso_pc_witt:
  forall smp ttso tthr bi sbis tm' t stso sm' tbr sthr sbr bp tmp,
    apply_buffer_item bi ttso.(tso_mem) = Some tm' ->
    apply_buffer sbis stso.(tso_mem) = Some sm' ->
    ttso.(tso_buffers) t = bi :: tbr ->
    bp t = sbis :: sbr ->
    tso_pc_related_witt (ttso, tthr) (stso, sthr) bp tmp smp ->
    exists bp', exists tmp', exists smp', exists stso',
      apply_buffer_reachable t stso sbis stso' /\
      stso'.(tso_mem) = sm' /\ (* might want to constrain buffers as well *)
      stso'.(tso_buffers) t = flatten sbr /\
      tso_pc_related_witt (mktsostate (tupdate t tbr ttso.(tso_buffers))
                                      tm', tthr)
                           (stso', sthr)
                           bp' tmp' smp'.
Proof.
  intros smp ttso tthr bi sbis tm' t stso sm' tbr sthr sbr bp tmp.
  intros TABI SAB TBUFF BPT TREL.

  pose proof TREL as TREL'.
  destruct TREL' as (MTB & NSMR & MR & SC & BPD & BNE & 
    SAF & MRPt & MRPs & TSREL).
  destruct (TSREL t) as [_ [BREL BSREL]].
  
  simpl in BREL.
  remember (tso_buffers ttso t) as tbuft.
  remember (tmp t) as tmpt.
  remember (bp t) as bpt.
  remember (smp t) as smpt.

  buffers_related_cases (destruct BREL) Case. 
  
  Case "buffers_related_empty". done.
  
  Case "buffers_related_alloc". 
    inv TBUFF. inv BPT. apply sym_eq in Heqbpt.
    eby eapply unbuffer_alloc_preserves_tso_pc_witt.
    
  Case "buffers_related_free".
    inv TBUFF. inv BPT.
    apply sym_eq in Heqtmpt. apply sym_eq in Heqbpt.
    eby eapply unbuffer_free_preserves_tso_pc_witt.

  Case "buffers_related_other".
    inv TBUFF. inv BPT. apply sym_eq in Heqbpt.
    eby eapply unbuffer_other_preserves_tso_pc_witt.
Qed.

Lemma tso_pc_buff_length_eq_to_bp:
  forall ttso tthr stso sthr bp tmp smp t,
    tso_pc_related_witt (ttso, tthr) (stso, sthr) bp tmp smp ->
    length(ttso.(tso_buffers) t) = length (bp t).
Proof.
  intros ttso tthr stso sthr bp tmp smp t 
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & TREL).
  destruct (TREL t) as (_ & BREL & _). simpl in BREL.
  induction BREL; try done; simpl; f_equal; done.
Qed.

Lemma unbuffer_unbuffer_safe_app:
  forall b1 b2 tso t,
    unbuffer_safe tso ->
    tso.(tso_buffers) t = b1 ++ b2 ->
    exists m', apply_buffer b1 tso.(tso_mem) = Some m'.
Proof.
  induction b1 as [|bi b1 IH].
  intros. exists (tso_mem tso). done.
  
  intros b2 tso t US DC.
  rewrite <- app_comm_cons in DC.
  destruct (unbuffer_unbuffer_safe US DC) as [mi [ABI US']].
  specialize (IH b2 _ t US'). simpl in IH.
  rewrite tupdate_s in IH. destruct (IH (refl_equal _)) as [m' AB].
  exists m'. simpl. rewrite ABI. done. 
Qed.

Lemma tgt_tso_consistent_unbuffer:
  forall ts t bi b m' tthr,
  ts.(tso_buffers) t = bi :: b ->
  apply_buffer_item bi ts.(tso_mem) = Some m' ->
  Comp.consistent tso_mm cst_sem (ts, tthr) ->
  Comp.consistent tso_mm cst_sem
     (mktsostate (tupdate t b (tso_buffers ts)) m', tthr).
Proof.
  intros ts t bi b m' tthr BD ABI [BC US].
  split. intros t' N'; simpl in *. specialize (BC t' N'). simpl in BC.
    unfold tupdate; destruct (peq t' t) as [-> | Nt]; by try rewrite BC in *.
  simpl. destruct ts; simpl in *; eby eapply apply_item_unbuffer_safe.
Qed.

Lemma tgt_tso_consistent_tso_step:
  forall ts ts' tthr,
  tso_step ts MMtau ts' ->
  Comp.consistent tso_mm cst_sem (ts, tthr) ->
  Comp.consistent tso_mm _ (ts', tthr).
Proof.
  intros; eapply Comp.step_preserves_consistency with (ge:=cst_globenv); vauto.
Qed.

Lemma unbuffer_item_preserves_tso_pc_unsafe:
  forall ttso t bi tbr tm' tthr stso sthr,
    ttso.(tso_buffers) t = bi :: tbr ->
    apply_buffer_item bi ttso.(tso_mem) = Some tm' ->
    tso_pc_unsafe_related (ttso, tthr) (stso, sthr) ->
    exists stso', exists b,
      b <> nil /\
      apply_buffer_reachable t stso b stso' /\
      tso_pc_unsafe_related 
        (mktsostate (tupdate t tbr ttso.(tso_buffers)) tm', tthr) 
        (stso', sthr).
Proof.
  intros ttso t bi tbr tm' tthr stso sthr BD ABI TREL.
  destruct TREL as [bp [tp [sp TREL]]].
  generalize TREL; intros (_ & _ & _ & (_ & US) & BP & BNE & _). 
  specialize (BP t).
  destruct (bp t) as [|sbis sbr] _eqn : BPT.
    pose proof (tso_pc_buff_length_eq_to_bp _ _ _ _ _ _ _ t TREL) as LE.
    by rewrite BPT, BD in LE.
  simpl in BP.    
  destruct (unbuffer_unbuffer_safe_app _ _ _ _ US BP) as [sm' SAB].
  destruct (unbuffer_item_preserves_tso_pc_witt _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
    ABI SAB BD BPT TREL) as [bp' [tmp' [smp' [stso' [UBR [MEq [Beq TREL']]]]]]].
  exists stso'. exists sbis.
  split. apply (BNE t). rewrite BPT. by left.
  split. done. 
  eexists; eexists; eexists. edone.
Qed.

Lemma unbuffer_item_preserves_tso_pc_unsafe_tso_step:
  forall ttso ttso' tthr stsothr
    (TSOUB: tso_step ttso MMtau ttso')
    (TREL: tso_pc_unsafe_related (ttso, tthr) stsothr),
    exists stsothr',
      taustep cshm_lts stsothr Etau stsothr' /\
      tso_pc_unsafe_related (ttso', tthr) stsothr'.
Proof.
  inversion 1; intros; clarify. 
  destruct stsothr as [stso sthr].
  destruct (unbuffer_item_preserves_tso_pc_unsafe _ _ _ _ _ _ _ _ 
      EQbufs AB TREL) as [stso' [b' (NE & UBR & TREL')]].
  exists (stso', sthr); split; [|done].
  eby eapply TSO.apply_buffer_reachable_taustep.
Qed. 

Lemma unbuffer_item_preserves_tso_pc:
  forall ttso ttso' tthr stsothr,
    tso_step ttso MMtau ttso' ->
    tso_pc_related (ttso, tthr) stsothr ->
    exists stsothr',
      taustep cshm_lts stsothr Etau stsothr' /\
      tso_pc_related (ttso', tthr) stsothr'.
Proof.
  intros ttso ttso' tthr stsothr TSOUB [TC TREL].
  destruct (unbuffer_item_preserves_tso_pc_unsafe_tso_step _ _ _ _ TSOUB TREL)
    as [ts' [TAU TREL']].
  exists ts'. split. done.
  split. eby eapply tgt_tso_consistent_tso_step.
  done.
Qed.

Lemma tso_pc_rel_load_eq:
  forall ttso tthr stso sthr tm sm t p c,
    machine_ptr p ->
    tso_pc_related (ttso, tthr) (stso, sthr) ->
    apply_buffer (ttso.(tso_buffers) t) ttso.(tso_mem) = Some tm ->
    apply_buffer (stso.(tso_buffers) t) stso.(tso_mem) = Some sm ->
      match load_ptr c tm p with
        | Some v => load_ptr c sm p = Some v /\ machine_val v \/
                    load_ptr c sm p = None
        | None => load_ptr c sm p = None
      end.
Proof.
  intros ttso tthr stso sthr tm sm t p c 
    MP [TC [bp [tmp [smp TREL]]]] TAB SAB.
  remember (tso_buffers ttso t) as tbuff.
  revert ttso tthr stso sthr bp smp tmp TC TREL Heqtbuff TAB SAB.
  induction tbuff as [|tbi tbr IH]; intros; simpl in *.

  (* Base case *)
  clarify.
  destruct (bp t) as [|?] _eqn : Bs.
    destruct TREL as (_ & _ & (_ & _ & LR & MCM) & _ & BE & _).
    rewrite BE, Bs in SAB. inv SAB.
    simpl in LR, MCM. specialize (LR p MP c). specialize (MCM p c).
    by destruct (load_ptr c ttso.(tso_mem) p);
      destruct (load_ptr c stso.(tso_mem) p); try done; vauto.
  pose proof (tso_pc_buff_length_eq_to_bp _ _ _ _ _ _ _ t TREL) as LE.
  by rewrite Bs, <- Heqtbuff in LE.

  (* Induction step *)
  generalize TREL; intros (_ & _ & _ & _ & BP & _); specialize (BP t); simpl in *.
  destruct (bp t) as [|sbis sbr] _eqn : BPT.
    pose proof (tso_pc_buff_length_eq_to_bp _ _ _ _ _ _ _ t TREL) as LE.
    by rewrite BPT, <- Heqtbuff in LE. 
  rewrite BP in SAB.
  destruct (apply_buffer_item tbi (tso_mem ttso)) as [tmi|] _eqn : TABI; 
    try done; simpl in *. 
  rewrite apply_buffer_app in SAB.
  destruct (apply_buffer sbis (tso_mem stso)) as [smi|] _eqn : SABi; 
    try done; simpl in SAB.
  destruct (unbuffer_item_preserves_tso_pc_witt _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
      TABI SABi (sym_eq Heqtbuff) BPT TREL) 
        as [bp' [tmp' [smp' [stso' [TAU [MEq [Beq TREL']]]]]]].
  eapply IH.
  - eby eapply tgt_tso_consistent_unbuffer; try edone; apply sym_eq.
  - apply TREL'.
  - by simpl; rewrite tupdate_s.
  - done.
  by rewrite MEq, Beq. 
Qed.

End UNBUFFER_SIMS.
