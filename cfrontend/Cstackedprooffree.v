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

Section FREEWRITE_SIM.

Variable cst_globenv : genv * gvarenv.
Variable csm_globenv : genv * gvarenv.

Let cshm_lts := (mklts event_labels (Comp.step tso_mm cs_sem csm_globenv)).
Let cst_lts := (mklts event_labels (Comp.step tso_mm cst_sem cst_globenv)).

Hypothesis globenv_machine:
  forall id p, Genv.find_symbol (Cstacked.ge cst_globenv) id = Some p -> machine_ptr p.

Hypothesis globenv_same:
  Genv.genv_match (fun a b => a = b) (Cstacked.ge cst_globenv) (ge csm_globenv) /\
  Cstacked.gvare cst_globenv = gvare csm_globenv.

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
 
(*============================================================================*)
(* Preservation of unbuffering errors by the simulation                       *)
(*============================================================================*)

Definition writes_or_frees (b : list buffer_item) :=
  forall bi, In bi b -> 
    match bi with
      | BufferedFree _ _ => True
      | BufferedWrite _ _ _ => True
      | _ => False 
    end.

Lemma tso_pc_related_unsafe_store_sim:
  forall ts tthr ss sthr t p c v tbr,
    tso_pc_unsafe_related (ts, tthr) (ss, sthr) ->
    ts.(tso_buffers) t = BufferedWrite p c v :: tbr ->
    store_ptr c ts.(tso_mem) p v <> None.
Proof.
  intros ts tthr ss sthr t p c v tbr TREL TB WR.
  destruct TREL as [bp [tp [sp (MTB & NSMR & (MCRt & MCRs & LR) & SC & 
    BPD & BNE & SAF & MRPt & MRPs & TREL)]]].
  destruct (TREL t) as (_ & BRELt & _). simpl in *.
 
  remember (tso_buffers ts t) as tbt. remember (tp t) as tpt.
  remember (bp t) as bpt. remember (sp t) as spt.
  destruct BRELt; try done. inv TB.
  pose proof (BPD t) as BPt. rewrite <- Heqbpt in BPt. simpl in BPt.
  destruct (unbuffer_unbuffer_safe (proj2 SC) BPt) as [sm' [ABI _]].
  unfold apply_buffer_item, fst in ABI.
  pose proof (store_chunk_allocated_spec c (tso_mem ss) p v) as SS.
  rewrite ABI in SS. destruct SS as [[r' [k' [RI RA]]] PCAL].
  pose proof (store_chunk_allocated_spec c (tso_mem ts) p v) as STS.
  rewrite WR in STS. elim STS; clear STS; split; [|done].
  (* Non-stack are easy bacause they are preserved by the sim *)
  destruct k' as [] _eqn : Ek'; 
    try by specialize (NSMR r' k'); rewrite Ek' in NSMR; apply NSMR in RA;
      exists r'; eexists; split; edone.
  (* Stack requires us to invoke partition injectivity *)
  destruct BIIR as [MP _]. destruct r' as [p' n'].
  assert (MP': machine_ptr p'). 
    destruct p; destruct p'; destruct RI as [-> _]; by simpl in *.
  apply (proj2 (proj2 MRPs)) in RA. destruct RA as [t' IN].
  destruct (proj1 (TREL t') _ _ MP' IN) as [rt [RIt INt]].
  exists rt. exists MObjStack. split. eby eapply range_inside_trans.
  apply (proj2 (proj2 MRPt) rt). eby eexists.
Qed.

Lemma tso_pc_related_unsafe_free_sim:
  forall ts tthr ss sthr t p k tbr,
    tso_pc_unsafe_related (ts, tthr) (ss, sthr) ->
    ts.(tso_buffers) t = BufferedFree p k :: tbr ->
    free_ptr p k ts.(tso_mem) <> None.
Proof.
  intros ts tthr ss sthr t p k tbr TREL TB FR.
  destruct TREL as [bp [tp [sp (MTB & NSMR & (MCRt & MCRs & LR) & SC & 
    BPD & BNE & SAF & MRPt & MRPs & TREL)]]].
  destruct (TREL t) as (_ & BRELt & _). simpl in *.
 
  remember (tso_buffers ts t) as tbt. remember (tp t) as tpt.
  remember (bp t) as bpt. remember (sp t) as spt.
  destruct BRELt; try done. inv TB.
    (* Freeing stack should be fine because it is in the partition *)
    assert (RA: range_allocated (p, n) MObjStack (tso_mem ts)).
      apply (proj2 (proj2 MRPt) (p, n)). exists t. rewrite <- Heqtpt.
      apply in_eq.
    pose proof (free_cond_spec p MObjStack (tso_mem ts)) as FS.
    rewrite FR in FS. eby eapply FS.
  (* Non-stack free - go to source to show that it is allocated*)
  inv TB.
  pose proof (BPD t) as BPt. rewrite <- Heqbpt in BPt. simpl in BPt.
  destruct (unbuffer_unbuffer_safe (proj2 SC) BPt) as [sm' [ABI _]].
  unfold apply_buffer_item, fst in ABI.
  pose proof (free_cond_spec p k (tso_mem ss)) as FS.
  rewrite ABI in FS. destruct FS as [n RA].
  assert (RAt: range_allocated (p, n) k (tso_mem ts)).
    by destruct k as [] _eqn : Ek; simpl in BIIR; try done;
      specialize (NSMR (p, n) k); rewrite Ek in NSMR; apply NSMR in RA.
  pose proof (free_cond_spec p k (tso_mem ts)) as FS.
  rewrite FR in FS. eby eapply FS.
Qed.

Lemma unbuffer_safety_rev_write_free_gen:
  forall t ts tthr ts' ss sthr fw,
    tso_fin_sup ts ->
    tso_pc_unsafe_related (ts, tthr) (ss, sthr) ->    
    mrestr ts'.(tso_mem) = low_mem_restr ->
    unbuffer_safe ts' ->
    writes_or_frees fw ->
    ts.(tso_buffers) t = ts'.(tso_buffers) t ++ fw ->
    (forall t', t' <> t -> ts.(tso_buffers) t' = ts'.(tso_buffers) t') ->
    (forall r k, range_allocated r k ts.(tso_mem) -> 
                 range_allocated r k ts'.(tso_mem)) ->
    unbuffer_safe ts.
Proof.
  intros t ts tthr ts' ss sthr fw [l [NDUP DOM]].
  
  remember (buffers_measure l ts.(tso_buffers)) as bsize.
  revert ss ts ts' fw DOM NDUP Heqbsize.
  induction bsize as [|bsize IH];
    intros ss ts ts' fw DOM NDUP BM TREL MACH' US DAL SBT SBO RAS.

  (* Base case *)
  constructor; [intros t' bi b Bs | intros t' bi b m' Bs];
    destruct (In_dec peq t' l) as [IN | NIN]; 
      try (by rewrite (buffer_measure_zero _ _ _ BM IN) in Bs);
        by rewrite DOM in Bs.

  (* Step case *)
  constructor.
  intros t' bi b Bs.
  destruct US as [ts' MABI US].
  destruct (apply_buffer_item bi (tso_mem ts)) as [m|] _eqn : FAIL. eby eexists.
  byContradiction.
  destruct bi as [pi ci vi | pi ni ki | pi ki].
      (* Write succeeds because the simulation relation says so *)
      by apply (tso_pc_related_unsafe_store_sim _ _ _ _ _ _ _ _ _ TREL Bs).
    (* Alloc succeeds because we have a more-allocated memory where 
       the alloc succeeds *)
    assert (Bs' : exists br, tso_buffers ts' t' = BufferedAlloc pi ni ki :: br).
      destruct (peq t' t) as [-> | N].
        rewrite Bs in SBT. 
        destruct (tso_buffers ts' t) as [| bi' br'].
           simpl in SBT. rewrite <- SBT in DAL.
             by specialize (DAL _ (in_eq _ _)).
          rewrite <- app_comm_cons in SBT. inv SBT.
        eby eexists.
      rewrite (SBO _ N) in Bs.
      eby eexists.
    destruct Bs' as [br Bs'].
    destruct (MABI _ _ _ Bs') as [m' ABI].
    unfold apply_buffer_item in ABI, FAIL. 
    pose proof (alloc_cond_spec (pi, ni) ki (tso_mem ts')) as AS'.
    pose proof (alloc_cond_spec (pi, ni) ki (tso_mem ts)) as AS.
    rewrite FAIL in AS. rewrite ABI in AS'.
    destruct AS' as (RA' & VAR' & RP' & OVNA').
    destruct TREL as [bp [tp [sp (_ & _ & (MCRt & _) & _)]]]. 
    simpl in RP'. 
    apply (restricted_low_pointer_machine pi _ MACH') in RP'.
    apply (restricted_low_pointer_machine pi _ MCRt) in RP'. simpl in RP'.
    destruct AS as [NVAR | [NRP | [r' [k' [OVER RA]]]]]; [done | done | ].
    apply RAS in RA.
    eby eapply OVNA'.
  (* Free succeeds because of the simulation *)
  by apply (tso_pc_related_unsafe_free_sim _ _ _ _ _ _ _ _ TREL Bs).

  (* Proof of preservation of the induction hypothesis *)
  intros t' bi tbr tm' BD ABIt.
  destruct (unbuffer_item_preserves_tso_pc_unsafe _ _ _ _ _ _ _ _ 
    BD ABIt TREL) as [stso' [b' (NEb' & ABR & TREL')]].
  destruct (In_dec peq t' l) as [INR | NINR].
    2: by rewrite DOM in BD.
  pose proof (preserve_dom_unbuffer _ _ _ _ _ BD DOM) as NDOM.
  destruct (measure_down_unbuffer _ _ _ _ _ NDUP BD INR) 
    as [s [BS SBS]].
  rewrite <- BM in SBS. inv SBS.
  destruct (peq t' t) as [-> | N].
    rewrite SBT in BD. 
    destruct (tso_buffers ts' t) as [|btsh' btst'] _eqn : Ebts'.
      (* Unbuffering the newly buffered allocs *)
      simpl in BD. subst. pose proof (DAL _ (in_eq _ _)) as DALh. 
      assert (NDAL : writes_or_frees tbr).
        intros bi' IN'. by eapply DAL, in_cons.
      eapply (IH _ _ ts' tbr); try edone. 
      simpl. rewrite tupdate_s. by rewrite Ebts'.
      intros tx Nx. simpl. by rewrite tupdate_o; [rewrite SBO|]. 
      simpl. intros r' k' RA'. apply RAS.
      unfold apply_buffer_item in ABIt.
      destruct bi; try done.
        by apply (store_preserves_allocated_ranges ABIt _ _).
      by apply (free_preserves_allocated_back ABIt).
    (* Unbuffering old stuff *)
    rewrite <- app_comm_cons in BD. inv BD.
    destruct (unbuffer_unbuffer_safe US Ebts') as [stm' [ABIts' US']].
    eapply (IH _ _ (mktsostate 
      (tupdate t btst' ts'.(tso_buffers)) stm') fw); try edone.
    simpl. eby erewrite mem_consistent_with_restr_apply_item.
    simpl. by rewrite ! tupdate_s.
    intros t' Nt'. simpl. by rewrite ! tupdate_o; [apply SBO | | ].
    simpl. eby eapply sim_apply_item_preserves_alloc_impl.
  (* Unbuffering another thread *)
  pose proof BD as BD'. rewrite SBO in BD'; [|done].
  destruct (unbuffer_unbuffer_safe US BD') as [stm' [ABIts' US']].
  eapply (IH _ _ (mktsostate (tupdate t' tbr ts'.(tso_buffers)) stm') fw); try edone.
  simpl. eby erewrite mem_consistent_with_restr_apply_item.
  simpl. rewrite ! tupdate_o; try done; intro E; by rewrite E in N.
  intros t'' N''. simpl. 
    unfold tupdate. by destruct (peq t'' t'); try rewrite SBO. 
  simpl. eby eapply sim_apply_item_preserves_alloc_impl.
Qed.

Inductive free_steps : Csharpminor.state -> 
                       list pointer -> 
                       Csharpminor.state -> Prop :=
| free_steps_refl: forall s,
  free_steps s nil s
| free_steps_step: forall s s' s'' p ps
  (STEP : cs_step csm_globenv s (TEmem (MEfree p MObjStack)) s')
  (FS : free_steps s' ps s''),
  free_steps s (p :: ps) s''.

Tactic Notation "free_steps_cases" tactic(first) tactic(c) :=
    first; [
      c "free_steps_refl" |
      c "free_steps_step"].

Definition free_item_of_ptr (p : pointer) := BufferedFree p MObjStack.
  
Lemma kfree_free_steps:
  forall ps v k e,
    free_steps (SKstmt Sskip e (Kfree ps v k))
               ps 
               (SKstmt Sskip e (Kfree nil v k)).
Proof.
  by induction ps as [|p ps IH]; intros; econstructor;
    [econstructor | apply IH].
Qed.

Lemma taustar_ne_taustep:
  forall {lbls lts} s s'
    (TAU : taustar lts s s')
    (NE  : s <> s'),
      taustep lts s (tau lbls) s'.
Proof.
  intros. eby inv TAU; [|eapply steptau_taustar_taustep].
Qed.

Lemma free_steps_appD:
  forall {l1 l2 s s'}
    (FS : free_steps s (l1 ++ l2) s'),
    exists si,
      free_steps s l1 si /\
      free_steps si l2 s'.
Proof.
  induction l1 as [|h l1 IH]; intros.

  simpl in FS. exists s. split. constructor. done.
  
  rewrite <- app_comm_cons in FS.
  inv FS.
  destruct (IH _ _ _ FS0) as [s'' [FS1 FS2]].
  eexists. 
  split. eby eapply free_steps_step.
  edone.
Qed.


Lemma free_steps_success:
  forall s ps s' thrs t tso tso' 
    (FS : free_steps s ps s')
    (CS : thrs ! t = Some s)
    (Etso' : tso' = buffer_insert_list t (map free_item_of_ptr ps) tso)
    (US : unbuffer_safe tso'),
      exists thrs',
        taustar cshm_lts (tso, thrs) (tso', thrs') /\
        thrs' ! t = Some s' /\
        forall t', t' <> t -> thrs' ! t' = thrs ! t'.
Proof.
  intros.

  remember (rev ps) as rps.
  revert ps Heqrps s' FS tso' Etso' US.

  induction rps as [|p rps IH]; intros.
  
  (* Base case *)
  rewrite (rev_nil Heqrps) in *. inv FS. 
  by exists thrs; split; [apply taustar_refl|split]. 

  (* Step case *)
  rewrite (rev_cons Heqrps) in *.
  destruct (free_steps_appD FS) as [si [FSrps FSp]].
  inv FSp. inv FS0.
  specialize (IH (rev rps)).
  exploit IH; clear IH; try edone.
      by rewrite rev_involutive.
    destruct (buffer_insert_list t (map free_item_of_ptr (rev rps)) tso)
      as [b' m'] _eqn : Ebil. 
    eapply unbuffer_safe_on_buffer_prefixes
      with (b := tupdate t (b' t ++ BufferedFree p MObjStack :: nil) b').
    by rewrite map_app, buffer_insert_list_app, Ebil in US.
    intros t'. simpl in *.
    destruct (peq t' t) as [-> | N].
      exists (BufferedFree p MObjStack :: nil). by rewrite tupdate_s.
    exists nil. by rewrite tupdate_o, <-app_nil_end.
  intros [thrs' (TAU & CS' & OS')].
  eexists.
  split.
    eapply taustar_trans. apply TAU. 
    apply steptau_taustar. simpl.
    eapply Comp.step_ord with (tid := t). apply STEP.
    apply tso_step_free; try edone.
      by rewrite map_app, buffer_insert_list_app. 
    done.
    edone.
  split.
    by rewrite PTree.gss.
  intros t' N. by rewrite PTree.gso, OS'.
Qed.

Lemma fin_sup_buffer_insert_list:
  forall t b tso,
    tso_fin_sup tso -> tso_fin_sup (buffer_insert_list t b tso).
Proof.
  intros t b.
  induction b as [|bi b IH]; intros; by try apply IH, fin_sup_buffer_insert.
Qed.

Lemma free_steps_fail:
  forall s ps s' thrs t tso tso' 
    (TC : Comp.consistent tso_mm cs_sem (tso, thrs))
    (FS : free_steps s ps s')
    (CS : thrs ! t = Some s)
    (Etso' : tso' = buffer_insert_list t (map free_item_of_ptr ps) tso)
    (NUS' : ~ unbuffer_safe tso'),
      can_reach_error csm_globenv (tso, thrs).
Proof.
  intros.
  assert (TFS:= TSO.tso_cons_impl_fin_sup _ _ TC).
  destruct TC as [_ US]; simpl in *.

  revert s' FS tso' Etso' NUS'.

  induction ps as [|p ps IH] using rev_ind; intros.
    by inv FS.

  (* Step case *)
  destruct (free_steps_appD FS) as [si [FSrps FSp]].
  inv FSp. inv FS0.
  specialize (IH _ FSrps _ (refl_equal _)).

  assert (FS' := fin_sup_buffer_insert_list t 
              (map free_item_of_ptr ps) _ TFS).
  destruct (unbuffer_safe_dec _ FS') as [USi | NUSi]; [|by exploit IH].
  destruct (free_steps_success _ _ _ _ _ _ _ FSrps CS (refl_equal _) USi)
    as [thrs' (TAU' & CS' & OS')].
  rewrite map_app, buffer_insert_list_app in NUS'; simpl in *. 
  eapply not_unbuffer_safe in NUS'; [|eby eapply fin_sup_buffer_insert].
  eapply tso_step_free_fail2 in NUS'; [|done].
  destruct NUS' as (? & ? & TAU & ?).
  eexists; split; [eby eapply taustar_trans, TSO.unbuffer_to_tsopc2|].
  by eexists; exists (Evisible Efail); split; vauto.
Qed.

Lemma range_remove_app:
  forall p l1 l1' l2,
    In p (map (@fst _ _) l1) ->
    range_remove p l1 = l1' ->
    range_remove p (l1 ++ l2) = l1' ++ l2.
Proof.
  intro p.
  induction l1 as [|[p' n'] l1 IH]; intros l1' l2 IN RR. done.

  simpl in *.
  destruct (Ptr.eq_dec p' p) as [-> | N]. by subst.
  erewrite IH. rewrite <- RR; reflexivity.
    by destruct IN.
  done.
Qed.

Lemma in_range_remove_decomp:
  forall p sp,
  In p (map (@fst _ _) sp) ->
  exists l1, exists l2, exists n,
    sp = l1 ++ (p, n) :: l2 /\
    range_remove p sp = l1 ++ l2.
Proof.
  intros p sp.
  
  induction sp as [|[p' n'] sp IH]; intro IN. done.
  
  simpl in IN. destruct (Ptr.eq_dec p' p) as [-> | N]. 
    exists nil. exists sp. exists n'. simpl.
    by destruct Ptr.eq_dec.
  destruct IN as [-> | IN]. done.
  destruct (IH IN) as [l1 [l2 [n [Esp Err]]]].
  exists ((p', n') :: l1). exists l2. exists n.
  simpl. destruct Ptr.eq_dec. done. 
  rewrite Err, Esp. done.
Qed.

Lemma pointer_in_range_list_false:
  forall l p n'
    (PIRL: pointer_in_range_list p l = false),
      ~ In (p, n') l.
Proof.
  induction l as [|[hp hn] l IH]; intros; intro IN. done.
  simpl in IN; destruct IN as [E | IN]; [inv E|]; simpl in PIRL;
    destruct Ptr.eq_dec; try done; eby eapply IH.
Qed.

Lemma part_update_buffer_free:
  forall {ps sp} sp'
    (PERM: Permutation (map (@fst _ _) sp) ps),
      part_update_buffer (map free_item_of_ptr ps) (sp ++ sp') = Some sp'.
Proof.
  induction ps as [|p ps IH]; intros.
  
  by apply Permutation_sym, Permutation_nil in PERM; destruct sp.
  
  unfold part_update_buffer in *. simpl.
  destruct (pointer_in_range_list p (sp ++ sp')) as [] _eqn : PIRL.
    simpl.
    pose proof (Permutation_in _ (Permutation_sym PERM) (in_eq _ _)) as IN.
    destruct (in_range_remove_decomp _ _ IN) as [sp1 [sp2 [n [Esp Err]]]].
    rewrite (range_remove_app _ _ _ _ IN Err).
    apply IH.
    rewrite Esp, map_app in PERM. simpl in PERM.
    rewrite map_app.
  eby eapply Permutation_sym, Permutation_cons_app_inv, Permutation_sym, PERM.
  pose proof (Permutation_in _ (Permutation_sym PERM) (in_eq _ _)) as INmap.
  apply in_map_iff in INmap. destruct INmap as [[px n] [E INmap]]. simpl in E.
  subst. apply pointer_in_range_list_false with (n' := n) in PIRL.
  elim PIRL. apply in_or_app. by left.
Qed.

Lemma machine_buffer_free_items_of_ptrs:
  forall ps, 
    machine_buffer (map free_item_of_ptr ps).
Proof.
  induction ps as [|h rs IH]. done.
  intros bi IN.
  simpl in IN. destruct IN as [<- | IN].
    by destruct h.
  by apply IH.
Qed.  

Lemma buffer_scratch_ranges_app_free:
  forall b ps,
    buffer_scratch_ranges b = 
    buffer_scratch_ranges (b ++ map free_item_of_ptr ps).
Proof.
  intros.
  induction b.
    simpl. by induction ps. 
  simpl. by rewrite <- IHb.
Qed.

Lemma scratch_allocs_fresh_free:
  forall tso sp ps t
    (SAF : scratch_allocs_fresh tso.(tso_buffers) sp),
    scratch_allocs_fresh
       (tso_buffers (buffer_insert_list t (map free_item_of_ptr ps) tso)) sp.
Proof.
  intros. destruct SAF as [RLD [RLDS PD]].
  split.
  intros t'. 
    destruct (peq t' t) as [<- | N]. 
      rewrite buffer_insert_list_s, <- buffer_scratch_ranges_app_free.
      by apply RLD.
    rewrite buffer_insert_list_o; [|done]; apply RLD.
  split.
    intros t1 t2 N.
    destruct (peq t1 t) as [-> | N1].
      rewrite buffer_insert_list_s, <- buffer_scratch_ranges_app_free.
      destruct (peq t2 t) as [-> | N2]. done.
      by rewrite buffer_insert_list_o; [|done]; apply RLDS.
    destruct (peq t2 t) as [-> | N2].
      rewrite buffer_insert_list_s, <- buffer_scratch_ranges_app_free.
      rewrite buffer_insert_list_o; [|done]. by apply RLDS.
    rewrite !buffer_insert_list_o; [|done|done]. by apply RLDS.
  intros t1 t2.
  destruct (peq t2 t) as [-> | N2].
    rewrite buffer_insert_list_s, <- buffer_scratch_ranges_app_free.
    by apply PD.
  rewrite buffer_insert_list_o; [|done]; apply PD.
Qed.

Lemma update_part_buffer_valid_alloc_range:
  forall tso t sp sp' r
  (US : unbuffer_safe tso)
  (PUB : part_update_buffer (tso_buffers tso t) (sp t) = Some sp')
  (MRWP : mem_related_with_partitioning tso.(tso_mem) sp)
  (IN : In r sp'),
    valid_alloc_range r.
Proof.
  intros.
  pose proof (no_unbuffer_errors _ t US) as AB'.
  destruct (apply_buffer (tso_buffers tso t) (tso_mem tso)) 
    as [m'|] _eqn : AB; [|done].
  eapply mem_consistent_with_part_valid_alloc.
  eby eapply apply_buffer_preserves_mem_partitioning.
  by rewrite update_partitioning_s.
Qed.  

Lemma update_part_buffer_mrestr:
  forall tso t sp sp' p n
  (US : unbuffer_safe tso)
  (PUB : part_update_buffer (tso_buffers tso t) (sp t) = Some sp')
  (MRWP : mem_related_with_partitioning tso.(tso_mem) sp)
  (IN : In (p, n) sp'),
     mrestr tso.(tso_mem) (Ptr.block p).
Proof.
  intros.
  pose proof (no_unbuffer_errors _ t US) as AB'.
  destruct (apply_buffer (tso_buffers tso t) (tso_mem tso)) 
    as [m'|] _eqn : AB; [|done].
  pose proof (apply_buffer_preserves_mem_partitioning _ _ _ _ _ _
                MRWP AB PUB) as MRWP'.
  rewrite <- (mem_consistent_with_restr_apply_buffer _ _ _ AB).
  eapply range_allocated_consistent_with_restr.
  apply -> (proj2 (proj2 MRWP')).
  exists t. eby rewrite update_partitioning_s. 
Qed.  

Lemma env_ranges_exists:
  forall r e,
    In r (env_ranges e) ->
    exists id, exists ei, e ! id = Some ei /\ csm_env_item_range ei = r.
Proof.
  intros r e IN.
  unfold env_ranges in IN. apply in_map_iff in IN. simpl in IN.
  destruct IN as [[id ei] [CEIR INelems]].
  eexists; eexists; split. 
    eby apply PTree.elements_complete. 
  done.
Qed.

Lemma related_env_partitions_injective:
  forall csal cmal vals cse cme,
    env_related csal cmal vals cse cme ->
    partition_injective csal cmal.
Proof.
  intros csal cmal vals cse cme [n [SF [DISJ [RNGS EM]]]]. 
  intros p' n' MPTR INcmal.
  apply (Permutation_in _ RNGS) in INcmal.
  destruct (env_ranges_exists _ _ INcmal) as [id [ei [GET CEIR]]].
  specialize (EM id). rewrite GET in EM.
  destruct ((csenv_env cse) ! id); try done.
  inv EM; subst; unfold csm_env_item_range in CEIR; inv CEIR.
      by destruct (machine_not_scratch _ MPTR SP).
    replace (csenv_sp cse) with (Some sp) in SF.
    exists (sp, n). destruct sp as [b ofs].
    destruct SF as (VAR & -> & _).
    split. 
      unfold range_inside.
    split. done. unfold valid_alloc_range in VAR.
    right; split; rewrite Int.add_unsigned; try rewrite size_chunk_repr;
      rewrite !Int.unsigned_repr; try rewrite Int.unsigned_repr;
        unfold Int.max_unsigned; pose proof (size_chunk_pos c);
          pose proof (Int.unsigned_range ofs); omega.
    by left.
  replace (csenv_sp cse) with (Some sp) in SF.
  exists (sp, n). destruct sp as [b ofs]. 
  destruct SF as (VAR & -> & _).
  unfold valid_alloc_range in VAR.
  split. 
    unfold range_inside. red. split. done.
    right; split; rewrite Int.add_unsigned; try rewrite size_chunk_repr;
      rewrite !Int.unsigned_repr; try rewrite Int.unsigned_repr;
        unfold Int.max_unsigned; pose proof (Zle_max_l 1 size);
          pose proof (Int.unsigned_range ofs); try omega.
  by left.
Qed.

Lemma partition_injective_app:
  forall sp1 sp2 tp1 tp2,
    partition_injective sp1 tp1 ->
    partition_injective sp2 tp2 ->
    partition_injective (sp1 ++ sp2) (tp1 ++ tp2).
Proof.
  intros sp1 sp2 tp1 tp2 PI1 PI2 p n MPTR IN.
  destruct (in_app_or _ _ _ IN) as [IN1 | IN2].
    destruct (PI1 _ _ MPTR IN1) as [r' [RI INt]].
    exists r'. split. done. by apply in_or_app; left.
  destruct (PI2 _ _ MPTR IN2) as [r' [RI INt]].
  exists r'. split. done. by apply in_or_app; right.
Qed.

Lemma related_cont_partitions_injective:
  forall tal sal smem tk sk,
    cont_related tal sal smem tk sk ->
    partition_injective tal sal.
Proof.
  intros tal sal smem tk sk C.
  (cont_related_cases (induction C) Case); try done. 
  
  Case "k_rel_call".
    eby apply partition_injective_app; 
      [eapply related_env_partitions_injective|]. 
Qed.

Lemma frees_mem_agrees_on_scratch:
  forall lp m m' sp
    (AB  : apply_buffer (map free_item_of_ptr lp) m = Some m')
    (SPAL: forall r, In r sp -> range_allocated r MObjStack m'),
      mem_agrees_on_scratch m m' sp.
Proof.
  induction lp as [|p lp IH] using rev_ind; intros.
    by inv AB.

  (* Step case *)
  rewrite map_app, apply_buffer_app in AB.
  destruct (apply_buffer (map free_item_of_ptr lp) m) 
    as [mi|] _eqn:AB'; [|done].
  simpl in AB.
  pose proof (free_cond_spec p MObjStack mi) as FS.
  destruct (free_ptr p MObjStack mi) as [m''|] _eqn : FP; [|done].
  inv AB. specialize (IH m mi sp AB').
  destruct FS as [n RA].  
  apply modusponens in IH.
    intros r p' c' IN RI SCR.
    rewrite (load_free_other FP RA). eby eapply IH.
    eapply disjoint_inside_disjoint, RI.
    apply SPAL in IN.
    pose proof (free_preserves_allocated_back FP _ _ IN) as RA'.
    destruct (ranges_are_disjoint RA' RA) as [[-> _] | DISJ]; [|done].
    destruct (free_not_allocated FP _ _ IN).
  intros r IN. 
  by apply (free_preserves_allocated_back FP), SPAL.
Qed.

Lemma free_sim_aux:
  forall s s' p k (st : PTree.t Cstacked.state) t tso cstso 
         (csst : PTree.t Csharpminor.state) csm_e lp v csm_k
    (ST : cst_step cst_globenv s (TEmem (MEfree p k)) s')
    (CS : st ! t = Some s)
    (Ess' : csst ! t = Some (SKstmt Sskip csm_e (Kfree lp v csm_k)))
    (USi : unbuffer_safe (buffer_insert_list t (map free_item_of_ptr lp) cstso))
    (TSOPCREL : tso_pc_related (tso, st) (cstso, csst)),
      can_reach_error csm_globenv (cstso, csst) \/
      (exists shms' : St cshm_lts,
        taustep cshm_lts (cstso, csst) Etau shms' /\ 
        tso_pc_unsafe_related (buffer_insert tso t (BufferedFree p k), 
                              st ! t <- s') 
                              shms').
Proof.
  intros.
  pose proof TSOPCREL as [TC [bp [tp [sp TRELW]]]].
  pose proof (tso_pc_related_to_buff_states _ _ _ _ _ _ _ t TRELW) as BOR.
  pose proof TRELW as (MTB & NSMR & (MCRt & MCRs & LR & MCM) & TCs &
    BPD & BNE & SAF & MRPt & MRPs & TREL). simpl in *.
  pose proof TCs as [BCs USs].
  rewrite CS in BOR.
  rewrite Ess' in BOR.
  destruct BOR as [sm' [sp' [tp' (AB' & PUBt & PUBs & SR & SCO)]]].

  assert (SCO' := step_consistent_with_env ST SCO).

  inv ST. inv SR.

  (* Get rid of cst_obs' *)
  destruct cst_obs' as [|[px n] []]; destruct OP as [CSB CMB];
    try done; []. inv CSB.

  assert (FS := kfree_free_steps lp v csm_k csm_e).
  (* Unbuffering is safe -> go ahead with the simulation *)
  right.
  destruct (free_steps_success _ _ _ _ _ _ _ FS Ess' (refl_equal _) USi)
    as [thrs' (TAU' & CS' & OS')].
  eexists (_, _). 

  assert(NElpnil : lp <> nil).
    destruct lp.
      pose proof (Permutation_nil (Permutation_sym P)).
      by destruct csm_obs'.
    done.
  end_assert NElpnil.

  assert(WS : taustep cshm_lts 
                     (cstso, csst) 
                     Etau 
                     (buffer_insert_list t (map free_item_of_ptr lp) 
                                         cstso, thrs')).
    eapply (taustar_ne_taustep _ _ TAU'). 
    by intro X; injection X; simpl in *; intros E1 _; rewrite E1, CS' in Ess'; inv Ess'.
  end_assert WS.

  assert (PUBf := part_update_buffer_free csm_obs P).

  (* TODO: should go to a separate lemma *)
  assert (BRt : buffers_related
     (tso_buffers tso t ++ BufferedFree p MObjStack :: nil)
     (tp t) (bp t ++ (map free_item_of_ptr lp :: nil)) 
     (sp t)).
    destruct (TREL t) as (PIt' & BRt' & _).
    eapply buffers_related_suffix; try edone.
    2 : eby rewrite <- BPD. 
    econstructor; try eby vauto.
      intros bi IN. apply in_map_iff in IN.
      destruct IN as [p' [Ebi IN]].
      apply (Permutation_in _ (Permutation_sym P)) in IN.
      apply in_map_iff in IN. destruct IN as [[pr nr] [Ep' INr]].
      simpl in Ep'; subst.
      specialize (PI p' nr). destruct p'; unfold machine_ptr in PI.
      simpl. destruct (low_mem_restr z).
        destruct (PI (refl_equal _) INr) as [r' [RI INr']].
        destruct INr' as [<- | ]; [|done].
        right. destruct p. unfold range_inside in RI.
        exploit update_part_buffer_valid_alloc_range. apply USs. edone.
        edone. apply in_or_app. eby left.
        unfold valid_alloc_range. omega. 
      by left.
    intros [pr pn] IN.
    pose proof (related_cont_partitions_injective _ _ _ _ _ KR) as PIC.
    specialize (PIC pr pn).
    destruct (machine_or_scratch pr) as [Mpr | Spr].
      destruct (PIC Mpr IN) as [r' [RIr' INr']].
      eapply disjoint_inside_disjoint. 2 : apply RIr'.
      eapply CSRLD; [done | by apply in_eq].
    eapply ranges_disjoint_comm, machine_scratch_disjoint.
      replace (machine_ptr p) with (low_mem_restr (Ptr.block p) = true);
        [|by destruct p].
      rewrite <- MCRt.
      eby destruct TC; eapply update_part_buffer_mrestr; try apply in_eq.
    done.

  split. eassumption.
  (* And the simulation relation... *)
  exists (tupdate t (bp t ++ (map free_item_of_ptr lp :: nil)) bp).
  exists tp. exists sp.
  split; simpl. (* machine buffers *)
    intro t'.
    destruct (peq t' t) as [-> | N].
      rewrite buffer_insert_list_s.
      intros bi IN. apply in_app_or in IN.
      destruct IN. eby eapply MTB.
      eby eapply machine_buffer_free_items_of_ptrs.
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
      intro Enil. by destruct lp. 
      done.
    rewrite tupdate_o in IN. eby eapply BNE. done.
  split. (* Scratch allocation freshness *)
    by apply scratch_allocs_fresh_free.
  split. done. (* Target memory consistent with partitioning *)
  split. (* Source memory consistent with partitioning *)
    by rewrite buffer_insert_list_m.
  intros t'.
  destruct (TREL t') as (PI' & BR' & BSR').
  split. done. (* Partitions injective *)
  split. (* Buffers related *)
    destruct (peq t' t) as [-> | N].
      rewrite !@tupdate_s. done.
    by rewrite !@tupdate_o. 
  (* Buffered states related *)
  simpl in *.
  destruct (peq t' t) as [-> | N].
    rewrite !@tupdate_s, !@PTree.gss, CS'.
    simpl. rewrite buffer_insert_list_m.
    pose proof (no_unbuffer_errors _ t USi) as AB.
    rewrite buffer_insert_list_s, buffer_insert_list_m in AB.
    destruct (apply_buffer (tso_buffers cstso t ++ map free_item_of_ptr lp)
                           (tso_mem cstso)) as [sm''|] _eqn : AB''; [|done].
    eexists sm''. eexists csm_obs. exists cst_obs.
    unfold part_update_buffer in *. 
    rewrite !flatten_app, <- ! BPD, !fold_left_opt_app, PUBs, PUBt. simpl.
    split. by rewrite <- app_nil_end.
    split. by destruct (Ptr.eq_dec p p) as [_|?]. 
    split. by simpl; rewrite <- app_nil_end. 
    (* Prove the state relation *)
    split; [|done].
    eapply st_rel_return; try edone.
      eapply cont_related_load_inv; try edone; [].
      eapply frees_mem_agrees_on_scratch.
        eby rewrite apply_buffer_app, AB' in AB''.
      exploit (apply_buffer_preserves_mem_partitioning _ _ _ _ 
        csm_obs t MRPs AB'').
        unfold part_update_buffer; rewrite fold_left_opt_app.
        by rewrite PUBs. 
      intros (_ & _ & MR) r IN.
      eapply MR. exists t. by rewrite update_partitioning_s.
  eby rewrite !@tupdate_o, !@PTree.gso, OS', buffer_insert_list_m.
Qed.

Lemma free_sim:
  forall s s' p k (st : PTree.t Cstacked.state) t tso csms
    (ST : cst_step cst_globenv s (TEmem (MEfree p k)) s')
    (CS : st ! t = Some s)
    (US : unbuffer_safe (buffer_insert tso t (BufferedFree p k)))
    (TSOPCREL : tso_pc_related (tso, st) csms),
      can_reach_error csm_globenv csms \/
      (exists shms' : St cshm_lts,
        taustep cshm_lts csms Etau shms' /\ 
        tso_pc_related (buffer_insert tso t (BufferedFree p k), 
                        st ! t <- s') 
                       shms').
Proof.
  intros. destruct csms as [cstso csst].
  pose proof TSOPCREL as [TC [bp [tp [sp TRELW]]]].
  pose proof (tso_pc_related_to_buff_states _ _ _ _ _ _ _ t TRELW) as BOR.
  pose proof TRELW as (MTB & NSMR & (MCRt & MCRs & LR & MCM) & TCs &
    BPD & BNE & SAF & MRPt & MRPs & TREL). simpl in *.
  rewrite CS in BOR.
  destruct (csst ! t) as [ss'|] _eqn : Ess'; simpl in BOR; try done.
  destruct BOR as [sm' [sp' [tp' (AB' & PUBt & PUBs & SR & SCO)]]].

  inversion ST; subst. inv SR.

  (* See whether we fail or succeed *)
  assert (TFS := TSO.tso_cons_impl_fin_sup _ _ TCs).
  assert (FS' := fin_sup_buffer_insert_list t 
              (map free_item_of_ptr lp) _ TFS).
  assert (FS := kfree_free_steps lp v csm_k csm_e).
  destruct (unbuffer_safe_dec _ FS') as [USi | NUSi].
    exploit free_sim_aux; try edone; []. 
    intros [ERR | [shms' (WS & TSOPCUNREL')]]. by left.
    right. 
    exists shms'. 
    split; try done.
    split; try done.
    by eapply Comp.step_preserves_consistency; vauto.
  left. 
  eby eapply free_steps_fail; try rewrite LE.
Qed.

Lemma free_fail_sim:
  forall s p k s' tso t tso' (st : PTree.t Cstacked.state) sms
  (ST : cst_step cst_globenv s (TEmem (MEfree p k)) s')
  (TS : tso_step tso (MMfreefail t p k) tso')
  (CS : st ! t = Some s)
  (TSOPCREL : tso_pc_related (tso, st) sms),
   can_reach_error csm_globenv sms.
Proof.
  intros. destruct sms as [cstso csst].
  pose proof TSOPCREL as [TC [bp [tp [sp TRELW]]]].
  pose proof (tso_pc_related_to_buff_states _ _ _ _ _ _ _ t TRELW) as BOR.
  pose proof TRELW as (MTB & NSMR & (MCRt & MCRs & LR & MCM) & TCs &
    BPD & BNE & SAF & MRPt & MRPs & TREL). simpl in *.
  pose proof TCs as [BCs USs].
  rewrite CS in BOR.
  destruct (csst ! t) as [ss'|] _eqn : Ess'; simpl in BOR; try done.
  destruct BOR as [sm' [sp' [tp' (AB' & PUBt & PUBs & SR & _)]]].

  inv TS.
  inversion ST; subst. inv SR.

  (* See whether we fail or succeed *)
  assert (TFS := TSO.tso_cons_impl_fin_sup _ _ TCs).
  assert (FS' := fin_sup_buffer_insert_list t (map free_item_of_ptr lp) _ TFS).
  assert (FS := kfree_free_steps lp v csm_k csm_e).
  destruct (unbuffer_safe_dec _ FS') as [USi | NUSi].
    exploit free_sim_aux; try edone; []. 
    intros [ERR | [shms' (WS & TSOPCUNREL')]]. done.
    assert (WF : writes_or_frees (BufferedFree p MObjStack :: nil)).
      intros bi IN. by destruct IN as [<- |].
    assert (FSP : tso_fin_sup (buffer_insert tso' t 
                                             (BufferedFree p MObjStack))).
      by apply fin_sup_buffer_insert, (TSO.tso_cons_impl_fin_sup _ _ TC).
    pose proof (unbuffer_safety_rev_write_free_gen t _ _ _ _ _ _  FSP 
      TSOPCUNREL' MCRt (proj2 TC) WF) as CUS. 
    exploit CUS. 
          by simpl; rewrite tupdate_s.
        intros t' N. simpl. by rewrite tupdate_o.
      done.
    (* show contradiction *)
    inversion 1; clarify; simpl in *. 
    specialize (ABIS t (BufferedFree p MObjStack) nil).
    specialize (UNBS t (BufferedFree p MObjStack) nil); simpl in *.
    rewrite tupdate_s, Bemp in ABIS, UNBS; simpl in *.
    destruct ABIS; try done; destruct (free_ptr p MObjStack); clarify'.
    destruct FAIL as (tid' & ? & ? & ? & ? & ? & ?). 
    exploit UNBS; try done; rewrite tupdate_red.
    assert (tid' <> t) by congruence.
    inversion 1; clarify; simpl in *.
    exploit (ABIS tid'); [eby rewrite tupdate_o|]; simpl.
    by intros [? ?]; clarify'.
  eby eapply free_steps_fail; try rewrite LE.
Qed.

Lemma eval_var_ref_related:
  forall tp sp sm cst_e csm_e id p c
    (ER : env_related tp sp sm cst_e csm_e)
    (EVR : Cstacked.eval_var_ref cst_globenv cst_e id p c),
  eval_var_ref csm_globenv csm_e id p c.
Proof.
  intros.
  destruct ER as [n (_ & _ & _ & EIR)].
  specialize (EIR id).
  inv EVR; rewrite EG in EIR.
    apply eval_var_ref_local.
    destruct (csm_e ! id); [|done].
    by inv EIR; rewrite EB in *; clarify.
  apply eval_var_ref_global. by destruct (csm_e ! id).
    by rewrite (proj1 (proj1 globenv_same)).
  by rewrite <- (proj2 globenv_same).
Qed.

Lemma store_machine_agrees_on_scratch:
  forall c m p v m' sp
    (SP : store_ptr c m p v = Some m')
    (MP : machine_ptr p),
      mem_agrees_on_scratch m m' sp.
Proof.
  intros; intros r' p' c' IN RIN SCR.
  by rewrite (load_store_other SP);
    [| apply machine_scratch_disjoint].
Qed.

Definition prefix_buffer_machine (tp : list arange)
                                 (tb : list buffer_item) : Prop :=
  forall tbpfx tbsfx tp',
    tbpfx ++ tbsfx = tb ->
    part_update_buffer tbpfx tp = Some tp' ->
    forall p n, In (p, n) tp' -> machine_ptr p.

Lemma unbuffer_safe_prefix_buffer_machine:
  forall t ttso tp,
    unbuffer_safe ttso ->
    mem_related_with_partitioning ttso.(tso_mem) tp ->
    mrestr ttso.(tso_mem) = low_mem_restr ->
      prefix_buffer_machine (tp t) (tso_buffers ttso t).
Proof.
  intros t ttso.
  remember (tso_buffers ttso t) as tb.
  revert ttso Heqtb.
  
  induction tb as [|bi tb IH];
    intros ttso Etb tp US MRWP LR pfx sfx tp' DC PUB p n IN.

  (* Base case *)
  apply app_eq_nil in DC. destruct DC as [-> _].
  inv PUB. 
  assert (RA : range_allocated (p, n) MObjStack (tso_mem ttso)).
    apply -> (proj2 (proj2 MRWP)).
    eby eexists.
  apply range_allocated_consistent_with_restr in RA.
  rewrite LR in RA. by destruct p.

  (* Inductive case *)
  destruct pfx as [|hpfd tpfx].
    inv PUB. 
    assert (RA : range_allocated (p, n) MObjStack (tso_mem ttso)).
      apply -> (proj2 (proj2 MRWP)).
      eby eexists.
    apply range_allocated_consistent_with_restr in RA.
    rewrite LR in RA. by destruct p.
  rewrite <- app_comm_cons in DC. inv DC.
  apply sym_eq in Etb.
  destruct (unbuffer_unbuffer_safe US Etb) as [tm' [ABI' US']].
  unfold part_update_buffer in PUB; simpl in PUB. 
  destruct (part_update bi (tp t)) as [tpt'|] _eqn : PU; [|done].
  pose proof (apply_buffer_item_preserves_mem_partitioning _ _ _ _ _ _ 
    MRWP ABI' PU).
  eapply IH; try edone. 
      simpl. by rewrite tupdate_s.
    simpl. by rewrite (mem_consistent_with_restr_apply_item ABI').
  by rewrite update_partitioning_s.
Qed.

Lemma machine_ptr_add:
  forall p n,
    machine_ptr p ->
    machine_ptr (p + n).
Proof. by intros [b o] n. Qed.

Lemma eval_var_ref_machine:
  forall tp sp sm te se p c id,
    env_related tp sp sm te se ->
    (forall p n, In (p, n) tp -> machine_ptr p) ->
    Cstacked.eval_var_ref cst_globenv te id p c ->
    machine_ptr p.
Proof.
  intros tp sp sm te se p c id ER MTP EVR.
  
  destruct ER as [n (TPD & _ & _ & EIR)].
  
  specialize (EIR id).
  inv EVR; rewrite EG in EIR;
    destruct (se ! id) as [sei|] _eqn : Esei; try done.
    inv EIR. rewrite EB in TPD. destruct TPD as (_ & TPD & _).
    apply machine_ptr_add. eapply MTP. rewrite TPD. eby left.
  eby eapply globenv_machine.
Qed.  

Lemma call_cont_related:
  forall {tp sp sm stk smk},
    cont_related tp sp sm stk smk ->
    cont_related tp sp sm (Cstacked.call_cont stk) (call_cont smk).
Proof.
  intros tp sp sm stk smk KR.
  
  eby induction KR; try edone; econstructor.
Qed.

Lemma machine_val_cast:
  forall v c,
    machine_val v ->
    machine_val (cast_value_to_chunk c v).
Proof.
  by intros [] [].
Qed.

Lemma write_thread_sim:
  forall {ts p c v ts' tp sp sm ss}
    (TPMP : forall p n, In (p, n) tp -> machine_ptr p)
    (ST : cst_step cst_globenv ts (TEmem (MEwrite p c v)) ts')
    (SR : state_related tp sp sm ts ss),
    machine_ptr p /\
    machine_val v /\
    exists ss',
      cs_step csm_globenv ss (TEmem (MEwrite p c v)) ss' /\
      (forall sm', store_ptr c sm p v = Some sm' ->
         state_related tp sp sm' ts' ss').
Proof.
  intros.
  inv ST.
  
  (* Assignment *)
  inv SR. inv EKR.
  assert (MP : machine_ptr p).
    eby eapply eval_var_ref_machine; try edone;
      intros p' n' IN'; eapply TPMP, in_or_app; left.
  split. done.
  split. by apply machine_val_cast.
  eexists. 
  split. constructor.
    eby eapply eval_var_ref_related.
  intros sm' STR. 
  eapply state_related_load_inv.
    eby econstructor.
  eby eapply store_machine_agrees_on_scratch. 

  (* Store *)
  inv SR. inv EKR.
  split. done.
  split. by apply machine_val_cast.
  eexists.
  split. econstructor. 
  intros sm' STR. 
  eapply state_related_load_inv.
    eby econstructor.
  eby eapply store_machine_agrees_on_scratch.

  (* Return Some *) 
  inv SR.
  pose proof (call_cont_related KR) as CCR.
  rewrite CC in CCR. inv CCR.
  assert (MP : machine_ptr p).
    eby eapply eval_var_ref_machine; try edone;
      intros p' n' IN'; eapply TPMP, in_or_app; left.
  split. done.
  split. by apply machine_val_cast.
  eexists.
  split. 
    econstructor.
      eby replace (call_cont csm_k) with (Kcall (Some id) fd csm_e0 csm_k0).
    eby eapply eval_var_ref_related.
  intros sm' STR. 
  eapply state_related_load_inv.
    eby econstructor.
  eby eapply store_machine_agrees_on_scratch. 

  (* Bind (of function parameters) *)
  inv SR.
  pose proof ER as [n (BP & _ & _ & EIR)].
  specialize (EIR id). rewrite EG in EIR.
  destruct (csm_e ! id) as [csm_ei|] _eqn : Eei; [|done].
  inv EIR. rewrite EB in *; clarify.
  assert (MP : machine_ptr (sp0 + Int.repr ofs)).
    apply machine_ptr_add. 
    eapply TPMP. apply in_or_app. 
    by left; destruct BP as (_ & -> & _); left.
  split. done.
  split. eapply machine_val_cast, MVL, in_eq.
  eexists.
  split.
    eby econstructor.
  intros sm' STR. 
  eapply state_related_load_inv.
    econstructor; try edone; intros v' IN'; eapply MVL, in_cons, IN'.
  eby eapply store_machine_agrees_on_scratch.  

  (* External return *)
  inv SR.
  assert (MP : machine_ptr p).
    eby eapply eval_var_ref_machine; try edone;
      intros p' n' IN'; eapply TPMP, in_or_app; left.
  split. done.
  split. by apply machine_val_cast.
  eexists.
  split. 
    econstructor.
    eby eapply eval_var_ref_related.
  intros sm' STR. 
  eapply state_related_load_inv.
    eby econstructor.
  eby eapply store_machine_agrees_on_scratch.
Qed.

Lemma buffer_scratch_ranges_app_write:
  forall b p c v,
    buffer_scratch_ranges b = 
    buffer_scratch_ranges (b ++ BufferedWrite p c v :: nil).
Proof.
  intros.
  induction b. done.
  simpl. by rewrite IHb.
Qed.

Lemma scratch_allocs_fresh_write:
  forall tso sp t p c v
    (SAF : scratch_allocs_fresh (tso_buffers tso) sp),
    scratch_allocs_fresh 
       (tupdate t (tso_buffers tso t ++ BufferedWrite p c v :: nil)
          (tso_buffers tso)) sp.
Proof.
  intros. destruct SAF as [RLD [RLDS PD]].
  split.
  intros t'. 
    destruct (peq t' t) as [<- | N]. 
      rewrite tupdate_s, <- buffer_scratch_ranges_app_write.
      by apply RLD.
    rewrite tupdate_o; [|done]; apply RLD.
  split.
    intros t1 t2 N.
    destruct (peq t1 t) as [-> | N1].
      rewrite tupdate_s, <- buffer_scratch_ranges_app_write.
      destruct (peq t2 t) as [-> | N2]. done.
      by rewrite tupdate_o; [|done]; apply RLDS.
    destruct (peq t2 t) as [-> | N2].
      rewrite tupdate_s, <- buffer_scratch_ranges_app_write.
      rewrite tupdate_o; [|done]. by apply RLDS.
    rewrite !tupdate_o; [|done|done]. by apply RLDS.
  intros t1 t2.
  destruct (peq t2 t) as [-> | N2].
    rewrite tupdate_s, <- buffer_scratch_ranges_app_write.
    by apply PD.
  rewrite tupdate_o; [|done]; apply PD.
Qed.

Lemma write_sim_aux:
  forall s s' p c v (st : PTree.t Cstacked.state) t tso cstso csst
    (ST : cst_step cst_globenv s (TEmem (MEwrite p c v)) s')
    (CS : st ! t = Some s)
    (US : unbuffer_safe (buffer_insert cstso t (BufferedWrite p c v)))
    (TSOPCREL : tso_pc_related (tso, st) (cstso, csst)),
      (exists shms' : St cshm_lts,
        taustep cshm_lts (cstso, csst) Etau shms' /\ 
        tso_pc_unsafe_related (buffer_insert tso t (BufferedWrite p c v), 
                               st ! t <- s') 
                              shms').
Proof.
  intros.
  pose proof TSOPCREL as [TC [bp [tp [sp TRELW]]]].
  pose proof (tso_pc_related_to_buff_states _ _ _ _ _ _ _ t TRELW) as BOR.
  pose proof TRELW as (MTB & NSMR & (MCRt & MCRs & LR & MCM) & TCs &
    BPD & BNE & SAF & MRPt & MRPs & TREL). simpl in *.
  pose proof TCs as [BCs USs].
  rewrite CS in BOR.
  destruct (csst ! t) as [ss'|] _eqn : Ess'; simpl in BOR; try done.
  destruct BOR as [sm' [sp' [tp' (AB' & PUBt & PUBs & SR & SCO)]]].

  assert (TPMP : forall p n, In (p, n) tp' -> machine_ptr p).
    pose proof (unbuffer_safe_prefix_buffer_machine t _ _ 
      (proj2 TC) MRPt MCRt) as PBM.
    by eapply (PBM _ nil); [rewrite app_nil_end | apply PUBt].
  end_assert TPMP.

  assert (SCO' := step_consistent_with_env ST SCO).

  
  destruct (write_thread_sim TPMP ST SR) as (MP & MV & [nss (NST & CSR)]).

  assert(WS : taustep cshm_lts 
                     (cstso, csst) 
                     Etau 
                     (buffer_insert cstso t (BufferedWrite p c v), 
                      csst ! t <- nss)).
    apply step_taustep. simpl.
    eby eapply Comp.step_ord; try edone; econstructor. 
  end_assert WS.

  assert (BRt : buffers_related
     (tso_buffers tso t ++ BufferedWrite p c v :: nil)
     (tp t) (bp t ++ ((BufferedWrite p c v :: nil) :: nil))
     (sp t)).
    destruct (TREL t) as (PIt' & BRt' & _).
    eapply buffers_related_suffix; try edone.
    2 : eby rewrite <- BPD. 
    eby econstructor; vauto.

  eexists (_, _). 
  split. eassumption.
  (* And the simulation relation... *)
  exists (tupdate t (bp t ++ ((BufferedWrite p c v :: nil) :: nil)) bp).
  exists tp. exists sp.
  split; simpl. (* machine buffers *)
    intro t'.
    destruct (peq t' t) as [-> | N].
      rewrite tupdate_s.
      intros bi IN. apply in_app_or in IN.
      eby destruct IN as [IN | [<- | ?]]; try edone; eapply MTB.
    by rewrite tupdate_o; [apply MTB | ].
  split. done. (* non-stack memory consistent *)
  split. done. (* memory contents related *)
  split. (* tso consistency for source *)
    eapply Comp.taustep_preserves_consistency.
    apply WS. done. 
  split. (* buffer partitioning *)
    intro t'.
    destruct (peq t' t) as [-> | N].
      by rewrite !@tupdate_s, flatten_app; simpl; rewrite <- BPD.
    by rewrite !@tupdate_o, BPD.
  split. (* buffer partitions non-empty *)
    intros t' bi IN.
    destruct (peq t' t) as [-> | N].
      rewrite tupdate_s in IN.
      apply in_app_or in IN. 
      destruct IN as [IN | [<- | IM]]. eby eapply BNE.
      done. done.
    rewrite tupdate_o in IN. eby eapply BNE. done.
  split. (* Scratch allocation freshness *)    
    by apply scratch_allocs_fresh_write.
  split. done. (* Target memory consistent with partitioning *)
  split. done. (* Source memory consistent with partitioning *)
  intros t'.
  destruct (TREL t') as (PI' & BR' & BSR').
  split. done. (* Partitions injective *)
  split. (* Buffers related *)
    destruct (peq t' t) as [-> | N].
      rewrite !@tupdate_s. done.
    by rewrite !@tupdate_o. 
  (* Buffered states related *)
  destruct (peq t' t) as [-> | N].
    rewrite !@tupdate_s, !@PTree.gss.
    simpl. 
    pose proof (no_unbuffer_errors _ t US) as AB. simpl in AB.
    rewrite tupdate_s in AB.
    destruct (apply_buffer (tso_buffers cstso t ++ BufferedWrite p c v :: nil)
                           (tso_mem cstso)) as [sm''|] _eqn : AB''; [|done].
    eexists sm''. eexists sp'. exists tp'.
    unfold part_update_buffer in *. 
    rewrite !flatten_app, <- ! BPD, !fold_left_opt_app, PUBs, PUBt. simpl.
    destruct (low_mem_restr (Ptr.block p)) as [] _eqn : LMR;
      [|by destruct p; simpl in *; rewrite LMR in MP].
    split. done. 
    split. done. 
    split. done.
    split; [|done].
    apply CSR.
    rewrite apply_buffer_app, AB' in AB''. simpl in AB''.
    by destruct (store_ptr c sm' p v) as [smx|]; clarify.
  eby rewrite !@tupdate_o, !@PTree.gso.
Qed.

Lemma write_step_fails:
  forall s p c v s' thrs t tso tso' 
    (TC : Comp.consistent tso_mm cs_sem (tso, thrs))
    (FS : cs_step csm_globenv s (TEmem (MEwrite p c v)) s')
    (CS : thrs ! t = Some s)
    (Etso' : tso' = buffer_insert tso t (BufferedWrite p c v))
    (NUS' : ~ unbuffer_safe tso'),
      can_reach_error csm_globenv (tso, thrs).
Proof.
  intros; clarify.
  eapply not_unbuffer_safe in NUS'.  
  2: by eapply fin_sup_buffer_insert, (TSO.tso_cons_impl_fin_sup _ _ TC).
  destruct (tso_step_write_fail (proj2 TC) NUS') as (? & ? & ? & ?).
  eexists; split; [eby eapply TSO.unbuffer_to_tsopc2|].
  by eexists; exists (Evisible Efail); split; vauto.
Qed.

Lemma write_sim:
  forall s s' p c v (st : PTree.t Cstacked.state) t tso csms
    (ST : cst_step cst_globenv s (TEmem (MEwrite p c v)) s')
    (CS : st ! t = Some s)
    (US : unbuffer_safe (buffer_insert tso t (BufferedWrite p c v)))
    (TSOPCREL : tso_pc_related (tso, st) csms),
      can_reach_error csm_globenv csms \/
      (exists shms' : St cshm_lts,
        taustep cshm_lts csms Etau shms' /\ 
        tso_pc_related (buffer_insert tso t (BufferedWrite p c v), 
                        st ! t <- s') 
                       shms').
Proof.
  intros. destruct csms as [cstso csst].
  pose proof TSOPCREL as [TC [bp [tp [sp TRELW]]]].
  pose proof (tso_pc_related_to_buff_states _ _ _ _ _ _ _ t TRELW) as BOR.
  pose proof TRELW as (MTB & NSMR & (MCRt & MCRs & LR & MCM) & TCs &
    BPD & BNE & SAF & MRPt & MRPs & TREL). simpl in *.
  pose proof TCs as [BCs USs].
  rewrite CS in BOR.
  destruct (csst ! t) as [ss'|] _eqn : Ess'; simpl in BOR; try done.
  destruct BOR as [sm' [sp' [tp' (AB' & PUBt & PUBs & SR & _)]]].

  assert (TPMP : forall p n, In (p, n) tp' -> machine_ptr p).
    pose proof (unbuffer_safe_prefix_buffer_machine t _ _ 
      (proj2 TC) MRPt MCRt) as PBM.
    by eapply (PBM _ nil); [rewrite app_nil_end | apply PUBt].
  end_assert TPMP.
  
  destruct (write_thread_sim TPMP ST SR) as (MP & MV & [nss (NST & CSR)]).

  (* See whether we fail or succeed *)
  assert (TFS := TSO.tso_cons_impl_fin_sup _ _ TCs).
  assert (FS' := fin_sup_buffer_insert_list t 
              (BufferedWrite p c v:: nil) _ TFS).
  destruct (unbuffer_safe_dec _ FS').
    exploit write_sim_aux; try edone; []. 
    intros [shms' (WS & TSOPCUNREL')].
    right. 
    exists shms'. 
    split; try done.
    split; try done.
    by eapply Comp.step_preserves_consistency; vauto.
  left. 
  eby eapply write_step_fails; try rewrite LE.
Qed.


Lemma write_fail_sim:
  forall s p c v s' tso t tso' (st : PTree.t Cstacked.state) sms
  (ST : cst_step cst_globenv s (TEmem (MEwrite p c v)) s')
  (TS : tso_step tso (MMreadfail t p c) tso')
  (CS : st ! t = Some s)
  (TSOPCREL : tso_pc_related (tso, st) sms),
   can_reach_error csm_globenv sms.
Proof.
  intros. destruct sms as [cstso csst].
  pose proof TSOPCREL as [TC [bp [tp [sp TRELW]]]].
  pose proof (tso_pc_related_to_buff_states _ _ _ _ _ _ _ t TRELW) as BOR.
  pose proof TRELW as (MTB & NSMR & (MCRt & MCRs & LR & MCM) & TCs &
    BPD & BNE & SAF & MRPt & MRPs & TREL). simpl in *.
  rewrite CS in BOR.
  destruct (csst ! t) as [ss'|] _eqn : Ess'; simpl in BOR; try done.
  destruct BOR as [sm' [sp' [tp' (AB' & PUBt & PUBs & SR & _)]]].

  inv TS.

  (* See whether we fail or succeed *)
  assert (TFS := TSO.tso_cons_impl_fin_sup _ _ TCs).
  assert (FS' := fin_sup_buffer_insert_list t 
              (BufferedWrite p c v:: nil) _ TFS).
  destruct (unbuffer_safe_dec _ FS') as [USi | NUSi].
    exploit write_sim_aux; try edone; []. 
    intros [shms' (WS & TSOPCUNREL')].
    assert (WF : writes_or_frees (BufferedWrite p c v :: nil)).
      intros bi IN. by destruct IN as [<- |].
    assert (FSP : tso_fin_sup (buffer_insert tso' t 
                                             (BufferedWrite p c v))).
      apply fin_sup_buffer_insert, (TSO.tso_cons_impl_fin_sup _ _ TC).
    pose proof (unbuffer_safety_rev_write_free_gen t _ _ _ _ _ _  FSP 
      TSOPCUNREL' MCRt (proj2 TC) WF) as CUS. 
    exploit CUS. 
          by simpl; rewrite tupdate_s.
        intros t' N. simpl. by rewrite tupdate_o.
      done.
    (* show contradiction *)
    inversion 1; simpl in *.
    exploit (ABIS t); [by rewrite tupdate_s, Bemp|]; intros [? STO]; simpl in *.
    by generalize (load_chunk_allocated_noneD LD),
               (store_chunk_allocated_someD STO).

  assert (TPMP : forall p n, In (p, n) tp' -> machine_ptr p).
    pose proof (unbuffer_safe_prefix_buffer_machine t _ _ 
      (proj2 TC) MRPt MCRt) as PBM.
    by eapply (PBM _ nil); [rewrite app_nil_end | apply PUBt].
  end_assert TPMP.
  
  destruct (write_thread_sim TPMP ST SR) as (MP & MV & [nss (NST & CSR)]).
  eby eapply write_step_fails; try rewrite LE.
Qed.


End FREEWRITE_SIM.
