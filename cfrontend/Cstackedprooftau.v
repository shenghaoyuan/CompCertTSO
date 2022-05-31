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
Require Cminorops.
Require Import Cminorgen.
Require Import Cstacked.
Require Import Csharpminor.
Require Import Simulations.
Require Import Mem.
Require Import Memeq.
Require Import Memcomp.
Require Import Cstackedproofsimdef.
Require Import Cstackedproofunbuffer.
Require Import Cstackedproofalloc.
Require Import Cstackedprooffree.
Require Import Permutation.

Section TAU_SIM.

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

Lemma eval_var_addr_machine:
  forall tp sp sm te se p id,
    env_related tp sp sm te se ->
    (forall p n, In (p, n) tp -> machine_ptr p) ->
    Cstacked.eval_var_addr cst_globenv te id p ->
    Csharpminor.eval_var_addr csm_globenv se id p /\
    machine_ptr p.
Proof.
  intros tp sp sm te se p id ER MTP EVA.
  
  destruct ER as [n (TPD & _ & _ & EIR)].
  
  specialize (EIR id).
  inv EVA; try (eby rewrite EG in EIR;
    destruct (se ! id) as [sei|] _eqn : Esei; try done;
    inv EIR; rewrite EB in *; clarify; destruct TPD as (_ & -> & _); 
      (split; [eapply eval_var_addr_local|
               apply machine_ptr_add; eapply MTP, in_eq])); [].
  split.
    rewrite EGN in EIR.
    destruct (se ! id) as [sei|] _eqn : Esei; try done.
    eapply eval_var_addr_global. done. by rewrite (proj1 (proj1 globenv_same)).
  eby eapply globenv_machine.
Qed.

Lemma machine_val_unop:
  forall op v v',
    machine_val v ->
    Cminorops.eval_unop op v = Some v' ->
    machine_val v'.
Proof.
  intros op v v' MV EU;
    destruct op; destruct v; simpl in EU; clarify; try done; [].
  by destruct(Int.eq i Int.zero).
Qed.

Ltac omapD :=
  match goal with 
    | H : option_map ?f ?x = Some ?y |- _ =>
        let H' := fresh in destruct x as [] _eqn : H'; [inv H|done]
  end.
  

Lemma machine_val_binop:
  forall op v1 v2 v',
    Cminorops.eval_binop op v1 v2 = Some v' ->
    machine_val v1 ->
    machine_val v2 ->
    machine_val v'.
Proof.
  intros op v1 v2 v' EB MV1 MV2;
    destruct op; destruct v1; destruct v2; simpl in EB; 
      clarify; try done; try (by destruct p); try (by
        match goal with
          | H : context[if ?E then _ else _] |- _ => destruct E; clarify
          | |- context[Val.of_bool ?E] => destruct E
            end);
    try (by destruct Ptr.sub_ptr; simpl in EB; clarify);
    try (by unfold Cminorops.eval_compare_null in EB;
         destruct Int.eq; destruct c; simpl in EB; clarify).
    by destruct Ptr.cmp; inv EB.
Qed.

Lemma is_call_cont_related:
  forall {tp sp sm tk sk}
    (KR: cont_related tp sp sm tk sk)
    (CC: Cstacked.is_call_cont tk),
      is_call_cont sk.
Proof. intros; destruct tk; try done; by inv KR. Qed.

Lemma get_fundef_related:
  forall {tp sp sm tk sk}
    (KR: cont_related tp sp sm tk sk),
      Cstacked.get_fundef tk = get_fundef sk.
Proof. intros; destruct tk; try done; by inv KR. Qed.

Scheme stmt_ind :=     Induction for stmt Sort Prop 
  with lbl_stmt_ind := Induction for lbl_stmt Sort Prop. 

Lemma find_label_related:
  forall {tp sp sm smk stk} lbl s
    (KR : cont_related tp sp sm stk smk),
      match Cstacked.find_label lbl s stk with
        | Some (s', stk') =>
            exists smk',
              find_label lbl s smk = Some (s', smk') /\
              cont_related tp sp sm stk' smk' 
        | None => find_label lbl s smk = None
      end.
Proof.
  intros tp sp sm smk stk lbl s. revert s smk stk.

  set (PLS ls := forall smk stk (KR : cont_related tp sp sm stk smk),
      match Cstacked.find_label_ls lbl ls stk with
        | Some (s', stk') =>
            exists smk',
              find_label_ls lbl ls smk = Some (s', smk') /\
              cont_related tp sp sm stk' smk' 
        | None => find_label_ls lbl ls smk = None
      end). 

  set (PS s := forall smk stk
    (KR : cont_related tp sp sm stk smk),
      match Cstacked.find_label lbl s stk with
        | Some (s', stk') =>
            exists smk',
              find_label lbl s smk = Some (s', smk') /\
              cont_related tp sp sm stk' smk' 
        | None => find_label lbl s smk = None
      end).

  induction s using stmt_ind with (P0 := PLS); 
    subst PS PLS; simpl; try done; intros.

  (* Sseq *)
  specialize (IHs1 (Kseq s2 smk) (Cstacked.Kseq s2 stk)).
  specialize (IHs2 _ _ KR).
  destruct Cstacked.find_label as [[? ?]|]; clarify; 
    (exploit IHs1; [eby econstructor|]).
    intros [smk' (-> & KR1)]. vauto. 
  intros ->.
  by destruct Cstacked.find_label as [[? ?]|]; [|done];
    destruct IHs2 as [smk' (Efl3 & KR3)]; vauto.

  (* Sifthenelse *)
  specialize (IHs1 _ _ KR); specialize (IHs2 _ _ KR).
  destruct Cstacked.find_label as [[? ?]|]; clarify.
    destruct IHs1 as [smk' (-> & KR')]. vauto.
  destruct Cstacked.find_label as [[? ?]|].
    destruct IHs2 as [sml' (-> & KR')].
    eexists. rewrite IHs1. vauto.
  by rewrite IHs2, IHs1.

  (* Sloop *)
  specialize (IHs (Kseq (Sloop s) smk) (Cstacked.Kseq (Sloop s) stk)).
  exploit IHs. eby econstructor.
  destruct Cstacked.find_label as [[? ?]|].
    intros [smk' (-> & KR1)]. vauto. 
  done.

  (* Sblock *)
  specialize (IHs (Kblock smk) (Cstacked.Kblock stk)).
  exploit IHs. eby econstructor.
  destruct Cstacked.find_label as [[? ?]|].
    intros [smk' (-> & KR1)]. vauto. 
  done.

  (* Slabel *)
  specialize (IHs _ _ KR).
  destruct ident_eq as [-> | N]. vauto.
  destruct Cstacked.find_label as [[? ?]|].
    destruct IHs as [smk' (-> & KR')]. vauto.
  done.

  (* LSCase *)
  specialize (IHs (Kseq (seq_of_lbl_stmt l) smk) 
                  (Cstacked.Kseq (seq_of_lbl_stmt l) stk)).
  specialize (IHs0 _ _ KR).
  exploit IHs. eby econstructor.
  destruct Cstacked.find_label as [[? ?]|].
    intros [smk' (-> & KR1)]. vauto. 
  intros ->.
  by destruct Cstacked.find_label_ls as [[? ?]|]; [|done];
    destruct IHs0 as [smk' (Efl3 & KR3)]; vauto.
Qed.

Lemma env_ranges_perm_sorted_pointers:
  forall e,
    Permutation (map (@fst _ _) (env_ranges e)) 
                (sorted_pointers_of_env e).
Proof.
  intro e; unfold sorted_pointers_of_env, env_ranges, csm_env_item_range.
  destruct Mergesort.mergesort as [l (_ & PERM & _)].
  by rewrite map_map; apply Permutation_map, Permutation_sym.
Qed.  


Definition append_items_to_bpart (its: list buffer_item)
                                 (bp : list (list buffer_item)) 
                                  : list (list buffer_item) :=
  match rev bp with
    | nil => its :: nil
    | l :: bl => rev bl ++ (l ++ its) :: nil
  end.

Lemma append_scratch_to_part_flatten:
  forall bp rs,
    flatten (append_items_to_bpart rs bp) =
    flatten bp ++ rs.
Proof.
  intros bp rs. unfold append_items_to_bpart.
  destruct (rev bp) as [|l bl] _eqn : Ebp. 
    rewrite (rev_nil (sym_eq Ebp)) in *.
    by simpl; rewrite <- app_nil_end.
  rewrite !(rev_cons (sym_eq Ebp)), !flatten_app in *.
  simpl. by rewrite <- ! app_nil_end, app_ass.
Qed.

Lemma buffers_related_app:
  forall tb1 tb2 tp sb1 sb2 sp,
  length tb1 = length sb1 ->
  buffers_related (tb1 ++ tb2) tp (sb1 ++ sb2) sp ->
  buffers_related tb1 tp sb1 sp /\
  exists tp', exists sp',
    part_update_buffer tb1 tp = Some tp' /\
    part_update_buffer (flatten sb1) sp = Some sp' /\
    buffers_related tb2 tp' sb2 sp'.
Proof.
  intros tb1 tb2 tp sb1 sb2 sp.
  revert tp sp sb1.
  induction tb1 as [| bi tb1 IH]; intros tp sp sb1 LE BR.
  
  destruct sb1; [|done].
  split. econstructor.
  simpl in BR. vauto.

  destruct sb1 as [|sbi sb1]. done.
  simpl in LE. inversion LE as [LE'].
  
  rewrite <- ! app_comm_cons in BR.
  inv BR; destruct (IH _ _ _ LE' BSR) 
    as [BR1 [tpi [spi (PUBt2 & PUBs2 & BR2)]]];
      (split; [eby econstructor|]); exists tpi; exists spi;
        unfold part_update_buffer in *.
  (* Allocation *)
  split. 
    simpl. 
    destruct valid_alloc_range_dec; [|done].
    destruct range_in_dec as [[r' [IN' OVER']] | RNI].
      destruct (OVER' (RIN _ IN')).
    done.
  split. 
    simpl. by rewrite fold_left_opt_app, PUB.
  done.
  (* Free *)
  split. 
    simpl; destruct Ptr.eq_dec; done.
  split. 
    simpl. by rewrite fold_left_opt_app, PUB.
  done.
  (* Other *)
  split. 
    simpl. by rewrite buffer_item_irrelevant_part_update.
  split. 
    simpl. rewrite buffer_item_irrelevant_part_update.
    simpl. by rewrite fold_left_opt_app, PUB.
    done.
  done.
Qed.

Lemma is_item_scratch_alloc_items_scratch:
  forall bi rs
    (PTRS : forall p n, In (p, n) rs -> scratch_ptr p)
    (IN : In bi (alloc_items_of_ranges rs)),
      is_item_scratch_update bi.
Proof.
  intros.
  unfold alloc_items_of_ranges in IN. apply in_map_iff in IN.
  destruct IN as [r [<- IN]]. destruct r; simpl; eby eapply PTRS.
Qed.


(*
Lemma apply_scratch_ranges_disjoint:
  forall b sp p n sp'
  (DISJ : forall r, In r sp' -> ranges_disjoint r (p, n))
  (MP   : machine_ptr p)
  (PUB  : part_update_buffer b sp = Some sp')
  (SCR  : forall bi, In bi b -> is_item_scratch_update bi),
    forall r (IN : In r sp), ranges_disjoint r (p, n).
Proof.
  induction b as [|bi b IH]; intros.
  
  inv PUB. by apply DISJ.

  unfold part_update_buffer in *.
  simpl in PUB. destruct (part_update bi sp) as [spi|] _eqn : PU; [|done].
  simpl in PUB.
  specialize (IH spi p n sp' DISJ MP PUB
                 (fun bi IN => SCR _ (in_cons _ bi  _ IN))).
  specialize (SCR _ (in_eq _ _)).
  destruct bi as [p' c' v'|p' n' []|p' []]; simpl in SCR;
    try done; simpl in PU.
      destruct low_mem_restr; destruct chunk_inside_range_list; inv PU;
        try done; apply IH, IN.
    destruct valid_alloc_range_dec; [|done].
    destruct range_in_dec; [done|]. inv PU.
    by apply IH; right.
  destruct pointer_in_range_list; [|done]. inv PU.
  destruct r as [pr nr].
  apply in_range_remove_back with (p := p') in IN.
  destruct IN as [<- | IN]. 
  eby eapply ranges_disjoint_comm, machine_scratch_disjoint.
  eby eapply IH.
Qed.
*)

Lemma apply_scratch_ranges_disjoint:
  forall b sp p n sp'
  (DISJ : forall r, In r sp -> ranges_disjoint r (p, n))
  (MP   : machine_ptr p)
  (PUB  : part_update_buffer b sp = Some sp')
  (SCR  : forall bi, In bi b -> is_item_scratch_update bi),
    forall r (IN : In r sp'), ranges_disjoint r (p, n).
Proof.
  induction b as [|bi b IH]; intros.
  
  inv PUB. by apply DISJ.

  unfold part_update_buffer in *.
  simpl in PUB. destruct (part_update bi sp) as [spi|] _eqn : PU; [|done].
  simpl in PUB. specialize (IH spi p n sp').
  eapply IH; try done.
    intros r' IN'. specialize (SCR _ (in_eq _ _)).
    destruct bi as [p' c' v'|p' n' []|p' []]; simpl in SCR;
      try done; simpl in PU.
        by destruct low_mem_restr; destruct chunk_inside_range_list; 
          inv PU; try apply DISJ.
      destruct valid_alloc_range_dec; [|done].
      destruct range_in_dec; [done|]. inv PU.
      simpl in IN'. destruct IN' as [<- | IN'].
        eby eapply ranges_disjoint_comm, machine_scratch_disjoint.
      by apply DISJ.
    destruct pointer_in_range_list; [|done]. inv PU.
    apply DISJ. by destruct r'; apply in_range_remove in IN'.
  intros bi' IN'. by apply SCR; right.
Qed.

Lemma buffers_related_append_scratch_ne:
  forall tb bpt tpt spt sbis spt' nspt'
    (TPMP: prefix_buffer_machine tpt tb)
    (PTRS: forall bi, In bi sbis -> is_item_scratch_update bi)
    (PUBsb: part_update_buffer (flatten bpt) spt = Some spt')
    (PUBrs: part_update_buffer sbis spt' = Some nspt')
    (BNE : rev bpt <> nil)
    (BR : buffers_related tb tpt bpt spt),
       buffers_related tb tpt (append_items_to_bpart sbis bpt) spt.
Proof.
  intros.
  unfold append_items_to_bpart.
  destruct (rev bpt) as [|hbpt tbpt] _eqn : Erbpt. done.
  rewrite !(rev_cons (sym_eq Erbpt)) in *; clear Erbpt.
  destruct (rev tb) as [|htb ttb] _eqn : Ertb.
    rewrite (rev_nil (sym_eq Ertb)) in *; clear Ertb.
    inv BR. 
    byContradiction. eby eapply app_cons_not_nil.
  destruct (buffers_related_part_update BR) as [[tpx PUBtx] _].
  rewrite !(rev_cons (sym_eq Ertb)) in *. clear Ertb.
  unfold part_update_buffer in *.
  rewrite fold_left_opt_app in PUBtx.
  destruct (fold_left_opt part_update (rev ttb) tpt) 
    as [tpti|] _eqn : PUBti; [|done]. unfold optbind in PUBtx.
  rewrite flatten_app, fold_left_opt_app in PUBsb.
  destruct (fold_left_opt part_update (flatten (rev tbpt)) spt)
    as [spti|] _eqn : PUBsi; [|done]. unfold optbind in PUBsb.

  exploit buffers_related_app. 2 : apply BR.
    apply buffered_states_related_length_eq in BR.
    rewrite !app_length in BR.
    simpl in BR. omega.
  unfold part_update_buffer.
  intros [BRpre [tpi' [spi' (PUBti' & PUBsi' & BRsuff)]]].
  rewrite PUBti in PUBti'. rewrite PUBsi in PUBsi'.
  inv PUBti'. inv PUBsi'. simpl in PUBsb. rewrite <-app_nil_end in PUBsb.

  eapply buffers_related_suffix; try edone.
  inv BRsuff.
  (* Allocation *)
  econstructor; try done; unfold part_update_buffer in *.
    intros bi IN. 
    apply in_app_or in IN.
    destruct IN as [IN | IN]. by apply AR.
    left. by apply PTRS.
  rewrite fold_left_opt_app; rewrite PUB in *; eby inv PUBsb.
  constructor.
  (* Free *)
  econstructor; try done; unfold part_update_buffer in *.
    intros bi IN. 
    apply in_app_or in IN.
    destruct IN as [IN | IN]. by apply FR.
    left. by apply PTRS.
  2 : rewrite fold_left_opt_app; rewrite PUB in *; eby inv PUBsb.
  intros r IN.
  rewrite PUBsb in PUB. inv PUB.
  eapply apply_scratch_ranges_disjoint; try edone. 
      eapply TPMP; eby vauto. 
  constructor.
  (* Other *)
  rewrite <- app_comm_cons.
  eapply buffers_related_other. done.
    intros bis IN.
    apply in_app_or in IN. destruct IN as [IN|IN].
      by apply OSCR.
    eby eapply PTRS.
  2 : constructor.
  unfold part_update_buffer in *. rewrite fold_left_opt_app.
  rewrite PUB. simpl.
  simpl in PUBsb. rewrite buffer_item_irrelevant_part_update in PUBsb.
  simpl in PUBsb. rewrite PUB in PUBsb. inv PUBsb. edone. done.
Qed.

Lemma buffers_related_append_scratch:
  forall tb bpt tpt spt sbis spt' nspt'
    (TPMP: prefix_buffer_machine tpt tb)
    (PTRS: forall bi, In bi sbis -> is_item_scratch_update bi)
    (PUBsb: part_update_buffer (flatten bpt) spt = Some spt')
    (PUBrs: part_update_buffer sbis spt' = Some nspt')
    (BR : buffers_related tb tpt bpt spt),
       buffers_ss_rel tb tpt (append_items_to_bpart sbis bpt) spt.
Proof.
  intros.
  destruct (rev bpt) as [|hbpt tbpt] _eqn : Erbpt.
    unfold append_items_to_bpart. rewrite Erbpt.
    rewrite (rev_nil (sym_eq Erbpt)) in *.
    inv BR.
    eapply buffers_ss_rel_scratch.
      intros bi IN. by apply PTRS.
      inv PUBsb. edone. 
    econstructor.  
  apply buffers_ss_rel_coarse.
  eapply buffers_related_append_scratch_ne; try edone.
  by rewrite Erbpt.
Qed.  

Lemma tso_bound_to_scratch:
  forall tso p bnd,
    tso_memory_upper_bound bnd tso ->
    bnd <= Ptr.block p ->
    scratch_ptr p.
Proof.
  intros tso [b ofs] bnd (_ & _ & BND) LE.
  simpl in *. 
  apply scratch_less_block. omega.
Qed.

Lemma buffer_scratch_ranges_if_scratch:
  forall rs
    (SCRP: forall p n, In (p, n) rs -> scratch_ptr p),
      buffer_scratch_ranges (alloc_items_of_ranges rs) = rs.
Proof.
  induction rs as [|[p' n'] rs IH]; intros.
  
  done.
  
  simpl. pose proof (SCRP _ _ (in_eq _ _)) as SCR. 
  unfold scratch_ptr in SCR. destruct p' as [b' o'].
  simpl. rewrite SCR. f_equal.
  apply IH. 
  intros p0 n0 IN0. eby eapply SCRP, in_cons.
Qed.

Lemma allocs_scratch_disjoint_to_unbuffer_safe:
  forall ttso tthr stso sthr bp sp tp t ttso' stso' rs bnd
    (TC  : Comp.consistent tso_mm cst_sem (ttso, tthr))
    (USt : unbuffer_safe ttso')
    (TREL: tso_pc_related_witt (ttso, tthr) (stso, sthr) bp tp sp)
    (DISJ: range_list_disjoint rs)
    (VARs: forall r, In r rs -> valid_alloc_range r)
    (TSOBND: tso_memory_upper_bound bnd stso)
    (INS : forall p' n', In (p', n') rs -> bnd <= Ptr.block p')
    (BAs : is_buffer_ins t (alloc_items_of_ranges rs) stso stso'),
      unbuffer_safe stso'.
Proof.
  intros.
  destruct TREL as (MTB & NSMR & (MCRt & MCRs & LR) & SC &
    BPD & BNE & SAF & MRPt & MRPs & TREL).
  simpl in *.

  assert(SSREL: tso_pc_ss_rel ttso stso').
    exists (tupdate t (append_items_to_bpart (alloc_items_of_ranges rs) 
                                             (bp t)) bp).
    exists tp. exists sp.

    assert (SAF' : scratch_allocs_fresh (tso_buffers stso') sp).
      eapply scratch_allocs_fresh_app; try edone.
      intros p' n' IN'; right; apply (INS p' n' IN').

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
    - by rewrite (is_buffer_ins_m _ _ _ _ BAs). 
    - (* source mem is machine *)
      by rewrite (is_buffer_ins_m _ _ _ _ BAs).
    - (* Finite support for ttso *) 
      by apply TSO.tso_cons_impl_fin_sup in TC. 
    - (* Finite support for stso *)
      eapply fin_sup_buffer_ins. eby eapply (TSO.tso_cons_impl_fin_sup cs_sem).
      edone.
    - by destruct TC. (* Unbuffer safety of target *)
    - (* Flattened buffer partitions correspond to buffers *)
      intro t'.
      destruct (peq t' t) as [-> | N].
        rewrite (is_buffer_ins_s _ _ _ _ BAs), tupdate_s.
        by rewrite BPD, append_scratch_to_part_flatten.
      rewrite tupdate_o. by rewrite (is_buffer_ins_o _ _ _ _ BAs), BPD.
      done.
    - (* Source memory consistent with partitioning *)
      by rewrite (is_buffer_ins_m _ _ _ _ BAs).
    - intros t'.
    destruct (TREL t') as (PI & BR & BSR).
    split. done. (* Partitions injective *)
    destruct (peq t' t) as [-> | N].
      rewrite tupdate_s.
      destruct (buffers_related_part_update BR) as [_ [sp' PUBs]].
      eapply buffers_related_append_scratch; try edone.
            destruct TC; eby eapply unbuffer_safe_prefix_buffer_machine.
          intros bi IN. eapply is_item_scratch_alloc_items_scratch, IN.
          intros p n IN'. eapply tso_bound_to_scratch. edone. eby eapply INS.
        eapply update_buffer_allocs; try edone.
      exploit (scratch_allocs_fresh_apply_buffer _ _ _ stso'.(tso_buffers) 
        (tupdate t (alloc_items_of_ranges rs) stso'.(tso_buffers)) _ PUBs).
        by rewrite (is_buffer_ins_s _ _ _ _ BAs), BPD, tupdate_s.
        intros t' N. by rewrite tupdate_o. 
        done.
      intros (_ & _ & RLDP).
      specialize (RLDP t t).
      rewrite tupdate_s, update_partitioning_s in RLDP.
      rewrite buffer_scratch_ranges_if_scratch in RLDP. done.
      intros p n IN'. eapply tso_bound_to_scratch. edone. eby eapply INS.
    by rewrite tupdate_o; [|done]; constructor.

  eapply alloc_unbuffer_safe; 
    try apply (is_buffer_ins_s _ _ _ _ BAs); try edone.
  - by destruct SC.
  - by apply (disjoint_allocs_from_alloc_items_of_ranges _ DISJ VARs).
  apply (is_buffer_ins_o _ _ _ _ BAs).
  intros r k. by rewrite (is_buffer_ins_m _ _ _ _ BAs).
Qed.

Lemma thread_tau_alloc:
  forall tso (st : PTree.t Cstacked.state) cstso csst bp tp sp nenv env f vs csm_k k t optid
  (TRELW : tso_pc_related_witt (tso, st) (cstso, csst) bp tp sp)
  (TC : Comp.consistent tso_mm cst_sem (tso, st))
  (* TPMP : forall (p : pointer) (n : int), In (p, n) tp' -> machine_ptr p *)
  (BE : build_env f = Some (nenv, 0%Z))
  (ND : NoDup (map (@fst _ _) (fn_variables f)))
  (Ess' : csst ! t = Some (SKcall vs csm_k))
  (SCO' : state_consistent_with_env 
     (Cstacked.SKbind f vs (map (@fst _ _) (fn_params f)) (mkcsenv None nenv)
          (Cstacked.Kcall optid (Internal f) env k)))
  (CS : st ! t =
        Some (Cstacked.SKcall vs (Cstacked.Kcall optid (Internal f) env k))),
   exists shms',
     taustep cshm_lts (cstso, csst) Etau shms' /\
     tso_pc_related
       (tso,
       st ! t <-
       (Cstacked.SKbind f vs (map (@fst _ _) (fn_params f)) (mkcsenv None nenv)
          (Cstacked.Kcall optid (Internal f) env k))) shms'.
Proof.
  intros.
  pose proof (tso_pc_related_to_buff_states _ _ _ _ _ _ _ t TRELW) as BOR.
  pose proof TRELW as (MTB & NSMR & (MCRt & MCRs & LR & MCM) & SC &
    BPD & BNE & SAF & MRPt & MRPs & TREL). simpl in *.
  rewrite CS, Ess' in BOR. simpl in BOR.
  destruct BOR as [sm' [sp' [tp' (AB' & PUBt & PUBs & SR & SCO)]]].

  inv SR.
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
  destruct FINP as [fid FINP].
  assert (LIM := function_stacksize_limit _ _ 
                   (PMap.init Var_global_array) FINP).
  destruct (build_compilenv (PMap.init Var_global_array) f) 
    as [cenv fsz] _eqn : Ebce.
  destruct (build_envmap (fn_variables f) cenv (PTree.empty env_item))
    as [e|] _eqn : Ee; [|done]. inv BE.
  set (p := Ptr 0 Int.zero).
  assert (MP : machine_ptr p). done.
  assert (PBND := scratch_min_block_mptr _ _ _ MP TSOUB).
  unfold build_compilenv in Ebce.
  simpl in LIM.

  (* Get the ranges of variables... *)  
  destruct (ranges_of_vars_succ _ _ _ 0 _ _ _ _ ND PBND Ebce 
                                (Zle_refl _) LIM (or_intror _ (refl_equal _)))
    as [rs (ROV & RLD & VARs & INOSCR)].

  assert(BNDrs : forall p' n', In (p', n') rs -> bnd <= Ptr.block p').
    intros p' n' IN'.
    specialize(VARs _ IN'). destruct(INOSCR _ IN') as [[RIN _]|B].
      destruct p'; destruct p.
      unfold range_inside, valid_alloc_range in *. 
      replace (Int.unsigned (Int.repr 0)) with 0 in RIN; [|by compute];
        omegaContradiction.
    simpl in B; omega.
  end_assert BNDrs.

  (* Get the unbuffer safety for source... *)
  assert(USsi: unbuffer_safe (buffer_insert_list t (alloc_items_of_ranges rs)
                                                 cstso)).
    eby destruct SC; eapply allocs_scratch_disjoint_to_unbuffer_safe,
               is_buffer_ins_buffer_insert_list.
  
  assert (ABs := no_unbuffer_errors _ t USsi).
  rewrite buffer_insert_list_s, buffer_insert_list_m, apply_buffer_app, AB' 
    in ABs. simpl in ABs.
  destruct (apply_buffer (alloc_items_of_ranges rs) sm') as [sm''|] _eqn:ABs'';
    [|done].

  (* Get allocation step and relation on environment items *)
  destruct (buffer_alloc_env_related csm_globenv csm_e f optid _ _ _ _ _ _ vs
    csm_k0 _ _ empty_env 
    _ _ _ _ _ _ ROV ABs'' Ee ND PBND (proj2 (proj2 TSOUB)) Ebce (Zle_refl _)
    LIM (or_intror _ (refl_equal _)) (refl_equal _) (empty_envs_items_rel _ _ _) 
    (empty_env_local_cons_with_ids _)) as (ASTEPS & ITSREL & LC).
  unfold mkcstenv in ITSREL.

  (* And transform to taustars *)
  destruct (alloc_steps_buffer csm_globenv _ _ _ _ _ _ 
    ASTEPS (PTree.gss _ _ csst) USsi) 
    as [sthrs' (TAUa & NSa & OSa)].


  set (ntso := buffer_insert_list t (alloc_items_of_ranges rs) cstso).

  set (nthr := sthrs' ! t <-
     (SKbind f vs (map (@fst _ _) (fn_params f))
        (build_csm_env (fn_variables f) cenv bnd p empty_env)
        (Kcall optid (Internal f) csm_e csm_k0))).
  
  (* Prove the weakstep *)
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
  end_assert WS.

  (* Build some auxiliary statements *)
  assert (SAF' : scratch_allocs_fresh (tso_buffers ntso) sp).
    eapply scratch_allocs_fresh_app; try edone.
    apply is_buffer_ins_buffer_insert_list.
    intros p' n' IN'. 
    destruct (INOSCR (p', n') IN') as [[RI _] | BND].
      left. by destruct p'; destruct p; destruct RI as [-> _].
    right. simpl in *. omega.
  end_assert SAF'.

  assert(SCRrs : forall px nx, In (px, nx) rs -> scratch_ptr px).
    intros px nx INx. eapply tso_bound_to_scratch. edone. eby eapply BNDrs.
  end_assert SCRrs.

  assert(SCRITrs: forall bi, In bi (alloc_items_of_ranges rs) -> 
                             is_item_scratch_update bi).
    eby intros bi IN; eapply is_item_scratch_alloc_items_scratch.

  assert (RLDrssp : range_lists_disjoint rs sp').
    exploit (scratch_allocs_fresh_apply_buffer _ _ _ ntso.(tso_buffers) 
      (tupdate t (alloc_items_of_ranges rs) ntso.(tso_buffers)) _ PUBs);
      unfold ntso.
      by rewrite buffer_insert_list_s, BPD, tupdate_s.
      intros t' N. by rewrite tupdate_o. 
      done.
    intros (_ & _ & RLDP).
    specialize (RLDP t t).
    rewrite tupdate_s, update_partitioning_s in RLDP.
    rewrite buffer_scratch_ranges_if_scratch in RLDP. done.
    done.
  end_assert RLDrssp.

  assert(PUBrs : part_update_buffer (alloc_items_of_ranges rs) sp' = 
                 Some (rev rs ++ sp')).
    eby eapply update_buffer_allocs.


  destruct (rev (bp t)) as [|hbpt tbpt] _eqn : Erbt.
    (* Buffer is empty, so we need to unbuffer the newly inserted allocations. *)
    pose proof (rev_nil (sym_eq Erbt)) as Erbnil.
    assert (Esbnil: tso_buffers cstso t = nil). by rewrite BPD, Erbnil.
    rewrite Esbnil in AB', PUBs. inv PUBs. inv AB'.
    exploit TSO.unbuffer_to_tso_state.
        pose proof (buffer_insert_list_s t (alloc_items_of_ranges rs) cstso)
          as Ebuf. rewrite app_nil_end in Ebuf. fold ntso in Ebuf; by apply Ebuf.
      rewrite Esbnil. unfold ntso. rewrite buffer_insert_list_m. apply ABs''.
    intros [ntso' (TAU & BUFt & BUFother & MEMntso')].
    eexists (_, _).
    split. 
      eby eapply tausteptau_taustar_taustep; [edone|];
        eapply TSO.apply_buffer_reachable_taustar.
    (* Now the simulation relation... *)      
    split.
      (* tso consistency of target *)
      eby eapply Comp.thread_update_preserves_consistency.
    exists (tupdate t nil bp). exists tp. 
    exists (update_partitioning t (rev rs ++ (sp t)) sp).
    unfold nthr.

    assert (Etbnil : tso_buffers tso t = nil).
      pose proof (buffered_states_related_length_eq _ _ _ _ 
        (proj1 (proj2 (TREL t)))) as Elbuffs.
      rewrite Erbnil in Elbuffs. by destruct (tso_buffers tso t).
    end_assert Etbnil.
    rewrite Etbnil in PUBt; inv PUBt.

    assert(TCs' : Comp.consistent tso_mm cs_sem (ntso', nthr)).
      eby eapply Comp.taustep_preserves_consistency;
        [eapply tausteptau_taustar_taustep; [edone|];
         eapply TSO.apply_buffer_reachable_taustar |].

    split; simpl. (* machine buffers *)
      intro t'.
      destruct (peq t' t) as [-> | N].
        rewrite BUFt; eby intros bi IN; 
          apply (machine_buffer_alloc_items_of_ranges rs).
      rewrite BUFother; [|done]; unfold ntso;
        rewrite buffer_insert_list_o; [apply MTB | ]; done.
    split. (* non-stack memory consistent *)
      eapply non_stack_mem_rel_preserved_by_stack_or_write_buffer; try edone.
      intros bi IN. 
      eby eapply scratch_impl_stack_or_write, SCRITrs.
    split. (* memory contents related *)
      (* mem_content_related preservation *)
      split. done.
      split.
        eby erewrite mem_consistent_with_restr_apply_buffer; [apply MCRs|].
      (* Load value relation requires some more work: *)
      split. 
        eby eapply apply_scratch_buffer_preserves_load_rel.
      (* Memory contents are machine values *)
      eapply apply_machine_buffer_preserves_machine_memory; [|apply ABs''|done].
      apply machine_buffer_alloc_items_of_ranges.
    split. apply TCs'. (* tso consistency for source *)
    split. (* buffer partitioning *)
      intro t'.
      destruct (peq t' t) as [-> | N].
        by rewrite BUFt, tupdate_s.
      rewrite BUFother; [unfold ntso|done]; 
        by rewrite buffer_insert_list_o, tupdate_o, BPD.
    split. (* buffer partitions non-empty *)
      intros t' bi IN.
      destruct (peq t' t) as [-> | N].
        by rewrite tupdate_s in IN.
      rewrite tupdate_o in IN. eby eapply BNE. done.
    split. (* Scratch allocation freshness *)
      eapply scratch_allocs_fresh_apply_buffer. edone. 
      3 : apply SAF'. 
      unfold ntso; by rewrite BUFt, <-app_nil_end, buffer_insert_list_s, Esbnil.
      by intros ? ?; rewrite BUFother.
    split. done. (* Target memory consistent with partitioning *)
    split. (* Source memory consistent with partitioning *)
      eby eapply apply_buffer_preserves_mem_partitioning.
    intros t'.
    destruct (TREL t') as (PI & BR & BSR).
    split. (* Partitions injective *)
      unfold update_partitioning.
      eby destruct (peq t' t) as [-> | N];
        [eapply update_part_buffer_scratch_preserves_partition_injectivity|].
    split. (* Buffers related *)
      destruct (peq t' t) as [-> | N].
        rewrite !@tupdate_s, Etbnil. constructor.
      by rewrite !@tupdate_o, update_partitioning_o. 
    (* Buffered states related *)
    destruct (peq t' t) as [-> | N].
      (* The allocating thread: *)
      rewrite !@tupdate_s, !@PTree.gss, update_partitioning_s, Etbnil; simpl.
      eexists. eexists. eexists.
      repeat (split; [done|]). 
      replace (tp t) with (nil ++ (tp t)); [|done].
      split; [|done].
      eapply st_rel_bind.
        eapply cont_related_load_inv. edone.
        eby eapply allocs_mem_agrees_on_scratch_mrwp with (b := nil).
      (* Environments related *)
      exists (Int.repr 0).
      split; simpl. 
        by split.
      split. 
        apply range_list_disjoint_perm with (l := rs).
        apply Permutation_rev.
        done.
      split.
        eapply Permutation_trans.
          apply Permutation_sym, Permutation_rev.
        eapply env_ranges_permut_range_of_vars.
        edone. edone. done. done. done.
        by intros r1 IN1 r2 IN2.
      intros r1 IN1 r2 IN2. apply In_rev in IN2. 
      apply ranges_disjoint_comm. eby eapply RLDrssp.
    (* Other threads - we must show that the unbuffering does not affect 
       the other threads. *)
    rewrite tupdate_o, update_partitioning_o, !@PTree.gso, OSa, !@PTree.gso; 
      try done; [].
    destruct (csst ! t') as [sst|]; destruct (st ! t') as [tst|]; 
      simpl in BSR; try done; simpl; [].
    pose proof MRPs as X; destruct X as [PDx [RLDx RLAx]].
    destruct (apply_buffer_preserves_mem_partitioning _ _ _ _ _ _ 
      MRPs ABs'' PUBrs) as [PR' [RLD' RLA']]. 
    apply buffered_states_related_load_inv with (smem := tso_mem cstso);
      try done.
          intros r IN. apply (RLAx r). eby eexists.
        intros r IN. apply (RLA' r). exists t'.
        rewrite update_partitioning_o. done. done.
      eapply unbuffer_safe_to_buffer_safe_for_mem; try edone.
        by destruct SC.
        rewrite <- app_nil_end. apply BPD.
      eapply unbuffer_safe_to_buffer_safe_for_mem; try edone. 
        by destruct TCs'.
      rewrite <- app_nil_end.
      rewrite BUFother. unfold ntso. by rewrite buffer_insert_list_o, BPD.
      done.
    eby eapply unbuffering_other_buffer_agrees_on_scratch.

  (* There is already something in the buffers, 
     so we do not have to unbuffer *)
  pose proof (rev_cons (sym_eq Erbt)) as Erbpt.

  assert (BRt : buffers_related
     (tso_buffers tso t)
     (tp t) (append_items_to_bpart (alloc_items_of_ranges rs) (bp t)) (sp t)).
    destruct (TREL t) as (PIt' & BRt' & _).
    eapply buffers_related_append_scratch_ne; try edone.
    eapply unbuffer_safe_prefix_buffer_machine; try edone. by destruct TC.
    rewrite <- BPD. apply PUBs.
    by rewrite Erbt.
  end_assert BRt.
                             
  eexists (_, _).
  split. apply WS.
  (* Finally, establish the simulation relation *)
  split. (* tso consistency of target *)
    eby eapply Comp.thread_update_preserves_consistency.
  exists (tupdate t (append_items_to_bpart  (alloc_items_of_ranges rs) 
                                            (bp t)) bp).
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
      by rewrite append_scratch_to_part_flatten, BPD.
    by rewrite buffer_insert_list_o, tupdate_o, BPD.
  split. (* buffer partitions non-empty *)
    intros t' bi IN.
    destruct (peq t' t) as [-> | N].
      rewrite tupdate_s in IN.
      unfold append_items_to_bpart in IN.
      rewrite Erbt in IN.
      apply in_app_or in IN. 
      destruct IN as [IN | [<- | IM]].
          apply (BNE t). rewrite Erbpt. apply in_or_app. by left.
        intro A. destruct (app_eq_nil _ _ A) as [Hnil _].
        revert Hnil. apply (BNE t). rewrite Erbpt. apply in_or_app. 
      by right; left. done.
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
    rewrite append_scratch_to_part_flatten in PUBs'.
    rewrite fold_left_opt_app, <- BPD, PUBs in PUBs'. 
    simpl in PUBs'. 
    rewrite (part_update_buffer_alloc_items_of_ranges PUBs') in PUBs'.
    eexists. eexists. eexists.
    split.
      eby rewrite append_scratch_to_part_flatten, <- BPD, apply_buffer_app, AB'.
    split. edone.
    split. unfold part_update_buffer.
      eby rewrite append_scratch_to_part_flatten, fold_left_opt_app, 
        <- BPD, PUBs.
    replace tp' with (nil ++ tp'); [|done].
    split; [|done].
    eapply st_rel_bind.
      eapply cont_related_load_inv.
        edone. 
        eapply allocs_mem_agrees_on_scratch_mrwp; try edone;
          intros r IN; apply in_or_app; by right.
    (* Environments related *)
    exists (Int.repr 0).
    split; simpl. 
      by split.
    split. 
      apply range_list_disjoint_perm with (l := rs).
      apply Permutation_rev.
      done.
    split.
      eapply Permutation_trans.
        apply Permutation_sym, Permutation_rev.
      eapply env_ranges_permut_range_of_vars.
      edone. edone. done. done. done.
      by intros r1 IN1 r2 IN2.
    intros r1 IN1 r2 IN2. apply In_rev in IN2. 
    apply ranges_disjoint_comm. eby eapply RLDrssp.
  rewrite !@tupdate_o, buffer_insert_list_m, !@PTree.gso; try done.
  by rewrite OSa, PTree.gso.
Qed.

Definition measure (s : Cstacked.state) : nat :=
  match s with 
    | SKfree _ _ _ => 1
    | _ => 0 
  end % nat.

Lemma load_result_idem:
  forall c v,
    Val.load_result c (Val.load_result c v) = Val.load_result c v.
Proof.
  intros.
  destruct c; try done; simpl; destruct v; try done;
    try (by rewrite Int.sign_ext_idem);
    try (by rewrite Int.zero_ext_idem);
    by rewrite Float.singleoffloat_idem.
Qed.

Lemma valid_alloc_range_chunk_aligned:
  forall p c, 
    valid_alloc_range (range_of_chunk p c) ->
    pointer_chunk_aligned p c.
Proof.
  intros [b ofs] c (_&_&_&ALG).
  simpl. rewrite size_chunk_repr in ALG.
  eapply Zdivide_trans, ALG.
  by destruct c; compute; apply Zmod_divide.
Qed.

Lemma load_res_cast:
  forall c v,
    Val.load_result c (cast_value_to_chunk c v) =
    Val.load_result c v.
Proof.
  intros c v.
  destruct c; destruct v; simpl; clarify; simpl;
    rewrite ?Int.sign_ext_zero_ext, ?Int.zero_ext_idem,
            ?Float.singleoffloat_idem; clarify.
Qed.

Lemma env_related_var_local_store:
  forall {sp sm tp te se te' id v c p}
  (AL : forall r, In r sp -> range_allocated r MObjStack sm)
  (ER : env_related tp sp sm te se)
  (VLS: var_local_store te id v te')
  (LOC: se ! id = Some (p, Vscalar c)),
  exists sm',
    store_ptr c sm p (cast_value_to_chunk c v) = Some sm' /\
    env_related tp sp sm' te' se /\
    In (range_of_chunk p c) sp /\
    scratch_ptr p.
Proof.
  intros.
  inv VLS.
  destruct ER as [n (BP & RLD & PERM & EIR)].
  pose proof (EIR id) as EIRid. rewrite EG, LOC in EIRid.
  inv EIRid.
  assert(INsp: In (range_of_chunk p c) sp).
    apply PTree.elements_correct in LOC.
    apply (Permutation_in _ (Permutation_sym PERM)).
    unfold env_ranges.
    apply in_map with (f := fun ei => csm_env_item_range (snd ei)) in LOC.
    by unfold range_of_chunk, csm_env_item_range, sizeof in *.
  pose proof (store_chunk_allocated_spec c sm p (cast_value_to_chunk c v)) as SSP.
  destruct (store_ptr c sm p (cast_value_to_chunk c v)) as [sm'|] _eqn : Est.
    2 : by elim SSP; split;
      [eexists; exists MObjStack;
       split; [apply range_inside_refl | apply AL] | 
       apply valid_alloc_range_chunk_aligned].
  exists sm'.
  split. done.
  split; [|done].
  exists n.
  split. done.
  split. done.
  split. done.
  intro id'.
  destruct (peq id' id) as [-> | N].
    simpl. rewrite PTree.gss.
    rewrite LOC. 
    econstructor; try edone.
    erewrite load_store_similar. 2 : edone.
    by destruct c; unfold compatible_chunks; rewrite load_res_cast. 
    done. apply Val.load_result_wt.
    apply load_result_idem.
  simpl. rewrite !@PTree.gso; try done.
  specialize (EIR id').
  destruct ((csenv_env te) ! id') as [] _eqn : EG';
    destruct (se ! id') as [] _eqn : LOC'; try done; [].
  inv EIR; try (eby econstructor); [].
  econstructor; try edone.
  erewrite <- load_store_other; try edone.
  apply (range_list_disjoint_perm _ _ PERM) in RLD.
  apply PTree.elements_correct in LOC.
  apply PTree.elements_correct in LOC'.
  revert LOC LOC' RLD.
  unfold env_ranges.
  induction (PTree.elements se) as [|eh et IH]. done.
  simpl; intros. destruct RLD as [RLD RNI].
  destruct LOC as [-> | LOC]; destruct LOC' as [E | LOC'].
        by inv E.
      apply RNI.
      apply in_map with (f := fun ei => csm_env_item_range (snd ei)) in LOC'.
      by unfold range_of_chunk, csm_env_item_range, sizeof in *.
    rewrite E in RNI; apply ranges_disjoint_comm, RNI.
    apply in_map with (f := fun ei => csm_env_item_range (snd ei)) in LOC.
    by unfold range_of_chunk, csm_env_item_range, sizeof in *.
  by apply IH.
Qed.

Lemma env_related_var_local_store_ref:
  forall {sp sm tp te se te' id v c p}
  (AL : forall r, In r sp -> range_allocated r MObjStack sm)
  (ER : env_related tp sp sm te se)
  (VLS: var_local_store te id v te')
  (EVR: eval_var_ref csm_globenv se id p c),
  exists sm',
    store_ptr c sm p (cast_value_to_chunk c v) = Some sm' /\
    env_related tp sp sm' te' se /\
    In (range_of_chunk p c) sp /\
    scratch_ptr p.
Proof.
  intros.
  inv EVR. eby eapply env_related_var_local_store.
  inv VLS.
  destruct ER as [n (BP & RLD & PERM & EIR)].
  pose proof (EIR id) as EIRid. 
  replace (se ! id) with (@None (pointer * var_kind)) in EIRid. 
  by rewrite EG in EIRid.
Qed.

Lemma mem_agrees_on_scratch_disjoint_write:
  forall c m p v m' sp
    (ST : store_ptr c m p v = Some m')
    (RNI: range_not_in (range_of_chunk p c) sp),
      mem_agrees_on_scratch m m' sp.
Proof.
  intros.
  intros r' p' c' IN' RI SCR.
  rewrite (load_store_other ST). done.
  eapply disjoint_inside_disjoint_r, RI.
  by apply RNI.
Qed.

Lemma cont_related_disjoint_write:
  forall c m p v m' tk sk tr sr srw
    (ST : store_ptr c m p v = Some m')
    (CR : cont_related tr sr m tk sk)
    (RLD: range_lists_disjoint sr srw)
    (ROC: In (range_of_chunk p c) srw), 
       cont_related tr sr m' tk sk.
Proof.
  intros.  
  eapply cont_related_load_inv. edone.
  eapply mem_agrees_on_scratch_disjoint_write. edone.
  intros rx INx. 
  by apply ranges_disjoint_comm, RLD.
Qed.

Lemma tau_write_thread_sim:
  forall ts ts' ss ss' p c v tp sp sm
    (AL  : forall r, In r sp -> range_allocated r MObjStack sm)
    (TS  : cst_step cst_globenv ts TEtau ts')
    (SS  : cs_step csm_globenv ss (TEmem (MEwrite p c v)) ss')
    (SR  : state_related tp sp sm ts ss),
    (exists sm',
      store_ptr c sm p v = Some sm' /\
      state_related tp sp sm' ts' ss' /\
      scratch_ptr p /\ machine_val v /\
      In (range_of_chunk p c) sp) \/
    ((measure ts' < measure ts) % nat /\
     state_related tp sp sm ts' ss).
Proof.
  intros.
  
  inv SS. 
  (* Assign *) 
  inv SR. inv EKR. inv TS.
  exploit @env_related_var_local_store_ref; [|edone|edone|edone|].
    by intros r IN; apply AL, in_or_app; left.
  intros [sm' (STP & ER' & IN' & SCR')].
  left. exists sm'. split. done.
  split.
    econstructor; try edone.
    eby eapply cont_related_disjoint_write.
  split; [done|]. 
  split; [by apply machine_val_cast|].
  apply in_or_app. by left.

  (* Store *)
  by inv SR; inv EKR; inv TS.

  (* Return some *)
  inv SR. 
      by inv EKR. 
    right. inv TS. subst. 
    destruct csm_obs' as [|[? ?] ?];
      [|by pose proof (Permutation_nil (Permutation_sym P))].
    split. done. simpl. eby econstructor.
  inv TS; pose proof (call_cont_related _ KR) as CCR; 
    rewrite CC, H4 in CCR; inv CCR.
  exploit @env_related_var_local_store_ref; [|edone |edone| edone|].
    by intros r IN; apply AL, in_or_app; left.
  intros [sm' (STP & ER' & IN' & SCR')].
  left. exists sm'. split. done.
  split.
    econstructor; try edone.
    eby eapply cont_related_disjoint_write.
  split; [done|]. 
  split; [by apply machine_val_cast|].
  apply in_or_app. by left.

  (* Bind *)
  inv SR. inv TS.
  exploit @env_related_var_local_store; [|edone|edone|edone|].
    by intros r IN; apply AL, in_or_app; left.
  intros [sm' (STP & ER' & IN' & SCR')].
  left. exists sm'. split. done.
  split.
    econstructor; try edone.
    eby eapply cont_related_disjoint_write.
    intros v' INv'. apply MVL. by right.
  split. done. 
  split. apply machine_val_cast, MVL, in_eq.
  apply in_or_app. by left.

  (* External return some *)
  inv SR. inv TS.
  exploit @env_related_var_local_store_ref; [|edone|edone|edone|].
    by intros r IN; apply AL, in_or_app; left.
  intros [sm' (STP & ER' & IN' & SCR')].
  left. exists sm'. split. done.
  split.
    econstructor; try edone.
    eby eapply cont_related_disjoint_write.
  split; [done|]. 
  split; [by apply machine_val_cast|].
  apply in_or_app. by left.
Qed.

Lemma chunk_inside_range_list_spec_rev:
  forall p c l r,
    In r l /\ range_inside (range_of_chunk p c) r ->
    chunk_inside_range_list p c l = true.
Proof.
  intros p c l r.
  
  induction l as [|h l IH]; intros [IN RIN]. done.

  simpl.
  destruct range_inside_dec as [RI' | RNI']. done.
  simpl in IN; destruct IN as [<- | IN]. done.
  by apply IH. 
Qed.

Lemma tau_write_sim_rel:
  forall ttso (tthr: PTree.t Cstacked.state) stso (sthr: PTree.t Csharpminor.state) bp tp sp t ts ts' ss ss' p c v
    (TRELW : tso_pc_related_witt (ttso, tthr) (stso, sthr) bp tp sp)
    (TC  : Comp.consistent _ cst_sem (ttso, tthr))
    (CTS : tthr ! t = Some ts)
    (CSS : sthr ! t = Some ss)
    (TS  : cst_step cst_globenv ts TEtau ts')
    (SS  : cs_step csm_globenv ss (TEmem (MEwrite p c v)) ss'),
      can_reach_error csm_globenv (stso, sthr) \/
      (exists stso',
        taustep cshm_lts (stso, sthr) Etau (stso', sthr ! t <- ss') /\
        tso_pc_related (ttso, tthr ! t <- ts') (stso', sthr ! t <- ss')) \/
      tso_pc_related (ttso, tthr ! t <- ts') (stso, sthr) /\
      (measure ts' < measure ts) % nat.
Proof.
  intros.
  pose proof TRELW as (MTB & NSMR & (MCRt & MCRs & LR & MCM) & SC &
    BPD & BNE & SAF & MRPt & MRPs & TREL).
  pose proof (proj2 (proj2 (TREL t))) as BSR. simpl in *.
  rewrite CTS, CSS in BSR; simpl in BSR.

  assert (TC' : Comp.consistent tso_mm cst_sem (ttso, tthr ! t <- ts')).
    eby eapply Comp.thread_update_preserves_consistency.
  end_assert TC'. 

  destruct BSR as [smt [spt [tpt (ABs & PUBt & PUBs & SRt & SCOt)]]].

  assert (SCO' := step_consistent_with_env TS SCOt).

  exploit tau_write_thread_sim; try edone; [|].
    destruct (apply_buffer_preserves_mem_partitioning _ _ _ _ _ _ 
      MRPs ABs PUBs) as (_ & _ & MR).
    intros r IN. apply -> MR. exists t. by rewrite update_partitioning_s.
  intros [[sm' (STP & SR' & SCR & MV & INsp)] | [ML SR']].
    assert (TFS := TSO.tso_cons_impl_fin_sup _ _ SC).
    assert (FS' := fin_sup_buffer_insert_list t 
                (BufferedWrite p c v:: nil) _ TFS).
    destruct (unbuffer_safe_dec _ FS') as [USi | NUSi].
      (* Unbuffer safe for the inserted write *)
      assert (SStso: stepr cshm_lts (stso, sthr) Etau
                       (buffer_insert_list t (BufferedWrite p c v :: nil) stso,
                       sthr ! t <- ss')).
        eby simpl; econstructor; try edone; econstructor.

      assert (PUBw : part_update_buffer (BufferedWrite p c v :: nil) spt = 
                     Some spt).
          unfold part_update_buffer; simpl. destruct p; simpl in *; rewrite SCR.
          erewrite chunk_inside_range_list_spec_rev. edone. split. apply INsp.
          apply range_inside_refl.
      end_assert PUBw.
      (* We still need to differentiate between an empty and a non-empty
         buffer (empty buffer needs to be unbuffered to maintan the 
         relation. *)
      destruct (rev (bp t)) as [|hbpt tbpt] _eqn : Erbt.
        (* Empty buffer *)
        pose proof (rev_nil (sym_eq Erbt)) as Erbnil.
        assert (Esbnil: tso_buffers stso t = nil). by rewrite BPD, Erbnil.
        rewrite Erbnil in ABs, PUBs. inv PUBs. inv ABs.
        assert (Etbnil : tso_buffers ttso t = nil).
          pose proof (buffered_states_related_length_eq _ _ _ _ 
                        (proj1 (proj2 (TREL t)))) as Elbuffs.
          rewrite Erbnil in Elbuffs. by destruct (tso_buffers ttso t).
        end_assert Etbnil.
        rewrite Etbnil in PUBt; inv PUBt.
        exploit TSO.unbuffer_to_tso_state.
            pose proof (buffer_insert_list_s t (BufferedWrite p c v::nil) stso)
              as Ebuf. 
            rewrite app_nil_end in Ebuf. by apply Ebuf.
          rewrite Esbnil. rewrite buffer_insert_list_m. simpl. rewrite STP.
          reflexivity.
        intros [stso' (TAU & BUFt & BUFother & MEMntso')].
        subst.
        assert(ABw: apply_buffer (BufferedWrite p c v :: nil) (tso_mem stso) =
                    Some (tso_mem stso')).
          by simpl; rewrite STP.
        assert(WS: taustep cshm_lts (stso, sthr) Etau (stso', sthr!t <- ss')).
          eby eapply (@steptau_taustar_taustep _ cshm_lts _ (_, _));
            [|eapply TSO.apply_buffer_reachable_taustar].
        assert(TCs' : Comp.consistent tso_mm cs_sem (stso', sthr!t <- ss')).
          eby eapply Comp.taustep_preserves_consistency.
        right; left; exists stso'.
        split. apply WS.
        split. done.
        exists bp. exists tp. exists sp.
        split; simpl. (* Machine buffers *)          
          intro t'.
          destruct (peq t' t) as [-> | N]. 
            by rewrite BUFt. 
          rewrite BUFother; [|done];
            rewrite buffer_insert_list_o; [apply MTB | ]; done.
        split. (* non-stack memory consistent *)
          eapply non_stack_mem_rel_preserved_by_stack_or_write_buffer; try edone.
          intros bi IN. by destruct IN as [<- | []].
        split. (* memory contents related *)
          (* mem_content_related preservation *)
          split. done.
          split.
            eby erewrite mem_consistent_with_restr_apply_buffer; [apply MCRs|].
          (* Load value relation requires some more work: *)
          split. 
            eapply apply_scratch_buffer_preserves_load_rel. apply ABw. 
            by intros bi [<- | []]. done.
          (* Memory contents are machine values *)
          eapply apply_machine_buffer_preserves_machine_memory; [|apply ABw|done].
          by intros bi [<- | []].
        split. apply TCs'. (* tso consistency for source *)
        split. (* buffer partitioning *)
          intro t'.
          destruct (peq t' t) as [-> | N].
            by rewrite BUFt, Erbnil.
          rewrite BUFother; [|done]; 
            by rewrite buffer_insert_list_o, BPD.
        split. (* buffer partitions non-empty *)
          intros t' bi IN.
          destruct (peq t' t) as [-> | N].
            by rewrite Erbnil in IN.
          eby eapply BNE.
        split. (* Scratch allocation freshness *)
          eapply scratch_allocs_fresh_ext. edone. done.
          intros t'. destruct (peq t' t) as [<- | N].
            by rewrite Esbnil, BUFt. 
          by rewrite BUFother, buffer_insert_list_o.
        split. done. (* Target memory consistent with partitioning *)
        split. (* Source memory consistent with partitioning *)
          eapply mem_related_with_partitioning_ext.
          eapply apply_buffer_preserves_mem_partitioning with (t := t); try edone.
          intro t'. 
          destruct (peq t' t) as [<- | N]. by rewrite update_partitioning_s.
          by rewrite update_partitioning_o.
        intros t'.
        destruct (TREL t') as (PI & BR & BSR).
        split. done. (* Partitions injective *)
        split. done. (* Buffers related *)
        (* States related *)
        destruct (peq t' t) as [-> | N].
          rewrite !@PTree.gss. simpl. 
          eexists. eexists. eexists.
          split. rewrite Erbnil. simpl. reflexivity.
          split. rewrite Etbnil. simpl. reflexivity.
          split. rewrite Erbnil. simpl. reflexivity.
          done.
        rewrite !@PTree.gso; try done; [].
        destruct (sthr ! t') as [sst|]; destruct (tthr ! t') as [tst|]; 
          simpl in BSR; try done; simpl; [].
        pose proof MRPs as X; destruct X as [PDx [RLDx RLAx]].
        exploit apply_buffer_preserves_mem_partitioning; try edone; [].
        intros [PR' [RLD' RLA']].
        apply buffered_states_related_load_inv with (smem := tso_mem stso);
          try done.
              intros r IN. apply (RLAx r). eby eexists.
            intros r IN. apply (RLA' r). exists t'.
            rewrite update_partitioning_o. done. done.
          eapply unbuffer_safe_to_buffer_safe_for_mem; try edone.
            by destruct SC. rewrite <- app_nil_end. apply BPD.
          eapply unbuffer_safe_to_buffer_safe_for_mem; try edone. 
            by destruct TCs'.
          rewrite <- app_nil_end.
          by rewrite BUFother; [rewrite buffer_insert_list_o, BPD|].
        eapply mem_agrees_on_scratch_disjoint_write. apply STP.
        specialize (PR' _ _ N).
        rewrite update_partitioning_s, update_partitioning_o in PR'; [|done].
        apply range_lists_disjoint_comm in PR'.
        by apply PR'.
      (* Non-empty buffer *)
      pose proof (rev_cons (sym_eq Erbt)) as Erbpt.
      
      assert(WS : taustep cshm_lts (stso, sthr) Etau
                    (buffer_insert stso t (BufferedWrite p c v), sthr ! t <- ss')).
        eby eapply step_taustep.

      assert (BRt : buffers_related (tso_buffers ttso t) (tp t)
        (append_items_to_bpart (BufferedWrite p c v :: nil) (bp t)) (sp t)).
        destruct (TREL t) as (PIt' & BRt' & _).
        eapply buffers_related_append_scratch_ne; try edone.
        eapply unbuffer_safe_prefix_buffer_machine; try edone. by destruct TC.
        by intros bi [<- | []]. 
        by rewrite Erbt.
      end_assert BRt.

      right; left.
      eexists. split. apply WS.
      split. done.
      (* Finally, establish the simulation relation *)
      exists (tupdate t (append_items_to_bpart (BufferedWrite p c v :: nil) 
                                             (bp t)) bp).
      exists tp. exists sp.
      split; simpl. (* machine buffers *)
        intro t'.
        destruct (peq t' t) as [-> | N].
          rewrite tupdate_s.
          intros bi IN. apply in_app_or in IN.
          destruct IN as [IN | [<- | []]]. eby eapply MTB. done.
        rewrite tupdate_o; [apply MTB | ]; done.
      split. done. (* non-stack memory consistent *)
      split. done. (* memory contents related *)
      split. (* tso consistency for source *)
        eby eapply Comp.taustep_preserves_consistency.
      split. (* buffer partitioning *)
        intro t'.
        destruct (peq t' t) as [-> | N].
          by rewrite !@tupdate_s, BPD, append_scratch_to_part_flatten.
        by rewrite !@tupdate_o, BPD.
      split. (* buffer partitions non-empty *)
        intros t' bi IN.
        destruct (peq t' t) as [-> | N].
          rewrite tupdate_s in IN.
          unfold append_items_to_bpart in IN; rewrite Erbt in IN.
          apply in_app_or in IN. 
          destruct IN as [IN | [<- | []]]. 
            eapply (BNE t). rewrite Erbpt. by apply in_or_app; left.
          intro. eby eapply app_cons_not_nil, sym_eq.
        rewrite tupdate_o in IN. eby eapply BNE. done.
      split. (* Scratch allocation freshness *)
        by apply scratch_allocs_fresh_write.
      split. done. (* Target memory consistent with partitioning *)
      split. done. (* Source memory consistent with partitioning *)
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
        simpl. 
        destruct (buffers_related_part_update BRt) as [_ [sps PUBs']].
        unfold part_update_buffer in *.
        rewrite append_scratch_to_part_flatten in PUBs'.
        eexists. exists spt. exists tpt. 
        split.
          rewrite append_scratch_to_part_flatten, apply_buffer_app, ABs.
          simpl. eby rewrite STP.
        split. edone.
        split. unfold part_update_buffer.
          by rewrite append_scratch_to_part_flatten, fold_left_opt_app, PUBs.
        done.
      by rewrite !@tupdate_o, !@PTree.gso.
    (* Unbuffer not safe. This should not really happen, but it is far
       easier to invoke the can_reach_error clause here. *)
    eby left; eapply write_step_fails.
  (* Handle the measure case *)
  right; right.
  split; [|done].
  split. done.
  exists bp. exists tp. exists sp.
  repeat (split; [done|]).
  intro t'.
  destruct (TREL t') as (PIt' & BRt' & SRt').
  repeat split; try done; [].
  destruct (peq t' t) as [-> | N]; simpl.
    rewrite PTree.gss, CSS. simpl.
    rewrite <- BPD in *.
    by exists smt; exists spt; exists tpt.
  by rewrite !@PTree.gso.
Qed.

Lemma ptree_store_same:
  forall A (t : PTree.t A) id v,
    t ! id = Some v ->
    t ! id <- v = t.
Proof.
  intros.
  apply PTree.ext.
  intro id'. destruct (peq id' id) as [<- | N].
    by rewrite PTree.gss.
  by rewrite PTree.gso.
Qed.

Lemma machine_buffer_free_items:
  forall lp, machine_buffer (map free_item_of_ptr lp).
Proof.
  intros lp bi IN. apply in_map_iff in IN. 
  by destruct IN as [p [<- IN]].
Qed.

Lemma tau_free_sim:
  forall ttso (tthr: PTree.t Cstacked.state) stso (sthr: PTree.t Csharpminor.state) bp tp sp t ts ts' ss ss' lp spt 
         spt' sm' tpt
    (TRELW : tso_pc_related_witt (ttso, tthr) (stso, sthr) bp tp sp)
    (TC  : Comp.consistent _ cst_sem (ttso, tthr))
    (CTS : tthr ! t = Some ts)
    (CSS : sthr ! t = Some ss)
    (TS  : cst_step cst_globenv ts TEtau ts')
    (M   : (measure ts' < measure ts) % nat)
    (FS  : free_steps csm_globenv ss lp ss')
    (LPSP: forall p, In p lp -> scratch_ptr p)
    (PUBt: part_update_buffer (tso_buffers ttso t) (tp t) = Some tpt)
    (PUBs: part_update_buffer (tso_buffers stso t) (sp t) = 
           Some (spt' ++ spt))
    (ABs : apply_buffer (tso_buffers stso t) (tso_mem stso) = Some sm')
    (NSR : forall sm'', 
             apply_buffer (map free_item_of_ptr lp) sm' = Some sm'' ->
             state_related tpt spt sm'' ts' ss')
    (SCO': state_consistent_with_env ts')
    (PERM: Permutation (map (@fst _ _) spt') lp),

      can_reach_error csm_globenv (stso, sthr) \/
      (exists sms',
        taustep cshm_lts (stso, sthr) Etau sms' /\
        tso_pc_related (ttso, tthr ! t <- ts') sms') \/
      tso_pc_related (ttso, tthr ! t <- ts') (stso, sthr) /\
      (measure ts' < measure ts) % nat.
Proof.
  intros.
  pose proof TRELW as (MTB & NSMR & (MCRt & MCRs & LR & MCM) & SC &
    BPD & BNE & SAF & MRPt & MRPs & TREL). simpl in *.

  (* Get unbuffer safety (otherwise use free_steps_fail to 
     get can_reach_error *)
  assert (TFS := TSO.tso_cons_impl_fin_sup _ _ SC).
  assert (FS' := fin_sup_buffer_insert_list t 
              (map free_item_of_ptr lp) _ TFS).
  destruct (unbuffer_safe_dec _ FS') as [USi | NUSi];
    [|eby left; eapply free_steps_fail].
  (* As a by-product, we know that we can apply the frees: *)
  pose proof (no_unbuffer_errors _ t USi) as ABfs; simpl in ABfs.
  rewrite buffer_insert_list_s, buffer_insert_list_m, apply_buffer_app, ABs 
    in ABfs; simpl in ABfs.
  destruct (apply_buffer (map free_item_of_ptr lp) sm') as [sm''|] _eqn : ABf;
    [clear ABfs | done].

  (* If lp is nil, we invoke the measure case *)
  assert (LPnildec : lp = nil \/ lp <> nil). by destruct lp; vauto.
  destruct LPnildec as [-> | Neqlpnil].
    inv FS.
    right; right; split.
    split.
      eby eapply Comp.thread_update_preserves_consistency.
    exists bp. exists tp. exists sp. repeat (split; [done|]).
    intro t'; destruct(TREL t') as (PIt' & BRt' & BSRt');repeat (split;[done|]).
    destruct (peq t' t) as [-> | N].
      simpl; rewrite !@PTree.gss, CSS; simpl.
      pose proof (Permutation_nil (Permutation_sym PERM)) as Emspt'.
      destruct spt' as [|[? ?] ?]; [|done].
      eexists; eexists; eexists. rewrite <- BPD; repeat (split; [edone|]).
      split. by apply NSR. done. 
    by simpl; rewrite !@PTree.gso.
    done.
  (* Now we know that we can move... *)
  right; left.
  destruct (free_steps_success _ _ _ _ _ _ _ _ FS CSS (refl_equal _) USi)
    as [sthr' (TAU' & CS' & OS')].
  assert (WS : taustep cshm_lts (stso, sthr) Etau 
    (buffer_insert_list t (map free_item_of_ptr lp) stso, sthr')).
    eapply (taustar_ne_taustep _ _ TAU').
    intro E. injection E. intros E1 E2. 
    apply (f_equal (fun b => length (tso_buffers b t))) in E2.
    rewrite buffer_insert_list_s, app_length in E2.
    destruct lp; [done | simpl in E2; omega].
  end_assert WS.
  assert (SAF' := scratch_allocs_fresh_free _ _ lp t SAF).

  assert (SCRb: forall bi, In bi (map free_item_of_ptr lp) -> 
                           is_item_scratch_update bi).
    by intros bi IN; apply in_map_iff in IN; destruct IN as [px [<- INpx]];
      simpl; apply LPSP.

  assert (PUBf := part_update_buffer_free spt PERM); unfold arange in PUBf.
  
  (* ... but we need to differentiate between an empty and non-empty buffers. *)
  destruct (rev (bp t)) as [|hbpt tbpt] _eqn : Erbt.
    (* Buffer is empty, so we need to unbuffer the newly inserted allocations. *)
    pose proof (rev_nil (sym_eq Erbt)) as Erbnil.
    assert (Esbnil: tso_buffers stso t = nil). by rewrite BPD, Erbnil.
    rewrite Esbnil in ABs, PUBs. inv ABs.
    injection PUBs; intro Espt. 
    assert (Etbnil : tso_buffers ttso t = nil).
      pose proof (buffered_states_related_length_eq _ _ _ _ 
        (proj1 (proj2 (TREL t)))) as Elbuffs.
      rewrite Erbnil in Elbuffs. by destruct (tso_buffers ttso t).
    end_assert Etbnil.
    rewrite Etbnil in PUBt; inv PUBt.
    exploit TSO.unbuffer_to_tso_state.
        pose proof (buffer_insert_list_s t (map free_item_of_ptr lp) stso)
          as Ebuf. rewrite app_nil_end in Ebuf. by apply Ebuf.
      rewrite Esbnil. rewrite buffer_insert_list_m. simpl; apply ABf.
    intros [stso' (TAU & BUFt & BUFother & MEMntso')].
    assert (WSb : taustep cshm_lts (stso, sthr) Etau (stso', sthr')).
      eapply tausteptau_taustar_taustep. edone.
      eby eapply TSO.apply_buffer_reachable_taustar.
    end_assert WSb.
    subst sm''.
    eexists. split. apply WSb.
    (* And establish the simulation relation *)
    split.
      (* tso consistency of target *)
      eby eapply Comp.thread_update_preserves_consistency.
    exists (tupdate t nil bp). exists tp. 
    exists (update_partitioning t spt sp).
    assert(TCs' : Comp.consistent tso_mm cs_sem (stso', sthr')).
      eby eapply Comp.taustep_preserves_consistency. 
    split; simpl. (* machine buffers *)
      intro t'.
      destruct (peq t' t) as [-> | N]. by rewrite BUFt.
      rewrite BUFother; [|done];
        rewrite buffer_insert_list_o; [apply MTB | ]; done.
    split. (* non-stack memory consistent *)
      eapply non_stack_mem_rel_preserved_by_stack_or_write_buffer; try edone.
      intros bi IN. apply in_map_iff in IN. by destruct IN as [px [<- INpx]].
    split. (* memory contents related *)
      (* mem_content_related preservation *)
      split. done.
      split.
        eby erewrite mem_consistent_with_restr_apply_buffer; [apply MCRs|].
      (* Load value relation *)
      split. 
        eby eapply apply_scratch_buffer_preserves_load_rel.
      (* Memory contents are machine values *)
      eapply apply_machine_buffer_preserves_machine_memory; [|apply ABf|done].
      apply machine_buffer_free_items.
    split. apply TCs'. (* tso consistency for source *)
    split. (* buffer partitioning *)
      intro t'.
      destruct (peq t' t) as [-> | N].
        by rewrite BUFt, tupdate_s.
      rewrite BUFother; [|done]; 
        by rewrite buffer_insert_list_o, tupdate_o, BPD.
    split. (* buffer partitions non-empty *)
      intros t' bi IN.
      destruct (peq t' t) as [-> | N].
        by rewrite tupdate_s in IN.
      rewrite tupdate_o in IN. eby eapply BNE. done.
    split. (* Scratch allocation freshness *)
      eapply scratch_allocs_fresh_apply_buffer. eby rewrite Espt. 
      3 : apply SAF'. 
      by rewrite BUFt, <-app_nil_end, buffer_insert_list_s, Esbnil.
      by intros ? ?; rewrite BUFother.
    split. done. (* Target memory consistent with partitioning *)
    split. (* Source memory consistent with partitioning *)
      eapply apply_buffer_preserves_mem_partitioning; try edone;
        eby rewrite Espt.
    intros t'.
    destruct (TREL t') as (PI & BR & BSR).
    split. (* Partitions injective *)
      unfold update_partitioning.
      destruct (peq t' t) as [-> | N].
        by eapply update_part_buffer_scratch_preserves_partition_injectivity;
          try edone; rewrite Espt in PI.
      done.
    split. (* Buffers related *)
      destruct (peq t' t) as [-> | N].
        rewrite !@tupdate_s, Etbnil. constructor.
      by rewrite !@tupdate_o, update_partitioning_o.
    simpl in *. 
    (* Buffered states related *)
    destruct (peq t' t) as [-> | N].
      (* The allocating thread: *)
      rewrite !@tupdate_s, !@PTree.gss, update_partitioning_s, Etbnil, CS'; simpl.
      eexists. eexists. eexists.
      repeat (split; [done|]); by split; [apply NSR|].
    (* Other threads - we must show that the unbuffering does not affect 
       the other threads. *)
    rewrite tupdate_o, update_partitioning_o, !@PTree.gso, OS'; try done; [].
    destruct (sthr ! t') as [sst|]; destruct (tthr ! t') as [tst|]; 
      simpl in BSR; try done; simpl; [].
    pose proof MRPs as X; destruct X as [PDx [RLDx RLAx]].
    fold arange in PUBf. rewrite <- Espt in PUBf.
    destruct (apply_buffer_preserves_mem_partitioning _ _ _ _ _ _ 
      MRPs ABf PUBf) as [PR' [RLD' RLA']]. 
    apply buffered_states_related_load_inv with (smem := tso_mem stso);
      try done.
          intros r IN. apply (RLAx r). eby eexists.
        intros r IN. apply (RLA' r). exists t'.
        rewrite update_partitioning_o. done. done.
      eapply unbuffer_safe_to_buffer_safe_for_mem; try edone.
        by destruct SC. rewrite <- app_nil_end. apply BPD.
      eapply unbuffer_safe_to_buffer_safe_for_mem; try edone. 
        by destruct TCs'.
      rewrite <- app_nil_end.
      rewrite BUFother. by rewrite buffer_insert_list_o, BPD.
      done.
    eby eapply unbuffering_other_buffer_agrees_on_scratch.

  (* Buffer is not empty  => just append the frees to the buffer *)
  pose proof (rev_cons (sym_eq Erbt)) as Erbpt.

  assert (BRt : buffers_related
     (tso_buffers ttso t)
     (tp t) (append_items_to_bpart (map free_item_of_ptr lp) (bp t)) (sp t)).
    destruct (TREL t) as (PIt' & BRt' & _).
    eapply buffers_related_append_scratch_ne; try edone.
    eapply unbuffer_safe_prefix_buffer_machine; try edone. by destruct TC.
    rewrite <- BPD. apply PUBs.
    by rewrite Erbt.
  end_assert BRt.
                             
  eexists (_, _).
  split. apply WS.
  (* Finally, establish the simulation relation *)
  split. (* tso consistency of target *)
    eby eapply Comp.thread_update_preserves_consistency.
  exists (tupdate t (append_items_to_bpart  (map free_item_of_ptr lp) 
                                            (bp t)) bp).
  exists tp. exists sp.
  split; simpl; rewrite ?buffer_insert_list_m. 
    (* machine buffers *)
    intro t'.
    destruct (peq t' t) as [-> | N].
      rewrite buffer_insert_list_s.
      intros bi IN. apply in_app_or in IN.
      destruct IN. eby eapply MTB.
      eby eapply machine_buffer_free_items.
    rewrite buffer_insert_list_o; [apply MTB | ]; done.
  split. done. (* non-stack memory consistent *)
  split. done. (* memory contents related *)
  split. (* tso consistency for source *)
    eapply Comp.taustep_preserves_consistency.
    apply WS. done. 
  split. (* buffer partitioning *)
    intro t'.
    destruct (peq t' t) as [-> | N].
      rewrite buffer_insert_list_s, tupdate_s.
      by rewrite append_scratch_to_part_flatten, BPD.
    by rewrite buffer_insert_list_o, tupdate_o, BPD.
  split. (* buffer partitions non-empty *)
    intros t' bi IN.
    destruct (peq t' t) as [-> | N].
      rewrite tupdate_s in IN.
      unfold append_items_to_bpart in IN.
      rewrite Erbt in IN.
      apply in_app_or in IN. 
      destruct IN as [IN | [<- | IM]].
          apply (BNE t). rewrite Erbpt. apply in_or_app. by left.
        intro A. destruct (app_eq_nil _ _ A) as [Hnil _].
        revert Hnil. apply (BNE t). rewrite Erbpt. apply in_or_app. 
      by right; left. done.
    rewrite tupdate_o in IN. eby eapply BNE. done.
  split. done. (* Scratch allocation freshness *)
  split. done. (* Target memory consistent with partitioning *)
  split. done. (* Source memory consistent with partitioning *)
  intros t'.
  destruct (TREL t') as (PI & BR & BSR).
  split. done. (* Partitions injective *)
  split. (* Buffers related *)
    destruct (peq t' t) as [-> | N].
      rewrite !@tupdate_s. done.
    by rewrite !@tupdate_o. 
  (* Buffered states related *)
  simpl in *.
  destruct (peq t' t) as [-> | N].
    rewrite !@tupdate_s, !@PTree.gss, CS', 
      append_scratch_to_part_flatten, <- BPD.
    simpl.
    eexists. eexists. eexists.
    split. eby rewrite apply_buffer_app, ABs.
    split. edone.
    split. 
      unfold part_update_buffer in *; rewrite fold_left_opt_app, PUBs.
      apply PUBf.
    split. by apply NSR. done.
  by rewrite !@tupdate_o, !@PTree.gso, OS'.
Qed.

Lemma find_funct_ptr_eq:
  forall p,
    Genv.find_funct_ptr (ge csm_globenv) p = 
    Genv.find_funct_ptr (Cstacked.ge cst_globenv) p.
Proof.
  intros p.
  destruct globenv_same as ((_ & FE) & _). 
  specialize (FE p).
  by repeat destruct Genv.find_funct_ptr; subst.
Qed.

Lemma find_funct_eq:
  forall vf,
    Genv.find_funct (ge csm_globenv) vf = 
    Genv.find_funct (Cstacked.ge cst_globenv) vf.
Proof.
  intros vf.
  destruct vf; try done; [].
  unfold Genv.find_funct. apply find_funct_ptr_eq.
Qed.

Lemma thread_tau_sim:
  forall s s' (st : PTree.t Cstacked.state) t sms tso
  (TS : cst_step cst_globenv s TEtau s')
  (CS : st ! t = Some s)
  (TSOPCREL : tso_pc_related (tso, st) sms),
   can_reach_error csm_globenv sms \/
   (exists shms' : St cshm_lts,
      taustep cshm_lts sms Etau shms' /\ 
      tso_pc_related (tso, st ! t <- s') shms') \/
   tso_pc_related (tso, st ! t <- s') sms /\
   (measure s' < measure s) % nat.
Proof.
  intros. destruct sms as [cstso csst].
  generalize TSOPCREL; intros [TC [bp [tp [sp TRELW]]]].
  pose proof (tso_pc_related_to_buff_states _ _ _ _ _ _ _ t TRELW) as BOR.
  pose proof TRELW as (MTB & NSMR & (MCRt & MCRs & LR & MCM) & SC &
    BPD & BNE & SAF & MRPt & MRPs & TREL). simpl in *.
  rewrite CS in BOR.
  destruct (csst ! t) as [ss'|] _eqn : Ess'; simpl in BOR; try done.
  destruct BOR as [sm' [sp' [tp' (AB & PUBt & PUBs & SR & SCO)]]].

  pose proof (step_consistent_with_env TS SCO) as SCO'.

  remember TEtau as xtau in TS.

  revert SR CS Heqxtau SCO'.
  

  assert(TPMP: forall p n, In (p, n) tp' -> machine_ptr p).
    pose proof (no_unbuffer_errors _ t (proj2 TC)) as NUE.
    simpl in NUE.
    destruct(apply_buffer (tso_buffers tso t) (tso_mem tso)) as [tm'|] _eqn:ABt;
      [|done].
    pose proof (apply_buffer_preserves_mem_partitioning _ _ _ _ _ _ 
      MRPt ABt PUBt) as MRPt'.
    intros p' n' IN'.
    assert (RA: range_allocated (p', n') MObjStack tm').
      apply -> (proj2 (proj2 MRPt')). 
      exists t. by rewrite update_partitioning_s.
    apply range_allocated_consistent_with_restr in RA.
    rewrite (mem_consistent_with_restr_apply_buffer _ _ _ ABt) in RA.
    simpl in MCRt; rewrite MCRt in RA. by destruct p'.

  (cst_step_cases (case TS) Case); intros; try done; 
    try (abstract by right; left; inv SR; eexists (_, _); (split; [
         eby apply step_taustep; simpl; 
            eapply Comp.step_tau; try apply Ess'; try econstructor |
         eapply memory_neutral_sim; try edone; intros tpt spt smt SR;
            inv SR; econstructor; try edone; eby econstructor]));
    try (abstract by right; left; inv SR; inv EKR; eexists (_, _); split;
      [eby apply step_taustep; simpl; 
        eapply Comp.step_tau; try apply Ess'; vauto |
       eapply memory_neutral_sim; try edone; intros tpt spt smt SR;
         inv SR; inv EKR; econstructor; try edone; eby econstructor]).

  Case "StepVarLocal".
    inv SR. inv EVL. 
    destruct ER as [n (BP & RLD & PERM & EIR)].
    pose proof (EIR id) as EIRid. rewrite EG in EIRid.
    destruct (csm_e ! id) as [csmei|] _eqn : Ecsmei; [|done].
    inv EIRid.
    right; left. eexists (_, _).
    split. 
      apply step_taustep. simpl.
      eapply Comp.step_ord; try edone.
        eby eapply Csharpminor.StepVar;
          [eapply eval_var_ref_local|].
      eby econstructor.
    eapply memory_neutral_sim; try edone.
    intros tpt spt smt SR.
    inv SR. econstructor; try edone.
    pose proof (apply_machine_buffer_preserves_machine_memory _ _ _ 
      (MTB t) AB MCM p c) as MV; rewrite LV in MV.
    done.

  Case "StepAddrOf".
    right; left. inv SR.
    assert(TPMP': forall p n, In (p, n) cst_obs' -> machine_ptr p).
      intros p' n' IN'. eapply TPMP. eby apply in_or_app; left.
    destruct (eval_var_addr_machine _ _ _ _ _ _ _ ER TPMP' EVA)
      as (EVAs & MP).
    eexists (_, _). split. apply step_taustep. simpl.
      eapply Comp.step_tau; [econstructor|apply Ess'|]; edone.
    eapply memory_neutral_sim; try edone.
    intros tpt spt smt SR.
    inv SR. econstructor; try edone.

  Case "StepConst".
    right; left; inv SR; eexists (_, _); split.
      eby apply step_taustep; simpl; 
         eapply Comp.step_tau; try apply Ess'; try econstructor.
    eapply memory_neutral_sim; try edone; intros tpt spt smt SR;
      inv SR; econstructor; try done; destruct cst; simpl in EC; clarify.
  
  Case "StepUnop".
    right; left; inv SR; inv EKR; eexists (_, _); split.
      eby apply step_taustep; simpl; 
         eapply Comp.step_tau; try apply Ess'; try econstructor.
    eapply memory_neutral_sim; try edone; intros tpt spt smt SR;
      inv SR; inv EKR; econstructor; try edone; eby eapply machine_val_unop.

  Case "StepBinop".
    right; left; inv SR; inv EKR; eexists (_, _); split.
      eby apply step_taustep; simpl; 
         eapply Comp.step_tau; try apply Ess'; try econstructor.
    eapply memory_neutral_sim; try edone; intros tpt spt smt SR;
      inv SR; inv EKR;  econstructor; try edone;
        eby eapply machine_val_binop.

  Case "StepAssignLocal".
    inv SR. inv EKR. inversion VLS. subst.
    destruct ER as [n (BP & RLD & PERM & EIR)].
    specialize (EIR id). rewrite EG in EIR.
    destruct (csm_e ! id) as [vid|] _eqn : Evid; [|done].
    inv EIR.
    exploit tau_write_sim_rel; try edone. 
        eby econstructor.
      econstructor; eby eapply eval_var_ref_local. 
    eby intros [CRO | [[stso' [WS TR]] | M]]; 
      [left | right; left; eexists; split| right; right]. 

  Case "StepEmptyCall".
    right; left; inv SR; inv EKR; eexists (_, _); split.
      eby apply step_taustep; simpl; 
         eapply Comp.step_tau; try apply Ess'; try eapply StepEmptyCall;
           try edone; rewrite find_funct_eq. 
    clear EK; clear ER.
    eapply memory_neutral_sim; try edone; intros tpt spt smt SR;
      inv SR; inv EKR;  econstructor; try edone; econstructor; try edone.
    destruct vf; try done.
    eby eexists.

(*  Case "StepCallArgs1".
    right; inv SR; inv EKR; exists (_, _); split.
      eby apply step_weakstep; simpl; 
         eapply Comp.step_tau; try apply Ess'; try eapply StepCallArgs1.
    eapply memory_neutral_sim; try edone; intros tpt spt smt SR;
      inv SR; inv EKR;  econstructor; try edone; econstructor; try edone.
    destruct vf; try done.
    eby eapply globenv_fn_in. *)
    
  Case "StepCallArgs2".
    right; left; inv SR; inv EKR; eexists (_, _); split.
      eby apply step_taustep; simpl; 
         eapply Comp.step_tau; try apply Ess'; try eapply StepCallArgs2.
    eapply memory_neutral_sim; try edone; intros tpt spt smt SR;
      inv SR; inv EKR;  econstructor; try edone; econstructor; try edone.
    intros v' IN'. apply in_app_or in IN'. 
    destruct IN' as [IN' | IN']. eby eapply MVL.
    by destruct IN' as [<- | IN'].

  Case "StepCallArgs".
    right; left; inv SR; inv EKR; eexists (_, _); split.
      eby apply step_taustep; simpl; 
         eapply Comp.step_tau; try apply Ess'; try eapply StepCallArgs; 
           try edone; rewrite find_funct_eq.
    eapply memory_neutral_sim; try edone; intros tpt spt smt SR;
      inv SR; inv EKR; eapply st_rel_call; try edone; try econstructor; 
        try edone.
    destruct vf; try done.
    eby eexists.
    intros v' IN'. apply in_app_or in IN'. 
    destruct IN' as [IN' | IN']. eby eapply MVL.
    by destruct IN' as [<- | IN'].

  Case "StepAtomicArgs".
    right; left; inv SR; inv EKR; eexists (_, _); split.
      eby apply step_taustep; simpl; 
         eapply Comp.step_tau; try apply Ess'; try eapply StepAtomicArgs; 
           try edone; rewrite find_funct_eq.
    eapply memory_neutral_sim; try edone; intros tpt spt smt SR;
      inv SR; inv EKR; econstructor; try edone; try econstructor; 
        try edone.
    intros v' IN'. apply in_app_or in IN'. 
    destruct IN' as [IN' | IN']. eby eapply MVL.
    by destruct IN' as [<- | IN'].

  Case "StepGoto".
    right; left; inv SR.
    pose proof (find_label_related lbl (fn_body f) (call_cont_related _ EKR)) 
       as FR.  
    rewrite FL in FR.
    destruct FR as [smk (FLs & KRs)].
    rewrite (get_fundef_related (call_cont_related _ EKR)) in GFD.
    unfold get_fundef in GFD.
    destruct (call_cont csm_k) as [] _eqn : CC; try done; []. inv GFD.
    eexists (_, _); split.
      apply step_taustep; simpl; 
        eapply Comp.step_tau; try apply Ess'; try eapply StepGoto; try edone.
      eby rewrite CC.
    eapply memory_neutral_sim; try edone; intros tpt spt smt SR;
      inv SR; econstructor; try edone. 
    pose proof (find_label_related lbl (fn_body f) (call_cont_related _ EKR0)) 
       as FR0.  
    rewrite FL in FR0.
    destruct FR0 as [smk0 (FLs0 & KRs0)].
    rewrite CC in FLs0. rewrite FLs in FLs0. clarify.
    
  Case "StepReturnNone".
    right; left; inv SR.
    pose proof (call_cont_related _ EKR) as CCR. rewrite CC in CCR.
    assert (CCRsm : exists csm_e', exists csm_k',
      call_cont csm_k = Kcall None (Internal f) csm_e' csm_k').
      inv CCR; eby eexists; eexists.
    destruct CCRsm as [csm_e' [csm_k' CCs]].
    eexists (_, _); split.
      eby apply step_taustep; simpl; 
        eapply Comp.step_tau; try apply Ess'; try eapply StepReturnNone; 
          try edone; apply sym_eq.
    eapply memory_neutral_sim; try edone; intros tpt spt smt SR;
      inv SR. 
    pose proof ER0 as [n (BPTR & RLD & PERM & EIR)].
    eapply st_rel_free; try edone.
      eby eapply related_env_partitions_injective.
      by destruct (csenv_sp env) as [p|] _eqn : Ep;
        [destruct BPTR as (_ & -> & NE); split | destruct BPTR as (_ & ->)].
      eapply Permutation_trans, env_ranges_perm_sorted_pointers;
        by apply Permutation_map.

  Case "StepReturnNoFree".
    inv SR.
    eapply tau_free_sim; try edone.
    - eby econstructor.
    - apply kfree_free_steps.
    - intros p' IN'.
      apply (Permutation_in _ (Permutation_sym P)), in_map_iff in IN'.
      destruct IN' as [[pr n'] [E IN']]. simpl in E. subst.
      destruct (machine_or_scratch p') as [MP | ?]; [|done].
      by destruct (PI p' n' MP IN') as [? [? ?]].
    - intros sm'' AB''. simpl. econstructor; [|done].
      eapply cont_related_load_inv; try edone; [].
      eapply frees_mem_agrees_on_scratch. edone. 
      exploit (apply_buffer_preserves_mem_partitioning 
        (tso_buffers cstso t ++ map free_item_of_ptr lp)
        _ sm'' _ csm_obs t MRPs).
        by rewrite apply_buffer_app, AB.
        unfold part_update_buffer in *; rewrite fold_left_opt_app, PUBs.
        simpl. by fold part_update_buffer; rewrite part_update_buffer_free.
      intros (_ & _ & MR) r IN.
      eapply MR. exists t. by rewrite update_partitioning_s.

  Case "StepReturnNoneFinish".
    right; left; inv SR. 
    pose proof (call_cont_related _ KR) as CCR. rewrite CC in CCR.
    assert (CCRsm : exists csm_e', exists csm_k',
      call_cont csm_k = Kcall None fd csm_e' csm_k').
      inv CCR; eby eexists; eexists.
    destruct CCRsm as [csm_e' [csm_k' CCs]].
    rewrite CCs in CCR.
    eexists (_, _); split.
      eby apply step_taustep; simpl; 
         eapply Comp.step_tau; try apply Ess'; try eapply StepReturnNoneFinish.
    eapply memory_neutral_sim; try edone; intros tpt spt smt SR;
      inv SR. 
    pose proof (call_cont_related _ KR0) as CCR0. rewrite CC in CCR0.
    rewrite CCs in CCR0. inv CCR0. econstructor.
    eby econstructor. 

  Case "StepReturnSome".
    right; left; inv SR.
    pose proof (call_cont_related _ EKR) as CCR.
    assert (CCRsm : get_fundef (call_cont csm_k) = Some (Internal f)).
      by destruct (Cstacked.call_cont k) as [] _eqn : CK; inv CC; inv CCR.
    eexists (_, _); split.
      eby apply step_taustep; simpl; 
        eapply Comp.step_tau; try apply Ess'; try eapply StepReturnSome; 
          try edone; apply sym_eq. 
    eapply memory_neutral_sim; try edone; intros tpt spt smt SR;
      inv SR.
    econstructor; try edone; econstructor; try edone.

  Case "StepReturnSome1".
    right; left; inv SR; inv EKR.
    eexists (_, _); split.
      eby apply step_taustep; simpl; 
        eapply Comp.step_tau; try apply Ess'; try eapply StepReturnSome1.
    eapply memory_neutral_sim; try edone; intros tpt spt smt SR;
      inv SR; inv EKR.
    pose proof ER0 as [n (BPTR & RLD & PERM & EIR)].
    eapply st_rel_free; try edone.
      eby eapply related_env_partitions_injective.
    by destruct (csenv_sp env); 
      [destruct BPTR as (_ & -> & NE); split | destruct BPTR as (_ & ->)]; 
      try edone; destruct csm_obs'0.
    eapply Permutation_trans, env_ranges_perm_sorted_pointers.
      eapply Permutation_map. edone.

  Case "StepReturnFinishLocal".
    inv SR.
    inversion VLS. subst.
    pose proof (call_cont_related _ KR) as CCR. 
    rewrite CC in CCR. inv CCR.
    destruct ER as [n (BP & RLD & PERM & EIR)].
    specialize (EIR id). rewrite EG in EIR.
    destruct (csm_e0 ! id) as [vid|] _eqn : Evid; [|done].
    inv EIR.
    exploit tau_write_sim_rel; try edone. 
        eby eapply StepReturnFinishLocal.
      econstructor. apply sym_eq. edone. 
      eby eapply eval_var_ref_local. 
    eby intros [CRO | [[stso' [WS TR]] | M]]; 
      [left | right; left; eexists; split| right; right].

  Case "StepFunctionInternalNoStack".
    right; left; inv SR.
    eapply thread_tau_alloc; try edone.

  Case "StepBindArgsEnv".
    inv SR.
    inversion VLS. subst.
    destruct ER as [n (BP & RLD & PERM & EIR)].
    specialize (EIR id). rewrite EG in EIR.
    destruct (csm_e ! id) as [vid|] _eqn : Evid; [|done].
    inv EIR.
    exploit tau_write_sim_rel; try edone. 
        eby econstructor.
      econstructor. edone.
    eby intros [CRO | [[stso' [WS TR]] | M]];
      [left | right; left; eexists; split| right; right]. 

  Case "StepExternalStoreEnv".
    inv SR. inversion VLS. subst.
    destruct ER as [n (BP & RLD & PERM & EIR)].
    specialize (EIR tgt). rewrite EG in EIR.
    destruct (csm_e ! tgt) as [vid|] _eqn : Evid; [|done].
    inv EIR.
    exploit tau_write_sim_rel; try edone. 
        eby econstructor.
      econstructor; eby eapply eval_var_ref_local. 
    eby intros [CRO | [[stso' [WS TR]] | M]]; 
      [left | right; left; eexists; split| right; right]. 

Qed.

End TAU_SIM.
