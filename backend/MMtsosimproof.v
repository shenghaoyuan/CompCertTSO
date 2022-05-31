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
Require Import Values.
Require Import Mem.
Require Import Memeq.
Require Import Memcomp.
Require Import TSOmachine.
Require Import TSOsimulation.
Require Import Simulations.
Require Import Events.
Require Import Globalenvs.
Require Import Libtactics.
Require Import MMperthreadsimdef.
Require Import MMtsoaux.
Require Import Traces.

Section Localsim.

Variables (Src Tgt : SEM).

(** Let as assume that there is a relation on global environments and
    a simulation relation on states. *)
Variable genv_rel  : Src.(SEM_GE) -> Tgt.(SEM_GE) -> Prop.

(** State relation is parametrized on partitions and target memory, in addition
    to the usual states and global environments. *)
Variable st_rel    : Src.(SEM_GE) -> (**r source global environment *)
                     Tgt.(SEM_GE) -> (**r target global environment *)
                     Tgt.(SEM_ST) -> (**r target state *)
                     list arange  -> (**r target allocation partition *)
                     mem ->          (**r target memory *)
                     Src.(SEM_ST) -> (**r source state *)
                     list arange ->  (**r source partition *)
                     Prop.
(** Measure order (for stuttering) *)
Variable st_order  : Src.(SEM_GE) -> Tgt.(SEM_GE) -> Tgt.(SEM_ST) -> Tgt.(SEM_ST) -> Prop.
(** Program matching (this is really only needed to talk about initialisation) *)
Variable match_prg : Src.(SEM_PRG) -> Tgt.(SEM_PRG) -> Prop.

(** * Usual assumptions *)

(** Related environments have the same main function. *)
Hypothesis main_ptr_eq:
  forall src_prog tgt_prog,
  forall sge tge
    (MP : match_prg src_prog tgt_prog)
    (GENVR: genv_rel sge tge),
    Src.(SEM_find_symbol) sge (Src.(SEM_main_fn_id) src_prog) = 
    Tgt.(SEM_find_symbol) tge (Tgt.(SEM_main_fn_id) tgt_prog).

(** We assume that for any intial global environment of the transformed 
    program there is a related initial env of the source program. *)
Hypothesis ge_init_related : 
  forall src_prog tgt_prog,
  forall tge m
    (MP : match_prg src_prog tgt_prog)
    (INIT: Tgt.(SEM_ge_init) tgt_prog tge m),
    exists sge, Src.(SEM_ge_init) src_prog sge m /\ genv_rel sge tge.

(** Initial memory has only global blocks allocated *)
Hypothesis ge_init_global:
  forall p ge initmem
    (INIT: Tgt.(SEM_ge_init) p ge initmem),
      forall r k, range_allocated r k initmem -> k = MObjGlobal.

(** Suppose that the initial states of threads spawned in related 
   environments are related. *)
Hypothesis thread_init_related:
  forall sge tge tgt_init fnp args args'
    (GENVR : genv_rel sge tge)
    (INIT : Tgt.(SEM_init) tge fnp args = Some tgt_init)
    (LD    : Val.lessdef_list args' args),
    exists src_init,
      Src.(SEM_init) sge fnp args' = Some src_init /\
      forall m, st_rel sge tge tgt_init nil m src_init nil.

(* This is not really needed but it simplifies the proof for now
   (and it should be true for our languages). *)
Hypothesis thread_init_related_none:
  forall sge tge fnp args args'
    (GENVR : genv_rel sge tge)
    (INITF : Tgt.(SEM_init) tge fnp args = None)
    (LD    : Val.lessdef_list args' args),
    Src.(SEM_init) sge fnp args' = None.

(** Per-thread local simulation. *)
Hypothesis sim :
  forall sge tge (GR : genv_rel sge tge),
  local_intro_simulation 
    Src.(SEM_ST) Tgt.(SEM_ST) 
    (Src.(SEM_step) sge) (Tgt.(SEM_step) tge)
    (st_rel sge tge) (st_order sge tge).

(** Per-thread stuckness simulation. *)
Hypothesis stuck_sim :
  forall sge tge (GR : genv_rel sge tge),
  stuck_simulation 
    Src.(SEM_ST) Tgt.(SEM_ST) 
    (Src.(SEM_step) sge) (Tgt.(SEM_step) tge)
    (st_rel sge tge).

(** Per-thread non-interference. *)
Hypothesis load_inv :
  forall sge tge (GR : genv_rel sge tge),
  simulation_local_invariant 
    Src.(SEM_ST) Tgt.(SEM_ST) (st_rel sge tge).

(** Well-foundedness of the stuttering order. *)
Hypothesis wf_order:
  forall sge tge (GR : genv_rel sge tge),
    well_founded (st_order sge tge).

(** * Simulation relation definition *)

Section SIMS.

Variable sge : Src.(SEM_GE).
Variable tge : Tgt.(SEM_GE).

Hypothesis ge_rel: genv_rel sge tge.

Notation stso_lts := (mklts event_labels (Comp.step tso_mm Src sge)).
Notation ttso_lts := (mklts event_labels (Comp.step tso_mm Tgt tge)).
Notation slts := (mklts thread_labels (Src.(SEM_step) sge)).
Notation tlts := (mklts thread_labels (Tgt.(SEM_step) tge)).

(** Relation of thread states after unbuffering. *)
Inductive buffered_states_related
                          (tb : list buffer_item) 
                          (tm : mem)
                          (tp : list arange)
                          (ts : Tgt.(SEM_ST))
                          (sb : list buffer_item)
                          (sp : list arange)
                          (ss : Src.(SEM_ST)) : Prop :=
| buffered_states_related_intro: forall tm' sp' tp'
  (ABt: apply_buffer tb tm = Some tm')
  (PUt: part_update_buffer tb tp = Some tp')
  (PUs: part_update_buffer sb sp = Some sp')
  (SR : st_rel sge tge ts tp' tm' ss sp'),
    buffered_states_related tb tm tp ts sb sp ss .

Definition buffered_ostates_related 
                          (tb : list buffer_item)
                          (tm : mem)
                          (tp : list arange)
                          (ots : option Tgt.(SEM_ST))
                          (sb : list buffer_item)
                          (sp : list arange)
                          (oss : option Src.(SEM_ST)) : Prop :=
  match ots, oss with
    | Some ts, Some ss => 
        buffered_states_related tb tm tp ts sb sp ss 
    | None, None => tp = nil /\ sp = nil /\ tb = nil /\ sb = nil
    | _, _ => False
  end.

Inductive tso_pc_related_witt  (ts : Comp.state tso_mm Tgt)
                               (tp : partitioning)
                               (ss : Comp.state tso_mm Src) 
                               (sp : partitioning)
                                : Prop :=
| tso_pc_related_witt_intro: forall
  (* The tso_states are related *)
  (TREL: tso_related_witt (fst ts) tp (fst ss) sp)
  (* all unbufferings are successful *)
  (TCs : Comp.consistent _ _ ss)
  (TCt : Comp.consistent _ _ ts)
  (* States must are related *)
  (SR  : forall t, 
  buffered_ostates_related 
                           ((fst ts).(tso_buffers) t) ((fst ts).(tso_mem)) (tp t) ((snd ts)!t)
                           ((fst ss).(tso_buffers) t) (sp t) ((snd ss)!t)),
  tso_pc_related_witt ts tp ss sp.

Definition tso_pc_related ts ss :=
  exists tp, exists sp, tso_pc_related_witt ts tp ss sp.

(** * Unbuffering proof *)

Lemma buffered_states_related_prepend_tgt:
  forall bi tb tm' tm tp ts sb sp ss tp'
    (PU : part_update bi tp' = Some tp)
    (ABI: apply_buffer_item bi tm' = Some tm),
    (buffered_states_related tb tm tp ts sb sp ss <->
     buffered_states_related (bi :: tb) tm' tp' ts sb sp ss).
Proof.
  intros.
  split.
    intros []; intros. 
    econstructor; try edone. 
    - eby simpl; rewrite ABI.
    - eby simpl; rewrite PU; simpl; rewrite PUt.
  intros []; intros.
  econstructor; try edone.
  by simpl in ABt; rewrite ABI in ABt.
  by simpl in PUt; rewrite PU in PUt.
Qed.

Lemma buffered_states_related_prepend_src:
  forall bi tb tm tp ts sb sp ss sp',
    part_update bi sp' = Some sp ->
    (buffered_states_related tb tm tp ts sb sp ss <->
     buffered_states_related tb tm tp ts (bi :: sb) sp' ss).
Proof.
  intros bi tb tm tp ts sb sp ss sp' PU.
  split; intros []; intros.
    econstructor; try edone.
    by simpl; rewrite PU.
  econstructor; try edone.
  by simpl in PUs; rewrite PU in PUs.
Qed.

Hint Resolve range_list_allocated_irrelevant : biir.

Lemma buffered_states_related_load_inv_gen:
  forall tb tp ts sb sp ss tm tm'
    (RLD : range_list_disjoint sp)
    (RLDt : range_list_disjoint tp)
    (RLA : range_list_allocated tp tm)
    (RLA': range_list_allocated tp tm')
    (*BS  : buffer_safe_for_mem tb tm*)
    (BS' : buffer_safe_for_mem tb tm')
    (MA  : mem_agrees_on_local tm tm' tp (remove_frees_from_part sp sb))
    (BR  : buffers_related tb tp sb sp)
    (SBR : buffered_states_related tb tm tp ts sb sp ss),
      buffered_states_related tb tm' tp ts sb sp ss.
Proof.
  intros.
  revert tm tm' BS' MA RLA RLA' SBR RLD RLDt.
  (buffers_related_cases (induction BR) Case); intros; inversion SBR; subst.

  Case "buffers_related_empty".
    econstructor; try edone.
    inv PUt; inv PUs; inv ABt.
    eby eapply load_inv. 

  Case "buffers_related_irrelevant".
    simpl in PUs, PUt. rewrite !(part_update_irrelevant BIIR) in *.
    simpl in PUs, PUt.
    destruct BS' as [tmf' ABt'].
    destruct (apply_buffer_consD ABt) as [tmi (ABI & ABti)].
    destruct (apply_buffer_consD ABt') as [tmi' (ABI' & ABti')].
    apply -> buffered_states_related_prepend_tgt; try edone.
    apply -> buffered_states_related_prepend_src; try edone.
    apply (IHBR tmi tmi'); eauto with biir; vauto.
    - eapply mem_agrees_on_local_preserved_by_irrelevant; try edone.
      eby eapply mem_agrees_on_local_unbuffer.
    - by rewrite (part_update_irrelevant BIIR).
    - by rewrite (part_update_irrelevant BIIR).

  Case "buffers_related_write".
    simpl in PUs, PUt. destruct BS' as [tmf' ABt'].
    destruct (apply_buffer_consD ABt) as [tmi (ABI & ABti)].
    destruct (apply_buffer_consD ABt') as [tmi' (ABI' & ABti')].
    apply -> buffered_states_related_prepend_tgt; try edone.
    apply -> buffered_states_related_prepend_src; try edone.
    apply (IHBR tmi tmi'); eauto using range_list_allocated_write; vauto.
    - eby eapply mem_agrees_on_local_preserved_by_write.

  Case "buffers_related_local_write".
    simpl in PUt. destruct BS' as [tmf' ABt'].
    destruct (apply_buffer_consD ABt) as [tmi (ABI & ABti)].
    destruct (apply_buffer_consD ABt') as [tmi' (ABI' & ABti')].
    apply -> buffered_states_related_prepend_tgt; try edone.
    apply (IHBR tmi tmi'); eauto using range_list_allocated_write; vauto.
    - eby eapply mem_agrees_on_local_preserved_by_write.

  Case "buffers_related_salloc".
    assert (PU: part_update (BufferedAlloc p n MObjStack) sp = Some ((p, n) :: sp)).
      simpl. destruct valid_alloc_range_dec; [|done].
      destruct range_in_dec as [[r' [IN RO]]|RI].
        by specialize (RNIN r' IN).
      done.
    simpl in *. rewrite PU in PUs. simpl in PUs.
    apply -> buffered_states_related_prepend_src; try edone.
    apply (IHBR tm tm'); try edone; vauto.
    eapply mem_agrees_on_local_mono_sp; [|edone].
    intros [p' n'] IN'. apply -> in_rfree_part in IN'.
    apply <- in_rfree_part. split. simpl; right; tauto. tauto.

  Case "buffers_related_sfree".
    assert (PU: part_update (BufferedFree p MObjStack) ((p, n) :: sp) = Some sp)
      by (by simpl; destruct Ptr.eq_dec).
    simpl in *. rewrite PU in PUs. simpl in PUs.
    apply -> buffered_states_related_prepend_src; try edone.
    apply (IHBR tm tm'); try edone; vauto.
    eapply mem_agrees_on_local_preserved_by_sfree; [|edone]; tauto.
    tauto.

  Case "buffers_related_talloc".
    assert (PU: part_update (BufferedAlloc p n MObjStack) tp = Some ((p, n) :: tp)).
      simpl. destruct valid_alloc_range_dec; [|done].
      destruct range_in_dec as [[r' [IN RO]]|RI].
        by specialize (RNIN r' IN).
      done.
    simpl in PU, PUt. rewrite PU in PUt. simpl in PUt.
    destruct BS' as [tmf' ABt'].
    destruct (apply_buffer_consD ABt) as [tmi (ABI & ABti)].
    destruct (apply_buffer_consD ABt') as [tmi' (ABI' & ABti')].
    apply -> buffered_states_related_prepend_tgt; try edone.
    apply (IHBR tmi tmi'); try edone; vauto.
    - eby eapply mem_agrees_on_local_preserved_by_talloc.
    - eby eapply range_list_allocated_part_alloc. 
    - eby eapply range_list_allocated_part_alloc. 

  Case "buffers_related_tfree".
    assert (PU: part_update (BufferedFree p MObjStack) ((p, n)::tp) = Some tp)
      by (by simpl; destruct Ptr.eq_dec).
    simpl in PU, PUt. rewrite PU in PUt. simpl in PUt.
    destruct BS' as [tmf' ABt'].
    destruct (apply_buffer_consD ABt) as [tmi (ABI & ABti)].
    destruct (apply_buffer_consD ABt') as [tmi' (ABI' & ABti')].
    apply -> buffered_states_related_prepend_tgt; try edone.
    destruct RLDt.
    apply (IHBR tmi tmi'); try edone; vauto.
    - eapply mem_agrees_on_local_preserved_by_tfree; try edone.
      by apply RLA; left.
      by apply RLA'; left.
    - eby eapply range_list_allocated_part_free.
    - eby eapply range_list_allocated_part_free.
Qed.


(*
Lemma unbuffering_other_item_agrees_on_local:
  forall t t' sm tm tm' sp tp
    (NE:   t' <> t)
    (MRPt: mem_related_with_partitioning tm tp)
    (MRPs: mem_related_with_partitioning sm sp)
    (ABI:  apply_buffer_item bi tm = Some tm')
    (PU:   part_update bi (tp t) = Some part'),
    mem_agrees_on_local tm tm' (tp t') (sp t').
Proof.
  intros bi m m' part part' t t' Nt [PD [RLD MR]] ABI PU.
  intros r p c IN RI SCR.
  unfold part_update in PU.
  unfold apply_buffer_item in ABI.
  buffer_item_cases (destruct bi as [pi ci vi | pi ni ki | pi ki]) Case.

  Case "BufferedWrite".
    rewrite (load_store_other ABI). done.
    destruct (low_mem_restr (Ptr.block pi)) as [] _eqn : LMR.
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
      destruct (low_mem_restr (Ptr.block pi)) as [] _eqn : LMR; try done;
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
      destruct (low_mem_restr (Ptr.block pi)) as [] _eqn : LMR; try done;
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
*)

Lemma mrwp_rla:
  forall m part t
    (MRWP: mem_related_with_partitioning m part),
      range_list_allocated (part t) m.
Proof.
  intros; intros r IN; eby eapply mrwp_in_alloc.
Qed.

Lemma mrwp_rld:
  forall m part t
    (MRWP: mem_related_with_partitioning m part),
      range_list_disjoint (part t).
Proof.
  intros. destruct MRWP as (_ & ? & _); eauto.
Qed.

Lemma unbuffer_safe_to_buffer_safe_for_mem2:
  forall stso t,
    unbuffer_safe stso ->
      buffer_safe_for_mem (tso_buffers stso t) (tso_mem stso).
Proof.
  intros.
  eapply unbuffer_safe_to_buffer_safe_for_mem with (t := t)(rb := nil).
    done.  
  by rewrite <- app_nil_end.
Qed.  

Hint Resolve mrwp_rla mrwp_rld 
  buffer_safe_for_mem_cons 
  unbuffer_safe_to_buffer_safe_for_mem2 : mrwp.

Lemma irrelevant_preserves_tso_pc_related_witt:
  forall ts tt tp ss st sp t btrest bsrest tm' sm' bi
    (REL:  tso_pc_related_witt (ts, tt) tp (ss, st) sp)
    (BIIR: buffer_item_irrelevant bi)
    (ABIt: apply_buffer_item bi ts.(tso_mem) = Some tm')
    (ABIs: apply_buffer_item bi ss.(tso_mem) = Some sm')
    (Bt:   ts.(tso_buffers) t = bi :: btrest)
    (Bs:   ss.(tso_buffers) t = bi :: bsrest)
    (BRr:  buffers_related btrest (tp t) bsrest (sp t)),
      tso_pc_related_witt 
        (mktsostate (tupdate t btrest ts.(tso_buffers)) tm', tt) tp
        (mktsostate (tupdate t bsrest ss.(tso_buffers)) sm', st) sp.
Proof.        
  intros. inv REL.
  assert (TCt': Comp.consistent tso_mm Tgt
     (mktsostate (tupdate t btrest (tso_buffers ts)) tm', tt)).
    by eapply Comp.step_preserves_consistency with (ge := tge); 
      [|edone]; vauto.
  constructor.
  - eby eapply irrelevant_preserves_tso_related_witt.
  - by eapply Comp.step_preserves_consistency with (ge := sge); vauto.
  - done. 
  - intros t'. specialize (SR t'). simpl in SR |- *.
    unfold tupdate; destruct (peq t' t) as [<- | N].  
      (* The unbuffering thread *)
      rewrite Bt, Bs in SR. 
      destruct (tt ! t'); destruct (st ! t'); try edone; simpl in SR |- *.
        apply <- buffered_states_related_prepend_tgt.
        apply <- buffered_states_related_prepend_src. edone.
        by rewrite part_update_irrelevant. done.
        by rewrite part_update_irrelevant.
      by destruct SR as (_ & _ & ? & _).
    (* Other threads *)
    destruct (tt ! t'); destruct (st ! t'); try edone; simpl in SR |- *.
    inversion TREL; subst; simpl in *.
    eapply buffered_states_related_load_inv_gen; 
      eauto using irrelevant_preserves_mem_partitioning with mrwp.
      pose proof(unbuffer_safe_to_buffer_safe_for_mem2 _ t' (proj2 TCt')) 
        as BSM.
      simpl in BSM. by rewrite tupdate_o in BSM.
    eby eapply irrelevant_agrees_on_local.
Qed.

Lemma write_preserves_tso_pc_related_witt:
  forall ts tt tp ss st sp t btrest bsrest tm' sm' p c v v'
    (REL:  tso_pc_related_witt (ts, tt) tp (ss, st) sp)
    (ABIt: apply_buffer_item (BufferedWrite p c v) ts.(tso_mem) = Some tm')
    (ABIs: apply_buffer_item (BufferedWrite p c v') ss.(tso_mem) = Some sm')
    (LD:   Val.lessdef v' v)
    (Bt:   ts.(tso_buffers) t = BufferedWrite p c v :: btrest)
    (Bs:   ss.(tso_buffers) t = BufferedWrite p c v' :: bsrest)
    (BRr:  buffers_related btrest (tp t) bsrest (sp t)),
      tso_pc_related_witt 
        (mktsostate (tupdate t btrest ts.(tso_buffers)) tm', tt) tp
        (mktsostate (tupdate t bsrest ss.(tso_buffers)) sm', st) sp.
Proof.
  intros. inv REL.
  assert (TCt': Comp.consistent tso_mm Tgt
     (mktsostate (tupdate t btrest (tso_buffers ts)) tm', tt)).
    by eapply Comp.step_preserves_consistency with (ge := tge); 
      [|edone]; vauto.
  constructor.
  - eby eapply write_preserves_tso_related_witt.
  - by eapply Comp.step_preserves_consistency with (ge := sge); vauto.
  - done. 
  - intros t'. specialize (SR t'). simpl in SR |- *.
    unfold tupdate; destruct (peq t' t) as [<- | N].  
      (* The unbuffering thread *)
      rewrite Bt, Bs in SR. 
      destruct (tt ! t'); destruct (st ! t'); try edone; simpl in SR |- *.
        apply <- buffered_states_related_prepend_tgt.
        apply <- buffered_states_related_prepend_src. edone.
        done. done. done.
      by destruct SR as (_ & _ & ? & _).
    (* Other threads *)
    destruct (tt ! t'); destruct (st ! t'); try edone; simpl in SR |- *.
    inversion TREL; subst; simpl in *.
    eapply buffered_states_related_load_inv_gen; 
      eauto using store_ptr_preserves_mem_partitioning with mrwp.
      pose proof(unbuffer_safe_to_buffer_safe_for_mem2 _ t' (proj2 TCt')) 
        as BSM.
      simpl in BSM. by rewrite tupdate_o in BSM.
    (* Agrees on local... *)
    intros p' c' CI.
    destruct (load_ptr c' (tso_mem ts) p') as [lv|] _eqn : L;
      destruct (load_ptr c' tm' p') as [lv'|] _eqn : L'; try done.
        (* Both succeed *)  
        intro RNI.
        rewrite <- (load_store_other ABIt), L in L'. clarify.
        destruct (store_chunk_allocated_someD ABIs) as
          [[rs [ks [RIs RAs]]] ALG].
        specialize (NSMR rs ks).
        destruct (chunk_inside_range_listD CI) as [rl [INl RIl]].
        pose proof (mrwp_in_alloc MRPt INl) as RAl.
        destruct ks; try (by apply NSMR in RAs;
          eapply disjoint_inside_disjoint_l, RIs;
            eapply disjoint_inside_disjoint_r, RIl;
              destruct (ranges_are_disjoint RAs RAl) as [[_ ?]|D]).
        destruct (mrwp_alloc_in MRPs RAs) as [trs INrs].
        destruct (peq trs t') as [<- | Ntrs].
          apply ranges_disjoint_comm.
          eapply disjoint_inside_disjoint_r, RIs.
          apply RNI.
          destruct (buffers_related_part_update_buffer _ _ _ _ 
                      (BR trs)).
          eapply unbuffer_write_free; eauto with mrwp.
          by destruct TCs.    
          intro D. apply (ranges_overlap_refl (range_of_chunk p c)).
            apply range_of_chunk_not_empty.
            eby eapply disjoint_inside_disjoint_r, RIs. 
        eapply disjoint_inside_disjoint_l, RIs;
          eapply disjoint_inside_disjoint_r, RIl.
        destruct (PI _ _ INrs) as [rs' [RIrs' INrs']].
        eapply disjoint_inside_disjoint_l, RIrs'.        
        by apply(proj1 MRPt _ _ Ntrs _ INrs' _ INl).
      apply load_chunk_allocated_someD in L.    
      apply load_chunk_allocated_noneD in L'.    
      by apply (store_preserves_chunk_allocation ABIt) in L.
    apply load_chunk_allocated_someD in L'.    
    apply load_chunk_allocated_noneD in L.    
    by apply (store_preserves_chunk_allocation ABIt) in L'.
Qed.

Lemma local_write_preserves_tso_pc_related_witt:
  forall ts tt tp ss st sp t btrest tm' p c v 
    (REL:  tso_pc_related_witt (ts, tt) tp (ss, st) sp)
    (ABIt: apply_buffer_item (BufferedWrite p c v) ts.(tso_mem) = 
             Some tm')
    (CI:   chunk_inside_range_list p c (tp t))
    (CNI:  range_not_in (range_of_chunk p c) (sp t))
    (Bt:   ts.(tso_buffers) t = BufferedWrite p c v :: btrest)
    (BRr:  buffers_related btrest (tp t) (tso_buffers ss t) (sp t)),
      tso_pc_related_witt 
        (mktsostate (tupdate t btrest ts.(tso_buffers)) tm', tt) tp
        (ss, st) sp.
Proof.
  intros. inv REL.
  assert (TCt': Comp.consistent tso_mm Tgt
     (mktsostate (tupdate t btrest (tso_buffers ts)) tm', tt)).
    by eapply Comp.step_preserves_consistency with (ge := tge); 
      [|edone]; vauto.
  constructor.
  - eby eapply local_write_preserves_tso_related_witt.
  - done.
  - done. 
  - intros t'. specialize (SR t'). simpl in SR |- *.
    unfold tupdate; destruct (peq t' t) as [<- | N].  
      (* The unbuffering thread *)
      rewrite Bt in SR. 
      destruct (tt ! t'); destruct (st ! t'); try edone; simpl in SR |- *.
        apply <- buffered_states_related_prepend_tgt. edone.
        done. done.
      by destruct SR as (_ & _ & ? & _).
    (* Other threads *)
    destruct (tt ! t'); destruct (st ! t'); try edone; simpl in SR |- *.
    inversion TREL; subst; simpl in *.
    eapply buffered_states_related_load_inv_gen; 
      eauto using store_ptr_preserves_mem_partitioning with mrwp.
      pose proof(unbuffer_safe_to_buffer_safe_for_mem2 _ t' (proj2 TCt')) 
        as BSM.
      simpl in BSM. by rewrite tupdate_o in BSM.
    (* Agrees on local... *)
    intros p' c' CI'.
    rewrite (load_store_other ABIt). by destruct load_ptr.
    destruct (chunk_inside_range_listD CI) as [? [IN RI]].
    destruct (chunk_inside_range_listD CI') as [? [IN' RI']].
    eapply disjoint_inside_disjoint_l, RI.
    eapply disjoint_inside_disjoint_r, RI'.
    apply ranges_disjoint_comm, (proj1 MRPt _ _ N _ IN' _ IN).
Qed.

Lemma salloc_preserves_tso_pc_related_witt:
  forall ts tt tp ss st sp t bsrest sm' p n r
    (REL:  tso_pc_related_witt (ts, tt) tp (ss, st) sp)
    (ABIs: apply_buffer_item (BufferedAlloc p n MObjStack) 
                             ss.(tso_mem) = Some sm')
    (Bs:   ss.(tso_buffers) t = BufferedAlloc p n MObjStack :: bsrest)
    (RNIN: range_not_in (p, n) (sp t))
    (RIr:  range_inside (p, n) r)
    (INtp: In r (tp t)) 
    (VAR:  valid_alloc_range (p, n))
    (BRr:  buffers_related (tso_buffers ts t) (tp t) 
                           bsrest ((p, n)::(sp t))),
      tso_pc_related_witt 
        (ts, tt) tp
        (mktsostate (tupdate t bsrest ss.(tso_buffers)) sm', st) 
        (tupdate t ((p, n)::(sp t)) sp).
Proof.
  intros. inv REL.
  constructor.
  - eby eapply salloc_preserves_tso_related_witt.
  - by eapply Comp.step_preserves_consistency with (ge := sge); vauto.
  - done. 
  - intros t'. specialize (SR t'). simpl in SR |- *.
    unfold tupdate; destruct (peq t' t) as [<- | N].  
      (* The unbuffering thread *)
      rewrite Bs in SR. 
      destruct (tt ! t'); destruct (st ! t'); try edone; simpl in SR |- *.
        apply <- buffered_states_related_prepend_src. edone.
        simpl. destruct valid_alloc_range_dec; [|done].
        destruct range_in_dec as [[? [IN O]]|]; eauto.
        by specialize (RNIN _ IN).      
      by destruct SR as (_ & _ & _ & ?).
    (* Other threads *)
    by destruct (tt ! t'); destruct (st ! t'). 
Qed.

Lemma sfree_preserves_tso_pc_related_witt:
  forall ts tt tp ss st sp t bsrest sptrest sm' p n
    (REL:  tso_pc_related_witt (ts, tt) tp (ss, st) sp)
    (ABIs: apply_buffer_item (BufferedFree p MObjStack) 
                             ss.(tso_mem) = Some sm')
    (Bs:   ss.(tso_buffers) t = BufferedFree p MObjStack :: bsrest)
    (Bspt: sp t = (p, n)::sptrest)
    (BRr:  buffers_related (tso_buffers ts t) (tp t) 
                           bsrest sptrest),
      tso_pc_related_witt 
        (ts, tt) tp
        (mktsostate (tupdate t bsrest ss.(tso_buffers)) sm', st) 
        (tupdate t sptrest sp).
Proof.
  intros. inv REL.
  constructor.
  - eby eapply sfree_preserves_tso_related_witt.
  - by eapply Comp.step_preserves_consistency with (ge := sge); vauto.
  - done. 
  - intros t'. specialize (SR t'). simpl in SR |- *.
    unfold tupdate; destruct (peq t' t) as [<- | N].  
      (* The unbuffering thread *)
      rewrite Bs in SR. 
      destruct (tt ! t'); destruct (st ! t'); try edone; simpl in SR |- *.
        apply <- buffered_states_related_prepend_src. edone.
        simpl. rewrite Bspt. by destruct Ptr.eq_dec.
      by destruct SR as (_ & _ & _ & ?).
    (* Other threads *)
    by destruct (tt ! t'); destruct (st ! t'). 
Qed.

Lemma talloc_preserves_tso_pc_related_witt:
  forall ts tt tp ss st sp t btrest tm' p n
    (REL:  tso_pc_related_witt (ts, tt) tp (ss, st) sp)
    (ABIt: apply_buffer_item (BufferedAlloc p n MObjStack) 
                             ts.(tso_mem) = Some tm')
    (Bt:   ts.(tso_buffers) t = BufferedAlloc p n MObjStack :: btrest)
    (RNIN: range_not_in (p, n) (tp t))
    (VAR:  valid_alloc_range (p, n))
    (BRr:  buffers_related btrest ((p, n)::(tp t))
                           (tso_buffers ss t) (sp t)),
      tso_pc_related_witt 
        (mktsostate (tupdate t btrest ts.(tso_buffers)) tm', tt) 
        (tupdate t ((p, n)::(tp t)) tp)
        (ss, st) sp.
Proof.
  intros. inv REL.
  assert (TCt': Comp.consistent tso_mm Tgt
     (mktsostate (tupdate t btrest (tso_buffers ts)) tm', tt)).
    by eapply Comp.step_preserves_consistency with (ge := tge); 
      [|edone]; vauto.
  constructor.
  - eby eapply talloc_preserves_tso_related_witt.
  - done.
  - done. 
  - intros t'. specialize (SR t'). simpl in SR |- *.
    unfold tupdate; destruct (peq t' t) as [<- | N].  
      (* The unbuffering thread *)
      rewrite Bt in SR. 
      destruct (tt ! t'); destruct (st ! t'); try edone; simpl in SR |- *.
        apply <- buffered_states_related_prepend_tgt. edone.
        done. 
        simpl. destruct valid_alloc_range_dec; [|done].
        destruct range_in_dec as [[? [IN O]]|]; eauto.
        by specialize (RNIN _ IN).      
      by destruct SR as (_ & _ & ? & _).
    (* Other threads *)
    destruct (tt ! t'); destruct (st ! t'); try edone; simpl in SR |- *.
    inversion TREL; subst; simpl in *.
    pose proof (alloc_ptr_stack_preserves_mem_partitioning 
      _ _ _ _ _ t MRPt ABIt) as MRPt'.
    pose proof (mrwp_rla _ _ t' MRPt') as RLA'.
    rewrite tupdate_o in RLA'; [|done].
    eapply buffered_states_related_load_inv_gen with (tm := tso_mem ts);
      eauto with mrwp.
      pose proof(unbuffer_safe_to_buffer_safe_for_mem2 _ t' (proj2 TCt')) 
        as BSM.
      simpl in BSM. by rewrite tupdate_o in BSM.
    (* Agrees on local... *)
    intros p' c' CI'.
    rewrite (load_alloc_other ABIt). by destruct load_ptr.
    apply ranges_disjoint_comm.
    destruct (chunk_inside_range_listD CI') as [? [IN' RI']].
    eauto using disjoint_inside_disjoint_r, @alloc_allocatedD, 
      @mrwp_in_alloc. 
Qed.

Lemma tfree_preserves_tso_pc_related_witt:
  forall ts tt tp ss st sp t btrest btptrest tm' p n
    (REL:  tso_pc_related_witt (ts, tt) tp (ss, st) sp)
    (ABIt: apply_buffer_item (BufferedFree p MObjStack) 
                             ts.(tso_mem) = Some tm')
    (Bt:   ts.(tso_buffers) t = BufferedFree p MObjStack :: btrest)
    (Etpt: tp t = (p, n)::btptrest)
    (RNIN: range_not_in (p, n) (sp t))
    (BRr:  buffers_related btrest btptrest
                           (tso_buffers ss t) (sp t)),
      tso_pc_related_witt 
        (mktsostate (tupdate t btrest ts.(tso_buffers)) tm', tt) 
        (tupdate t btptrest tp)
        (ss, st) sp.
Proof.
  intros. inv REL.
  assert (TCt':    Comp.consistent tso_mm Tgt
     (mktsostate (tupdate t btrest (tso_buffers ts)) tm', tt)).
    by eapply Comp.step_preserves_consistency with (ge := tge); 
      [|edone]; vauto.
  constructor.
  - eby eapply tfree_preserves_tso_related_witt.
  - done.
  - done. 
  - intros t'. specialize (SR t'). simpl in SR |- *.
    unfold tupdate; destruct (peq t' t) as [<- | N].  
      (* The unbuffering thread *)
      rewrite Bt in SR. 
      destruct (tt ! t'); destruct (st ! t'); try edone; simpl in SR |- *.
        apply <- buffered_states_related_prepend_tgt. edone.
        done. 
        simpl. rewrite Etpt. by destruct Ptr.eq_dec.
      by destruct SR as (_ & _ & ? & _).
    (* Other threads *)
    destruct (tt ! t'); destruct (st ! t'); try edone; simpl in SR |- *.
    inversion TREL; subst; simpl in *.
    pose proof (free_ptr_preserves_mem_partitioning 
      _ _ _ _ _ _ _ t MRPt ABIt Etpt) as MRPt'.
    pose proof (mrwp_rla _ _ t' MRPt') as RLA'.
    rewrite tupdate_o in RLA'; [|done].
    eapply buffered_states_related_load_inv_gen with (tm := tso_mem ts);
      eauto with mrwp.
      pose proof(unbuffer_safe_to_buffer_safe_for_mem2 _ t' (proj2 TCt')) 
        as BSM.
      simpl in BSM. by rewrite tupdate_o in BSM.
    (* Agrees on local... *)
    intros p' c' CI'.
    assert (IN: In (p, n) (tp t)). by rewrite Etpt; left.
    assert (range_allocated (p, n) MObjStack (tso_mem ts)).
      eby eapply @mrwp_in_alloc with (t := t). 
    erewrite (load_free_other ABIt). by destruct load_ptr. edone.
    destruct (chunk_inside_range_listD CI') as [? [IN' RI']].
    eapply disjoint_inside_disjoint_l, RI'.
    apply (proj1 MRPt _ _ N _ IN' _ IN).
Qed.

(** Unbuffering simulation *)
Lemma unbuffer_item_preserves_tso_pc_witt:
  forall {bi ts tm' tbr tt tp ss st sp t}
    (ABIt: apply_buffer_item bi ts.(tso_mem) = Some tm')
    (Bt:   ts.(tso_buffers) t = bi :: tbr)
    (REL:  tso_pc_related_witt (ts, tt) tp (ss, st) sp),
    exists bs1, exists bs2, exists sm', exists tp', exists sp', exists ss',
      ss.(tso_buffers) t = bs1 ++ bs2 /\
      apply_buffer bs1 ss.(tso_mem) = Some sm' /\
      part_update_buffer bs1 (sp t) = Some (sp' t) /\
      part_update bi (tp t) = Some (tp' t) /\
      apply_buffer_reachable t ss bs1 ss' /\
      ss'.(tso_mem) = sm' /\ (* might want to constrain buffers as well *)
      ss'.(tso_buffers) t = bs2 /\
      tso_pc_related_witt (mktsostate (tupdate t tbr ts.(tso_buffers))
                                      tm', tt) tp'
                           (ss', st) sp'.
Proof.
  intros.
  assert (BRt:
    buffers_related (tso_buffers ts t) (tp t) (tso_buffers ss t) (sp t)).
    inv REL. inv TREL. by eauto.
  remember (tso_buffers ts t) as tb.
  remember (tp t) as tpt.
  remember (tso_buffers ss t) as sb.
  remember (sp t) as spt.
  revert sp ss Heqspt Heqsb REL.

  (buffers_related_cases (induction BRt) Case); intros; inv Bt.
 
  Case "buffers_related_irrelevant".
    exists (bi::nil). exists sb.
    assert (A: exists sm', apply_buffer_item bi ss.(tso_mem) = Some sm').
      inv REL. destruct TCs as [_ US]. simpl in US.
      destruct (unbuffer_unbuffer_safe US (sym_eq Heqsb)) 
        as [sm' (ABIs & _)]. vauto.
    destruct A as [sm' ABIs].
    exists sm'. exists tp. exists sp0.
    exists (mktsostate (tupdate t sb ss.(tso_buffers)) sm').
    split. done.
    split. simpl. by rewrite ABIs.
    split. simpl. by rewrite part_update_irrelevant.
    split. by rewrite part_update_irrelevant.
    split. econstructor; try edone. eby symmetry. vauto.
    split. done.
    split. simpl. by rewrite tupdate_s.
    eby eapply irrelevant_preserves_tso_pc_related_witt.

  Case "buffers_related_write".
    exists (BufferedWrite p c v'::nil). exists sb.
    assert (A: exists sm', apply_buffer_item (BufferedWrite p c v') 
                                             ss.(tso_mem) = Some sm').
      inv REL. destruct TCs as [_ US]. simpl in US.
      destruct (unbuffer_unbuffer_safe US (sym_eq Heqsb)) 
        as [sm' (ABIs & _)]. vauto.
    destruct A as [sm' ABIs].
    exists sm'. exists tp. exists sp0.
    exists (mktsostate (tupdate t sb ss.(tso_buffers)) sm').
    split. done.
    split. simpl in *. by rewrite ABIs.
    split. done.
    split. done.
    split. econstructor; try edone. eby symmetry. vauto.
    split. done.
    split. simpl. by rewrite tupdate_s.
    eby eapply write_preserves_tso_pc_related_witt.

  Case "buffers_related_local_write".
    exists nil. exists (tso_buffers ss t).
    exists (tso_mem ss). exists tp. exists sp0. exists ss.
    repeat (split; [vauto|]).
    eby eapply local_write_preserves_tso_pc_related_witt.

  Case "buffers_related_salloc".
    assert (A: exists sm', apply_buffer_item (BufferedAlloc p n MObjStack) 
                                             ss.(tso_mem) = Some sm').
      inv REL. destruct TCs as [_ US]. simpl in US.
      destruct (unbuffer_unbuffer_safe US (sym_eq Heqsb)) 
        as [sm' (ABIs & _)]. vauto.
    destruct A as [sm' ABIs].
    exploit IHBRt; try done.
    - instantiate (1 := tupdate t ((p, n)::(sp0 t)) sp0).
      by rewrite tupdate_s.     
    - instantiate (1 := mktsostate (tupdate t sb ss.(tso_buffers)) sm').
      by simpl; rewrite tupdate_s.
    - eby eapply salloc_preserves_tso_pc_related_witt.
    intros [bs1 [bs2 [sm'' [tp'' [sp'' [ss'' 
      (B & AB & ABR & PUs & PUt & M & BR & TR)]]]]]].    
    exists (BufferedAlloc p n MObjStack :: bs1). exists bs2.
    exists sm''. exists tp''. exists sp''. exists ss''.
    split. by rewrite B.
    split. by simpl in *; rewrite ABIs.
    split. simpl.
      destruct valid_alloc_range_dec; [|done].
      by destruct range_in_dec as [[r' [IN RO]]|RI]; [specialize (RNIN r' IN)|].
    split. done.
    split. econstructor; try edone. eby symmetry. 
    split. done.
    split. done.
    done.

  Case "buffers_related_sfree".
    assert (A: exists sm', apply_buffer_item (BufferedFree p MObjStack) 
                                             ss.(tso_mem) = Some sm').
      inv REL. destruct TCs as [_ US]. simpl in US.
      destruct (unbuffer_unbuffer_safe US (sym_eq Heqsb)) 
        as [sm' (ABIs & _)]. vauto.
    destruct A as [sm' ABIs].
    exploit IHBRt; auto.
    - instantiate (1 := tupdate t sp sp0).
      by rewrite tupdate_s.     
    - instantiate (1 := mktsostate (tupdate t sb ss.(tso_buffers)) sm').
      by simpl; rewrite tupdate_s.
    - eapply sfree_preserves_tso_pc_related_witt; try edone.
      eby symmetry.
    intros [bs1 [bs2 [sm'' [tp'' [sp'' [ss'' 
      (B & AB & ABR & PUs & PUt & M & BR & TR)]]]]]].    
    exists (BufferedFree p MObjStack :: bs1). exists bs2.
    exists sm''. exists tp''. exists sp''. exists ss''.
    split. by rewrite B.
    split. by simpl in *; rewrite ABIs.
    split. simpl. by destruct Ptr.eq_dec.
    split. done.
    split. econstructor; try edone. eby symmetry. 
    split. done.
    split. done.
    done.

  Case "buffers_related_talloc".
    exists nil. exists (tso_buffers ss t).
    exists (tso_mem ss). 
    exists (tupdate t ((p, n)::(tp t)) tp). 
    exists sp0. exists ss.
    repeat (split; [vauto|]).
    simpl; destruct valid_alloc_range_dec; [|done].
    destruct range_in_dec as [[r' [IN RO]]|RI].
    by specialize (RNIN r' IN). by rewrite tupdate_s.
    eby eapply talloc_preserves_tso_pc_related_witt.

  Case "buffers_related_tfree".
    exists nil. exists (tso_buffers ss t).
    exists (tso_mem ss). 
    exists (tupdate t tp0 tp). 
    exists sp0. exists ss.
    repeat (split; [vauto|]).
    simpl. rewrite tupdate_s. by destruct Ptr.eq_dec.
    eapply tfree_preserves_tso_pc_related_witt; try edone.
    eby symmetry.
Qed.

Require Import Relations.Relation_Operators.

Section PRODUCT_WF.
  Variable A : Type.
  Variable B : Type.
  Variable leA : B -> A -> A -> Prop.
  Variable leB : B -> B -> Prop.

  Definition lexi ab ab' :=
    leB (snd ab) (snd ab') \/ 
    snd ab = snd ab' /\ leA (snd ab) (fst ab) (fst ab').

  Hypothesis wfA : forall b, well_founded (leA b).
  Hypothesis wfB : well_founded leB.

  Lemma lexi_wf: well_founded lexi.
  Proof.
    intros [a b].

    set (IH b := forall a, Acc lexi (a, b)).
    apply (well_founded_ind wfB IH). unfold IH. clear b IH.
    intros b IHb.
    
    set (IH a := Acc lexi (a, b)).
    apply (well_founded_ind (wfA b) IH). unfold IH. clear IH a.
    intros a IHa.
    
    constructor.
    intros [a' b'] [LTa | [E LTb]]; eauto.
    simpl in E. subst. eauto.
  Qed.    

End PRODUCT_WF.

Definition threads_order := 
  (fun (t1 t2 : PTree.t (SEM_ST Tgt)) =>
    PTree.order (st_order sge tge) t1 t2).

Definition tsom_order (threads : PTree.t (SEM_ST Tgt)) (t s : tso_state) := 
 (buffers_measure (map (@fst _ _) (PTree.elements threads)) (tso_buffers t) < 
  buffers_measure (map (@fst _ _) (PTree.elements threads)) (tso_buffers s))%nat.

Definition tso_order : Comp.state tso_mm Tgt -> Comp.state tso_mm Tgt -> Prop := 
  lexi _ _ tsom_order threads_order.

Lemma st_order_to_ts_order:
  forall tt t s s' ts ts'
  (CS : tt ! t = Some s)
  (LT : st_order sge tge s' s),
    tso_order (ts', tt ! t <- s')  (ts, tt).
Proof.
  intros.
  left. simpl. 
  unfold threads_order. 
  eby eapply PTree.order_set_lt.
Qed.

Lemma tso_order_wf:
  well_founded tso_order.
Proof.
  apply lexi_wf.
    intro b. unfold tsom_order.
    apply well_founded_ltof. 
  eapply PTree.order_wf. auto.
Qed.

Lemma unbuffer_sim:
  forall ts ts' tt s
    (TSOS: tso_step ts MMtau ts')
    (TREL: tso_pc_related (ts, tt) s),
      (tso_pc_related (ts', tt) s /\ 
       tso_order (ts', tt) (ts, tt)) \/
      exists s',
        taustep stso_lts s Etau s' /\
        tso_pc_related (ts', tt) s'.
Proof.
  intros until 1. intros [tp [sp TREL]]. destruct s as [ss st].
  inv TSOS.
  destruct (unbuffer_item_preserves_tso_pc_witt AB EQbufs TREL)
    as [bs1 [bs2 [sm' [tp' [sp' [ss' (Ebs & ABs & PUt & PUs & ABR & M & B & TREL')]]]]]].
  destruct bs1 as [|bsi bsrest].
    left.
    split.
      inv ABR.
      eby eexists; eexists.
    right. 
    split. done. 
    inv TREL; simpl. destruct TCt as [BC _].
    assert (IN: In t (map (@fst _ _) (PTree.elements tt))).
      destruct (tt ! t) as [] _eqn : Ettt.
        apply PTree.elements_correct in Ettt.
        change t with (fst (t, s)). by eapply in_map.
      by specialize (BC t); simpl in BC; rewrite PTree.gmap, Ettt in BC; rewrite BC in EQbufs.
    assert (ND: NoDup (map (@fst _ _) (PTree.elements tt)))
      by (apply PTree.elements_keys_norepet).
    pose proof (measure_down_unbuffer _ _ _ _ _ ND EQbufs IN) as [? [E1 E2]].
    unfold tsom_order. simpl. rewrite <- E1, <- E2. omega.
  right; eexists.
  split. by eapply TSO.apply_buffer_reachable_taustep; try edone.
  eby eexists; eexists.
Qed.

(** Unbuffering to empty buffers (helper for read simulation). *)

Lemma unbuffer_item_preserves_tso_pc_witt_empty:
  forall ts tt tp ss st sp t
    (Bt:   ts.(tso_buffers) t = nil)
    (REL:  tso_pc_related_witt (ts, tt) tp (ss, st) sp),
    exists sm', exists sp', exists ss',
      apply_buffer (ss.(tso_buffers) t) ss.(tso_mem) = Some sm' /\
      apply_buffer_reachable t ss (tso_buffers ss t) ss' /\
      part_update_buffer (tso_buffers ss t) (sp t) = Some (sp' t) /\
      ss'.(tso_mem) = sm' /\
      ss'.(tso_buffers) t = nil /\
      tso_pc_related_witt (ts, tt) tp (ss', st) sp'.
Proof.
  intros.
  assert (BRt:
    buffers_related (tso_buffers ts t) (tp t) (tso_buffers ss t) (sp t)).
    inv REL. inv TREL. by eauto.
  remember (tso_buffers ts t) as tb.
  remember (tp t) as tpt.
  remember (tso_buffers ss t) as sb.
  remember (sp t) as spt.
  revert sp ss Heqspt Heqsb REL.

  (buffers_related_cases (induction BRt) Case); intros; inv Bt.

  Case "buffers_related_empty".
    exists (tso_mem ss). exists sp0. exists ss.
    split. done.
    split. vauto.
    done.

  Case "buffers_related_salloc".
    assert (A: exists sm', apply_buffer_item (BufferedAlloc p n MObjStack) 
                                             ss.(tso_mem) = Some sm').
      inv REL. destruct TCs as [_ US]. simpl in US.
      destruct (unbuffer_unbuffer_safe US (sym_eq Heqsb)) 
        as [sm' (ABIs & _)]. vauto.
    destruct A as [sm' ABIs].
    exploit IHBRt; try done.
    - instantiate (1 := tupdate t ((p, n)::(sp0 t)) sp0).
      by rewrite tupdate_s.     
    - instantiate (1 := mktsostate (tupdate t sb ss.(tso_buffers)) sm').
      by simpl; rewrite tupdate_s.
    - eby eapply salloc_preserves_tso_pc_related_witt.
    intros [sm'' [sp'' [ss'' 
      (AB & ABR & PUs & M & BR & TR)]]].    
    exists sm''. exists sp''. exists ss''.
    split. by simpl in *; rewrite ABIs.
    split. econstructor; try edone. eby symmetry. 
    split. simpl.
      destruct valid_alloc_range_dec; [|done].
      by destruct range_in_dec as [[r' [IN RO]]|RI]; [specialize (RNIN r' IN)|].
    done.

  Case "buffers_related_sfree".
    assert (A: exists sm', apply_buffer_item (BufferedFree p MObjStack) 
                                             ss.(tso_mem) = Some sm').
      inv REL. destruct TCs as [_ US]. simpl in US.
      destruct (unbuffer_unbuffer_safe US (sym_eq Heqsb)) 
        as [sm' (ABIs & _)]. vauto.
    destruct A as [sm' ABIs].
    exploit IHBRt; auto.
    - instantiate (1 := tupdate t sp sp0).
      by rewrite tupdate_s.     
    - instantiate (1 := mktsostate (tupdate t sb ss.(tso_buffers)) sm').
      by simpl; rewrite tupdate_s.
    - eapply sfree_preserves_tso_pc_related_witt; try edone.
      eby symmetry.
    intros [sm'' [sp'' [ss'' (AB & ABR & M & BR & TR)]]].
    exists sm''. exists sp''. exists ss''.
    split. by simpl in *; rewrite ABIs.
    split. econstructor; try edone. eby symmetry.
    split. simpl. by destruct Ptr.eq_dec.
    done.
Qed.

Lemma apply_buffer_reachable_app:
  forall t s s' b1 b2 s''
  (AB1: apply_buffer_reachable t s b1 s')
  (AB2: apply_buffer_reachable t s' b2 s''),
    apply_buffer_reachable t s (b1 ++ b2) s''.
Proof.
  intros; induction AB1. done.
  simpl. econstructor; eauto. 
Qed.

Lemma tso_pc_rel_unbuffer_to_empty:
  forall {ts tt ss st tp sp tpt spt tm sm t}
    (REL: tso_pc_related_witt (ts, tt) tp (ss, st) sp)
    (ABt: apply_buffer (ts.(tso_buffers) t) ts.(tso_mem) = Some tm)
    (ABs: apply_buffer (ss.(tso_buffers) t) ss.(tso_mem) = Some sm)
    (PUt: part_update_buffer (ts.(tso_buffers) t) (tp t) = Some tpt)
    (PUs: part_update_buffer (ss.(tso_buffers) t) (sp t) = Some spt),
    exists ts', exists ss', exists tp', exists sp',
      ts'.(tso_buffers) t = nil /\
      ss'.(tso_buffers) t = nil /\
      ts'.(tso_mem) = tm /\
      ss'.(tso_mem) = sm /\
      tp' t = tpt /\
      sp' t = spt /\
      apply_buffer_reachable t ss (tso_buffers ss t) ss' /\
      tso_pc_related_witt (ts', tt) tp' (ss', st) sp'.
Proof.
  intros.
  remember (tso_buffers ts t) as tb. apply sym_eq in Heqtb.
  revert ts tt ss st tp sp Heqtb PUt PUs ABt ABs REL.
  
  induction tb as [|tbi tb IH]; intros.

  (* Base case *)
  exploit unbuffer_item_preserves_tso_pc_witt_empty; try edone.
  intros [sm' [sp' [ss' (AB & ABR & PUs' & M & E & REL')]]].
  rewrite AB in ABs. inv ABs. inv ABt.
  eexists; eexists; eexists; eexists; simpl in *; subst.
  split. apply Heqtb. 
  split. apply E.
  split. done. 
  split. done.
  split; [| split; [|split; [|edone]]]. 
      by inv PUt.
    by clarify'.
  done.
  
  (* Step case *)
  simpl in ABt. 
  destruct (apply_buffer_item tbi (tso_mem ts)) as [tm''|] _eqn:ABIt; [|done].
  simpl in ABt.
  exploit @unbuffer_item_preserves_tso_pc_witt; try edone.
  intros [bs1 [bs2 [sm' [tp' [sp' [ss' (B & AB & PUs' & PUt' & ABR & M & Bs & REL')]]]]]].
  exploit IH; [| | | | |apply REL'|].
  - simpl. by rewrite tupdate_s.
  - simpl in PUt. by rewrite PUt' in PUt.
  - simpl in PUs. rewrite B, fold_left_opt_app, PUs' in PUs.
    by rewrite Bs. 
  - done.
  - rewrite Bs. rewrite B in ABs.
    rewrite apply_buffer_app, AB in ABs. by rewrite M. 
  intros [ts'' [ss'' [tp'' [sp'' (Et & Es & Etm & Esm & Etp & Esp & ABR' & REL'')]]]].
  exists ts''; exists ss''; exists tp''; exists sp''.
  repeat (split; [edone|]).
  split. subst. rewrite B. eby eapply apply_buffer_reachable_app. 
  done.
Qed.

Lemma tso_pc_rel_load_eq:
  forall ts tt ss st tm sm t
    (REL: tso_pc_related (ts, tt) (ss, st))
    (ABt: apply_buffer (ts.(tso_buffers) t) ts.(tso_mem) = Some tm)
    (ABs: apply_buffer (ss.(tso_buffers) t) ss.(tso_mem) = Some sm),
      load_values_related tm sm.
Proof.
  intros.
  remember (tso_buffers ts t) as tb. apply sym_eq in Heqtb.
  destruct REL as [tp [sp REL]].
  revert ts tt ss st tp sp Heqtb ABt ABs REL.
  
  induction tb as [|tbi tb IH]; intros.

  (* Base case *)
  exploit unbuffer_item_preserves_tso_pc_witt_empty; try edone.
  intros [sm' [sp' [ss' (AB & _ & _ & M & _ & REL')]]].
  rewrite AB in ABs. inv ABs. inv ABt.
  inv REL'. by inv TREL. 
  
  (* Step case *)
  simpl in ABt. 
  destruct (apply_buffer_item tbi (tso_mem ts)) as [tm''|] _eqn:ABIt; [|done].
  simpl in ABt.
  exploit @unbuffer_item_preserves_tso_pc_witt; try edone.
  intros [bs1 [bs2 [sm' [tp' [sp' [ss' (B & AB & _ & _ & _ & M & Bs & REL')]]]]]].
  eapply IH; [| | |edone].
  - simpl. by rewrite tupdate_s.
  - done.
  - rewrite Bs. rewrite B in ABs.
    rewrite apply_buffer_app, AB in ABs. by rewrite M. 
Qed.

Definition can_reach_error shms :=
    exists shms', taustar stso_lts shms shms' /\
                  can_do_error stso_lts shms'.

Lemma taustar_to_tso:
  forall {t thr ts ts'} tso
    (E: thr ! t = Some ts)
    (TAU: taustar slts ts ts'),
    exists thr',
      taustar stso_lts (tso, thr) (tso, thr') /\
      (forall t', t' <> t -> thr!t' = thr'!t') /\
      thr'!t = Some ts'.
Proof.
  intros; revert thr E.
  induction TAU as [s|s1 s2 s3 ST TST IH]; intros thr E; simpl in *. 
    by eexists; vauto.
  destruct (IH (thr ! t <- s2) (PTree.gss _ _ _)) as
    [thr' [TAU' [OTH TSP]]].
  exists thr'.
  split.
    eapply taustar_step; try eassumption; simpl.
    eby eapply Comp.step_tau.
  split; try done.
  by intros t' NE; rewrite <- (OTH t' NE), PTree.gso; auto.
Qed.

Lemma error_to_tso:
  forall st t s ss
  (S    : st ! t = Some s)
  (SERR : stuck_or_error slts s),
    can_reach_error (ss, st).
Proof.
  intros.
  destruct SERR as [STUCK | [s' [l' [ISERR ST']]]].
    eexists. split. apply taustar_refl.
    eexists. exists (Evisible Efail). split. done.
    eby eapply Comp.step_thread_stuck. 
  eexists. split. apply taustar_refl.
  eexists. exists (Evisible Efail). split. done.
  destruct l'; try done; []; destruct ev; try done; [].
  eby eapply Comp.step_ext.
Qed. 

(** * Tau simulation *)
Lemma thread_tau_sim:
  forall s s' (tt : PTree.t Tgt.(SEM_ST)) t sst ts
    (TS : Tgt.(SEM_step) tge s TEtau s')
    (CS : tt ! t = Some s)
    (TSOPCREL : tso_pc_related (ts, tt) sst),
      can_reach_error sst \/
      (exists sst', 
         taustep stso_lts sst Etau sst' /\ 
         tso_pc_related (ts, tt ! t <- s') sst') \/
      tso_pc_related (ts, tt ! t <- s') sst /\
      tso_order (ts, tt ! t <- s') (ts, tt).
Proof.
  intros. destruct sst as [ss st].
  pose proof TSOPCREL as [tp [sp REL]]. inversion REL; subst.
  pose proof (SR t) as SRt; simpl in SRt. rewrite CS in SRt.
  destruct (st ! t) as [s0|] _eqn : Estt; simpl in SRt; [|done].
  inv SRt.
  destruct (sim sge tge ge_rel _ _ _ _ _ _ _ TS SR0)
    as [SERR | 
       [[ss' ([s1 (TAU & ST')] & SR')] |
       [(SR' & ORD) |
       [[p [n (VAR & [r (RI & IN & RNIN)] & 
               [ss' ([s1 (TAU & ST')] & SR')])]] | 
       [p [n [sp'' (Esp & [ss' ([s1 (TAU & ST')] & SR')])]]]]]]].

  (* Error or stuck *)
  left. eby eapply error_to_tso.
  
  (* Corresponding tau *)
  right; left.
  destruct (taustar_to_tso ss Estt TAU) as [st1 (TAUs & OS & Es1)].
  assert (TS' : taustep stso_lts (ss, st) Etau (ss, st1 ! t <- ss')).
    eexists. split. edone.
    eby eapply Comp.step_tau. 
  eexists. 
  split. edone.
  exists tp; exists sp. 
  econstructor. 
  - done.
  - eby eapply Comp.taustep_preserves_consistency.
  - eby eapply Comp.step_preserves_consistency; vauto.
  - intro t'; simpl; destruct (peq t' t) as [<- | N].
      by rewrite !PTree.gss; vauto.
    by rewrite !PTree.gso, <- OS.

  (* Stutter *)
  right; right.
  split; [|by eauto using st_order_to_ts_order].
  exists tp; exists sp. 
  econstructor; try done.
  - eby eapply Comp.step_preserves_consistency; vauto.
  - intro t'; simpl; destruct (peq t' t) as [<- | N].
      by rewrite !PTree.gss, Estt; vauto.
    by rewrite !PTree.gso.
  
  (* Allocation in source *)
  right; left.
  destruct (taustar_to_tso ss Estt TAU) as [st1 (TAUs & OS & Es1)].
  assert (R: tso_related_witt_sf ts tp
    (buffer_insert ss t (BufferedAlloc p n MObjStack)) sp).
    constructor. by destruct TCt.
      pose proof (TSO.tso_cons_impl_fin_sup _ _ TCs).
      by apply fin_sup_buffer_insert.
    inversion TREL; subst.
    constructor; try done; [].
    intros t'. specialize (BR t'). simpl in BR.
    destruct (peq t' t) as [-> | N]; unfold buffer_insert; simpl.
      rewrite tupdate_s.
      rewrite (app_nil_end (tso_buffers ts t)).
      eapply buffers_related_suffix; try edone.
      by eapply buffers_related_salloc; try edone; vauto. 
    by rewrite tupdate_o. 
  assert (TS' : taustep stso_lts (ss, st) Etau 
    (buffer_insert ss t (BufferedAlloc p n MObjStack), st1 ! t <- ss')).
    eexists. split. edone.
    eapply Comp.step_ord; try edone; [].
    eapply tso_step_alloc. done.
    eapply alloc_unbuffer_safe with (t := t).
    - vauto.
    - apply (proj2 TCs). 
    - eby right; reflexivity.
    - eby unfold buffer_insert; simpl; rewrite tupdate_s.
    - by intros t' N; unfold buffer_insert; simpl; rewrite tupdate_o.
    - done.
  eexists; split. edone.
  exists tp. exists sp. 
  constructor. by inv R.
  eby eapply Comp.taustep_preserves_consistency.
  eby eapply Comp.step_preserves_consistency; vauto.
  intros t'. specialize (SR t'). simpl in SR |- *.
  destruct (peq t' t) as [<- | N]; 
    [|by rewrite tupdate_o, !@PTree.gso, <- OS].
  rewrite !@PTree.gss, tupdate_s; simpl.
  econstructor; try edone.
  rewrite fold_left_opt_app, PUs; simpl.
  destruct valid_alloc_range_dec; [|done].
  destruct range_in_dec as [[r' [IN' RO]]|RI'].
    by specialize (RNIN r' IN').
  done.
  
  (* Free in source *)
  destruct (taustar_to_tso ss Estt TAU) as [st1 (TAUs & OS & Es1)].
  assert(FS: tso_fin_sup (buffer_insert ss t (BufferedFree p MObjStack))).
    by apply tso_fin_sup_tupdate, (TSO.tso_cons_impl_fin_sup _ _ TCs).
  destruct (unbuffer_safe_dec _ FS) as [US|NS].
  2: edestruct (TSO.taustep_free_fail _ sge ST' NS Es1) as (? & ? & ? & ?); 
       [eby eapply Comp.taustar_preserves_consistency|];
     left; eexists; split; [eby eapply taustar_trans|];
     eby eexists; exists (Evisible Efail).
  right; left.
  assert (R: tso_related_witt_sf ts tp
    (buffer_insert ss t (BufferedFree p MObjStack)) sp).
    constructor. by destruct TCt.
      pose proof (TSO.tso_cons_impl_fin_sup _ _ TCs).
      by apply fin_sup_buffer_insert.
    inversion TREL; subst.
    constructor; try done; [].
    intros t'. specialize (BR t'). simpl in BR.
    destruct (peq t' t) as [-> | N]; unfold buffer_insert; simpl.
      rewrite tupdate_s.
      rewrite (app_nil_end (tso_buffers ts t)).
      eapply buffers_related_suffix; try edone.
      by eapply buffers_related_sfree; try edone; vauto. 
    by rewrite tupdate_o.
  assert (TS' : taustep stso_lts (ss, st) Etau 
    (buffer_insert ss t (BufferedFree p MObjStack), st1 ! t <- ss')).
    eexists. split. edone.
    eapply Comp.step_ord; try edone; [].
    eby eapply tso_step_free. 
  eexists; split. edone.
  exists tp. exists sp. 
  constructor. by inv R.
  eby eapply Comp.taustep_preserves_consistency.
  eby eapply Comp.step_preserves_consistency; vauto.
  intros t'. specialize (SR t'). simpl in SR |- *.
  destruct (peq t' t) as [<- | N]; 
    [|by rewrite tupdate_o, !@PTree.gso, <- OS].
  rewrite !@PTree.gss, tupdate_s; simpl.
  econstructor; try edone.
  rewrite fold_left_opt_app, PUs; simpl.
  subst. by destruct Ptr.eq_dec.  
Qed.

(** Write simulation *)
Lemma write_sim:
  forall s s' (tt : PTree.t Tgt.(SEM_ST)) t sst ts p c v
    (TS : Tgt.(SEM_step) tge s (TEmem (MEwrite p c v)) s')
    (CS : tt ! t = Some s)
    (US : unbuffer_safe (buffer_insert ts t (BufferedWrite p c v)))
    (TSOPCREL : tso_pc_related (ts, tt) sst),
      can_reach_error sst \/
      (exists sst',
         taustep stso_lts sst Etau sst' /\ 
         tso_pc_related (buffer_insert ts t (BufferedWrite p c v), tt ! t <- s') sst') \/
      tso_pc_related (buffer_insert ts t (BufferedWrite p c v), tt ! t <- s') sst /\
      tso_order (buffer_insert ts t (BufferedWrite p c v), tt ! t <- s') (ts, tt).
Proof.
  intros. destruct sst as [ss st].
  pose proof TSOPCREL as [tp [sp REL]]. inversion REL; subst.
  pose proof (SR t) as SRt; simpl in SRt. rewrite CS in SRt.
  destruct (st ! t) as [s0|] _eqn : Estt; simpl in SRt; [|done].
  inv SRt.
  destruct (sim sge tge ge_rel _ _ _ _ _ _ _ TS SR0) 
    as [SERR | 
       [(CIRL & RNIR & [tm'' (ST & [[ss' ([s1 (TAU & ST')] & SR')] | [SR' ORD]])]) | 
       [v' (LD & [ss' ([s1 (TAU & ST')] & SR')])]]].

  (* Error or stuck *)
  left. eby eapply error_to_tso.

  (* Local write - taustep *)
  right; left.
  destruct (taustar_to_tso ss Estt TAU) as [st1 (TAUs & OS & Es1)].
  assert (TS' : taustep stso_lts (ss, st) Etau (ss, st1 ! t <- ss')).
    eexists. split. edone.
    eby eapply Comp.step_tau. 
  eexists. 
  split.
    eexists. split. edone.
    eby eapply Comp.step_tau.
  exists tp; exists sp. 
  econstructor. simpl.
  - inv TREL; econstructor; try edone; [].
    (* Buffer relation *)
    intros t'. specialize (BR t'). simpl in BR.
    destruct (peq t' t) as [-> | N]; unfold buffer_insert; simpl.
      rewrite tupdate_s.
      rewrite (app_nil_end (tso_buffers ss t)).
      eapply buffers_related_suffix; try edone.
      eapply buffers_related_local_write; try edone; vauto; [].
      by destruct (store_chunk_allocated_someD ST).
    by rewrite tupdate_o. 
  - eby eapply Comp.taustep_preserves_consistency.
  - eby eapply Comp.step_preserves_consistency; [eapply Comp.step_ord;vauto|]. 
  - intro t'; simpl; destruct (peq t' t) as [<- | N].
      rewrite !PTree.gss, tupdate_s.
      econstructor; try edone.
        rewrite apply_buffer_app, ABt. simpl. by rewrite ST.
      by rewrite fold_left_opt_app, PUt. 
    by rewrite !PTree.gso, tupdate_o, <- OS.

  (* Local write - stutter *)
  right; right.
  split.
  exists tp; exists sp. 
  econstructor.
  - inv TREL; econstructor; try edone; [].
    (* Buffer relation *)
    intros t'. specialize (BR t'). simpl in BR.
    destruct (peq t' t) as [-> | N]; unfold buffer_insert; simpl.
      rewrite tupdate_s.
      rewrite (app_nil_end (tso_buffers ss t)).
      eapply buffers_related_suffix; try edone.
      eapply buffers_related_local_write; try edone; vauto; [].
      by destruct (store_chunk_allocated_someD ST).
    by rewrite tupdate_o. 
  - done.
  - eby eapply Comp.step_preserves_consistency; [eapply Comp.step_ord;vauto|]. 
  - intro t'; simpl; destruct (peq t' t) as [<- | N].
      rewrite !PTree.gss, tupdate_s, Estt.
      econstructor; try edone.
        rewrite apply_buffer_app, ABt. simpl. by rewrite ST.
      by rewrite fold_left_opt_app, PUt. 
    by rewrite !PTree.gso, tupdate_o.
  eby eapply st_order_to_ts_order.

  (* Write on both sides *)
  destruct (taustar_to_tso ss Estt TAU) as [st1 (TAUs & OS & Es1)].
  assert(FS: tso_fin_sup (buffer_insert ss t (BufferedWrite p c v'))).
    apply tso_fin_sup_tupdate. 
    by pose proof (TSO.tso_cons_impl_fin_sup _ _ TCs).
  destruct (unbuffer_safe_dec _ FS) as [US'|NS].
  2: destruct (tso_step_write_fail (proj2 TCs) (not_unbuffer_safe FS NS)) as (? & ? & ? & ?); 
     eby left; eexists (_, _); split; [eapply taustar_trans, TSO.unbuffer_to_tsopc2
                                      | eexists; exists (Evisible Efail); split; vauto].
  assert (TS' : taustep stso_lts (ss, st) Etau 
    (buffer_insert ss t (BufferedWrite p c v'), st1 ! t <- ss')).
    eexists. split. edone.
    eby eapply Comp.step_ord; vauto. 
  right; left.
  eexists; split. edone.
  exists tp; exists sp. 
  econstructor.
  - inv TREL; econstructor; try edone; [].
    (* Buffer relation *)
    intros t'. specialize (BR t'). simpl in BR.
    destruct (peq t' t) as [-> | N]; unfold buffer_insert; simpl.
      rewrite !tupdate_s.
      eapply buffers_related_suffix; try edone.
      by eapply buffers_related_write; vauto.
    by rewrite !tupdate_o. 
  - eby eapply Comp.taustep_preserves_consistency.
  - eby eapply Comp.step_preserves_consistency; [eapply Comp.step_ord;vauto|]. 
  - intro t'; simpl; destruct (peq t' t) as [<- | N].
      destruct (unbuffer_safe_to_buffer_safe_for_mem2 _ t' US') as [sm'' ABs''].
      destruct (unbuffer_safe_to_buffer_safe_for_mem2 _ t' US) as [tm'' ABt''].
      simpl in ABs'', ABt''. rewrite tupdate_s in ABs'', ABt''.
      rewrite !PTree.gss, !tupdate_s.
      econstructor. edone. 
        rewrite fold_left_opt_app, PUt. eby simpl.
        rewrite fold_left_opt_app, PUs. eby simpl.
      (* We have to show that the write does not affect local data 
         (and thus the individual thread simulation relation). *)
      eapply (load_inv _ _ ge_rel); [|edone]. simpl in TREL.
      rewrite apply_buffer_app in ABs''.
      destruct (apply_buffer (tso_buffers ss t') (tso_mem ss)) as [smi|] _eqn : ABsmi;
        [|done]; simpl in ABs''.
      destruct (store_ptr c smi p v') as [smx|] _eqn:STi; [|done]. inv ABs''.
      rewrite apply_buffer_app, ABt in ABt''; simpl in ABt''.
      destruct (store_ptr c tm' p v) as [tmx|] _eqn:STti; [|done]. inv ABt''.
      destruct (tso_pc_rel_unbuffer_to_empty REL ABt ABsmi PUt PUs)
        as [ts'' [ss'' [tp'' [sp'' (Etb & Esb & Etm & Esm & Etpt & Espt & ABR & REL')]]]]. subst.
      destruct (store_chunk_allocated_someD STi) as [[rs [ks [RIs RAs]]] ALG].
      intros p' c' CI.
      destruct (chunk_inside_range_listD CI) as [rpc [IN RI]].
      destruct (load_ptr c' (tso_mem ts'') p') as [v1|] _eqn:L.
        destruct (load_ptr c' tm'' p') as [v2|] _eqn:L'.
          intro RNI.
          rewrite (load_store_other STti) in L. clarify'.
          inv REL'. inv TREL0. simpl in *. specialize (NSMR rs ks).
          destruct ks;
            try by apply <- NSMR in RAs; apply (mrwp_in_alloc MRPt) in IN;
              eapply disjoint_inside_disjoint_r, RI;
                eapply disjoint_inside_disjoint_l, RIs;
                  destruct (ranges_are_disjoint RAs IN) as [[_ E]|].
          destruct (mrwp_alloc_in MRPs RAs) as [t'' INt''].
          destruct (peq t'' t') as [<- | N].
            specialize (RNI _ INt'').
            by eapply ranges_disjoint_comm, disjoint_inside_disjoint_r, RIs.
          pose proof (PI _ _ INt'') as [r' (RIt & INt)].
          eapply disjoint_inside_disjoint_r, RI.
          eapply disjoint_inside_disjoint_l, RIs.
          eapply disjoint_inside_disjoint_l, RIt.
          apply (proj1 MRPt _ _ N _ INt _ IN).
        apply load_chunk_allocated_someD in L.
        apply (store_preserves_chunk_allocation STti) in L.
        by apply load_chunk_allocated_noneD in L'.
      destruct (load_ptr c' tm'' p') as [] _eqn:L'; [|done].
      apply load_chunk_allocated_someD in L'.
      apply (store_preserves_chunk_allocation STti) in L'.
      by apply load_chunk_allocated_noneD in L.
    by rewrite !PTree.gso, !tupdate_o, <- OS.
Qed.

Lemma write_fail_sim:
  forall s s' (tt : PTree.t Tgt.(SEM_ST)) t sst ts ts' p c v
    (ST : Tgt.(SEM_step) tge s (TEmem (MEwrite p c v)) s')
    (TS : tso_step ts (MMreadfail t p c) ts')
    (CS : tt ! t = Some s)
    (TSOPCREL : tso_pc_related (ts, tt) sst),
      can_reach_error sst.
Proof.
  intros. destruct sst as [ss st].
  pose proof TSOPCREL as [tp [sp REL]]. inversion REL; subst.
  pose proof (SR t) as SRt; simpl in SRt. rewrite CS in SRt.
  destruct (st ! t) as [s0|] _eqn : Estt; simpl in SRt; [|done].
  inv SRt.
  inv TS.

  rewrite Bemp in *; simpl in *; clarify.

  destruct (sim sge tge ge_rel _ _ _ _ _ _ _ ST SR0) 
    as [SERR | 
       [(CIRL & RNIR & [tm'' (ST' & X)]) | 
       [v' (LD' & [ss' ([s1 (TAU & ST')] & SR')])]]].

  (* Error or stuck *)
  eby eapply error_to_tso.

  (* Local write *)
  by generalize (store_chunk_allocated_someD ST'),
                (load_chunk_allocated_noneD LD).

  (* Write in source and target *)
  destruct (unbuffer_item_preserves_tso_pc_witt_empty _ _ _ _ _ _ _ Bemp REL)
    as [sm'' [sp'' [ss'' (ABs & ABR & Espt & Esm & Esb & REL')]]]. 
  inv REL'. inv TREL0. simpl in *. specialize (LR p c). rewrite LD in LR.
  destruct (load_ptr c (tso_mem ss'') p) as [] _eqn : L'; [done|].
  destruct (taustar_to_tso ss Estt TAU) as [st1 (TAUs & OS & Es1)].
  eexists; split; [eby eapply taustar_trans, TSO.apply_buffer_reachable_taustar|]. 
  by eexists; exists (Evisible Efail); split; vauto.
Qed.

(** Free simulation *)
Lemma non_stack_or_stack:
  forall k,
    non_stack k \/ k = MObjStack.
Proof.
  intros []; try (by left); by right.
Qed.

Lemma free_sim:
  forall s s' (tt : PTree.t Tgt.(SEM_ST)) t sst ts p k
    (TS : Tgt.(SEM_step) tge s (TEmem (MEfree p k)) s')
    (CS : tt ! t = Some s)
    (US : unbuffer_safe (buffer_insert ts t (BufferedFree p k)))
    (TSOPCREL : tso_pc_related (ts, tt) sst),
      can_reach_error sst \/
      (exists sst',
         taustep stso_lts sst Etau sst' /\ 
         tso_pc_related (buffer_insert ts t (BufferedFree p k), tt ! t <- s') sst') \/
      tso_pc_related (buffer_insert ts t (BufferedFree p k), tt ! t <- s') sst /\
      tso_order (buffer_insert ts t (BufferedFree p k), tt ! t <- s') (ts, tt).
Proof.
  intros. destruct sst as [ss st].
  pose proof TSOPCREL as [tp [sp REL]]. inversion REL; subst.
  pose proof (SR t) as SRt; simpl in SRt. rewrite CS in SRt.
  destruct (st ! t) as [s0|] _eqn : Estt; simpl in SRt; [|done].
  inv SRt.
  destruct (sim sge tge ge_rel _ _ _ _ _ _ _ TS SR0) as [SERR | FRSIM].

  (* Error or stuck *)
  left. eby eapply error_to_tso.

  (* Free simulation *)
  destruct (unbuffer_safe_to_buffer_safe_for_mem2 _ t US) as [tm'' ABt''].
  simpl in ABt''. rewrite tupdate_s, apply_buffer_app, ABt in ABt''.
  simpl in ABt''. destruct (free_ptr p k tm') as [tmx|] _eqn : F; [|done]. 
  inv ABt''.
  destruct (non_stack_or_stack k) as [NS | ->].
    (* Non-stack free *)
    assert(FSM:  exists ss' : St slts,
                taustep slts s0 (TEmem (MEfree p k)) ss' /\
                st_rel sge tge s' tp' tm' ss' sp').
      by destruct k.
    destruct FSM as [ss' ([s1 (TAU & ST')] & SR')].
    destruct (taustar_to_tso ss Estt TAU) as [st1 (TAUs & OS & Es1)].
    assert(FS: tso_fin_sup (buffer_insert ss t (BufferedFree p k))).
      apply tso_fin_sup_tupdate. 
      by pose proof (TSO.tso_cons_impl_fin_sup _ _ TCs).
    destruct (unbuffer_safe_dec _ FS) as [US'|NUS].
    2: edestruct (TSO.taustep_free_fail _ sge ST' NUS Es1) as (? & ? & ? & ?); 
         [eby eapply Comp.taustar_preserves_consistency|];
       left; eexists; split; [eby eapply taustar_trans|];
       eby eexists; exists (Evisible Efail).
    assert (TS' : taustep stso_lts (ss, st) Etau
      (buffer_insert ss t (BufferedFree p k), st1 ! t <- ss')).
      eexists. split. edone.
      eby eapply Comp.step_ord; vauto. 
    right; left.
    eexists. 
    split. edone.
    exists tp; exists sp. 
    assert (BIIR: buffer_item_irrelevant (BufferedFree p k)).
      by destruct k.
    econstructor. 
    - simpl.
      inv TREL; econstructor; try edone.
      intros t'. specialize (BR t'). simpl in BR.
      destruct (peq t' t) as [-> | N]; unfold buffer_insert; simpl.
        rewrite !tupdate_s.
        eapply buffers_related_suffix; try edone.
        eby eapply buffers_related_irrelevant; vauto.
      by rewrite !tupdate_o. 
    - eby eapply Comp.taustep_preserves_consistency.
    - eby eapply Comp.step_preserves_consistency; 
      [eapply Comp.step_ord; vauto|]. 
    intro t'; simpl; destruct (peq t' t) as [<- | N].
      rewrite !PTree.gss, !tupdate_s.
      econstructor.
      - rewrite apply_buffer_app. rewrite ABt. simpl. 
        eby simpl; rewrite F.
      - rewrite fold_left_opt_app, PUt.
        unfold fold_left_opt, optbind.
        eby rewrite (part_update_irrelevant BIIR).
      - rewrite fold_left_opt_app, PUs.
        unfold fold_left_opt, optbind.
        eby rewrite (part_update_irrelevant BIIR).
        (* We have to show that the free does not affect local data 
           (and thus the individual thread simulation relation). *)
      - eapply (load_inv _ _ ge_rel); [|edone]. simpl in TREL.
        destruct (unbuffer_safe_to_buffer_safe_for_mem2 _ t' US') as [sm'' ABs''].
        unfold buffer_insert in ABs''; simpl in ABs''; rewrite tupdate_s in ABs''.
        rewrite apply_buffer_app in ABs''.
        destruct (apply_buffer (tso_buffers ss t') (tso_mem ss)) as [smi|] _eqn : ABsmi;
          [|done]; simpl in ABs''.
        destruct (free_ptr p k smi) as [smx|] _eqn:Fi; [|done]. inv ABs''.
        destruct (tso_pc_rel_unbuffer_to_empty REL ABt ABsmi PUt PUs)
          as [ts'' [ss'' [tp'' [sp'' (Etb & Esb & Etm & Esm & Etpt & Espt & ABR & REL')]]]]. subst.
        destruct (free_someD Fi) as [n RAs].
        inv REL'. inv TREL0. 
        assert (RAt : range_allocated (p, n) k (tso_mem ts'')).
          specialize (NSMR (p, n) k); unfold fst in NSMR.
          by destruct k; try apply NSMR in RAs.
        intros p' c' CI.
        destruct (chunk_inside_range_listD CI) as [rpc [IN RI]].
        rewrite (load_free_other F RAt). by destruct load_ptr.
        eapply disjoint_inside_disjoint_l, RI.
        destruct (ranges_are_disjoint (mrwp_in_alloc MRPt IN) RAt) as [[_ E]|D].
          by destruct k.
        done.
    by rewrite !tupdate_o, !PTree.gso, <- OS; eauto.
  destruct FRSIM as [n [tpx (E & FRSIM)]].
  specialize (FRSIM _ (refl_equal _)).
  destruct FRSIM as (RNI & [[ss' ([s1 (TAU & ST')] & SR')] | (SR' & ORD)]).
  (* Corresponding tau *)
  right; left.
  destruct (taustar_to_tso ss Estt TAU) as [st1 (TAUs & OS & Es1)].
  assert (TS' : taustep stso_lts (ss, st) Etau (ss, st1 ! t <- ss')).
    eexists. split. edone.
    eby eapply Comp.step_tau. 
  eexists. 
  split.
    eexists. split. edone.
    eby eapply Comp.step_tau.
  exists tp; exists sp. 
  econstructor. 
  - simpl.
    inv TREL; econstructor; try edone.
    intros t'. specialize (BR t'). simpl in BR.
    destruct (peq t' t) as [-> | N]; unfold buffer_insert; simpl.
      rewrite !tupdate_s.
      rewrite (app_nil_end (tso_buffers ss t)).
      eapply buffers_related_suffix; try edone.
      eapply buffers_related_tfree; vauto.
    by rewrite !tupdate_o.
  - eby eapply Comp.taustep_preserves_consistency.
  - eby eapply Comp.step_preserves_consistency; 
      [eapply Comp.step_ord; vauto|]. 
  intro t'; simpl; destruct (peq t' t) as [<- | N].
    rewrite !PTree.gss, tupdate_s.
    econstructor.
    - rewrite apply_buffer_app. rewrite ABt. simpl. 
      eby simpl; rewrite F.
    - rewrite fold_left_opt_app, PUt, E. simpl.
      eby destruct Ptr.eq_dec.
    - edone. 
    - done.
  by rewrite !PTree.gso, !tupdate_o, <- OS.

  (* Stutter *)
  right; right.
  split; [|eauto using st_order_to_ts_order].
  exists tp; exists sp. 
  econstructor; try done.
  - simpl.
    inv TREL; econstructor; try edone.
    intros t'. specialize (BR t'). simpl in BR.
    destruct (peq t' t) as [-> | N]; unfold buffer_insert; simpl.
      rewrite !tupdate_s.
      rewrite (app_nil_end (tso_buffers ss t)).
      eapply buffers_related_suffix; try edone.
      eapply buffers_related_tfree; vauto.
    by rewrite !tupdate_o.
  - eby eapply Comp.step_preserves_consistency; 
      [eapply Comp.step_ord; vauto|]. 
  intro t'; simpl; destruct (peq t' t) as [<- | N].
    rewrite !PTree.gss, tupdate_s, Estt.
    econstructor.
    - rewrite apply_buffer_app. rewrite ABt. simpl. 
      eby simpl; rewrite F.
    - rewrite fold_left_opt_app, PUt, E. simpl.
      eby destruct Ptr.eq_dec.
    - edone. 
    - done.
  by rewrite !PTree.gso, !tupdate_o.
Qed.

Lemma free_fail_sim:
  forall s s' (tt : PTree.t Tgt.(SEM_ST)) t sst ts ts' p k
    (ST : Tgt.(SEM_step) tge s (TEmem (MEfree p k)) s')
    (TS : tso_step ts (MMfreefail t p k) ts')
    (CS : tt ! t = Some s)
    (TSOPCREL : tso_pc_related (ts, tt) sst),
      can_reach_error sst.
Proof.
  intros. destruct sst as [ss st].
  pose proof TSOPCREL as [tp [sp REL]]. inversion REL; subst.
  pose proof (SR t) as SRt; simpl in SRt. rewrite CS in SRt.
  destruct (st ! t) as [s0|] _eqn : Estt; simpl in SRt; [|done].
  inv SRt.
  inv TS.

  destruct (sim sge tge ge_rel _ _ _ _ _ _ _ ST SR0) as [SERR | FRSIM].

  (* Error or stuck *)
  eby eapply error_to_tso.

  (* Free can be on stack or heap *)
  destruct (non_stack_or_stack k) as [NS | ->].
    (* Heap free *)
    assert(FSM:  exists ss' : St slts,
                taustep slts s0 (TEmem (MEfree p k)) ss' /\
                st_rel sge tge s' tp' tm' ss' sp').
      by destruct k.
    destruct FSM as [ss' ([s1 (TAU & ST')] & SR')].
    destruct (taustar_to_tso ss Estt TAU) as [st1 (TAUs & OS & Es1)].
    assert(FS: tso_fin_sup (buffer_insert ss t (BufferedFree p k))).
      apply tso_fin_sup_tupdate. 
      by pose proof (TSO.tso_cons_impl_fin_sup _ _ TCs).
    destruct (unbuffer_safe_dec _ FS) as [US'|NUS].
    2: edestruct (TSO.taustep_free_fail _ sge ST' NUS Es1) as (? & ? & ? & ?); 
         [eby eapply Comp.taustar_preserves_consistency|];
       eexists; split; [eby eapply taustar_trans|];
       eby eexists; exists (Evisible Efail).
    assert (BIIR: buffer_item_irrelevant (BufferedFree p k)).
      by destruct k.
    exploit (unbuffer_safety_rev_write_free_gen t 
      (buffer_insert ts' t (BufferedFree p k)) ts' 
      (buffer_insert ss t (BufferedFree p k))
      (BufferedFree p k::nil)); try done.
    - eapply fin_sup_buffer_insert, TSO.buffer_cons_impl_fin_sup. 
      instantiate (1 := tt).
      by red; simpl; intros ? XX; eapply TCt; simpl; rewrite PTree.gmap, XX.
    - eapply (tso_related_witt_fw_intro _ _ tp sp). 
      by destruct TCs.
      inv TREL; constructor; try done.
      (* Buffer relation *)
      intros t'. specialize (BR t'). simpl in BR.
      destruct (peq t' t) as [-> | N]; unfold buffer_insert; simpl.
        rewrite !tupdate_s.
        eapply buffers_related_suffix; try edone.
        by eapply buffers_related_irrelevant; vauto.
      by rewrite !tupdate_o. 
    - by destruct TCt.
    - by intros bi [<- | IN].
    - by unfold buffer_insert; simpl; rewrite tupdate_s.
    - by intros t' N; unfold buffer_insert; simpl; rewrite tupdate_o.
  (* show contradiction *)
  clear FRSIM BIIR.
  simpl in *; rewrite Bemp in *; simpl in *; clarify.
  inversion 1.
  exploit (ABIS t); simpl; [by rewrite tupdate_s, Bemp|intros [? ?]].
  simpl in *; destruct (free_ptr p k (tso_mem ts')) as [] _eqn: FREE; clarify; des.
  exploit (UNBS t); simpl; [by rewrite tupdate_s, Bemp|by apply FREE|]; simpl. 
  rewrite tupdate_red.
  inversion 1; clarify; simpl in *.
  exploit (ABIS0 tid'); simpl; [rewrite tupdate_o; try edone; congruence|intros [? ?]].
  by simpl in *; clarify'.

  (* Free stack *)
  destruct FRSIM as [n [tpx (E & FRSIM)]].
  assert (RAt : range_allocated (p, n) MObjStack tm').
    destruct (unbuffer_safe_to_buffer_safe_for_mem2 _ t (proj2 TCs)) as [sm' ABs'].
    destruct (tso_pc_rel_unbuffer_to_empty REL ABt ABs' PUt PUs)
      as [ts'' [ss'' [tp'' [sp'' (Etb & Esb & Etm & Esm & Etpt & Espt & ABR & REL')]]]]. subst.
    inv REL'. inv TREL0.
    assert (IN: In (p, n) (tp'' t)). by rewrite Etpt; left.
    apply (mrwp_in_alloc MRPt IN).
  destruct (free_ptr p MObjStack tm') as [tmi|] _eqn:F;
    [|by elim (free_noneD F n)].
  destruct (FRSIM _ (refl_equal _)) as (RNI & S).
  
  exploit (unbuffer_safety_rev_write_free_gen t 
    (buffer_insert ts' t (BufferedFree p MObjStack)) ts' ss 
    (BufferedFree p MObjStack::nil)); try done.
  - eapply fin_sup_buffer_insert, TSO.buffer_cons_impl_fin_sup. 
    instantiate (1 := tt).
    by red; simpl; intros ? XX; eapply TCt; simpl; rewrite PTree.gmap, XX.
  - eapply (tso_related_witt_fw_intro _ _ tp sp). 
    by destruct TCs.
    inv TREL; constructor; try done.
    (* Buffer relation *)
    intros t'. specialize (BR t'). simpl in BR.
    destruct (peq t' t) as [-> | N]; unfold buffer_insert; simpl.
      rewrite tupdate_s.
      rewrite (app_nil_end (tso_buffers ss t)).
      eapply buffers_related_suffix; try edone.
      by eapply buffers_related_tfree; try edone; vauto.
    by rewrite tupdate_o.
  - by destruct TCt.
  - by intros bi [<- | IN].
  - by unfold buffer_insert; simpl; rewrite tupdate_s.
  - by intros t' N; unfold buffer_insert; simpl; rewrite tupdate_o.
  (* show contradiction *)
  simpl in *; rewrite Bemp in *; simpl in *; clarify.
  clear S; rewrite F in *; clarify; des.
  inversion 1; clarify; simpl in *.
  exploit (UNBS t); simpl; [by rewrite tupdate_s, Bemp|edone|]; simpl.
  rewrite tupdate_red.
  inversion 1; clarify; simpl in *.
  exploit (ABIS0 tid'); simpl; [rewrite tupdate_o; try edone; congruence|intros [? ?]].
  by simpl in *; clarify'.
Qed.

Lemma alloc_sim:
  forall s s' (tt : PTree.t Tgt.(SEM_ST)) t sst ts p n k
    (TS : Tgt.(SEM_step) tge s (TEmem (MEalloc p n k)) s')
    (CS : tt ! t = Some s)
    (US : unbuffer_safe (buffer_insert ts t (BufferedAlloc p n k)))
    (TSOPCREL : tso_pc_related (ts, tt) sst),
      can_reach_error sst \/
      (exists sst',
         taustep stso_lts sst Etau sst' /\ 
         tso_pc_related (buffer_insert ts t (BufferedAlloc p n k), tt ! t <- s') sst') \/
      tso_pc_related (buffer_insert ts t (BufferedAlloc p n k), tt ! t <- s') sst /\
      tso_order (buffer_insert ts t (BufferedAlloc p n k), tt ! t <- s') (ts, tt).
Proof.
  intros. destruct sst as [ss st].
  pose proof TSOPCREL as [tp [sp REL]]. inversion REL; subst.
  pose proof (SR t) as SRt; simpl in SRt. rewrite CS in SRt.
  destruct (st ! t) as [s0|] _eqn : Estt; simpl in SRt; [|done].
  inv SRt.
  destruct (sim sge tge ge_rel _ _ _ _ _ _ _ TS SR0) as [SERR | ALSIM].

  (* Error or stuck *)
  left. eby eapply error_to_tso.

  (* Alloc simulation *)
  destruct (unbuffer_safe_to_buffer_safe_for_mem2 _ t US) as [tm'' ABt''].
  simpl in ABt''. rewrite tupdate_s, apply_buffer_app, ABt in ABt''.
  simpl in ABt''. destruct (alloc_ptr (p, n) k tm') as [tmx|] _eqn : A; [|done]. 
  inv ABt''.
  destruct (non_stack_or_stack k) as [NS | ->].
    (* Non-stack free *)
    assert(ASM:  exists ss' : St slts,
                taustep slts s0 (TEmem (MEalloc p n k)) ss' /\
                st_rel sge tge s' tp' tm' ss' sp').
      by destruct k. 
    destruct ASM as [ss' ([s1 (TAU & ST')] & SR')].
    destruct (taustar_to_tso ss Estt TAU) as [st1 (TAUs & OS & Es1)].
    (* assert(FS: tso_fin_sup (buffer_insert ss t (BufferedAlloc p n k))).
      apply tso_fin_sup_tupdate. 
      by pose proof (TSO.tso_cons_impl_fin_sup _ _ TCs).
    destruct FS as [l [ND DOM]]. *)
    assert (BIIR: buffer_item_irrelevant (BufferedAlloc p n k)).
      by destruct k.
    assert (R: tso_related_witt_sf 
      (buffer_insert ts t (BufferedAlloc p n k)) tp
      (buffer_insert ss t (BufferedAlloc p n k)) sp).
      constructor. by destruct TCt.
        pose proof (TSO.tso_cons_impl_fin_sup _ _ TCs).
        by apply fin_sup_buffer_insert.
      inversion TREL; subst.
      constructor; try done; [].
      intros t'. specialize (BR t'). simpl in BR.
      destruct (peq t' t) as [-> | N]; unfold buffer_insert; simpl.
        rewrite !tupdate_s.
        eapply buffers_related_suffix; try edone.
        by eapply buffers_related_irrelevant; try edone; vauto. 
      by rewrite !tupdate_o. 
    assert(US': unbuffer_safe (buffer_insert ss t (BufferedAlloc p n k))).
      eapply alloc_unbuffer_safe with (t := t).
      - vauto.
      - apply (proj2 TCs). 
      - eby right; reflexivity.
      - eby unfold buffer_insert; simpl; rewrite tupdate_s.
      - by intros t' N; unfold buffer_insert; simpl; rewrite tupdate_o.
      - done.
    assert (TS' : taustep stso_lts (ss, st) Etau 
      (buffer_insert ss t (BufferedAlloc p n k), st1 ! t <- ss')).
      eexists. split. edone.
      eby eapply Comp.step_ord; vauto. 
    right; left.
    eexists. 
    split. edone.
    exists tp; exists sp. 
    econstructor. 
    - simpl.
      inv TREL; econstructor; try edone.
      intros t'. specialize (BR t'). simpl in BR.
      destruct (peq t' t) as [-> | N]; unfold buffer_insert; simpl.
        rewrite !tupdate_s.
        eapply buffers_related_suffix; try edone.
        eby eapply buffers_related_irrelevant; vauto.
      by rewrite !tupdate_o. 
    - eby eapply Comp.taustep_preserves_consistency.
    - eby eapply Comp.step_preserves_consistency; 
      [eapply Comp.step_ord; vauto|]. 
    intro t'; simpl; destruct (peq t' t) as [<- | N].
      rewrite !PTree.gss, !tupdate_s.
      econstructor.
      - rewrite apply_buffer_app. rewrite ABt. simpl. 
        eby simpl; rewrite A.
      - rewrite fold_left_opt_app, PUt.
        unfold fold_left_opt, optbind.
        eby rewrite (part_update_irrelevant BIIR).
      - rewrite fold_left_opt_app, PUs.
        unfold fold_left_opt, optbind.
        eby rewrite (part_update_irrelevant BIIR).
        (* We have to show that the free does not affect local data 
           (and thus the individual thread simulation relation). *)
      - eapply (load_inv _ _ ge_rel); [|edone]. simpl in TREL.
        destruct (unbuffer_safe_to_buffer_safe_for_mem2 _ t' US') as [sm'' ABs''].
        unfold buffer_insert in ABs''; simpl in ABs''; rewrite tupdate_s in ABs''.
        rewrite apply_buffer_app in ABs''.
        destruct (apply_buffer (tso_buffers ss t') (tso_mem ss)) as [smi|] _eqn : ABsmi;
          [|done]; simpl in ABs''.
        destruct (alloc_ptr (p, n) k smi) as [smx|] _eqn:Ai; [|done]. inv ABs''.
        destruct (tso_pc_rel_unbuffer_to_empty REL ABt ABsmi PUt PUs)
          as [ts'' [ss'' [tp'' [sp'' (Etb & Esb & Etm & Esm & Etpt & Espt & ABR & REL')]]]]. subst.
        inv REL'. inv TREL0. 
        (* assert (RAt : range_allocated (p, n) k (tso_mem ts'')).
          specialize (NSMR (p, n) k); unfold fst in NSMR.
          by destruct k; try apply NSMR in RAs. *)
        intros p' c' CI.
        destruct (chunk_inside_range_listD CI) as [rpc [IN RI]].
        rewrite (load_alloc_other A). by destruct load_ptr.
        eapply ranges_disjoint_comm, disjoint_inside_disjoint_r, RI.
        destruct (alloc_someD A) as (_ & _ & _ & ONA).
        destruct (ranges_disjoint_dec (p, n) rpc) as [D|O]; [done|].
        eelim ONA. edone. 
        eby apply (mrwp_in_alloc MRPt IN).
    by rewrite !tupdate_o, !PTree.gso, <- OS; eauto.
  specialize (ALSIM _ (refl_equal _)).
  destruct (alloc_someD A) as (_ & VAR & _ & ONA).
  assert(RNI: range_not_in (p, n) tp').
    destruct (unbuffer_safe_to_buffer_safe_for_mem2 _ t (proj2 TCs)) as [sm' ABs'].
    destruct (tso_pc_rel_unbuffer_to_empty REL ABt ABs' PUt PUs)
      as [ts'' [ss'' [tp'' [sp'' (Etb & Esb & Etm & Esm & Etpt & Espt & ABR & REL')]]]]. subst.
    inv REL'. inv TREL0.
    intros r IN.
    destruct (ranges_disjoint_dec (p, n) r) as [D|O]; [done|].
    eelim ONA. edone. 
    apply (mrwp_in_alloc MRPt IN).
  destruct ALSIM as [[ss' ([s1 (TAU & ST')] & SR')] | (SR' & ORD)].
  (* Corresponding tau *)
  right; left.
  destruct (taustar_to_tso ss Estt TAU) as [st1 (TAUs & OS & Es1)].
  assert (TS' : taustep stso_lts (ss, st) Etau (ss, st1 ! t <- ss')).
    eexists. split. edone.
    eby eapply Comp.step_tau. 
  eexists. 
  split. edone.
  exists tp; exists sp. 
  econstructor. 
  - simpl.
    inv TREL; econstructor; try edone.
    intros t'. specialize (BR t'). simpl in BR.
    destruct (peq t' t) as [-> | N]; unfold buffer_insert; simpl.
      rewrite !tupdate_s.
      rewrite (app_nil_end (tso_buffers ss t)).
      eapply buffers_related_suffix; try edone.
      eapply buffers_related_talloc; vauto.
    by rewrite !tupdate_o.
  - eby eapply Comp.taustep_preserves_consistency.
  - eby eapply Comp.step_preserves_consistency; 
      [eapply Comp.step_ord; vauto|]. 
  intro t'; simpl; destruct (peq t' t) as [<- | N].
    rewrite !PTree.gss, tupdate_s.
    econstructor.
    - rewrite apply_buffer_app. rewrite ABt. simpl. 
      eby simpl; rewrite A.
    - rewrite fold_left_opt_app, PUt. simpl.
      destruct valid_alloc_range_dec; [|done].
      destruct range_in_dec as [[r' [IN RO]]|RI].
        by specialize (RNI r' IN).
      edone.
    - edone. 
    - done.
  by rewrite !PTree.gso, !tupdate_o, <- OS.

  (* Stutter *)
  right; right.
  split; [|eauto using st_order_to_ts_order].
  exists tp; exists sp. 
  econstructor; try done.
  - simpl.
    inv TREL; econstructor; try edone.
    intros t'. specialize (BR t'). simpl in BR.
    destruct (peq t' t) as [-> | N]; unfold buffer_insert; simpl.
      rewrite !tupdate_s.
      rewrite (app_nil_end (tso_buffers ss t)).
      eapply buffers_related_suffix; try edone.
      eapply buffers_related_talloc; vauto.
    by rewrite !tupdate_o.
  - eby eapply Comp.step_preserves_consistency; 
      [eapply Comp.step_ord; vauto|]. 
  intro t'; simpl; destruct (peq t' t) as [<- | N].
    rewrite !PTree.gss, tupdate_s, Estt.
    econstructor.
    - rewrite apply_buffer_app. rewrite ABt. simpl. 
      eby simpl; rewrite A.
    - rewrite fold_left_opt_app, PUt. simpl.
      destruct valid_alloc_range_dec; [|done].
      destruct range_in_dec as [[r' [IN RO]]|RI].
        by specialize (RNI r' IN).
      edone.
    - edone. 
    - done.
  by rewrite !PTree.gso, !tupdate_o.
Qed.

Lemma read_sim:
  forall s s' (tt : PTree.t Tgt.(SEM_ST)) t sst ts c p v m
    (TS : Tgt.(SEM_step) tge s (TEmem (MEread p c v)) s')
    (CS : tt ! t = Some s)
    (AB : apply_buffer (ts.(tso_buffers) t) ts.(tso_mem) = Some m)
    (LP : load_ptr c m p = Some v)
    (TSOPCREL : tso_pc_related (ts, tt) sst),
      can_reach_error sst \/
      (exists sst',
         taustep stso_lts sst Etau sst' /\ 
         tso_pc_related (ts, tt ! t <- s') sst') \/
      tso_pc_related (ts, tt ! t <- s') sst /\
      tso_order (ts, tt ! t <- s') (ts, tt).
Proof.
  intros. destruct sst as [ss st].
  pose proof TSOPCREL as [tp [sp REL]]. inversion REL; subst.
  pose proof (SR t) as SRt; simpl in SRt. rewrite CS in SRt.
  destruct (st ! t) as [s0|] _eqn : Estt; simpl in SRt; [|done].
  inv SRt.
  simpl in *.
  rewrite ABt in AB. inv AB.
  destruct (unbuffer_safe_to_buffer_safe_for_mem2 _ t (proj2 TCs)) as [sm' ABs'].
  destruct (tso_pc_rel_unbuffer_to_empty REL ABt ABs' PUt PUs)
    as [ts'' [ss'' [tp'' [sp'' (Etb & Esb & Etm & Esm & Etpt & Espt & ABR & REL')]]]]. subst.

  destruct (sim sge tge ge_rel _ _ _ _ _ _ _ TS SR0) as 
    [SERR | 
    [(CI & RNI & SUCC & LD) | 
     LSIM]].

  (* Error or stuck *)
  left. eby eapply error_to_tso.

  (* Local load *)
  destruct (LD LP) as      
    [[ss' ([s1 (TAU & ST')] & SR')] | [(SR' & ORD) | SERR]].
  (* Tau-step *)
  right; left.
  destruct (taustar_to_tso ss Estt TAU) as [st1 (TAUs & OS & Es1)].
  assert (TS' : taustep stso_lts (ss, st) Etau (ss, st1 ! t <- ss')).
    eexists. split. edone.
    eby eapply Comp.step_tau. 
  eexists. 
  split. edone.
  exists tp; exists sp. econstructor. 
  - done.
  - eby eapply Comp.taustep_preserves_consistency.
  - eby eapply Comp.step_preserves_consistency; 
      [eapply Comp.step_ord; vauto|].
  intro t'; simpl; destruct (peq t' t) as [<- | N].
    rewrite !PTree.gss. vauto.
  by rewrite !PTree.gso, <- OS.
  (* Stutter *)
  right; right.
  split. 
  exists tp; exists sp. econstructor; try done.
  - eby eapply Comp.step_preserves_consistency; 
      [eapply Comp.step_ord; vauto|].
  intro t'; simpl; destruct (peq t' t) as [<- | N].
    rewrite !PTree.gss, Estt. vauto.
  by rewrite !PTree.gso.
  eauto using st_order_to_ts_order.

  (* Error again??? This should not be necessary? *)
  left. eby eapply error_to_tso.

  (* Load from shared data *)
  inv REL'. inv TREL0. simpl in *. specialize (LR p c). rewrite LP in LR.
  destruct (load_ptr c (tso_mem ss'') p) as [v'|] _eqn : L'. 
    (* Load succeeded -> use the simulation *)
    destruct (LSIM _ LR) as [ss' ([s1 (TAU & ST')] & SR')].
    destruct (taustar_to_tso ss Estt TAU) as [st1 (TAUs & OS & Es1)].
    assert (TS' : taustep stso_lts (ss, st) Etau (ss, st1 ! t <- ss')).
      eexists. split. edone.
      eby eapply Comp.step_ord; vauto. 
    right; left.
    eexists. 
    split. edone.
    exists tp; exists sp. econstructor. 
    - done.
    - eby eapply Comp.taustep_preserves_consistency.
    - eby eapply Comp.step_preserves_consistency; 
        [eapply Comp.step_ord; vauto|].
    intro t'; simpl; destruct (peq t' t) as [<- | N].
      rewrite !PTree.gss. vauto.
    by rewrite !PTree.gso, <- OS.
  (* Load fails -> can fail in source *)
  left. exploit LSIM. apply Val.lessdef_refl.
  intros [ss' ([s1 (TAU & ST')] & SR')].
  destruct (taustar_to_tso ss Estt TAU) as [st1 (TAUs & OS & Es1)].
  eexists. split. eapply taustar_trans. edone. 
    eby eapply TSO.apply_buffer_reachable_taustar. 
  eexists. exists (Evisible Efail). split. done.
  eapply Comp.step_read_fail; try edone; vauto.
Qed.

Lemma read_fail_sim:
  forall s s' (tt : PTree.t Tgt.(SEM_ST)) t sst ts ts' c p v
    (ST : Tgt.(SEM_step) tge s (TEmem (MEread p c v)) s')
    (TS : tso_step ts (MMreadfail t p c) ts')
    (CS : tt ! t = Some s)
    (TSOPCREL : tso_pc_related (ts, tt) sst),
      can_reach_error sst.
Proof.
  intros. destruct sst as [ss st].
  pose proof TSOPCREL as [tp [sp REL]]. inversion REL; subst.
  pose proof (SR t) as SRt; simpl in SRt. rewrite CS in SRt.
  destruct (st ! t) as [s0|] _eqn : Estt; simpl in SRt; [|done].
  inv SRt.
  simpl in *.
  inv TS. rewrite Bemp in ABt. inv ABt.
  destruct (unbuffer_item_preserves_tso_pc_witt_empty _ _ _ _ _ _ _ Bemp REL)
    as [sm'' [sp'' [ss'' (ABs & ABR & Espt & Esm & Esb & REL')]]]. subst.

  destruct (sim sge tge ge_rel _ _ _ _ _ _ _ ST SR0) as 
    [SERR | [(CI & RNI & SUCC & LDSIM) | LSIM]].

  (* Error or stuck *)
  eby eapply error_to_tso.

  (* Local load *)
  by rewrite LD in SUCC.

  (* Load from shared data *)
  inv REL'. inv TREL0. simpl in *. specialize (LR p c). rewrite LD in LR.
  destruct (load_ptr c (tso_mem ss'') p) as [v'|] _eqn : L'; [done|].
  exploit LSIM. apply Val.lessdef_refl.
  intros [ss' ([s1 (TAU & ST')] & SR')].
  destruct (taustar_to_tso ss Estt TAU) as [st1 (TAUs & OS & Es1)].
  eexists. split. eapply taustar_trans. edone. eby eapply TSO.apply_buffer_reachable_taustar. 
  eexists. exists (Evisible Efail). split. done.
  eapply Comp.step_read_fail; try edone; vauto.
Qed.

Lemma ext_eq:
  forall {t largs ts args ts' vargs evargs tm'}
  (AB : apply_buffer (tso_buffers ts t) (tso_mem ts) = Some tm')
  (TS : Comp.mm_ext_arglist tso_mm ts t largs args ts')
  (MAL : mem_arglist tm' (map val_of_eval_memarg largs) = Some vargs)
  (MVE : map val_of_eval evargs = vargs),
    evargs = args.
Proof.
  intros. revert vargs evargs args TS MAL MVE.
  induction largs as [|h largs IH]; intros.
  
  (* Base case *)
  inv TS. by destruct evargs.

  (* Step case *)
  unfold mem_arglist in *.
  inv TS.
    simpl in MAL.
    destruct (map_olist (mem_arg tm') (map val_of_eval_memarg largs)) 
      as [vals'|]; [|done].
    simpl in MAL. destruct evargs. done. inv MAL.
    f_equal. by apply val_of_eval_eq.
    eby eapply IH. 
  inv RD. clarify'.
  simpl in MAL. rewrite LD in MAL. simpl in MAL.
  destruct (map_olist (mem_arg m') (map val_of_eval_memarg largs)) 
    as [vals'|]; [|done].
  simpl in MAL. destruct evargs. done. inv MAL.
  f_equal. by apply val_of_eval_eq.
  eby eapply IH. 
Qed.

Lemma tso_ext_arglist_eq:
  forall {ts t largs args ts'}
    (TS : Comp.mm_ext_arglist tso_mm ts t largs args ts'), ts = ts'.
Proof.
  intros; induction TS; eauto. by inv RD.
Qed.

Lemma extmem_sim:
  forall s s' (tt : PTree.t Tgt.(SEM_ST)) t sst ts ts' id largs args
    (ST : Tgt.(SEM_step) tge s (TEexternalcallmem id largs) s')
    (TS : Comp.mm_ext_arglist tso_mm ts t largs args ts')
    (CS : tt ! t = Some s)
    (TSOPCREL : tso_pc_related (ts, tt) sst),
      can_reach_error sst \/
      (exists sst',
         taustep stso_lts sst (Evisible (Ecall id args)) sst' /\ 
         tso_pc_related (ts', tt ! t <- s') sst').
Proof.
  intros. destruct sst as [ss st].
  pose proof TSOPCREL as [tp [sp REL]]. inversion REL; subst.
  pose proof (SR t) as SRt; simpl in SRt. rewrite CS in SRt.
  destruct (st ! t) as [s0|] _eqn : Estt; simpl in SRt; [|done].
  inv SRt; simpl in *.
  destruct (sim sge tge ge_rel _ _ _ _ _ _ _ ST SR0) as
    [SERR | [vargs [evargs (ARGL & MAL & MVE & [ss' ([s1 (TAU & ST')] & SR')])]]].

  (* Error *)
  left. eby eapply error_to_tso.

  (* Ext call *)
  destruct (taustar_to_tso ss Estt TAU) as [st1 (TAUs & OS & Es1)].
  rewrite (ext_eq ABt TS MAL MVE) in *.
  pose proof (tso_ext_arglist_eq TS); subst.
  assert (TS' : taustep stso_lts (ss, st) (Evisible (Ecall id args)) (ss, st1 ! t <- ss')).
    eexists. split. edone.
    eby eapply Comp.step_ext. 
  right. eexists. 
  split. edone.
  exists tp; exists sp. 
  econstructor.
  - done.
  - eby eapply Comp.taustep_preserves_consistency.
  - eby eapply Comp.step_preserves_consistency; [eapply Comp.step_extcallmem|]. 
  - intro t'; simpl; destruct (peq t' t) as [<- | N].
      by rewrite !PTree.gss; vauto.
    by rewrite !PTree.gso, <- OS.
Qed.

Lemma ext_no_fail:
  forall {t largs ts evargs vargs tm'}
  (AB : apply_buffer (tso_buffers ts t) (tso_mem ts) = Some tm')
  (TS : Comp.mm_ext_arglist_fail tso_mm ts t largs)
  (MAL : mem_arglist tm' (map val_of_eval_memarg largs) = Some vargs)
  (MVE : map val_of_eval evargs = vargs),
    False.
Proof.
  intros. revert vargs evargs TS MAL MVE.
  induction largs as [|h largs IH]; intros.
  
  (* Base case *)
  inv TS. 

  (* Step case *)
  unfold mem_arglist in *.
  inv TS; simpl in MAL.
  - inv TST. rewrite Bemp in AB. inv AB. by rewrite LD in MAL.
  - inv TST. clarify'. rewrite LD in MAL. simpl in MAL.
    destruct (map_olist (mem_arg m') (map val_of_eval_memarg largs)) 
      as [vals'|]; [|done]. simpl in MAL.
    destruct evargs; [done|]. specialize (NVOE e).
    by inv MAL.
  - destruct (map_olist (mem_arg tm') (map val_of_eval_memarg largs)) 
      as [vals'|]; [|done].
    destruct evargs; [done|]. inv MAL.
    eby eapply IH.
  - inv RD. clarify'. rewrite LD in MAL. simpl in MAL.
    destruct (map_olist (mem_arg m') (map val_of_eval_memarg largs)) 
      as [vals'|]; [|done].
    destruct evargs; [done|]. inv MAL.
    eby eapply IH.
Qed.

Lemma extmem_sim_fail:
  forall s s' (tt : PTree.t Tgt.(SEM_ST)) t sst ts id largs
    (ST : Tgt.(SEM_step) tge s (TEexternalcallmem id largs) s')
    (TS : Comp.mm_ext_arglist_fail tso_mm ts t largs)
    (CS : tt ! t = Some s)
    (TSOPCREL : tso_pc_related (ts, tt) sst),
      can_reach_error sst.
Proof.
  intros. destruct sst as [ss st].
  pose proof TSOPCREL as [tp [sp REL]]. inversion REL; subst.
  pose proof (SR t) as SRt; simpl in SRt. rewrite CS in SRt.
  destruct (st ! t) as [s0|] _eqn : Estt; simpl in SRt; [|done].
  inv SRt; simpl in *.
  destruct (sim sge tge ge_rel _ _ _ _ _ _ _ ST SR0) as
    [SERR | [vargs [evargs (ARGL & MAL & MVE & [ss' ([s1 (TAU & ST')] & SR')])]]].

  (* Error *)
  eby eapply error_to_tso.

  (* Ext call *)
  by pose proof (ext_no_fail ABt TS MAL MVE).
Qed.

Lemma start_arg_eq:
  forall {t largs ts args ts' vargs tm'}
  (AB : apply_buffer (tso_buffers ts t) (tso_mem ts) = Some tm')
  (TS : Comp.mm_arglist tso_mm ts t largs args ts')
  (MAL : mem_arglist tm' largs = Some vargs),
    args = vargs.
Proof.
  intros. revert vargs args TS MAL.
  induction largs as [|h largs IH]; intros.
  
  (* Base case *)
  inv TS. by destruct vargs.

  (* Step case *)
  unfold mem_arglist in *.
  inv TS.
    simpl in MAL.
    destruct (map_olist (mem_arg tm') largs) 
      as [vals'|]; [|done].
    simpl in MAL. destruct vargs. done. inv MAL.
    f_equal. eby eapply IH. 
  inv RD. clarify'.
  simpl in MAL. rewrite LD in MAL. simpl in MAL.
  destruct (map_olist (mem_arg m') largs) 
    as [vals'|]; [|done].
  simpl in MAL. destruct vargs. done. inv MAL.
  f_equal. eby eapply IH. 
Qed.

Lemma startmem_no_fail:
  forall {t largs ts vargs tm'}
  (AB : apply_buffer (tso_buffers ts t) (tso_mem ts) = Some tm')
  (TS : Comp.mm_arglist_fail tso_mm ts t largs)
  (MAL : mem_arglist tm' largs = Some vargs),
    False.
Proof.
  intros. revert vargs TS MAL.
  induction largs as [|h largs IH]; intros.
  
  (* Base case *)
  inv TS. 

  (* Step case *)
  unfold mem_arglist in *.
  inv TS; simpl in MAL.
  - inv TST. rewrite Bemp in AB. inv AB. by rewrite LD in MAL.
  - destruct (map_olist (mem_arg tm') largs) 
      as [vals'|]; [|done].
    destruct vargs; [done|]. inv MAL.
    eby eapply IH.
  - inv RD. clarify'. rewrite LD in MAL. simpl in MAL.
    destruct (map_olist (mem_arg m') largs)
      as [vals'|]; [|done].
    destruct vargs; [done|]. inv MAL.
    eby eapply IH.
Qed.

Lemma tso_arglist_eq:
  forall {ts t largs args ts'}
    (TS : Comp.mm_arglist tso_mm ts t largs args ts'), ts = ts'.
Proof.
  intros; induction TS; eauto. by inv RD.
Qed.

Lemma startmem_sim:
  forall s s' (tt : PTree.t Tgt.(SEM_ST)) t sst ts ts' ts'' newtid fn args sinit p vargs
    (ST : Tgt.(SEM_step) tge s (TEstartmem fn args) s')
    (TS : Comp.mm_arglist tso_mm ts t (fn::args) (Vptr p::vargs) ts')
    (TS2: tso_step ts' (MMstart t newtid) ts'')
    (CS : tt ! t = Some s)
    (FR : tt ! newtid = None)
    (INIT: Tgt.(SEM_init) tge p vargs = Some sinit)
    (TSOPCREL : tso_pc_related (ts, tt) sst),
      can_reach_error sst \/
      (exists sst',
         taustep stso_lts sst Etau sst' /\ 
         tso_pc_related (ts'', (tt ! t <- s') ! newtid <- sinit) sst').
Proof.
  intros. destruct sst as [ss st].
  pose proof TSOPCREL as [tp [sp REL]]. inversion REL; subst.
  pose proof (SR t) as SRt; simpl in SRt. rewrite CS in SRt.
  destruct (st ! t) as [s0|] _eqn : Estt; simpl in SRt; [|done].
  inv SRt; simpl in *.
  destruct (sim sge tge ge_rel _ _ _ _ _ _ _ ST SR0) as
    [SERR |
    [vfnargs [fn' [args' (ARGL & MAL & LDL & [ss' ([s1 (TAU & ST')] & SR')])]]]].

  (* Error *)
  eby left; eapply error_to_tso.

  (* Starting... *)
  destruct (taustar_to_tso ss Estt TAU) as [st1 (TAUs & OS & Es1)].
  inversion LDL as [|? fns ? argss LD' LDL']. subst. inv LD'.
  pose proof (tso_arglist_eq TS); subst.
  pose proof (start_arg_eq ABt TS MAL). subst. inv H.
  destruct (thread_init_related _ _ _ _ _ args' ge_rel INIT LDL') as [sis (SI & R)].
  assert (NE : newtid <> t). by intro E; clarify'.
  pose proof (SR newtid) as SRnewtid. rewrite FR in SRnewtid.
  destruct (st ! newtid) as [] _eqn : Ent. done. 
  destruct SRnewtid as (Etpnt & Espnt & Etbnt & Esbnt).
  assert (TS' : taustep stso_lts (ss, st) Etau 
    (mktsostate (tupdate newtid nil ss.(tso_buffers)) ss.(tso_mem), 
      (st1 ! t <- ss') ! newtid <- sis)).
    eexists. split. edone.
    eapply Comp.step_start; try edone; vauto. 
    by rewrite <- OS.
  right. eexists. 
  split. edone.
  exists tp; exists sp. 
  econstructor.
  - simpl. inv TS2. inv TREL.
    econstructor; simpl; try done.
    intros t'. unfold tupdate. destruct peq. vauto. eauto.
  - eby eapply Comp.taustep_preserves_consistency.
  - eby eapply Comp.step_preserves_consistency; [eapply Comp.step_startmem|]. 
  - inv TS2; intro t'; simpl; destruct (peq t' newtid) as [<- | N].
      rewrite !PTree.gss, !tupdate_s.
      econstructor; try edone. by rewrite Etpnt, Espnt.
    destruct (peq t' t) as [<- | Nt].
      repeat (rewrite PTree.gso, ?PTree.gss); try done; [].
      rewrite !tupdate_o; try done; []. vauto.
    by rewrite !PTree.gso, !tupdate_o, <- OS.
Qed.

Lemma startmem_sim_fail:
  forall s s' (tt : PTree.t Tgt.(SEM_ST)) t sst ts ts' fn args vfn vargs
    (ST : Tgt.(SEM_step) tge s (TEstartmem fn args) s')
    (TS : Comp.mm_arglist tso_mm ts t (fn::args) (vfn::vargs) ts')
    (CS : tt ! t = Some s)
    (INIT: match vfn with Vptr p => Tgt.(SEM_init) tge p vargs = None 
                       | _ => True end)
    (TSOPCREL : tso_pc_related (ts, tt) sst),
      can_reach_error sst.
Proof.
  intros. destruct sst as [ss st].
  pose proof TSOPCREL as [tp [sp REL]]. inversion REL; subst.
  pose proof (SR t) as SRt; simpl in SRt. rewrite CS in SRt.
  destruct (st ! t) as [s0|] _eqn : Estt; simpl in SRt; [|done].
  inv SRt; simpl in *.
  destruct (sim sge tge ge_rel _ _ _ _ _ _ _ ST SR0) as
    [SERR |
    [vfnargs [fn' [args' (ARGL & MAL & LDL & [ss' ([s1 (TAU & ST')] & SR')])]]]].

  (* Error *)
  eby eapply error_to_tso.

  (* Start fail... *)
  destruct (taustar_to_tso ss Estt TAU) as [st1 (TAUs & OS & Es1)].
  inversion LDL as [|? fns ? argss LD' LDL']. subst. inv LD'.
  pose proof (tso_arglist_eq TS); subst.
  pose proof (start_arg_eq ABt TS MAL). inv H.
  pose proof (thread_init_related_none _ _ _ _ args' ge_rel INIT LDL') as SFAIL.
  by eexists (_, _); split; eauto; eexists; exists (Evisible Efail); split; vauto.
Qed.

Lemma startmem_sim_read_fail:
  forall s s' (tt : PTree.t Tgt.(SEM_ST)) t sst ts fn args
    (ST : Tgt.(SEM_step) tge s (TEstartmem fn args) s')
    (TS:  Comp.mm_arglist_fail tso_mm ts t (fn::args))
    (CS : tt ! t = Some s)
    (TSOPCREL : tso_pc_related (ts, tt) sst),
      can_reach_error sst.
Proof.
  intros. destruct sst as [ss st].
  pose proof TSOPCREL as [tp [sp REL]]. inversion REL; subst.
  pose proof (SR t) as SRt; simpl in SRt. rewrite CS in SRt.
  destruct (st ! t) as [s0|] _eqn : Estt; simpl in SRt; [|done].
  inv SRt; simpl in *.
  destruct (sim sge tge ge_rel _ _ _ _ _ _ _ ST SR0) as
    [SERR |
    [vfnargs [fn' [args' (ARGL & MAL & LDL & [ss' ([s1 (TAU & ST')] & SR')])]]]].

  (* Error *)
  eby eapply error_to_tso.

  (* Start failure not possible *)
  by pose proof (startmem_no_fail ABt TS MAL).
Qed.

Lemma exit_sim:
  forall s s' (tt : PTree.t Tgt.(SEM_ST)) t sst ts ts'
    (ST : Tgt.(SEM_step) tge s TEexit s')
    (TS : tso_step ts (MMexit t) ts')
    (CS : tt ! t = Some s)
    (TSOPCREL : tso_pc_related (ts, tt) sst),
      can_reach_error sst \/
      (exists sst',
         taustep stso_lts sst Etau sst' /\ 
         tso_pc_related (ts', PTree.remove t tt) sst').
Proof.
  intros. destruct sst as [ss st].
  pose proof TSOPCREL as [tp [sp REL]]. inversion REL; subst.
  pose proof (SR t) as SRt; simpl in SRt. rewrite CS in SRt.
  destruct (st ! t) as [s0|] _eqn : Estt; simpl in SRt; [|done].
  inv SRt; simpl in *.
  destruct (sim sge tge ge_rel _ _ _ _ _ _ _ ST SR0) as
    [SERR | [ss' ([s1 (TAU & ST')] & ETP & ESP)]].

  (* Error *)
  eby left; eapply error_to_tso.

  (* Starting... *)
  destruct (taustar_to_tso ss Estt TAU) as [st1 (TAUs & OS & Es1)].
  inv TS.
  destruct (unbuffer_item_preserves_tso_pc_witt_empty _ _ _ _ _ _ _ Bemp REL)
    as [sm'' [sp'' [ss'' (ABs & ABR & Espt & Esm & Esb & REL')]]].
  inv REL'.
  assert (TS' : taustep stso_lts (ss, st) Etau (ss'', PTree.remove t st1)).
    eexists. split. eapply taustar_trans. edone. eby eapply TSO.apply_buffer_reachable_taustar.
    by eapply Comp.step_exit; try edone; vauto. 
  right. eexists. 
  split. edone.
  exists tp; exists sp''. 
  econstructor; try done.
  - eby eapply Comp.taustep_preserves_consistency.
  - eby eapply Comp.step_preserves_consistency; [eapply Comp.step_exit; vauto|]. 
  - simpl. intro t'. destruct (peq t' t) as [<- | N].
      rewrite !PTree.grs. simpl.
      rewrite PUs in Espt. inv Espt. rewrite Bemp in *. inv PUt.
      by rewrite Esb. 
    by rewrite !PTree.gro, <- OS.
Qed.


Lemma ext_sim:
  forall s s' (tt : PTree.t Tgt.(SEM_ST)) t sst ts ev
    (ST : Tgt.(SEM_step) tge s (TEext ev) s')
    (CS : tt ! t = Some s)
    (TSOPCREL : tso_pc_related (ts, tt) sst),
      can_reach_error sst \/
      (exists sst' ,
         taustep stso_lts sst (Evisible ev) sst' /\ 
         tso_pc_related (ts, tt ! t <- s') sst').
Proof.
  intros. destruct sst as [ss st].
  pose proof TSOPCREL as [tp [sp REL]]. inversion REL; subst.
  pose proof (SR t) as SRt; simpl in SRt. rewrite CS in SRt.
  destruct (st ! t) as [s0|] _eqn : Estt; simpl in SRt; [|done].
  inv SRt; simpl in *.

  assert (SES: same_ev_simulation (SEM_ST Src) (SEM_ST Tgt) 
            (SEM_step Src sge) (st_rel sge tge) s0 s' tm' sp' tp' 
            (TEext ev)).
    pose proof (sim sge tge ge_rel _ _ _ _ _ _ _ ST SR0).
    by destruct ev.
  destruct SES as [SERR | [ss' ([s1 (TAU & ST')] & SR')]].

  (* Error *)
  left. eby eapply error_to_tso.

  (* Ext call *)
  destruct (taustar_to_tso ss Estt TAU) as [st1 (TAUs & OS & Es1)].
  assert (TS' : taustep stso_lts (ss, st) (Evisible ev)
                                 (ss, st1 ! t <- ss')).
    eexists. split. edone.
    eby eapply Comp.step_ext. 
  right. eexists. 
  split. edone.
  exists tp; exists sp. 
  econstructor.
  - done.
  - eby eapply Comp.taustep_preserves_consistency.
  - eby eapply Comp.step_preserves_consistency; [eapply Comp.step_ext|]. 
  - intro t'; simpl; destruct (peq t' t) as [<- | N].
      by rewrite !PTree.gss; vauto.
    by rewrite !PTree.gso, <- OS.
Qed.

Lemma start_sim:
  forall s s' (tt : PTree.t Tgt.(SEM_ST)) t sst ts ts' newtid fn args sinit
    (ST : Tgt.(SEM_step) tge s (TEstart fn args) s')
    (TS2: tso_step ts (MMstart t newtid) ts')
    (CS : tt ! t = Some s)
    (FR : tt ! newtid = None)
    (INIT: Tgt.(SEM_init) tge fn args = Some sinit)
    (TSOPCREL : tso_pc_related (ts, tt) sst),
      can_reach_error sst \/
      (exists sst',
         taustep stso_lts sst Etau sst' /\ 
         tso_pc_related (ts', (tt ! t <- s') ! newtid <- sinit) sst').
Proof.
  intros. destruct sst as [ss st].
  pose proof TSOPCREL as [tp [sp REL]]. inversion REL; subst.
  pose proof (SR t) as SRt; simpl in SRt. rewrite CS in SRt.
  destruct (st ! t) as [s0|] _eqn : Estt; simpl in SRt; [|done].
  inv SRt; simpl in *.
  destruct (sim sge tge ge_rel _ _ _ _ _ _ _ ST SR0) as
    [SERR | 
    [ss' ([s1 (TAU & ST')] & SR')]].

  (* Error *)
  eby left; eapply error_to_tso.

  (* Starting... *)
  destruct (taustar_to_tso ss Estt TAU) as [st1 (TAUs & OS & Es1)].
  destruct (thread_init_related _ _ _ _ _ _ ge_rel INIT 
    (Val.lessdef_list_refl _)) as [sis (SI & R)].
  assert (NE : newtid <> t). by intro E; clarify'.
  pose proof (SR newtid) as SRnewtid. rewrite FR in SRnewtid.
  destruct (st ! newtid) as [] _eqn : Ent. done. 
  destruct SRnewtid as (Etpnt & Espnt & Etbnt & Esbnt).
  assert (TS' : taustep stso_lts (ss, st) Etau 
    (mktsostate (tupdate newtid nil ss.(tso_buffers)) ss.(tso_mem), 
      (st1 ! t <- ss') ! newtid <- sis)).
    eexists. split. edone.
    eapply Comp.step_start; try edone; vauto. 
    by rewrite <- OS.
  right. eexists. 
  split. edone.
  exists tp; exists sp. 
  econstructor.
  - simpl. inv TS2. inv TREL.
    econstructor; simpl; try done.
    intros t'. unfold tupdate. destruct peq. vauto. eauto.
  - eby eapply Comp.taustep_preserves_consistency.
  - eby eapply Comp.step_preserves_consistency; [eapply Comp.step_start|].
  - inv TS2; intro t'; simpl; destruct (peq t' newtid) as [<- | N].
      rewrite !PTree.gss, !tupdate_s.
      econstructor; try edone. by rewrite Etpnt, Espnt.
    destruct (peq t' t) as [<- | Nt].
      repeat (rewrite PTree.gso, ?PTree.gss); try done; [].
      rewrite !tupdate_o; try done; []. vauto.
    by rewrite !PTree.gso, !tupdate_o, <- OS.
Qed.

Lemma start_sim_fail:
  forall s s' (tt : PTree.t Tgt.(SEM_ST)) t sst ts fn args
    (ST : Tgt.(SEM_step) tge s (TEstart fn args) s')
    (CS : tt ! t = Some s)
    (INIT: Tgt.(SEM_init) tge fn args = None)
    (TSOPCREL : tso_pc_related (ts, tt) sst),
      can_reach_error sst.
Proof.
  intros. destruct sst as [ss st].
  pose proof TSOPCREL as [tp [sp REL]]. inversion REL; subst.
  pose proof (SR t) as SRt; simpl in SRt. rewrite CS in SRt.
  destruct (st ! t) as [s0|] _eqn : Estt; simpl in SRt; [|done].
  inv SRt; simpl in *.
  destruct (sim sge tge ge_rel _ _ _ _ _ _ _ ST SR0) as
    [SERR | 
    [ss' ([s1 (TAU & ST')] & SR')]].

  (* Error *)
  eby eapply error_to_tso.

  (* Start fail... *)
  destruct (taustar_to_tso ss Estt TAU) as [st1 (TAUs & OS & Es1)].
  pose proof (thread_init_related_none _ _ _ _ _ ge_rel INIT
    (Val.lessdef_list_refl _)) as SFAIL.
  by eexists (_, _); split; eauto; eexists; exists (Evisible Efail); split; vauto.
Qed.

Lemma unbuffer_write_free_or_fail_reachable:
  forall p c t r sp' stso sp
    (US:  unbuffer_safe stso)
    (RO:  ranges_overlap (range_of_chunk p c) r)
    (IN:  In r sp)
    (RLA: range_list_allocated sp stso.(tso_mem))
    (RLD: range_list_disjoint sp)
    (PU:  part_update_buffer (tso_buffers stso t) sp = Some sp'),
      In r (remove_frees_from_part sp (tso_buffers stso t)) \/
      exists stso', exists sb, 
        apply_buffer_reachable t stso sb stso' /\
        ~ range_in_allocated (range_of_chunk p c) stso'.(tso_mem).
Proof.
  intros until stso.
  remember (tso_buffers stso t) as bt.
  revert stso Heqbt.
  
  induction bt as [|bi btrest IH]; intros. by left.

  inversion US; subst; destruct (ABIS _ _ _ (sym_eq Heqbt)) as [m' ABI].
  pose proof (UNBS _ _ _ _ (sym_eq Heqbt) ABI) as US'.
  specialize (IH (mktsostate (tupdate t btrest (tso_buffers stso)) m')).
  simpl in IH. rewrite tupdate_s in IH. specialize (IH (refl_equal _)).

  apply sym_eq in Heqbt.

  (buffer_item_cases (destruct bi as [p' c' v' | p' n' k' | p' k']) Case).

  Case "BufferedWrite".
    exploit IH; try edone.
    - eby eapply range_list_allocated_write.
    intros [IN' | [stso' [sb [ABR NRIA]]]].
      by left. 
    by right; eauto using apply_buffer_reachable_step. 

  Case "BufferedAlloc".
    destruct k';
      try (by exploit IH; try edone; 
        try (by eapply range_list_allocated_irrelevant; try edone);
          intros [IN' | [stso' [sb [ABR NRIA]]]]; [left|
            right; eauto using apply_buffer_reachable_step]). 
    (* Stack *)
    specialize (IH ((p', n') :: sp)).
    exploit IH; try edone.
    - by right.
    - eby eapply range_list_allocated_part_alloc.
    - split. done.
      intros r' IN'. simpl in ABI.
      destruct (alloc_someD ABI) as (_ & _ & _ & ROA).
      destruct (ranges_disjoint_dec (p', n') r'). done.
      specialize (RLA _ IN').
      by specialize (ROA _ _ n RLA).
    - simpl in PU. destruct valid_alloc_range_dec; [|done].
      by destruct range_in_dec.
    intros [RF | [stso' [sb [ABR NRIA]]]].
      left. destruct r as [pr nr]. 
      apply <- in_rfree_part. apply -> in_rfree_part in RF.
      split. done.
      destruct RF as [_ NIN].
      by intro INf; elim NIN; destruct INf.
    by right; eauto using apply_buffer_reachable_step. 
    
  Case "BufferedFree".  
    destruct k';
    (* Global, heap *)
    try (by exploit IH; try edone;
      try (by eapply range_list_allocated_irrelevant; try edone);
          intros [IN' | [stso' [sb [ABR NRIA]]]]; [left|
            right; eauto using apply_buffer_reachable_step]). 
    (* Stack *)
    simpl in PU. destruct sp as [|[spp n'] sp]. done.
    destruct Ptr.eq_dec; [|done].
    subst spp.
    simpl. rewrite range_remove_comm_remove_frees.
    simpl. destruct Ptr.eq_dec; [|done].
    rewrite (remove_disjoint RLD RLA).
    destruct r as [rp rn].
    simpl in ABI.
    destruct IN as [E | IN].
      inv E.
      right.
      assert (RA := RLA _ (in_eq _ _)).
      eexists. eexists. split. 
        eapply apply_buffer_reachable_step; try edone.
        apply apply_buffer_reachable_refl.
      simpl. intros [r' [k' [RI' RA']]]. 
      assert (RAm := free_preserves_allocated_back ABI _ _ RA').
      destruct (ranges_are_disjoint RA RAm) as [[<- <-] | DISJ].        
        by apply (free_not_allocated ABI _ _ RA').
      eapply RO. apply ranges_disjoint_comm.
      by eapply disjoint_inside_disjoint_r, RI'.    
    exploit IH; try edone.
    - eby destruct RLD; eapply range_list_allocated_part_free.
    - by destruct RLD.
    intros [IN' | [stso' [sb [ABR NRIA]]]].
      by left. 
    by right; eauto using apply_buffer_reachable_step. 
Qed.  

Lemma error_or_chunk_allocated:
  forall p c v instr t t' st s s' ss
    (ALG: pointer_chunk_aligned p c)
    (Es: st ! t = Some s)
    (Bemp: tso_buffers ss t = nil)
    (US: unbuffer_safe ss)
    (ST: stepr slts s (TEmem (MErmw p c v instr)) s'),
    can_reach_error (ss, st) \/
    forall ss' sb
      (ABR: apply_buffer_reachable t' ss sb ss'),
        range_in_allocated (range_of_chunk p c) (tso_mem ss').
Proof.
  intros.
  remember (tso_buffers ss t') as bs.
  revert ss US Bemp Heqbs.
  induction bs as [|bi bs IH]; intros.
  (* Base case *)
  destruct (load_ptr c (tso_mem ss) p) as [v'|] _eqn : L.
    right; intros; inv ABR.
      by destruct (load_chunk_allocated_someD L).
    by rewrite BTD in *.
  left. eexists (_, _); eexists. apply taustar_refl.
  eexists. exists (Evisible Efail); split; [done|].
  eby eapply Comp.step_rmw_fail; vauto.
  (* Step case *) 
  destruct (unbuffer_unbuffer_safe US (sym_eq Heqbs)) as [m' [ABI US']].
  destruct (load_ptr c (tso_mem ss) p) as [v'|] _eqn : L.
    exploit (IH (mktsostate (tupdate t' bs (tso_buffers ss)) m')).
        done.
      by simpl; unfold tupdate; destruct (peq t t') as [<- | N];
        [rewrite Bemp in Heqbs|].
    by simpl; rewrite tupdate_s.
    intros [[nss [TAU ERR]] | R].        
      left. eexists. split; [|edone]. eapply taustar_step; [|edone].
      eapply Comp.step_unbuf. econstructor; try edone; eby symmetry. 
    right; intros; inv ABR. 
      by destruct (load_chunk_allocated_someD L).
    rewrite BTD in Heqbs; inv Heqbs.
    rewrite ABI in ABI0; inv ABI0.
    eby eapply R. 
  left. eexists (_, _); eexists. apply taustar_refl.
  eexists. exists (Evisible Efail); split; [done|].
  eby eapply Comp.step_rmw_fail; vauto.
Qed.

Lemma rmw_sim:
  forall s s' (tt : PTree.t Tgt.(SEM_ST)) t sst ts c p v instr m'
    (TS : Tgt.(SEM_step) tge s (TEmem (MErmw p c v instr)) s')
    (CS : tt ! t = Some s)
    (Bemp : tso_buffers ts t = nil)    
    (LP : load_ptr c ts.(tso_mem) p = Some v)
    (STO: store_ptr c ts.(tso_mem) p (rmw_instr_semantics instr v) = Some m')
    (TSOPCREL : tso_pc_related (ts, tt) sst),
      can_reach_error sst \/
      (exists sst',
         taustep stso_lts sst Etau sst' /\ 
         tso_pc_related (mktsostate ts.(tso_buffers) m', tt ! t <- s') sst') \/
      tso_pc_related (mktsostate ts.(tso_buffers) m', tt ! t <- s') sst /\
      tso_order (mktsostate ts.(tso_buffers) m', tt ! t <- s') (ts, tt).
Proof.
  intros. destruct sst as [ss st].
  pose proof TSOPCREL as [tp [sp REL]]. 
  destruct (unbuffer_item_preserves_tso_pc_witt_empty _ _ _ _ _ _ _ Bemp REL)
    as [sm'' [sp'' [ss'' (ABs & ABR & Espt & Esm & Esb & REL')]]]. subst.
  inversion REL'.
  pose proof (SR t) as SRt; simpl in SRt. rewrite CS in SRt.
  destruct (st ! t) as [s0|] _eqn : Estt; simpl in SRt; [|done].
  inv SRt. simpl in *.
  rewrite Bemp in ABt. inv ABt.
  inversion TREL; simpl in *; subst.
  pose proof (LR p c) as LRpc. rewrite LP in LRpc.
  destruct (sim sge tge ge_rel _ _ _ _ _ _ _ TS SR0) as [SERR | RMW].

  (* Error *)
  eby left; eapply error_to_tso.

  destruct (load_ptr c (tso_mem ss'') p) as [v'|] _eqn : L.
    destruct (RMW _ LRpc) as [ss' ([s1 (TAU & ST')] & SR')].
    destruct (store_ptr c (tso_mem ss'') p (rmw_instr_semantics instr v')) 
      as [sm'|] _eqn : STOs; 
      [|elim (store_chunk_allocated_noneD STOs (load_chunk_allocated_someD L))].
    destruct (taustar_to_tso ss Estt TAU) as [st1 (TAUs & OS & Es1)].
    assert (TS' : taustep stso_lts (ss, st) Etau 
      (mktsostate (tso_buffers ss'') sm', st1 ! t <- ss')).
      eexists. split. 
        eapply taustar_trans. edone. eby eapply TSO.apply_buffer_reachable_taustar. 
        by eapply Comp.step_ord; try edone; vauto.

    (* TODO should go to a separate lemma *)
    destruct (TSO.tso_cons_impl_fin_sup _ _ TCs) as [l [ND DOM]].
    assert (NF: can_reach_error (ss'', st1) \/
      forall t' stso' sb (ABR' : apply_buffer_reachable t' ss'' sb stso'),
      range_in_allocated (range_of_chunk p c) (tso_mem stso') \/
      ~ In t' l).
      clear DOM ND.
      induction l as [|ht l IH]. 
      right. intros. by right.
      destruct IH as [|IH]. by left.
      exploit error_or_chunk_allocated; try edone.
          by destruct(load_chunk_allocated_someD L).
        by destruct TCs.
      intros [[se [TAUe ERR]] | R]. 
        left. eexists. split; [|edone].
        eauto using taustar_trans.          
      right. intros.
      destruct (peq t' ht) as [<- | N].
        left. eauto.
      destruct (IH _ _ _ ABR'). by left. 
      right. intros IN. by simpl in IN; destruct IN as [<- | IN].
    destruct NF as [[se [TAUe ERR]] | NF].
      left. eexists; split; [|edone].
      eapply taustar_trans, TAUe.
      eapply taustar_trans. edone.
      eby eapply TSO.apply_buffer_reachable_taustar. 
    assert(NF':  
      forall t' stso' sb (ABR' : apply_buffer_reachable t' ss'' sb stso'),
                range_in_allocated (range_of_chunk p c) (tso_mem stso')).
      intros; destruct (NF t' stso' sb ABR') as [|NIN]. done.
      specialize (DOM _ NIN).        
      inv ABR'. by destruct (load_chunk_allocated_someD L).
      by simpl in DOM; rewrite BTD in DOM.
    clear NF DOM ND RMW.
    right; left.
    eexists. split. edone.
    exists tp; exists sp''. 
    assert (TCt':  Comp.consistent tso_mm Tgt (mktsostate (tso_buffers ts) m', tt ! t <- s')).
      eapply Comp.step_preserves_consistency; [|edone].
      eapply Comp.step_ord; try edone. 
      eby eapply tso_step_rmw.
    constructor.
    assert (ABIs : apply_buffer_item (BufferedWrite p c (rmw_instr_semantics instr v')) 
                     (tso_mem ss'') = Some sm'). done.
    assert (ABIt : apply_buffer_item (BufferedWrite p c (rmw_instr_semantics instr v)) 
                     (tso_mem ts) = Some m'). done.
    assert (LDrmw := rmw_lessdef instr LRpc). 
    (* Sim. relation *)
    constructor; simpl.
    - eby eapply non_stack_mem_rel_preserved_by_stack_or_write_tgt; try edone;
      try eapply non_stack_mem_rel_preserved_by_stack_or_write.
    - eby eapply write_preserves_load_rel.
    - by simpl; rewrite (mem_consistent_with_restr_apply_item ABIt),
                        (mem_consistent_with_restr_apply_item ABIs).
    - eby eapply store_ptr_preserves_mem_partitioning.
    - eby eapply store_ptr_preserves_mem_partitioning.
    - done.
    - done. 
    - eby inv REL; eapply Comp.taustep_preserves_consistency.
    - done. 
    - intro t'; simpl; destruct (peq t' t) as [<- | N].
        rewrite !PTree.gss. rewrite Bemp, Esb in *. inv PUt. inv PUs.
        econstructor; simpl; try edone. 
        eapply (load_inv _ _ ge_rel); [|edone].
        destruct (store_chunk_allocated_someD STOs) as [[rs [ks [RIs RAs]]] ALG].
        intros p' c' CI.
        destruct (chunk_inside_range_listD CI) as [rpc [IN RI]].
        destruct (load_ptr c' (tso_mem ts) p') as [v1|] _eqn:LI.
          destruct (load_ptr c' m' p') as [v2|] _eqn:LI'.
            intro RNI.
            rewrite (load_store_other STO) in LI. clarify'.
            specialize (NSMR rs ks).
            destruct ks;
              try by apply <- NSMR in RAs; apply (mrwp_in_alloc MRPt) in IN;
                eapply disjoint_inside_disjoint_r, RI;
                  eapply disjoint_inside_disjoint_l, RIs;
                    destruct (ranges_are_disjoint RAs IN) as [[_ E]|].
            destruct (mrwp_alloc_in MRPs RAs) as [t'' INt''].
            destruct (peq t'' t') as [<- | N].
              specialize (RNI _ INt'').
              by eapply ranges_disjoint_comm, disjoint_inside_disjoint_r, RIs.
            pose proof (PI _ _ INt'') as [r' (RIt & INt)].
            eapply disjoint_inside_disjoint_r, RI.
            eapply disjoint_inside_disjoint_l, RIs.
            eapply disjoint_inside_disjoint_l, RIt.
            apply (proj1 MRPt _ _ N _ INt _ IN).
          apply load_chunk_allocated_someD in LI.
          apply (store_preserves_chunk_allocation STO) in LI.
          by apply load_chunk_allocated_noneD in LI'.
        destruct (load_ptr c' m' p') as [] _eqn:LI'; [|done].
        apply load_chunk_allocated_someD in LI'.
        apply (store_preserves_chunk_allocation STO) in LI'.
        by apply load_chunk_allocated_noneD in LI.
      rewrite !PTree.gso, <- OS; try done. specialize (SR t'). simpl in *.
      destruct (tt ! t'); destruct (st ! t'); try edone; simpl in SR |- *.
      eapply buffered_states_related_load_inv_gen; 
        eauto using store_ptr_preserves_mem_partitioning with mrwp.
        apply (unbuffer_safe_to_buffer_safe_for_mem2 _ t' (proj2 TCt')).
      (* Agrees on local... *)
      intros p' c' CI.
      destruct (load_ptr c' (tso_mem ts) p') as [lv|] _eqn : LI;
        destruct (load_ptr c' m' p') as [lv'|] _eqn : LI'; try done.
          (* Both succeed *)  
          intro RNI.
          rewrite <- (load_store_other STO), LI in LI'. clarify.
          destruct (store_chunk_allocated_someD STOs) as
            [[rs [ks [RIs RAs]]] ALG].
          specialize (NSMR rs ks).
          destruct (chunk_inside_range_listD CI) as [rl [INl RIl]].
          pose proof (mrwp_in_alloc MRPt INl) as RAl.
          destruct ks; try (by apply NSMR in RAs;
            eapply disjoint_inside_disjoint_l, RIs;
              eapply disjoint_inside_disjoint_r, RIl;
                destruct (ranges_are_disjoint RAs RAl) as [[_ ?]|D]).
          destruct (mrwp_alloc_in MRPs RAs) as [trs INrs].
          destruct (peq trs t') as [<- | Ntrs].
            apply ranges_disjoint_comm.
            eapply disjoint_inside_disjoint_r, RIs.
            apply RNI.
            destruct (buffers_related_part_update_buffer _ _ _ _ 
                        (BR trs)).
            destruct TCs.
            exploit unbuffer_write_free_or_fail_reachable; eauto with mrwp.
            intro D. apply (ranges_overlap_refl (range_of_chunk p c)).
              apply range_of_chunk_not_empty.
              eby eapply disjoint_inside_disjoint_r, RIs. 
            intros [IN | [stso' [sb [ABR' NIA]]]]. done.
            by specialize (NF' _ _ _ ABR'). 
          eapply disjoint_inside_disjoint_l, RIs;
            eapply disjoint_inside_disjoint_r, RIl.
          destruct (PI _ _ INrs) as [rs' [RIrs' INrs']].
          eapply disjoint_inside_disjoint_l, RIrs'.        
          by apply(proj1 MRPt _ _ Ntrs _ INrs' _ INl).
        apply load_chunk_allocated_someD in LI.    
        apply load_chunk_allocated_noneD in LI'.    
        by apply (store_preserves_chunk_allocation STO) in LI.
      apply load_chunk_allocated_someD in LI'.    
      apply load_chunk_allocated_noneD in LI.    
      by apply (store_preserves_chunk_allocation STO) in LI'.
  left.   
  destruct (RMW _ (Val.lessdef_refl _)) as [ss' ([s1 (TAU & ST')] & SR')].
  destruct (taustar_to_tso ss'' Estt TAU) as [st1 (TAUs & OS & Es1)].
  eexists. split. eby eapply taustar_trans; [eapply TSO.apply_buffer_reachable_taustar|].
  eexists. exists (Evisible Efail). split. done.
  eapply Comp.step_rmw_fail; try edone. eby econstructor. 
Qed.

Lemma rmw_fail_sim:
  forall s s' (tt : PTree.t Tgt.(SEM_ST)) t sst ts c p v instr 
    (TS : Tgt.(SEM_step) tge s (TEmem (MErmw p c v instr)) s')
    (CS : tt ! t = Some s)
    (Bemp : tso_buffers ts t = nil)    
    (LP : load_ptr c ts.(tso_mem) p = None)
    (TSOPCREL : tso_pc_related (ts, tt) sst),
      can_reach_error sst.
Proof.
  intros. destruct sst as [ss st].
  pose proof TSOPCREL as [tp [sp REL]]. 
  destruct (unbuffer_item_preserves_tso_pc_witt_empty _ _ _ _ _ _ _ Bemp REL)
    as [sm'' [sp'' [ss'' (ABs & ABR & Espt & Esm & Esb & REL')]]]. subst.
  inversion REL'.
  pose proof (SR t) as SRt; simpl in SRt. rewrite CS in SRt.
  destruct (st ! t) as [s0|] _eqn : Estt; simpl in SRt; [|done].
  inv SRt. simpl in *.
  rewrite Bemp in ABt. inv ABt.
  inversion TREL; simpl in *; subst.
  pose proof (LR p c) as LRpc. rewrite LP in LRpc.
  destruct (sim sge tge ge_rel _ _ _ _ _ _ _ TS SR0) as [SERR | RMW].

  (* Error *)
  eby eapply error_to_tso.

  (* Load fail sim *)
  specialize (LR p c).
  destruct (load_ptr c (tso_mem ss'') p) as [] _eqn : L'; [done|].
  destruct (RMW _ (Val.lessdef_refl _)) as [ss' ([s1 (TAU & ST')] & SR')].
  destruct (taustar_to_tso ss'' Estt TAU) as [st1 (TAUs & OS & Es1)].
  eexists. split. eby eapply taustar_trans; [eapply TSO.apply_buffer_reachable_taustar|].
  eexists. exists (Evisible Efail). split. done.
  eapply Comp.step_rmw_fail; try edone. eby econstructor. 
Qed.  

Lemma thread_stuck_sim:
  forall s (tt : PTree.t Tgt.(SEM_ST)) t sst ts  
    (TS : forall s' l', ~ Tgt.(SEM_step) tge s l' s')
    (CS : tt ! t = Some s)
    (TSOPCREL : tso_pc_related (ts, tt) sst),
      can_reach_error sst.
Proof.
  intros. destruct sst as [ss st].
  pose proof TSOPCREL as [tp [sp REL]].
  inversion REL; subst.
  pose proof (SR t) as SRt; simpl in SRt. rewrite CS in SRt.
  destruct (st ! t) as [s0|] _eqn : Estt; simpl in SRt; [|done].
  inv SRt. simpl in *.
 
  eexists. split. apply taustar_refl. eexists; exists (Evisible Efail); split. done.
  eapply Comp.step_thread_stuck; try edone.
  intros s' l' SRS. 
  pose proof (stuck_sim _ _ ge_rel) as SS.
  destruct (SS _ _ _ _ _ _ _ SRS SR0) as [t1 [l1 TGTS]].
  eby eapply TS.
Qed.

Lemma fence_sim:
  forall s s' (tt : PTree.t Tgt.(SEM_ST)) t sst ts
    (TS : Tgt.(SEM_step) tge s (TEmem MEfence) s')
    (CS : tt ! t = Some s)
    (Bemp : tso_buffers ts t = nil)    
    (TSOPCREL : tso_pc_related (ts, tt) sst),
      can_reach_error sst \/
      (exists sst',
         taustep stso_lts sst Etau sst' /\ 
         tso_pc_related (ts, tt ! t <- s') sst').
Proof.
  intros. destruct sst as [ss st].
  pose proof TSOPCREL as [tp [sp REL]]. 
  destruct (unbuffer_item_preserves_tso_pc_witt_empty _ _ _ _ _ _ _ Bemp REL)
    as [sm'' [sp'' [ss'' (ABs & ABR & Espt & Esm & Esb & REL')]]]. subst.
  inversion REL'.
  pose proof (SR t) as SRt; simpl in SRt. rewrite CS in SRt.
  destruct (st ! t) as [s0|] _eqn : Estt; simpl in SRt; [|done].
  inv SRt. simpl in *.
  rewrite Bemp in ABt. inv ABt.

  destruct (sim sge tge ge_rel _ _ _ _ _ _ _ TS SR0) 
    as [SERR | [ss' ([s1 (TAU & ST')] & SR')]].

  (* Error *)
  eby left; eapply error_to_tso.

  (* Fence *)
  destruct (taustar_to_tso ss'' Estt TAU) as [st1 (TAUs & OS & Es1)].
  right.
  assert (TS' : taustep stso_lts (ss'', st) Etau (ss'', st1 ! t <- ss')).
    eexists. split. edone.
    eby eapply Comp.step_ord; vauto. 
   eexists. split. 
     eapply taustar_taustep. eby eapply TSO.apply_buffer_reachable_taustar. edone.
  exists tp; exists sp''. 
  econstructor. 
  - done.
  - eby eapply Comp.taustep_preserves_consistency.
  - eby eapply Comp.step_preserves_consistency; [eapply Comp.step_ord; vauto|]. 
  - intro t'; simpl; destruct (peq t' t) as [<- | N].
      rewrite !PTree.gss. econstructor; try edone; by rewrite Bemp.
    by rewrite !PTree.gso, <- OS.
Qed.

Lemma bsim:
  forall ts ss ts' e
    (PCREL: tso_pc_related ts ss)
    (NOOM: e <> Eoutofmemory)
    (TSOST: ttso_lts.(stepr) ts e ts'),
  can_reach_error ss \/
  (exists ss', taustep stso_lts ss e ss' /\ tso_pc_related ts' ss') \/
  e = Etau /\ tso_pc_related ts' ss /\ tso_order ts' ts.
Proof.
  intros; revert ss NOOM PCREL.
  (comp_step_cases (case TSOST) Case); clear TSOST ts ts' e; try done;
    try (by intros; inv tidSTEP).

  Case "step_ord".
    intros until 0. intros ST TSOST CS NS s0 _ TREL.

    mem_event_cases (destruct ev) SCase.
    
    SCase "MEfence".
      eby inv TSOST; exploit fence_sim; try edone; intros [ERR | WS]; vauto.

    SCase "MEwrite".
      eby inv TSOST; exploit write_sim; try edone; 
        intros [ERR | [WS | STUTTER]]; vauto.

    SCase "MEread".
      eby inv TSOST; exploit read_sim; try edone; 
        intros [ERR | [WS | STUTTER]]; vauto.

    SCase "MErmw".
      eby inv TSOST; exploit rmw_sim; try edone; 
        intros [ERR | [WS | STUTTER]]; vauto.

    SCase "MEalloc".
      eby inv TSOST; exploit alloc_sim; try edone; 
        intros [ERR | [WS | STUTTER]]; vauto.
 
    SCase "MEfree". 
      eby inv TSOST; exploit free_sim; try edone; 
        intros [ERR | [WS | STUTTER]]; vauto.

  Case "step_ext".
    intros; subst; exploit ext_sim; try edone. 
    eby intros [ERR | WS]; vauto.

  Case "step_unbuf".
    eby intros; right; exploit unbuffer_sim; try edone;
      intros [ERR | WS]; vauto.

  Case "step_tau".
    by intros; subst; exploit thread_tau_sim; try edone; 
      intros [ERR | [WS | STUTTER]]; vauto.

  Case "step_start".
    intros; subst.
    eby exploit start_sim; try edone; intros [ERR | WS]; vauto.

  Case "step_start_fail".
    eby intros; exploit start_sim_fail; try edone; vauto.

  Case "step_exit".
    eby intros; exploit exit_sim; try edone; intros [ERR | WS]; vauto.

  Case "step_read_fail".
    eby intros; subst; exploit read_fail_sim; try edone; vauto.

  Case "step_write_fail".
    eby intros; subst; exploit write_fail_sim; try edone; vauto.

  Case "step_free_fail". 
    eby intros; subst; exploit free_fail_sim; try edone; vauto.

  Case "step_rmw_fail".
    intros; subst; inv tsoSTEP; exploit rmw_fail_sim; try edone; vauto.

  Case "step_thread_stuck".
    eby intros; subst; exploit thread_stuck_sim; try edone; vauto.

  Case "step_extcallmem".
    eby intros; exploit extmem_sim; try edone; intros [ERR | WS]; vauto.

  Case "step_extcallmem_fail".
    eby intros; exploit extmem_sim_fail; try edone; vauto.

  Case "step_startmem".
    eby intros; exploit startmem_sim; try edone; intros [ERR | WS]; vauto.

  Case "step_startmem_read_fail".
    eby intros; exploit startmem_sim_read_fail; try edone; vauto.

  Case "step_startmem_spawn_fail".
    eby intros; exploit startmem_sim_fail; try edone; vauto.
Qed.

End SIMS.


(** For each intial state of the target TSO there is a corresponding 
    initial state of the source machine. *)
Theorem tso_init_related: 
  forall src_prog tgt_prog args tge tstate,
    match_prg src_prog tgt_prog ->
    Comp.init _ _ tgt_prog args tge tstate ->
    exists sge, exists sstate,
      Comp.init _ _ src_prog args sge sstate /\ genv_rel sge tge /\
      tso_pc_related sge tge tstate sstate.
Proof.
    destruct tstate as [[tb tm] ts].
    intros MP [mtst [mtid [inm [mp [GEINIT [GEMAIN [MINIT Etst]]]]]]]; clarify. 
    destruct (ge_init_related src_prog tgt_prog _ _ MP GEINIT) 
      as [sge [SGEINIT GEREL]].
    destruct (thread_init_related _ _ _ _ _ _ GEREL MINIT 
      (Val.lessdef_list_refl _) ) as [smt [SMINIT mREL]].
    exists sge.
    exists (mktsostate (fun _ : thread_id => nil) inm,
             (PTree.empty Src.(SEM_ST)) ! mtid <- smt).
    split. 
      exists smt; exists mtid; exists inm; exists mp.
      repeat split; try assumption.
      by rewrite (main_ptr_eq _ _ _ _ MP GEREL), <- GEMAIN.
    split. done.
    (* Establish the simulation relation *)
    exists (fun _ => nil). exists (fun _ => nil).
    constructor.
      constructor; simpl.
      - intros r k. by destruct k.
      - intros p c. by destruct load_ptr.
      - done.
      - split. intros t1 t2 N. done.
        split. done.
        intro; split. by intros [? ?].
        intro RA. by pose proof (ge_init_global _ _ _ GEINIT _ _ RA).
      - split. intros t1 t2 N. done.
        split. done.
        intro; split. by intros [? ?].
        intro RA. by pose proof (ge_init_global _ _ _ GEINIT _ _ RA).
      - by intros t r IN.
      - by intro; constructor.
    repeat (split; try by simpl; try apply unbuffer_safe_unbuffer).
    repeat (split; try by simpl; try apply unbuffer_safe_unbuffer).
    simpl.
    intro t. destruct (peq t mtid) as [<- | N].
      rewrite !PTree.gss; simpl.
      eby econstructor.
    by rewrite !PTree.gso, !PTree.gempty. 
Qed.

Definition full_basic_sim : Bsim.sim tso_mm tso_mm Src Tgt match_prg.
Proof.
  apply (Bsim.make match_prg
     (fun sge tge s t => genv_rel sge tge /\ tso_pc_related sge tge t s)
     (fun sge tge t t' => genv_rel sge tge /\ tso_order sge tge t' t));
    simpl; vauto.
  - intros; destruct REL as (_ & (? & ? & [])).
     eapply PTree.ext; intro tid;  
       generalize (SR tid); simpl; rewrite EMPTY, !PTree.gempty; simpl.
       by destruct s as [sm sthr]; simpl; destruct (sthr ! tid).
  - eby intros; exploit tso_init_related. 
  intros; des; edestruct bsim; des; eauto.
  - by right; left; eexists; vauto. 
  - by right; right.
Defined.

Theorem full_sim : Sim.sim tso_mm tso_mm Src Tgt match_prg.
Proof.
  apply (Sim.make full_basic_sim); simpl.
  constructor; intros i (REL & _).
  induction i using (well_founded_ind (tso_order_wf sge tge REL)).
  constructor; intros; des; auto.
Qed.

End Localsim.
