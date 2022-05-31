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
Require Import Relations.Relation_Operators.
Require Import Wellfounded.
Require Import Integers.
Require Import Values.
Require Import Pointers.
Require Import Events.
Require Import Mem.
Require Import Ast.
Require Import Globalenvs.
Require Import Maps.
Require Import Simulations.
Require Import Floats.
Require Import TSOmachine.
Require Import Memcomp.
Require Import Memeq.
Require Import Traces.
Require Import MCsimulation.
Require Import Libtactics.

(** * Generic results about the TSO machine *)

Section TSOresults.

  Variables (Sem : SEM).
  Let tsolts ge := (mklts event_labels (Comp.step tso_mm Sem ge)).
  Let lts ge := (mklts thread_labels (SEM_step Sem ge)).

  Hint Constructors tso_step : myhints.
  Hint Constructors Comp.mm_arglist : myhints.
  Hint Constructors Comp.mm_arglist_fail : myhints.
  Hint Constructors Comp.mm_ext_arglist : myhints.
  Hint Constructors Comp.mm_ext_arglist_fail : myhints.
  Hint Constructors Val.lessdef_list.

  Hint Extern 0 (MM_step _ _ _ _) => simpl. 

  Lemma stuck_threads_empty_buff_impl_stuck_tso:
    forall ge stso sthr
      (FINSUP: tso_fin_sup stso)
      (STUCK: 
        (exists t, exists ts, exists e, exists ts',
          sthr ! t = Some ts /\ e = TEext Efail /\ SEM_step _ ge ts e ts') \/
        forall t, sthr ! t = None)
      (BE: forall t, stso.(tso_buffers) t = nil),
      stuck_or_error (tsolts ge) (stso, sthr).
  Proof.
    destruct 2 as [(t & ts & e & ts' & ST & Eerr & ERR) | STUCK]; intros.
    (* There is a thread that can do an error *)
      destruct e; try destruct ev; simpl in Eerr; try done. 
      right; exists (stso, sthr ! t <- ts'); exists (Evisible Efail); split; [done|].
      by simpl; eapply Comp.step_ext; eauto.
    (* All threads are stuck *)
    exploit (strong_in_dec_prop (fun (x: thread_id * _) => 
                                   ~ (exists l', exists s', SEM_step _ ge (snd x) l' s'))).
    - intros [tid s]; simpl.
      destruct (SEM_progress_dec _ ge s) as [NO|]; [|by right]. 
        eby left; intros (? & ? & ?); ecase NO.
      instantiate (1 := (PTree.elements sthr)).
      intros [[[tid ?] [IN NOST]]|ALL]; simpl in *. 
    - eapply PTree.elements_complete in IN.
      right; eexists (_, _); exists (Evisible Efail); split; [done|]; simpl.
      eapply Comp.step_thread_stuck; try eassumption. 
      eby intros l' s' STEP; elim NOST; do 2 eexists.
    left; intros s' l' ST.
    (comp_step_cases (inv ST) Case); try by rewrite STUCK in *.
    Case "step_unbuf"; by inv tsoSTEP; rewrite BE in *.
  Qed.

  (** ** Less-defined memories, buffers, and tso states *)

  Inductive lessdef_mem (m m' : mem) :=
    | lessdef_mem_cons: forall
        (LVS: mem_lessdef m m')
        (RAS: arange_eq (fun _ => true) m m'),
        lessdef_mem m m'.

  Definition lessdef_buffer_item (bi bi' : buffer_item) : Prop :=
    match bi, bi' with
      | BufferedWrite p c v, BufferedWrite p' c' v' =>
          p = p' /\ c = c' /\ Val.lessdef v v'
      | _, _ => bi = bi'
    end.

  Inductive lessdef_tso : tso_state -> tso_state -> Prop :=
  | lessdef_tso_cons: forall b m b' m'
      (LDM : lessdef_mem m m')
      (LDB : forall t, list_forall2 lessdef_buffer_item (b t) (b' t)),
      lessdef_tso (mktsostate b m) (mktsostate b' m').

  Lemma lessdef_buffer_item_refl:
    forall bi, lessdef_buffer_item bi bi.
  Proof. by intros []. Qed.

  Lemma lessdef_mem_refl: forall t, lessdef_mem t t.
  Proof. split; auto using arange_eq_refl. Qed.

  Hint Resolve lessdef_buffer_item_refl.
  Hint Resolve lessdef_mem_refl.

  Lemma  lessdef_listsum_pfx:
    forall {A l l'} (h : A + val)
    (LD : Val.lessdef_listsum l l') ,
    Val.lessdef_listsum (h :: l) (h :: l').
  Proof. by intros; destruct h; vauto. Qed.    

  Lemma lessdef_listsum_refl:
    forall {A} (l : list (A + val)),
      Val.lessdef_listsum l l.
  Proof. by induction l as [|[|]]; constructor. Qed.

  Lemma list_forall2_app:
    forall A B (P : A -> B -> Prop) l1 l2 l1' l2'
      (LFA : list_forall2 P l1 l2)
      (LFA': list_forall2 P l1' l2'),
      list_forall2 P (l1 ++ l1') (l2 ++ l2').
  Proof.
    intros until l1.
    induction l1 as [|h l1 IH]; intros; inv LFA. done.
    rewrite <- ! app_comm_cons. by constructor; auto.
  Qed.

  Lemma alloc_lessdef_mem:
    forall {m m'} r k
      (LDM  : lessdef_mem m m'),
      match alloc_ptr r k m, alloc_ptr r k m' with
        | Some nm, Some nm' => lessdef_mem nm nm'
        | None, None => True
        | _, _ => False
      end. 
  Proof.
    intros; inv LDM.
    destruct (alloc_ptr r k m) as [nm|] _eqn : Enm;
      destruct (alloc_ptr r k m') as [nm'|] _eqn : Enm'; try done.
    - constructor. eby destruct r; eapply mem_lessdef_sim_alloc.
      eby eapply alloc_ptr_some_arange1.
    - by rewrite (alloc_ptr_none_arange _ _ _ _ 
        Enm' (arange_eq_sym RAS)) in Enm.
    - by rewrite (alloc_ptr_none_arange _ _ _ _ Enm RAS) in Enm'.
  Qed.

  Lemma free_lessdef_mem:
    forall {m m'} p k
      (LDM  : lessdef_mem m m'),
      match free_ptr p k m, free_ptr p k m' with
        | Some nm, Some nm' => lessdef_mem nm nm'
        | None, None => True
        | _, _ => False
      end. 
  Proof.
    intros; inv LDM.
    destruct (free_ptr p k m) as [nm|] _eqn : Enm;
      destruct (free_ptr p k m') as [nm'|] _eqn : Enm'; try done.
    - constructor. 
      destruct (free_someD Enm) as [n RA].
      destruct (free_someD Enm') as [n' RA'].
      unfold arange_eq in RAS.
      assert (RAo : range_allocated (p, n) k m').
        eby eapply RAS.
      destruct (alloc_ranges_same RAo RA') as [<- _].
      eby eapply mem_lessdef_sim_free_same_size.
      eby eapply free_ptr_some_arange1.
    - by rewrite (free_ptr_none_arange _ _ _ _ _ Enm' (arange_eq_sym RAS)) in Enm.
    - by rewrite (free_ptr_none_arange _ _ _ _ _ Enm RAS) in Enm'.
  Qed.

  Lemma store_lessdef_mem:
    forall {m m' v v'} c p
      (LDM : lessdef_mem m m')
      (LDV : Val.lessdef v v'),
      match store_ptr c m p v, store_ptr c m' p v' with
        | Some nm, Some nm' => lessdef_mem nm nm'
        | None, None => True
        | _, _ => False
      end. 
  Proof.
    intros; inv LDM.
    destruct (store_ptr c m p v) as [nm|] _eqn : Enm;
      destruct (store_ptr c m' p v') as [nm'|] _eqn : Enm'; try done.
    - constructor. 
      eby eapply mem_lessdef_sim_write.
      eby eapply store_ptr_some_arange1.
    - by rewrite (store_ptr_none_arange _ Enm' (arange_eq_sym RAS)) in Enm.
    - by rewrite (store_ptr_none_arange _ Enm RAS) in Enm'.
  Qed.

  Lemma apply_buffer_item_lessdef_mem:
    forall {m m' bi bi'}
      (LDM : lessdef_mem m m')
      (LDV : lessdef_buffer_item bi bi'),
      match apply_buffer_item bi m, apply_buffer_item bi' m' with
        | Some nm, Some nm' => lessdef_mem nm nm'
        | None, None => True
        | _, _ => False
      end. 
  Proof.
    intros; inv LDM.
    destruct bi; destruct bi'; try done.
        destruct LDV as (-> & -> & LDV).
        by apply store_lessdef_mem.
      rewrite LDV.
      by apply alloc_lessdef_mem.
    rewrite LDV.
    by apply free_lessdef_mem.
  Qed.

  Lemma apply_buffer_lessdef_mem:
    forall {m m' b b'}
      (LDM : lessdef_mem m m')
      (LDB : list_forall2 lessdef_buffer_item b b'),
      match apply_buffer b m, apply_buffer b' m' with
        | Some nm, Some nm' => lessdef_mem nm nm'
        | None, None => True
        | _, _ => False
      end. 
  Proof.
    intros m m' b; revert m m'.
    induction b as [| bi b IH]; intros. by inv LDB.
    inversion LDB as [|bi1 bt1 bi2 bt2 LDBI LDBF E1 E2]. subst.
    pose proof (apply_buffer_item_lessdef_mem LDM LDBI) as LDM'.
    simpl.
    destruct (apply_buffer_item bi m) as [nm|] _eqn : ABI;
      destruct (apply_buffer_item bi2 m') as [nm'|] _eqn : ABI'; 
        try done; [].
    by apply IH.
  Qed.

  Lemma unbuffer_lessdef_tso:
    forall b m bi bt nm b' m' bi' bt' nm' t
      (LD  : lessdef_tso (mktsostate b m) (mktsostate b' m'))
      (BD  : b t = bi :: bt)
      (ABI : apply_buffer_item bi m = Some nm)
      (BD' : b' t = bi' :: bt')
      (ABI': apply_buffer_item bi' m' = Some nm'),
        lessdef_tso (mktsostate (tupdate t bt b) nm)
          (mktsostate (tupdate t bt' b') nm').
  Proof.
    intros.
    inversion LD. subst. assert (LDBt := LDB t). rewrite BD, BD' in LDBt.
    inversion LDBt as [|bi1 bt1 bi2 bt2 LDBI LDBF E1 E2]. subst.
    constructor.
      assert (LDM' := apply_buffer_item_lessdef_mem LDM LDBI).
      by rewrite ABI, ABI' in LDM'.
    by intro t'; destruct (peq t' t) as [-> | N];
      [rewrite !tupdate_s | rewrite !tupdate_o].
  Qed.

  Lemma buffer_insert_lessdef_tso:
    forall {tso tso' bi bi'} t
    (LD   : lessdef_tso tso tso')
    (LDBI : lessdef_buffer_item bi bi'),
      lessdef_tso (buffer_insert tso t bi) (buffer_insert tso' t bi').
  Proof.
    intros. inv LD.
    constructor. done.
    intros t'. specialize (LDB t').
    destruct (peq t' t) as [-> | N].
      rewrite !tupdate_s. apply list_forall2_app. done.
      by constructor; vauto.
    by rewrite !tupdate_o.
  Qed.

  Lemma load_lessdef_mem:
    forall {m m'} p c
    (LD : lessdef_mem m m'),
    match load_ptr c m p, load_ptr c m' p with
      | Some v, Some v' => Val.lessdef v v'
      | None, None => True
      | _, _ => False
    end.
  Proof.
    intros.
    pose proof (load_chunk_allocated_spec c m p) as LS.
    pose proof (load_chunk_allocated_spec c m' p) as LS'.
    inv LD. specialize (LVS p c).
    destruct (load_ptr c m p) as [v|] _eqn : Ev;
      destruct (load_ptr c m' p) as [v'|] _eqn : Ev'; 
        simpl in *; try done.
    destruct LS' as [[r [k (RI & RA)]] ALG].
    apply RAS in RA; [|done].
    elim LS. by split; vauto. 
  Qed.

  (** Unbuffer safety does not depend on value definedness. *)

  Lemma unbuffer_safe_lessdef:
    forall t t',
      lessdef_tso t t' ->
      unbuffer_safe t' ->
      unbuffer_safe t.
  Proof.
    intros tso tso' LD US. revert tso LD. 
    induction US; intros; inversion LD; subst.
    constructor; simpl in *.
    - intros t bi bt BD. specialize (LDB t).
      rewrite BD in LDB. 
      inversion LDB as [|bi1 bt1 bi2 bt2 LDBI LDBF E1 E2]. subst.
      exploit ABIS. eby symmetry.
      intros [nm' ABInm'].
      assert (LDMn := apply_buffer_item_lessdef_mem LDM LDBI).
      destruct (apply_buffer_item bi m) as [nm|] _eqn:ABInm;
        rewrite ABInm' in LDMn; [|done].
      eby eexists.
    - intros t bi bt nm BD ABInm.      
      specialize (LDB t). rewrite BD in LDB. 
      inversion LDB as [|bi1 bt1 bi2 bt2 LDBI LDBF E1 E2]. subst.
      exploit ABIS. eby symmetry. intros [nm' ABInm'].
      assert (LDMn := apply_buffer_item_lessdef_mem LDM LDBI).
      rewrite ABInm', ABInm in LDMn.
      eapply H. eby symmetry. edone.
      apply sym_eq in E2. eby eapply unbuffer_lessdef_tso. 
  Qed.

  Lemma unbuffer_safe_lessdef_rev:
    forall t t',
      lessdef_tso t' t ->
      unbuffer_safe t' ->
      unbuffer_safe t.
  Proof.
    intros tso tso' LD US. revert tso LD. 
    induction US; intros; inversion LD; subst.
    constructor; simpl in *.
    - intros t bi bt BD. specialize (LDB t).
      rewrite BD in LDB. 
      inversion LDB as [|bi1 bt1 bi2 bt2 LDBI LDBF E1 E2]. subst.
      exploit ABIS. eby symmetry.
      intros [nm' ABInm'].
      assert (LDMn := apply_buffer_item_lessdef_mem LDM LDBI).
      destruct (apply_buffer_item bi m') as [nm|] _eqn:ABInm;
        rewrite ABInm' in LDMn; [|done].
      eby eexists.
    - intros t bi bt nm BD ABInm.      
      specialize (LDB t). rewrite BD in LDB. 
      inversion LDB as [|bi1 bt1 bi2 bt2 LDBI LDBF E1 E2]. subst.
      exploit ABIS. eby symmetry. intros [nm' ABInm'].
      assert (LDMn := apply_buffer_item_lessdef_mem LDM LDBI).
      rewrite ABInm', ABInm in LDMn.
      eapply H. eby symmetry. edone.
      apply sym_eq in E1. eby eapply unbuffer_lessdef_tso. 
  Qed.

  Lemma unbuffer_safe_lessdef_iff:
    forall t t',
      lessdef_tso t' t ->
      (unbuffer_safe t <-> unbuffer_safe t').
  Proof. split; eauto using unbuffer_safe_lessdef, unbuffer_safe_lessdef_rev. Qed.

  Lemma ldo_step_simulation:
    forall {stso ttso t ev ttso' l'}
      (LD   : lessdef_tso stso ttso)
      (TSOST: tso_step ttso (MMmem t ev) ttso')
      (LDO  : te_ldo l' (TEmem ev)),
      exists ev', exists stso',
        l' = TEmem ev' /\
        tso_step stso (MMmem t ev') stso' /\
        lessdef_tso stso' ttso'.
  Proof.
    intros.
    destruct l' as [| [ | p c v | | | | ]  | | | | | |]; try done; [].
    destruct ev as [ | p' c' v' | | | | ]; try done; [].
    destruct LDO as [<- [<- LDV]].
    eexists; exists (buffer_insert stso t (BufferedWrite p c v)).
    split; try done.
    assert(LD' : lessdef_tso (buffer_insert stso t (BufferedWrite p c v)) ttso').
      inv TSOST. by apply buffer_insert_lessdef_tso.
    inv TSOST.
    split; [econstructor|]; eauto using unbuffer_safe_lessdef.
  Qed.

  Lemma tso_step_ldi:
    forall {stso ttso t ev ttso'}
      (LD : lessdef_tso stso ttso)
      (TST: tso_step ttso (MMmem t ev) ttso'),
      exists ev', exists stso',
        te_ldi (TEmem ev') (TEmem ev) /\
        tso_step stso (MMmem t ev') stso' /\
        lessdef_tso stso' ttso'.
  Proof.
    intros; inv TST;
      try (eby eexists; eexists; split; [apply ldi_refl|];
        split; [econstructor; try edone; []; eapply unbuffer_safe_lessdef;
                  [eapply buffer_insert_lessdef_tso|] |
                eapply buffer_insert_lessdef_tso]).
    (* Read *)
    inv LD.
    pose proof (apply_buffer_lessdef_mem LDM (LDB t)) as ABLD.
    simpl in AB. rewrite AB in ABLD.
    destruct (apply_buffer (b t) m) as [nm|] _eqn : AB'; [|done].
    pose proof (load_lessdef_mem p c ABLD) as LDLD.
    rewrite LD0 in LDLD.
    destruct (load_ptr c nm p) as [v'|] _eqn : LD'; [|done].
    by exists (MEread p c v'); eexists; split; vauto.
    (* Fence *)
    eexists; eexists; split; [by apply ldi_refl|].
    split; [|eassumption].
    inv LD; simpl in *; constructor. 
    by generalize (LDB t); rewrite Bemp; inversion 1.
    (* rmw *)
    inv LD; simpl in *.
    assert (LDBt := LDB t). rewrite Bemp in LDBt.
    pose proof (load_lessdef_mem p c LDM) as LDLD.
    rewrite LD0 in LDLD.
    destruct (load_ptr c m p) as [v'|] _eqn : LD'; [|done].
    pose proof (store_lessdef_mem c p LDM 
      (rmw_lessdef instr LDLD)) as STLD.
    rewrite STO in STLD.
    destruct (store_ptr c m p (rmw_instr_semantics instr v')) 
      as [ms|] _eqn : STO' ; [|done].
    inv LDBt.
    by exists (MErmw p c v' instr); eexists; split; vauto.
  Qed.   

  Lemma tso_step_arglist:
    forall  tlocs stso ttso ttso' slocs t tvals
    (LD : lessdef_tso stso ttso)
    (LDlocs : Val.lessdef_listsum slocs tlocs)
    (MA : Comp.mm_arglist tso_mm ttso t tlocs tvals ttso'),
       exists stso', exists svals,
         Val.lessdef_list svals tvals /\
         Comp.mm_arglist tso_mm stso t slocs svals stso' /\
         lessdef_tso stso' ttso'.
  Proof.
    induction tlocs as [|h tlocs IH]; intros.
    
    (* Base case *)
    inv LDlocs. inv MA.
    by eauto 8 with myhints.
    
    (* Step case *)
    inversion LDlocs as [|hslocs tslocks htlocks ttlocks LDh LDt]; subst.
    inv MA.
    (* Head is a value *)
    destruct hslocs as [|v']. done.
    destruct (IH _ _ _ _ _ _ LD LDt MA0) as [stso' [svals (LD' & MA' & LDtso')]].
    by eauto 8 with myhints.
    (* Head is a memory location *)
    destruct hslocs as [[p' c']|]; [|done]. inv LDh. 
    inv RD.
    destruct (IH _ _ _ _ _ _ LD LDt MA0) as [stso' [svals (LD' & MA' & LDtso')]].
    inversion LD; subst.
    pose proof (apply_buffer_lessdef_mem LDM (LDB t)) as ABLD. 
    simpl in AB. rewrite AB in ABLD.
    destruct (apply_buffer (b t) m) as [nm|] _eqn : AB'; [|done].
    pose proof (load_lessdef_mem p c ABLD) as LDLD.
    rewrite LD0 in LDLD.
    destruct (load_ptr c nm p) as [v'|] _eqn : LDx; [|done].
    by eauto 9 with myhints.
  Qed.

  Lemma tso_step_arglist_fail:
    forall  tlocs stso ttso slocs t
    (LD : lessdef_tso stso ttso)
    (LDlocs : Val.lessdef_listsum slocs tlocs)
    (MA : Comp.mm_arglist_fail tso_mm ttso t tlocs),
       Comp.mm_arglist_fail tso_mm stso t slocs.
  Proof.
    induction tlocs as [|h tlocs IH]; intros.
    
    (* Base case *)
    inv LDlocs. inv MA. 
    
    (* Step case *)
    inversion LDlocs as [|hslocs tslocks htlocks ttlocks LDh LDt]; subst.
    inv MA.
    (* Read error *)
    destruct hslocs as [[p' c']|]; [|done]. inv LDh. 
    inv TST. inversion LD; subst. simpl in Bemp.
    pose proof (apply_buffer_lessdef_mem LDM (LDB t)) as ABLD.
    pose proof (LDB t) as LDBt. rewrite Bemp in *. inv LDBt. 
    replace (b t) with (@nil buffer_item)  in ABLD. simpl in *.
    pose proof (load_lessdef_mem p c ABLD) as LDLD.
    rewrite LD0 in LDLD.
    by destruct (load_ptr c m p) as [] _eqn : LDs; eauto with myhints.
    (* Head is a value *)
    destruct hslocs as [|v']. done.
    specialize (IH _ _ _ _ LD LDt MA0).
    by constructor.
    (* Head is a memory location *)
    destruct hslocs as [[p' c']|]; [|done]. inv LDh. 
    inv RD.
    specialize (IH _ _ _ _ LD LDt MA0).
    inversion LD; subst.
    pose proof (apply_buffer_lessdef_mem LDM (LDB t)) as ABLD. 
    simpl in AB. rewrite AB in ABLD.
    destruct (apply_buffer (b t) m) as [nm|] _eqn : AB'; [|done].
    pose proof (load_lessdef_mem p c ABLD) as LDLD.
    rewrite LD0 in LDLD.
    destruct (load_ptr c nm p) as [v'|] _eqn : LDx; [|done].
    eauto with myhints. 
  Qed.

  Lemma tso_step_ext_arglist_fail:
    forall stso ttso locs t
    (LD : lessdef_tso stso ttso)
    (MA : Comp.mm_ext_arglist_fail tso_mm ttso t locs),
       Comp.mm_ext_arglist_fail tso_mm stso t locs.
  Proof.
    induction locs as [|h locs IH]; intros.
    
    (* Base case *)
    by inv MA. 
    
    (* Step case *)
    inv MA; eauto with myhints.
    (* Failed read *)
    inv TST. inversion LD; subst. simpl in Bemp.
    pose proof (apply_buffer_lessdef_mem LDM (LDB t)) as ABLD.
    pose proof (LDB t) as LDBt. rewrite Bemp in *. inv LDBt. 
    replace (b t) with (@nil buffer_item)  in ABLD. simpl in *.
    pose proof (load_lessdef_mem p c ABLD) as LDLD.
    rewrite LD0 in LDLD.
    by destruct (load_ptr c m p) as [] _eqn; eauto with myhints.
    (* Not eventval error *)
    inv TST.
    inversion LD; subst.
    pose proof (apply_buffer_lessdef_mem LDM (LDB t)) as ABLD. 
    simpl in AB. rewrite AB in ABLD.
    destruct (apply_buffer (b t) m) as [nm|] _eqn : AB'; [|done].
    pose proof (load_lessdef_mem p c ABLD) as LDLD.
    rewrite LD0 in LDLD.
    destruct (load_ptr c nm p) as [v'|] _eqn : LDx; [|done].
    inv LDLD; eapply Comp.mm_ext_arglist_fail_everr; vauto;
      try done; by intros [].
    (* Head is a memory location *)
    inv RD.
    inversion LD; subst.
    pose proof (apply_buffer_lessdef_mem LDM (LDB t)) as ABLD. 
    simpl in AB. rewrite AB in ABLD.
    destruct (apply_buffer (b t) m) as [nm|] _eqn : AB'; [|done].
    pose proof (load_lessdef_mem p c ABLD) as LDLD.
    rewrite LD0 in LDLD.
    by destruct (load_ptr c nm p) as [] _eqn; eauto with myhints.
  Qed.

  Lemma tso_step_ext_arglist:
    forall stso ttso ttso' locs t vals
    (LD : lessdef_tso stso ttso)
    (MA : Comp.mm_ext_arglist tso_mm ttso t locs vals ttso'),
       Comp.mm_ext_arglist_fail tso_mm stso t locs \/
       exists stso',
         Comp.mm_ext_arglist tso_mm stso t locs vals stso' /\
         lessdef_tso stso' ttso'.
  Proof.
    induction locs as [|h locs IH]; intros; inv MA; eauto with myhints.
      (* Head is a value *)
    - by destruct (IH _ _ LD MA0) as [FAIL | [stso' (MA' & LDtso')]]; 
         eauto with myhints.
    (* Head is a memory location *)
    inv RD. inversion LD; subst.
    pose proof (apply_buffer_lessdef_mem LDM (LDB t)) as ABLD. 
    simpl in AB. rewrite AB in ABLD.
    destruct (apply_buffer (b t) m) as [nm|] _eqn : AB'; [|done].
    pose proof (load_lessdef_mem p c ABLD) as LDLD.
    rewrite LD0 in LDLD.
    destruct (load_ptr c nm p) as [v'|] _eqn : LDx; [|done].
    destruct (IH _ _ LD MA0) as [FAIL | [stso' (MA' & LDtso')]]; 
      [by eauto with myhints|].
    destruct (val_of_eval_dec v') as [[ev' <-] | NVOE]; [|by eauto with myhints].
    apply lessdef_val_of_eval, val_of_eval_eq in LDLD. subst ev'.
    by right; eauto 8 with myhints.
  Qed.

  Lemma tso_step_nomem_sim:
    forall {stso ttso ev ttso'}
      (LD : lessdef_tso stso ttso)
      (TST: tso_step ttso ev ttso')
      (NM : match ev with MMmem _ _ => False | _ => True end),
      exists stso',
        tso_step stso ev stso' /\
        lessdef_tso stso' ttso'.
  Proof.
    intros.
    inv TST; try done;
      try (by exists stso; split; [|assumption]; econstructor; [edone|];
        intro US; elim UNS; refine (unbuffer_safe_lessdef_rev _ _ _ US);
          by apply buffer_insert_lessdef_tso).
    (* Read fail *)
    exists stso; split; [|assumption]; econstructor; inv LD; simpl in *.
    - specialize (LDB t). rewrite Bemp in LDB. by inv LDB.
    - pose proof (load_lessdef_mem p c LDM) as LDLD.
      rewrite LD0 in LDLD. by destruct (load_ptr c m p).
    (* Free fail *)
    exists stso; split; [|assumption]; econstructor; inv LD; simpl in *.
    - by generalize (LDB t); rewrite Bemp; inversion 1.
    pose proof (free_lessdef_mem p k LDM).
    do 2 (destruct free_ptr; clarify); des.
    eexists tid'.
    specialize (LDB tid'). 
    destruct (b' tid'); clarify. 
    destruct (b tid') as [|[]]; inv LDB; clarify.
    pose proof (apply_buffer_item_lessdef_mem H H4); simpl in *.
    repeat eexists; try done.
    by do 2 (destruct store_ptr; clarify).
    (* Out of memory *)
    exists stso; split; [|assumption]; econstructor.
    intros p US. elim (OOM p).
    refine (unbuffer_safe_lessdef_rev _ _ _ US);
    by apply buffer_insert_lessdef_tso.
    (* Unbuffer *)
    inversion LD; subst. 
    specialize (LDB t). simpl in *. rewrite EQbufs in LDB.
    inversion LDB as [|bi1 bt1 bi2 bt2 LDBI LDBF E1 E2]. subst.
    pose proof (apply_buffer_item_lessdef_mem LDM LDBI) as LDAB.
    rewrite AB in LDAB.
    destruct (apply_buffer_item bi1 m) as [nm'|] _eqn : ABI'; [|done].
    eexists. split. econstructor; try edone; eby symmetry.
    by eapply unbuffer_lessdef_tso; try edone.
    (* Thread start *)    
    eexists; split; [by vauto|]. 
    inv LD. split. done.
    intro t'; destruct (peq t' newtid) as [<- | N].
      rewrite !tupdate_s. by constructor.
    by rewrite !tupdate_o; auto.
    (* Thread exit *)
    eexists; split.
      econstructor.
      inv LD. simpl in *. specialize (LDB t).
      by rewrite Bemp in LDB; inv LDB.
    done. 
  Qed.

End TSOresults.


(** * TSO backward simulation from per-thread backward simulation *)

Module TSOsim_with_undefs.

Section TSObackwardsim.

  Variables (Src Tgt : SEM).

  (** Let as assume that there is a relation on global environments and
      a simulation relation on states. *)
  Variable genv_rel  : Src.(SEM_GE) -> Tgt.(SEM_GE) -> Prop.
  Variable st_rel    : Src.(SEM_GE) -> Tgt.(SEM_GE) -> Tgt.(SEM_ST) -> Src.(SEM_ST) -> Prop.
  Variable st_order  : Src.(SEM_GE) -> Tgt.(SEM_GE) -> Tgt.(SEM_ST) -> Tgt.(SEM_ST) -> Prop.
  Variable match_prg : Src.(SEM_PRG) -> Tgt.(SEM_PRG) -> Prop.

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

  (** Suppose that the initial states of threads spawned in related 
     environments are related. *)
  Hypothesis thread_init_related:
    forall sge tge tgt_init fnp args args'
      (GENVR : genv_rel sge tge)
      (INIT : Tgt.(SEM_init) tge fnp args = Some tgt_init)
      (LD    : Val.lessdef_list args' args),
      exists src_init,
        Src.(SEM_init) sge fnp args' = Some src_init /\
        st_rel sge tge tgt_init src_init.

  (* This is not really needed but it simplifies the proof for now
     (and it should be true for our languages). *)
  Hypothesis thread_init_related_none:
    forall sge tge fnp args args'
      (GENVR : genv_rel sge tge)
      (INITF : Tgt.(SEM_init) tge fnp args = None)
      (LD    : Val.lessdef_list args' args),
      Src.(SEM_init) sge fnp args' = None.

  (** ... and assume that there is a per-thread backward simulation in
     related environments. *)
  Hypothesis thread_backward_sim:
    forall sge tge
      (GENR : genv_rel sge tge),
      backward_sim_with_undefs
                               (mklts thread_labels (Src.(SEM_step) sge))
                               (mklts thread_labels (Tgt.(SEM_step) tge))
                               te_ldo
                               te_ldi
                               (st_rel sge tge)
                               (st_order sge tge).

  (** We extend this simulation to the simulation on the tso_states *)
  Definition tso_rel sge tge (sst : Comp.state tso_mm Src) (tst : Comp.state tso_mm Tgt)  :=
     let '((stso, srct), (ttso, tgtt)) := (sst, tst) in
       lessdef_tso stso ttso /\
       forall t, srct ! t = None /\ tgtt ! t = None \/
         exists ss, exists ts, srct ! t = Some ss /\
                               tgtt ! t = Some ts /\
                               st_rel sge tge ts ss.

  Definition tso_order sge tge (t1 t2 : Comp.state tso_mm _) := 
       PTree.order (st_order sge tge) (snd t1) (snd t2) /\ fst t1 = fst t2.

  (** For each intial state of the target TSO there is a corresponding 
      initial state of the source machine. *)
  Theorem tso_init_related: 
    forall src_prog tgt_prog args tge tstate,
      match_prg src_prog tgt_prog ->
      Comp.init _ _ tgt_prog args tge tstate ->
      exists sge, exists sstate,
        Comp.init _ _ src_prog args sge sstate /\ genv_rel sge tge /\
        tso_rel sge tge sstate tstate.
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
    split.
      done.
    repeat (split; try by simpl; try apply unbuffer_safe_unbuffer).
    - intro; constructor.
    intro t. 
    destruct (tid_eq_dec t mtid) as [Eq|Neq]; clarify.
      by right; exists smt; exists mtst; rewrite !PTree.gss. 
    left; rewrite !PTree.gso, !PTree.gempty; tauto.
  Qed.

  Lemma wf_tso_order:
    forall sge tge (GREL: genv_rel sge tge), well_founded (tso_order sge tge).
  Proof.
    intros; apply thread_backward_sim, proj1, PTree.order_wf in GREL.
    intros [tso threads].
    eapply (well_founded_ind GREL (fun x, Acc (tso_order sge tge) (tso, x))).
    intros x IH; apply Acc_intro.
    intros [tso' x']; unfold tso_order; simpl; intros [H1 ->].
    by apply IH. 
  Qed.

  Section TSObackwardsim1.

  Variables (sge : Src.(SEM_GE)) (tge : Tgt.(SEM_GE)).
  Variable (sge_tge_rel : genv_rel sge tge).

  Let srctsolts := (mklts event_labels (Comp.step tso_mm _ sge)).
  Let tgttsolts := (mklts event_labels (Comp.step tso_mm _ tge)).

  Let srclts := (mklts thread_labels (SEM_step _ sge)).
  Let tgtlts := (mklts thread_labels (SEM_step _ tge)).

  Lemma tso_rel_buff_empty:
    forall {ttso tthr stso sthr t},
      tso_rel sge tge (stso, sthr) (ttso, tthr) ->
      tso_buffers ttso t = nil ->
      tso_buffers stso t = nil.
  Proof. 
    destruct 1 as [[] _].
    simpl. specialize (LDB t). intro E. rewrite E in LDB. by inv LDB.
  Qed.

  Hint Resolve taustar_refl.

  Lemma stuck_rel_tau_stuck_aux:
    forall (tl : list thread_id) stso ttso sthr tthr,
      (forall t ts, tthr!t = Some ts -> False) ->
      tso_rel sge tge (stso, sthr) (ttso, tthr) ->
      exists thr', 
        taustar srctsolts (stso, sthr) (stso, thr') /\ 
        ((exists t, exists ts, exists e, exists ts',
          thr' ! t = Some ts /\ e = TEext Efail /\
          Src.(SEM_step) sge ts e ts') \/
        forall t, 
          (sthr ! t = None /\ thr' ! t = None) \/
          (~ In t tl /\ sthr ! t = thr' ! t)).
  Proof.
    intros tl stso ttso sthr tthr TSTUCK REL. 
    induction tl as [|it irest IH]. 
    (* Base case *)
    exists sthr; split; try done.
    by right; right; auto. 

    (* Step case *)
    destruct IH as [thri [TST [ERR | IH]]].
    (* If error in the IH, we are done... *)
    exists thri. split; auto.

    destruct (tthr ! it) as [tits|] _eqn : Etit.
    (* Stuck in target -> use backward simulation *)
    by pose proof (TSTUCK it tits Etit). 
    exists thri.
    split; try done.
    right. intro t.
    destruct (IH t) as [[SN TN] | [NI E]];
      try (repeat (try (left; tauto); right); fail).
    destruct (tid_eq_dec it t) as [Eitt | Neitt]. 
      subst. 
      destruct (proj2 REL t) 
        as [[RELN _]|[sit [tst [Esit [Etst RELs]]]]].
        left. rewrite <- E; split; auto.
        by rewrite Etit in Etst. 
    right; split; auto. intro NINit.
    destruct (in_inv NINit); subst; auto.
  Qed.

  Lemma stuck_rel_tau_stuck:
    forall stso ttso sthr tthr,
      (forall t ts, tthr!t = Some ts -> False) ->
      tso_rel sge tge (stso, sthr) (ttso, tthr) ->
      exists thr', 
        taustar srctsolts (stso, sthr) (stso, thr') /\ 
        ((exists t, exists ts, exists e, exists ts',
          thr' ! t = Some ts /\ e = TEext Efail /\ SEM_step _ sge ts e ts') \/
        forall t, thr' ! t = None).
  Proof.
    intros stso ttso sthr tthr STUCK REL.
    destruct (stuck_rel_tau_stuck_aux (ptkeys sthr) _ _ _ _ STUCK REL) as
      [tso' [TAU [ERR | SP]]].
    by exists tso'; split; [|left]. 
    exists tso'. split. auto. right.
    intro t. destruct (SP t) as [H |[H E]];
      try (repeat (try (try left; tauto); right); fail).
    destruct (sthr ! t) as [sit|] _eqn : Esit; try done.
    elim H. apply (proj2 (ptkeys_spec _ _)).
    by rewrite Esit.
  Qed.

  Lemma backward_sim_sandwich_step:
    forall sthr stso tthr ttso tso' stso' t ss ss1 ss' ts e
      (STREL: st_rel sge tge ts ss')
      (TSOREL: tso_rel sge tge (stso, sthr) (ttso, tthr))
      (Ess: sthr ! t = Some ss)
      (TGTST: Comp.step _ _ tge (ttso, tthr) e (tso', tthr ! t <- ts))
      (TAU1: taustar srclts ss ss1)
      (TLD: lessdef_tso stso' tso')
      (MST: forall thr',
        thr' ! t = Some ss1 ->
        (forall t', t <> t' -> sthr ! t' = thr' ! t') ->
        Comp.step _ _ sge (stso, thr') e (stso', thr' ! t <- ss')),
      exists srcs,
        taustep srctsolts (stso, sthr) e srcs /\
        tso_rel sge tge srcs (tso', tthr ! t <- ts).
  Proof.
    intros.
    destruct (taustar_to_comp _ _ stso Ess TAU1) 
      as [sthr1 [STAU1 [SP1 ST1]]].
    pose proof (MST sthr1 ST1 SP1) as SSTEP1.
    eexists. 
    split. by econstructor; econstructor; eauto. 
    split; [done|].
    intro ot. destruct (tid_eq_dec ot t). subst.
      by right; eexists ss'; exists ts; rewrite !PTree.gss.
    by rewrite !PTree.gso, <- SP1; auto; apply (proj2 TSOREL). 
  Qed.

  (** The main theorem for converting a thread-local simulation to a TSO simulation *)

  Lemma tso_backward_sim:
    well_founded  (tso_order sge tge) /\
    (forall s t, stuck tgttsolts t -> tso_rel sge tge s t ->
        Comp.consistent _ _ s -> Comp.consistent _ _ t ->
      exists s', taustar srctsolts s s' /\ stuck_or_error _ s') /\
    (forall s t l t', stepr tgttsolts t l t' -> tso_rel sge tge s t ->
        Comp.consistent _ _ s -> Comp.consistent _ _ t ->
      (exists s', taustep srctsolts s l s' /\ tso_rel sge tge s' t') \/
      (l = tau _ /\ tso_rel sge tge s t' /\ tso_order sge tge t' t) \/
      (exists s', taustar srctsolts s s' /\ can_do_error _ s')).
  Proof.
    split; [by apply wf_tso_order|].
    split.
    (* Stuck state correspondence. *)
    intros [stso sthr] [ttso tthr] STUCK REL sCONS tCONS.
    pose proof (Comp.stuck_imp_no_threads _ _ _ _ tCONS (fun l s' => STUCK s' l)) as STK.
    eexists; split; try done.
    left; red; simpl; intros.
    eapply (Comp.no_threads_stuck _ _ _ _ _ _ sCONS); eauto; simpl in *.
    eapply PTree.ext; intro t; clarify.
    by destruct (proj2 REL t); des; rewrite PTree.gempty in *.
    (* Transition correspondence *)
    intros [stso sthr] [ttso tthr] l t' TSTEP TREL sCONS tCONS; simpl in *.
    pose proof TREL as [LD REL].
    destruct (thread_backward_sim _ _ sge_tge_rel) as [_ [SS BS]].
    (comp_step_cases (inversion TSTEP
        as [os os' ev ot tso tso' st st' SST TST TG TS | 
            os os' ev tso st st' ot SST TG TS | 
            tso tso' st TST | 
            os os' ot tso st st' SST TG TS | 
            os os' newtid p v ot tso tso' st st' sinit SST TST TG TGN TS IN | 
            os os' p v ot tso st SST TG IN | 
            os os' ot tso tso' st SST TST TG | 
            os os' ot tso tso' st st' p c v SST TST TG TS |
            os os' ot tso tso' st st' p c v SST TST TG TS | 
            os os' ot tso tso' st st' p k SST TST TG TS |
            os os' ot tso tso' st st' p c v instr SST TST TG TS |
            os ot tso st NO_STEP TG |
            os os' ot tso tso' st st' p n k SST TST TG TS |
            os os' ot tso st st' SST TG TS |
            os os' largs args ot tso tso' st st' id SST TST TG TS |
            os os' largs ot tso st st' id SST TST TG TS | 
            os os' args ot tso tso' tso''  st st' v sinit newtid fn p SST TST TST2 TG TGN TS IN |
            os os' args ot tso st st' fn SST TST TG TS |
            os os' ot tso st st' lfn largs fn args tso' SST TST TG IN TS]) Case); subst;
      first [Case "step_unbuf" | destruct (REL ot) as [[? ?] | [ss [ts [Est [Ett RELs]]]]]]; 
      try rewrite TG in *; clarify;
      try destruct (BS _ _ _ _ SST RELs) 
            as [[ISTAU [NREL ORD]] | 
                 [ERROR | 
                  [[ts' [l' (LDO & [ts1 (TAU1 & MST)] & RELts')]] | 
                    LDIIMPL]]];
(*      try done; *)
      try (eby right; right; destruct TREL; eapply thread_ev_stuck_to_comp_tau_error);
      try (by pose proof LDO as _; destruct l' as [|[]| | | | | |]);
      try (by destruct (LDIIMPL _ (ldi_refl _)) as [ts' [[ts1 (TAU1 & MST)] RELts']];
              try destruct (tso_step_nomem_sim LD TST I) as [stso' [TST' LD']];
                left; eapply backward_sim_sandwich_step; try eassumption; []; vauto).

    Case "step_ord".
      (* LDO case *)
      by left; destruct (ldo_step_simulation LD TST LDO) 
        as [ev' [stso' (-> & TST' & LD')]];
          eapply backward_sim_sandwich_step; try eassumption; []; vauto.

      (* LDI case *)
      left.
      destruct (tso_step_ldi LD TST) as [ev' [stso' (LDI & TST' & LD')]].
      destruct (LDIIMPL _ LDI) as [ts' [[ts1 (TAU1 & MST)] RELts']].
      by eapply backward_sim_sandwich_step; try eassumption; []; vauto.

    Case "step_unbuf".
      destruct (tso_step_nomem_sim LD TST I) as [stso' [TST' LD']].
      assert (WS : taustep srctsolts (stso, sthr) Etau (stso', sthr)).
        by eapply step_taustep; simpl; vauto.
      left; eexists (_, _); split. edone.
      split. done. 
      apply REL.
    Case "step_tau".
      (* stutter decreases order in the tso parallel composition state*)
      right; left. 
      split. done.
      split. split. by apply (proj1 TREL).
      intro xt. destruct (tid_eq_dec xt ot). subst.
          right. exists ss. exists os'. rewrite PTree.gss; auto.
      repeat rewrite PTree.gso; auto. 
      by split; try done; apply (PTree.order_set_lt _ _ _ _ TG ORD).  
    Case "step_start".
      (* There is a matching step in source *)
      left.
      destruct (tso_step_nomem_sim LD TST I) as [stso' [TST' LD']].
      destruct l' as [| [] | | | p' v' | | |]; try done.
      destruct LDO as [-> LDv].
      destruct (taustar_to_comp tso_mm _ stso Est TAU1) 
        as [sthr1 [STAU1 [SP1 ST1]]].
      destruct (thread_init_related _ _ _ _ _ _ sge_tge_rel IN LDv) 
        as [inits [INITS INREL]].
      destruct (REL newtid) as [[NTIDN _] | [ds [dt [_ [Edt _]]]]];
        try (rewrite Edt in TGN; discriminate).
      destruct (tid_eq_dec ot newtid) as [NTE | NTNE]. 
        rewrite NTE, NTIDN in Est; discriminate.
      rewrite SP1 in NTIDN; auto.
      pose proof (Comp.step_start tso_mm _ _ _ _ _  _ _ _ _  _ _ _ _ 
        MST TST' ST1 NTIDN (refl_equal _) INITS) as STARTST.
      set (sthr' := (sthr1 ! ot <- ts') ! newtid <- inits). 
      assert (ETS2: sthr' ! ot = Some ts'). 
        by unfold sthr'; rewrite PTree.gso, PTree.gss; auto.
      econstructor. 
      split. eexists. split. apply STAU1. by vauto.
      split; try done.
      intro t. 
      destruct (tid_eq_dec t ot). subst.
        by right; exists ts'; exists os'; repeat rewrite PTree.gso, PTree.gss.
      unfold sthr' in *.
      destruct (tid_eq_dec t newtid). subst. 
        by right; exists inits; exists sinit; rewrite !PTree.gss.
      by rewrite !PTree.gso, <- SP1; auto; apply (proj2 REL). 
      
      (* TODO : Reuse the almost-the-same bit above *)
      destruct (tso_step_nomem_sim LD TST I) as [stso' [TST' LD']].
      destruct (LDIIMPL _ (ldi_refl _)) as [ts' [[ts1 (TAU1 & MST)] RELts']].
      left.
      destruct (taustar_to_comp tso_mm _ stso Est TAU1) 
        as [sthr1 [STAU1 [SP1 ST1]]].
      destruct (thread_init_related _ _ _ _ _ _ sge_tge_rel IN 
        (Val.lessdef_list_refl _)) as [inits [INITS INREL]].
      destruct (REL newtid) as [[NTIDN _] | [ds [dt [_ [Edt _]]]]];
        try (rewrite Edt in TGN; discriminate).
      destruct (tid_eq_dec ot newtid) as [NTE | NTNE]. 
        rewrite NTE, NTIDN in Est; discriminate.
      rewrite SP1 in NTIDN; auto.
      pose proof (Comp.step_start tso_mm _ _ _ _ _  _ _ _ _  _ _ _ _ 
        MST TST' ST1 NTIDN (refl_equal _) INITS) as STARTST.
      set (sthr' := (sthr1 ! ot <- ts') ! newtid <- inits). 
      assert (ETS2: sthr' ! ot = Some ts'). 
        by unfold sthr'; rewrite PTree.gso, PTree.gss; auto.
      econstructor. 
      split. eexists. split. apply STAU1. by vauto.
      split; try done.
      intro t. 
      destruct (tid_eq_dec t ot). subst.
        by right; exists ts'; exists os'; repeat rewrite PTree.gso, PTree.gss.
      unfold sthr' in *.
      destruct (tid_eq_dec t newtid). subst. 
        by right; exists inits; exists sinit; rewrite !PTree.gss.
      by rewrite !PTree.gso, <- SP1; auto; apply (proj2 REL). 
    Case "step_start_fail".
      (* There is a matching step in source *)
      destruct l' as [| [] | | | p' v'| | |]; try done.
      destruct LDO as [-> LDv].
      left.
      eapply (backward_sim_sandwich_step); try eassumption. 
      intros thr' TS1 _.
      pose proof (thread_init_related_none _ _ _ _ _ sge_tge_rel IN LDv) as IN'.
      eby eapply Comp.step_start_fail.

      (* TODO : Reuse the almost-the-same bit above *)
      destruct (LDIIMPL _ (ldi_refl _)) as [ts' [[ts1 (TAU1 & MST)] RELts']].
      left.
      eapply (backward_sim_sandwich_step); try eassumption. 
      intros thr' TS1 _.
      pose proof (thread_init_related_none _ _ _ _ _ sge_tge_rel IN 
        (Val.lessdef_list_refl _)) as IN'.
      eby eapply Comp.step_start_fail.
    Case "step_exit".
      (* There is a matching step in source *)
      destruct (tso_step_nomem_sim LD TST I) as [stso' [TST' LD']].
      destruct (LDIIMPL _ (ldi_refl _)) as [ts' [[ts1 (TAU1 & MST)] RELts']].
      left.
      destruct (taustar_to_comp tso_mm _ stso Est TAU1) 
        as [sthr1 [STAU1 [SP1 ST1]]].
      pose proof (Comp.step_exit tso_mm _ _ _ _ _ _ _ _
        MST TST' ST1) as EXITST.
      econstructor. split.
        eby eexists; eexists. 
      split; [done|].
      intro t.
      destruct (tid_eq_dec t ot); clarify.
        by left; rewrite !PTree.grs.
      by rewrite !PTree.gro, <- SP1; auto; apply (proj2 REL).
    Case "step_write_fail".
      left. destruct l' as [|[]| | | | | |]; try done.
      destruct LDO as [-> [-> LDV]]. inv TST.
      assert(TST' : tso_step stso (MMreadfail ot p c) stso).
        econstructor; try edone.
        - eby eapply tso_rel_buff_empty.
        revert LD0; destruct LD; simpl.
        by generalize (load_lessdef_mem p c LDM); clear; do 2 (destruct load_ptr; clarify).
      by eapply backward_sim_sandwich_step; try eassumption; []; vauto.
    Case "step_free_fail".
      destruct (LDIIMPL _ (ldi_refl _)) as [ts' [[ts1 (TAU1 & MST)] RELts']].
      destruct (taustar_to_comp tso_mm _ stso Est TAU1) as [sthr1 [STAU1 [SP1 ST1]]].
      eapply tso_step_nomem_sim in TST; try edone; des.
      right; right; eexists; split; try edone. 
      by eexists (_, _); exists (Evisible Efail); split; simpl; vauto.
    Case "step_thread_stuck".
      exploit SS; [|apply RELs|intros ERROR].
      - by intros s' l' STEP; specialize (NO_STEP _ _ STEP).
      eby right; right; destruct TREL; eapply thread_ev_stuck_to_comp_tau_error.
    Case "step_extcallmem".
      destruct (LDIIMPL _ (ldi_refl _)) as [ts' [[ts1 (TAU1 & MST)] RELts']].
      destruct (tso_step_ext_arglist _ _ _ _ _ _ LD TST) 
        as [FAIL | [stso' (MEA' & LD')]].
      (* Failed memory reads *)
      right. right.
      destruct (taustar_to_comp tso_mm _ stso Est TAU1) 
        as [sthr1 [STAU1 [SP1 ST1]]].
      eexists. split. edone.
      eexists (_, _). exists (Evisible Efail). split. done.
      simpl. eby eapply Comp.step_extcallmem_fail.
      (* Memory reads of arguments successful *)
      left. eapply backward_sim_sandwich_step; try eassumption; vauto.
    Case "step_extcallmem_fail".
      destruct (LDIIMPL _ (ldi_refl _)) as [ts' [[ts1 (TAU1 & MST)] RELts']].
      pose proof (tso_step_ext_arglist_fail _ _ _ _ LD TST) as FAIL.      
      right; right.
      destruct (taustar_to_comp tso_mm _ stso Est TAU1) 
        as [sthr1 [STAU1 [SP1 ST1]]].
      eexists. split. edone.
      eexists (_, _). exists (Evisible Efail). split. done.
      simpl. eby eapply Comp.step_extcallmem_fail.
    Case "step_startmem".
      (* LDO case *)
      destruct l' as [| [] | | | | |fn' args'|]; try done.
      destruct LDO as [-> LDargs].
      pose proof (lessdef_listsum_pfx fn LDargs) as LDfnargs.
      destruct (tso_step_arglist _ _ _ _ _ _ _ LD LDfnargs TST) 
        as [stsoi [svals (LDsvals & MAi & LDstsoi)]].
      destruct (tso_step_nomem_sim LDstsoi TST2 I) as [stso' [TST' LD']].
      destruct (taustar_to_comp tso_mm _ stso Est TAU1) 
        as [sthr1 [STAU1 [SP1 ST1]]].
      inversion LDsvals as [|hsvals ? tsvals ? LDhsvals LDtsvals]; subst.
      destruct (thread_init_related _ _ _ _ _ _ sge_tge_rel IN LDtsvals) 
        as [inits [INITS INREL]].
      destruct (REL newtid) as [[NTIDN _] | [ds [dt [_ [Edt _]]]]];
        try (rewrite Edt in TGN; discriminate).
      destruct (tid_eq_dec ot newtid) as [NTE | NTNE]. 
        rewrite NTE, NTIDN in Est; discriminate.
      rewrite SP1 in NTIDN; auto.
      inv LDhsvals.
      (* the function pointer is Vptr in the source *)
      pose proof (Comp.step_startmem tso_mm _ _ _ _ _  _ _ _ _  _ _ _ _ _ _ _ 
        MST MAi TST' ST1 NTIDN (refl_equal _) INITS) as STARTST.
      set (sthr' := (sthr1 ! ot <- ts') ! newtid <- inits). 
      assert (ETS2: sthr' ! ot = Some ts'). 
        by unfold sthr'; rewrite PTree.gso, PTree.gss; auto.
      left; econstructor. 
      split. eexists. split. apply STAU1. by vauto.
      split; try done.
      intro t. 
      destruct (tid_eq_dec t ot). subst.
        by right; exists ts'; exists os'; repeat rewrite PTree.gso, PTree.gss.
      unfold sthr' in *.
      destruct (tid_eq_dec t newtid). subst. 
        by right; exists inits; exists sinit; rewrite !PTree.gss.
      by rewrite !PTree.gso, <- SP1; auto; apply (proj2 REL). 
      (* the function pointer is Vundef in the source => error! *)
      right; right. 
      eexists. split. edone.
      eexists (_, _); exists (Evisible Efail). split. done.
      simpl. eby eapply Comp.step_startmem_spawn_fail.

      (* LDI case *)      
      (* TODO : Reuse the almost-the-same bit above *)
      destruct (LDIIMPL _ (ldi_refl _)) as [ts' [[ts1 (TAU1 & MST)] RELts']].
      pose proof (lessdef_listsum_refl (fn :: args)) as LDfnargs.
      destruct (tso_step_arglist _ _ _ _ _ _ _ LD LDfnargs TST) 
        as [stsoi [svals (LDsvals & MAi & LDstsoi)]].
      destruct (tso_step_nomem_sim LDstsoi TST2 I) as [stso' [TST' LD']].
      destruct (taustar_to_comp tso_mm _ stso Est TAU1) 
        as [sthr1 [STAU1 [SP1 ST1]]].
      inversion LDsvals as [|hsvals ? tsvals ? LDhsvals LDtsvals]; subst.
      destruct (thread_init_related _ _ _ _ _ _ sge_tge_rel IN LDtsvals) 
        as [inits [INITS INREL]].
      destruct (REL newtid) as [[NTIDN _] | [ds [dt [_ [Edt _]]]]];
        try (rewrite Edt in TGN; discriminate).
      destruct (tid_eq_dec ot newtid) as [NTE | NTNE]. 
        rewrite NTE, NTIDN in Est; discriminate.
      rewrite SP1 in NTIDN; auto.
      inv LDhsvals.
      (* the function pointer is Vptr in the source *)
      pose proof (Comp.step_startmem _ _ _ _ _ _  _ _ _ _  _ _ _ _ _ _ _ 
        MST MAi TST' ST1 NTIDN (refl_equal _) INITS) as STARTST.
      set (sthr' := (sthr1 ! ot <- ts') ! newtid <- inits). 
      assert (ETS2: sthr' ! ot = Some ts'). 
        by unfold sthr'; rewrite PTree.gso, PTree.gss; auto.
      left; econstructor. 
      split. eexists. split. apply STAU1. by vauto.
      split; try done.
      intro t. 
      destruct (tid_eq_dec t ot). subst.
        by right; exists ts'; exists os'; repeat rewrite PTree.gso, PTree.gss.
      unfold sthr' in *.
      destruct (tid_eq_dec t newtid). subst. 
        by right; exists inits; exists sinit; rewrite !PTree.gss.
      by rewrite !PTree.gso, <- SP1; auto; apply (proj2 REL). 
      (* the function pointer is Vundef in the source => error! *)
      right; right. 
      eexists. split. edone.
      eexists (_, _); exists (Evisible Efail). split. done.
      simpl. eby eapply Comp.step_startmem_spawn_fail.
    Case "step_startmem_read_fail".
      (* LDO case *)
      destruct l' as [| [] | | | | |fn' args'|]; try done.
      destruct LDO as [-> LDargs].
      pose proof (lessdef_listsum_pfx fn LDargs) as LDfnargs.
      destruct (taustar_to_comp tso_mm _ stso Est TAU1) 
        as [sthr1 [STAU1 [SP1 ST1]]].
      right; right. eexists. split. edone.
      pose proof (tso_step_arglist_fail _ _ _ _ _ LD LDfnargs TST) as FAIL.
      eexists (_, _); exists (Evisible Efail). split. done.
      simpl. eby eapply Comp.step_startmem_read_fail. 
      (* LDI case *)
      (* TODO - reuse *)
      destruct (LDIIMPL _ (ldi_refl _)) as [ts' [[ts1 (TAU1 & MST)] RELts']].
      pose proof (lessdef_listsum_refl (fn :: args)) as LDfnargs.
      destruct (taustar_to_comp tso_mm _ stso Est TAU1) 
        as [sthr1 [STAU1 [SP1 ST1]]].
      right; right. eexists. split. edone.
      pose proof (tso_step_arglist_fail _ _ _ _ _ LD LDfnargs TST) as FAIL.
      eexists (_, _); exists (Evisible Efail). split. done.
      simpl. eby eapply Comp.step_startmem_read_fail. 
    Case "step_startmem_spawn_fail".
      (* LDO case *)
      destruct l' as [| [] | | | | |fn' args'|]; try done.
      destruct LDO as [-> LDargs].
      pose proof (lessdef_listsum_pfx lfn LDargs) as LDfnargs.
      destruct (tso_step_arglist _ _ _ _ _ _ _ LD LDfnargs TST) 
        as [stsoi [svals (LDsvals & MAi & LDstsoi)]].
      (*destruct (tso_step_nomem_sim LDstsoi TST2 I) as [stso' [TST' LD']].*)
      destruct (taustar_to_comp tso_mm _ stso Est TAU1) 
        as [sthr1 [STAU1 [SP1 ST1]]].
      inversion LDsvals as [|hsvals ? tsvals ? LDhsvals LDtsvals]; subst.
      right; right. eexists. split. edone.
      eexists (_, _); exists (Evisible Efail). split. done.
      simpl. eapply Comp.step_startmem_spawn_fail; try edone; []. 
      inv LDhsvals. destruct fn; try done.
      eby eapply thread_init_related_none. done. 

      (* LDI case *)
      (* TODO : reuse *)
      destruct (LDIIMPL _ (ldi_refl _)) as [ts' [[ts1 (TAU1 & MST)] RELts']].
      pose proof (lessdef_listsum_refl (lfn :: largs)) as LDfnargs.
      destruct (tso_step_arglist _ _ _ _ _ _ _ LD LDfnargs TST) 
        as [stsoi [svals (LDsvals & MAi & LDstsoi)]].
      (*destruct (tso_step_nomem_sim LDstsoi TST2 I) as [stso' [TST' LD']].*)
      destruct (taustar_to_comp tso_mm _ stso Est TAU1) 
        as [sthr1 [STAU1 [SP1 ST1]]].
      inversion LDsvals as [|hsvals ? tsvals ? LDhsvals LDtsvals]; subst.
      right; right. eexists. split. edone.
      eexists (_, _); exists (Evisible Efail). split. done.
      simpl. eapply Comp.step_startmem_spawn_fail; try edone; [].
      inv LDhsvals. destruct fn; try done.
      eby eapply thread_init_related_none. done. 
    Qed.

  End TSObackwardsim1.

  (** Packaging everything into a [sim] structure. *)

  Definition bsim : Bsim.sim tso_mm tso_mm Src Tgt match_prg.
  Proof.
  apply (@Bsim.make _ _ Src Tgt match_prg
      (fun sge tge s t => genv_rel sge tge /\ tso_rel sge tge s t)
      (fun sge tge t t' => genv_rel sge tge /\ tso_order sge tge t' t)). 
  - intros ? ? [? ?] [? ?] (_ & _ & A) ? ?; simpl.
    by intro X; eapply PTree.ext; intro tid; 
       generalize (A tid); rewrite X, !PTree.gempty;
       intros [(? & ?)|(? & ? & ? & ? & _)].
  - eby intros; exploit tso_init_related.
  - intros; des.
    exploit tso_backward_sim; try edone; [].
    intros [_ [_ X]]; exploit X; try edone; intro; des; eauto.
      eby right; left; eexists.
    by right; right; vauto. 
  Defined.

  Theorem sim : Sim.sim tso_mm tso_mm Src Tgt match_prg.
  Proof.
    apply (@Sim.make _ _ _ _ match_prg bsim); simpl.
    constructor; intros i (REL & _).
    induction i as [i H] using (well_founded_ind (wf_tso_order sge tge REL)).
    by constructor; intros; des; auto.
  Qed.

End TSObackwardsim.

End TSOsim_with_undefs.

