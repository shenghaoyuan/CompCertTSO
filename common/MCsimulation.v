Require Import Coqlib.
Require Import Wellfounded.
Require Import Values.
Require Import Events.
Require Import Ast.
Require Import Globalenvs.
Require Import Maps.
Require Import Simulations.
Require Import Memcomp Traces.
Require Import Libtactics.

Set Implicit Arguments.

(** * Generic results about the composite machine *)

Section MCresults.

  Variables (Mm: MM) (Sem : SEM).
  Let mmlts ge := (mklts event_labels (Comp.step Mm Sem ge)).
  Let lts ge := (mklts thread_labels (SEM_step Sem ge)).

  Hint Resolve taustar_refl.

  (** Lifting thread taustar-transitions to the composite machine. *)

  Lemma taustar_to_comp:
    forall {ge t thr ts ts'} mem
      (E: thr ! t = Some ts)
      (TAU: taustar (lts ge) ts ts'),
      exists thr',
        taustar (mmlts ge) (mem, thr) (mem, thr') /\
        (forall t', t <> t' -> thr!t' = thr'!t') /\
        thr'!t = Some ts'.
  Proof.
    intros; revert thr E.
    induction TAU as [s|s1 s2 s3 ST TST IH]; intros thr E; simpl in *. 
      by eexists.
    destruct (IH (thr ! t <- s2) (PTree.gss _ _ _)) as (thr' & TAU' & OTH & TSP).
    exists thr'.
    split.
      eapply taustar_step; try eassumption; simpl.
      eby eapply Comp.step_tau.
    split; try done.
    by intros t' NE; rewrite <- (OTH t' NE), PTree.gso; auto.
  Qed.

  Lemma taustar_mm_to_comp :
    forall mem mem'
      (TAU: taustar (mklts mm_event_labels (MM_step Mm)) mem mem') ge thr ,
      taustar (mmlts ge) (mem, thr) (mem', thr).
  Proof.
    induction 1; intros; eauto. 
    by eapply taustar_step; eauto; vauto.
  Qed. 

  (** If a thread is eventually stuck, the MC machine can reach an error. *)

  Lemma thread_ev_stuck_to_comp_tau_error: 
    forall ge smem sthr t s
      (STS: sthr ! t = Some s)
      (STUCK: ev_stuck_or_error (lts ge) s)
      (CONS: Comp.consistent Mm Sem (smem, sthr)),
    exists spc, 
      taustar (mmlts ge) (smem, sthr) spc /\ 
      can_do_error (mmlts ge) spc.
  Proof.
    intros; revert smem sthr STS CONS; induction STUCK; try done; intros.
    Case "stuck".
      eexists; split; [by eapply taustar_refl|].
      eexists; exists (Evisible Efail); split; try done; simpl.
      eby eapply Comp.step_thread_stuck. 
    Case "error".
      eexists; split; [by eapply taustar_refl|].
      eexists (_, _); exists (Evisible Efail); split; try done; simpl.
      destruct l as [[]| | | | | | |]; try done.
      eby eapply Comp.step_ext.
    Case "tau".
      simpl in TAUSTEP.
      destruct (IHSTUCK smem (sthr ! t <- s') (PTree.gss _ _ _))
          as (ss & STAU1 & ERR).
      - by eapply Comp.step_preserves_consistency, CONS; vauto.
      by eexists; split; [eapply taustar_step|]; try eassumption; vauto.
    Case "pseudotau".
      destruct l as [|[]| | | | | |]; clarify.
      exploit (MM_can_move Mm).
        by apply CONS.
        instantiate (1 := (MMmem t (MEread p chunk v))); unfold taustep; intro; des.
      SCase "successful load".
      assert (EX: exists s', stepr _ s (TEmem (MEread p chunk v')) s').
        eby eapply (SEM_receptive Sem ge).
      clear STEP; destruct EX as [s'' STEP].
      exploit H; [|eapply STEP|eapply PTree.gss| |]; [done| |]. 
      + eapply Comp.taustep_preserves_consistency, CONS.
        eexists (_, _); split; [eby eapply taustar_mm_to_comp|].
        by simpl in *; vauto.
      + intros (s''' & TAU & ERR').
        eexists; split; [eapply taustar_trans, taustar_step, TAU|edone].
          eby instantiate (1 := (_, _)); eapply taustar_mm_to_comp.
        by simpl in *; eapply Comp.step_ord; try eapply STEP; try edone; vauto.          
      SCase "failed load".
      eexists (_, _); split; [eby eapply taustar_mm_to_comp|].
      eexists (_, _); exists (Evisible Efail); split; [done|].
      simpl; eapply Comp.step_read_fail; try edone.
  Qed.

End MCresults.

Definition ptkeys {A : Type} (m : PTree.t A) := 
  map (@fst positive A) (PTree.elements m).

Lemma ptkeys_spec: 
  forall (A : Type) (m : PTree.t A) (i : positive),
    In i (ptkeys m) <-> 
    match m!i with 
      | Some _ => True 
      | None => False
    end.
Proof.
  split; intro IN. 
  destruct (proj1 (in_map_iff (@fst positive A) (PTree.elements m) i) IN)
    as [[i' e] [Ei INM]]; simpl in *; clarify. 
    by apply PTree.elements_complete in INM; rewrite INM; auto.
  destruct (m!i) as [h|] _eqn : E; clarify. 
  apply PTree.elements_correct in E. 
  by apply (in_map (@fst positive A)) in E. 
Qed.

(** * Machine backward simulation from per-thread backward simulation *)

Module MCsim.

Section MCbackwardsim.

  Variable (Mm : MM).
  Variable allow_pseudotaus: bool.
  Hypothesis pseudotau_cond: allow_pseudotaus -> MM_pure_load_condition Mm.

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
    forall sge tge tgt_init fnp args
      (GENVR : genv_rel sge tge)
      (INIT : Tgt.(SEM_init) tge fnp args = Some tgt_init),
      exists src_init,
        Src.(SEM_init) sge fnp args = Some src_init /\
        st_rel sge tge tgt_init src_init.

  (* This is not really needed but it simplifies the proof for now
     (and it should be true for our languages). *)
  Hypothesis thread_init_related_none:
    forall sge tge fnp args
      (GENVR : genv_rel sge tge)
      (INITF : Tgt.(SEM_init) tge fnp args = None),
      Src.(SEM_init) sge fnp args = None.

  (** ... and assume that there is a per-thread backward simulation in
     related environments. *)
  Hypothesis thread_backward_sim:
    forall sge tge
      (GENR : genv_rel sge tge),
      backward_sim
                   (mklts thread_labels (Src.(SEM_step) sge))
                   (mklts thread_labels (Tgt.(SEM_step) tge))
                   allow_pseudotaus
                   (st_rel sge tge)
                   (st_order sge tge).

    (** We extend this simulation to the simulation on the Comp.states *)
    Definition mm_rel sge tge (sst : Comp.state Mm Src) (tst : Comp.state Mm Tgt)  :=
       let '((smem, srct), (tmem, tgtt)) := (sst, tst) in
         smem = tmem /\ forall t, srct ! t = None /\
                                  tgtt ! t = None \/
                                  exists ss, exists ts,
                                    srct ! t = Some ss /\
                                    tgtt ! t = Some ts /\
                                    st_rel sge tge ts ss.
    
    Definition mm_order sge tge (t1 t2 : Comp.state Mm _) := 
         PTree.order (st_order sge tge) (snd t1) (snd t2) /\ fst t1 = fst t2.

    (** For every intial state of the target machine, 
        there is a corresponding initial state of the source machine. *)
    Lemma mm_init_related: 
      forall src_prog tgt_prog args tge tstate,
        match_prg src_prog tgt_prog ->
        Comp.init _ _ tgt_prog args tge tstate ->
        exists sge, exists sstate,
          Comp.init _ _ src_prog args sge sstate /\ genv_rel sge tge /\
          mm_rel sge tge sstate tstate.
    Proof.
      intros until 0. 
      intros MP [mtst [mtid [inm [mp [GEINIT [GEMAIN [MINIT Etst]]]]]]]; clarify. 
      destruct (ge_init_related _ _ MP GEINIT) as [sge [SGEINIT GEREL]].
      destruct (thread_init_related _ _ GEREL MINIT)
        as [smt [SMINIT mREL]].
      exists sge.
      eexists (_, (PTree.empty Src.(SEM_ST)) ! mtid <- smt).
      split. 
        exists smt; exists mtid; exists inm; exists mp.
        repeat split; try assumption.
        by rewrite (main_ptr_eq MP GEREL), <- GEMAIN.
      split.
        done.
      repeat (split; try by simpl; try apply unbuffer_safe_unbuffer).
      intro t. 
      destruct (tid_eq_dec t mtid) as [Eq|Neq]; clarify.
        by right; exists smt; exists mtst; rewrite !PTree.gss. 
      left; rewrite !PTree.gso, !PTree.gempty; tauto.
    Qed.

    Lemma wf_mm_order:
      forall sge tge (GREL: genv_rel sge tge), well_founded (mm_order sge tge).
    Proof.
      intros; apply thread_backward_sim, proj1, PTree.order_wf in GREL.
      intros [mem threads].
      eapply (well_founded_ind GREL (fun x, Acc (mm_order sge tge) (mem, x))).
      intros x IH; apply Acc_intro.
      intros [mem' x']; unfold mm_order; simpl; intros [H1 ->].
      by apply IH. 
    Qed.

    Section MCbackwardsim1.

    Variables (sge : Src.(SEM_GE)) (tge : Tgt.(SEM_GE)).
    Variable (sge_tge_rel : genv_rel sge tge).

    Let srcmemlts := (mklts event_labels (Comp.step Mm _ sge)).
    Let tgtmemlts := (mklts event_labels (Comp.step Mm _ tge)).

    Let srclts := (mklts thread_labels (SEM_step _ sge)).
    Let tgtlts := (mklts thread_labels (SEM_step _ tge)).

    Hint Resolve taustar_refl.

    Lemma stuck_rel_tau_stuck_aux:
      forall (tl : list thread_id) smem tmem sthr tthr
        (TSTUCK: forall t ts, tthr!t = Some ts -> False)
        (REL: mm_rel sge tge (smem, sthr) (tmem, tthr)),
        exists thr', 
          taustar srcmemlts (smem, sthr) (smem, thr') /\ 
          ((exists t, exists ts, exists e, exists ts',
            thr' ! t = Some ts /\ e = TEext Efail /\
            Src.(SEM_step) sge ts e ts') \/
          forall t, 
            (sthr ! t = None /\ thr' ! t = None) \/
            (~ In t tl /\ sthr ! t = thr' ! t)).
    Proof.
      intros; induction tl as [|it irest IH]; [by eauto 8|]. 
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
      forall smem tmem sthr tthr,
        (forall t ts, tthr!t = Some ts -> False) ->
        mm_rel sge tge (smem, sthr) (tmem, tthr) ->
        exists thr', 
          taustar srcmemlts (smem, sthr) (smem, thr') /\ 
          ((exists t, exists ts, exists e, exists ts',
            thr' ! t = Some ts /\ e = TEext Efail /\ SEM_step _ sge ts e ts') \/
          forall t, thr' ! t = None).
    Proof.
      intros smem tmem sthr tthr STUCK REL.
      destruct (stuck_rel_tau_stuck_aux (ptkeys sthr) STUCK REL) as
        [mem' [TAU [ERR | SP]]].
      by exists mem'; split; [|left]. 
      exists mem'. split. auto. right.
      intro t. destruct (SP t) as [H |[H E]];
        try (repeat (try (try left; tauto); right); fail).
      destruct (sthr ! t) as [sit|] _eqn : Esit; try done.
      elim H. apply (proj2 (@ptkeys_spec _ _ _)).
      by rewrite Esit.
    Qed.

    Lemma backward_sim_sandwich_step:
      forall sthr smem tthr tmem mem' t ss ss1 ss' ts e
        (STREL: st_rel sge tge ts ss')
        (MEMREL: mm_rel sge tge (smem, sthr) (tmem, tthr))
        (Ess: sthr ! t = Some ss)
        (TGTST: Comp.step _ _ tge (tmem, tthr) e (mem', tthr ! t <- ts))
        (TAU1: taustar srclts ss ss1)
        (MST: forall thr', 
          thr' ! t = Some ss1 ->
          (forall t', t <> t' -> sthr ! t' = thr' ! t') ->
          Comp.step _ _ sge (smem, thr') e (mem', thr' ! t <- ss')),
        exists srcs,
          taustep srcmemlts (smem, sthr) e srcs /\
          mm_rel sge tge srcs (mem', tthr ! t <- ts).
    Proof.
      intros.
      destruct (taustar_to_comp _ _ smem Ess TAU1) 
        as [sthr1 [STAU1 [SP1 ST1]]].
      pose proof (MST sthr1 ST1 SP1) as SSTEP1.
      eexists. 
      split. by econstructor; econstructor; eauto. 
      split; [done|].
      intro ot. destruct (tid_eq_dec ot t). subst.
        by right; eexists ss'; exists ts; rewrite !PTree.gss.
      by rewrite !PTree.gso, <- SP1; auto; apply (proj2 MEMREL). 
    Qed.
  
    (** The main theorem for converting a thread-local simulation 
        to a whole-system simulation. *)

    Lemma mm_backward_sim:
      well_founded  (mm_order sge tge) /\
      (forall s t, stuck tgtmemlts t -> mm_rel sge tge s t -> 
        Comp.consistent _ _ s -> Comp.consistent _ _ t ->
        exists s', taustar srcmemlts s s' /\ stuck_or_error _ s') /\
      (forall s t l t', stepr tgtmemlts t l t' -> mm_rel sge tge s t ->
        Comp.consistent _ _ s -> Comp.consistent _ _ t ->
        (exists s', taustep srcmemlts s l s' /\ mm_rel sge tge s' t') \/
        (l = tau _ /\ mm_rel sge tge s t' /\ mm_order sge tge t' t) \/
        (exists s', taustar srcmemlts s s' /\ can_do_error _ s')).
    Proof.
      split; [by apply wf_mm_order|].
      split.
      (* Stuck state correspondence. *)
      intros [smem sthr] [tmem tthr] STUCK REL sCONS tCONS.
      pose proof (Comp.stuck_imp_no_threads _ _ _ _ tCONS (fun l s' => STUCK s' l)) as STK.
      eexists; split; try done.
      left; red; simpl; intros.
      eapply (Comp.no_threads_stuck _ _ _ _ _ _ sCONS); eauto; simpl in *.
      eapply PTree.ext; intro t; clarify.
      by destruct (proj2 REL t); des; rewrite PTree.gempty in *.
      (* Transition correspondence *)
      intros [smem sthr] [tmem tthr] l t' TSTEP REL sCONS tCONS; simpl in *.
      assert (tmem = smem) by (destruct REL; done); subst.
      destruct (thread_backward_sim sge_tge_rel) as [_ [SS BS]].
      (comp_step_cases (inversion TSTEP
        as [os os' ev ot mem mem' st st' SST TST TG TS | 
            os os' ev mem st st' ot SST TG TS | 
            mem mem' st TST | 
            os os' ot mem st st' SST TG TS | 
            os os' newtid p v ot mem mem' st st' sinit SST TST TG TGN TS IN | 
            os os' p v ot mem st SST TG IN | 
            os os' ot mem mem' st SST TST TG | 
            os os' ot mem mem' st st' p c v SST TST TG TS |
            os os' ot mem mem' st st' p c v SST TST TG TS | 
            os os' ot mem mem' st st' p k SST TST TG TS |
            os os' ot mem mem' st st' p c v instr SST TST TG TS |
            os ot mem st NO_STEP TG |
            os os' ot mem mem' st st' p n k SST TST TG TS |
            os os' ot mem st st' SST TG TS |
            os os' largs args ot mem mem' st st' id SST TST TG TS |
            os os' largs ot mem st st' id SST TST TG TS | 
            os os' args ot mem mem' mem''  st st' v sinit newtid fn p SST TST TST2 TG TGN TS IN |
            os os' args ot mem st st' fn SST TST TG TS |
            os os' ot mem st st' lfn largs fn args mem' SST TST TG IN TS]) Case); subst;
(*        rewrite <- (proj1 REL) in *; *)
        first [Case "step_unbuf" | destruct (proj2 REL ot) as [[? ?] | [ss [ts [Est [Ett RELs]]]]]]; 
        try rewrite TG in *; clarify;
        try (destruct (BS _ _ _ _ SST RELs) 
          as [[ts' [[ts1 [TAU1 MST]] RELts']] | 
            [[ISTAU [NREL ORD]] | [[? [ISTAU [l0 X]]] |
             [(ISFENCE & ts' & (ts1 & TAU1 & MST) & RELts')|ERROR]]]]);
        try done;
        try (eby right; right; eapply thread_ev_stuck_to_comp_tau_error);
        try (eby left; 
                 eapply backward_sim_sandwich_step; try eassumption; [];
                 vauto).
      Case "step_ord". (* removed fence *)
        destruct ev; simpl in *; clarify. 
        rewrite (MM_fence_tau _ _ _ _ TST) in *.
        by left; eapply backward_sim_sandwich_step; try eassumption; vauto.
      Case "step_unbuf".
        left; exists (mem', sthr). 
        assert (WS : taustep srcmemlts (smem, sthr) Etau (mem', sthr)).
          by eapply step_taustep; simpl; eapply Comp.step_unbuf.
        by destruct REL.
      Case "step_tau".
        (* stutter decreases order in the mem parallel composition state*)
        right; left. 
        split; [done|].
        split. 
        split; [done|].
        intro xt. destruct (tid_eq_dec xt ot). subst.
            right. exists ss; exists os'. rewrite PTree.gss; auto.
        repeat rewrite PTree.gso; auto. apply (proj2 REL). 
        by split; try done; apply (PTree.order_set_lt _ _ _ _ TG ORD).  
        (* unnecessary memory read in src *)

        assert (Y: exists p, exists chunk, exists v, l0 = TEmem (MEread p chunk v)).
          assert (Y: samekind thread_labels l0 l0) by (destruct l0 as [[]|[]| | | | | |]; done).
          destruct (X l0 Y) as [s' [? [M ?]]]; revert M.
          by destruct l0 as [|[]| | | | | |]; try done; eexists; eexists; eexists.
        des; clarify. 

      edestruct (pseudotau_cond H _ _ sCONS ot p chunk) 
        as [(v' & mREAD & HT)|(mem'' & mem' & TAU & FAIL)].

      SCase "successful load".
      simpl in *; exploit (X (TEmem (MEread p chunk v'))); try done; [].
      intros (ts'' & (ts' & sTAU & READ) & _ & REL'); simpl in *.
      eapply taustar_to_comp in sTAU; try eassumption; destruct sTAU as (sthr' & sTAU & ? & ?). 
      left; eexists (_, _); split. 
        by eexists; split; [edone|eby simpl; eapply Comp.step_ord].
      split; try done.
      intros; rewrite !PTree.gsspec; destruct peq; clarify; eauto 8.
      by rewrite <- H0; destruct REL; auto.

      SCase "failed load".
      simpl in *; exploit (X (TEmem (MEread p chunk v))); try done; [].
      unfold taustep; intro; des; clarify.
      exploit taustar_to_comp; try eapply H0; try edone; []; intros; des.
      right; right; eexists (_, _); split.
      eapply taustar_trans; [eassumption|eby eapply taustar_mm_to_comp].
      eexists (_, _); exists (Evisible Efail); split; [done|].
      by simpl; eapply Comp.step_read_fail; try edone.


      Case "step_start".
        (* There is a matching step in source *)
          left.
          destruct (taustar_to_comp _ _ smem Est TAU1) 
            as [sthr1 [STAU1 [SP1 ST1]]].
          destruct (thread_init_related _ _ sge_tge_rel IN) 
            as [inits [INITS INREL]].
          destruct (proj2 REL newtid) as [[NTIDN _] | [ds [dt [_ [Edt _]]]]];
            try (rewrite Edt in TGN; discriminate).
          destruct (tid_eq_dec ot newtid) as [NTE | NTNE]. 
            rewrite NTE, NTIDN in Est; discriminate.
          rewrite SP1 in NTIDN; auto.
          pose proof (Comp.step_start _ _ _ _ _ _  _ _ _ _  _ _ _ _ 
            MST TST ST1 NTIDN (refl_equal _) INITS) as STARTST.
          set (sthr' := (sthr1 ! ot <- ts') ! newtid <- inits). 
          assert (ETS2: sthr' ! ot = Some ts'). 
            by unfold sthr'; rewrite PTree.gso, PTree.gss; auto.
          econstructor. 
          split. by vauto.
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
          left; eapply backward_sim_sandwich_step; try eassumption; [].
          intros thr' TS1 _.
          apply (thread_init_related_none _ _ sge_tge_rel) in IN.
          by eapply Comp.step_start_fail; eauto.
      Case "step_exit".
        (* There is a matching step in source *)
          left.
          destruct (taustar_to_comp _ _ smem Est TAU1) 
            as [sthr1 [STAU1 [SP1 ST1]]].
          pose proof (Comp.step_exit _ _ _ _ _ _ _ _ _
            MST TST ST1) as EXITST.
          econstructor. split.
            eby eexists; eexists. 
          split; [done|].
          intro t.
          destruct (tid_eq_dec t ot); clarify.
            by left; rewrite !PTree.grs.
          by rewrite !PTree.gro, <- SP1; auto; apply (proj2 REL).
      Case "step_free_fail".
        destruct (taustar_to_comp _ _ smem Est TAU1) as [sthr1 [STAU1 [SP1 ST1]]].
        right; right; eexists; split; try edone. 
        eexists (_, _); exists (Evisible Efail); split; simpl; vauto. 
      Case "step_thread_stuck".
        exploit SS; [|apply RELs|intros ERROR]. 
        - by intros s' l' STEP; specialize (NO_STEP _ _ STEP).
        eby right; right; eapply thread_ev_stuck_to_comp_tau_error.
      Case "step_startmem".
          left.
          destruct (taustar_to_comp _ _ smem Est TAU1) 
            as [sthr1 [STAU1 [SP1 ST1]]].
          destruct (thread_init_related _ _ sge_tge_rel IN) 
            as [inits [INITS INREL]].
          destruct (proj2 REL newtid) as [[NTIDN _] | [ds [dt [_ [Edt _]]]]];
            try (rewrite Edt in TGN; discriminate).
          destruct (tid_eq_dec ot newtid) as [NTE | NTNE]. 
            rewrite NTE, NTIDN in Est; discriminate.
          rewrite SP1 in NTIDN; auto.
          pose proof (Comp.step_startmem _ _ _ _ _ _  _ _ _ _  _ _ _ _  _ _ _
            MST TST TST2 ST1 NTIDN (refl_equal _) INITS) as STARTST.
          set (sthr' := (sthr1 ! ot <- ts') ! newtid <- inits). 
          assert (ETS2: sthr' ! ot = Some ts'). 
            by unfold sthr'; rewrite PTree.gso, PTree.gss; auto.
          econstructor. 
          split. by vauto.
          split; try done.
          intro t. 
          destruct (tid_eq_dec t ot). subst.
            by right; exists ts'; exists os'; repeat rewrite PTree.gso, PTree.gss.
          unfold sthr' in *.
          destruct (tid_eq_dec t newtid). subst. 
            by right; exists inits; exists sinit; rewrite !PTree.gss.
          by rewrite !PTree.gso, <- SP1; auto; apply (proj2 REL). 
      Case "step_startmem_spawn_fail".  
          left; eapply backward_sim_sandwich_step; try eassumption; [].
          intros thr' TS1 _. 
          destruct fn; try apply (thread_init_related_none _ _ sge_tge_rel) in IN;
          eapply Comp.step_startmem_spawn_fail; eauto. 
    Qed.

  End MCbackwardsim1.

  (** Packaging everything into a [sim] structure. *)

  Program Definition bsim : Bsim.sim Mm Mm Src Tgt match_prg :=
    {| Bsim.rel sge tge s t := genv_rel sge tge /\ mm_rel sge tge s t ;
       Bsim.order sge tge t' t := genv_rel sge tge /\ mm_order sge tge t t' |}.
  Next Obligation.
      eapply PTree.ext; intro tid.
      destruct s; destruct t; destruct H0 as [A B]; simpl.
      specialize (B tid); des; simpl in *; clarify; rewrite PTree.gempty in *; clarify.
  Qed.
  Next Obligation. eby intros; exploit mm_init_related. Qed.
  Next Obligation. 
    exploit mm_backward_sim; try edone; [].
    intros (_ & _ & X); edestruct X; des; simpl in *; eauto 8.
  Qed.

  Theorem sim : Sim.sim Mm Mm Src Tgt match_prg.
  Proof.
    eapply (@Sim.make _ _ _ _ match_prg bsim); simpl.
    intros; constructor; intros i (REL & _).
    induction i as [i H] using (well_founded_ind (wf_mm_order REL)).
    by constructor; intros; des; auto.
  Qed.

End MCbackwardsim.

End MCsim.

Lemma false_pure_load_cond Mm : false -> MM_pure_load_condition Mm.
Proof. done. Qed.
