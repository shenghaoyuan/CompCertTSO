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

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for the [Allocation] pass (translation from
  RTL to LTL). *)

Require Import FSets.
Require Import SetoidList.
Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Ast.
Require Import Integers.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import RTLtyping.
Require Import Locations.
Require Import Conventions.
Require Import Coloring.
Require Import Coloringproof.
Require Import Allocation.
Require Import MCsimulation Simulations.
Require Import Memcomp Traces.
Require Import Libtactics.


(** * Properties of allocated locations *)

(** We list here various properties of the locations [alloc r],
  where [r] is an RTL pseudo-register and [alloc] is the register
  assignment returned by [regalloc]. *)

Section REGALLOC_PROPERTIES.

Variable f: function.
Variable env: regenv.
Variable live: PMap.t Regset.t.
Variable alloc: reg -> loc.
Hypothesis ALLOC: regalloc f live (live0 f live) env = Some alloc.

Lemma regalloc_noteq_diff:
  forall r1 l2,
  alloc r1 <> l2 -> Loc.diff (alloc r1) l2.
Proof.
  intros. apply loc_acceptable_noteq_diff. 
  eapply regalloc_acceptable; eauto.
  auto.
Qed.   

Lemma regalloc_notin_notin:
  forall r ll,
  ~(In (alloc r) ll) -> Loc.notin (alloc r) ll.
Proof.
  intros. apply loc_acceptable_notin_notin. 
  eapply regalloc_acceptable; eauto. auto.
Qed.

Lemma regalloc_notin_notin_2:
  forall l rl,
  ~(In l (map alloc rl)) -> Loc.notin l (map alloc rl).
Proof.
  induction rl; simpl; intros. auto. 
  split. apply Loc.diff_sym. apply regalloc_noteq_diff. tauto.
  apply IHrl. tauto.
Qed.
  
Lemma regalloc_norepet_norepet:
  forall rl,
  NoDup (List.map alloc rl) ->
  Loc.norepet (List.map alloc rl).
Proof.
  induction rl; simpl; intros.
  apply Loc.norepet_nil.
  inversion H.
  apply Loc.norepet_cons.
  eapply regalloc_notin_notin; eauto.
  auto.
Qed.

Lemma regalloc_not_temporary:
  forall (r: reg), 
  Loc.notin (alloc r) temporaries.
Proof.
  intros. apply temporaries_not_acceptable. 
  eapply regalloc_acceptable; eauto.
Qed.

Lemma regalloc_disj_temporaries:
  forall (rl: list reg),
  Loc.disjoint (List.map alloc rl) temporaries.
Proof.
  intros. 
  apply Loc.notin_disjoint. intros.
  generalize (list_in_map_inv _ _ _ H). intros [r [EQ IN]].
  subst x. apply regalloc_not_temporary; auto.
Qed.

End REGALLOC_PROPERTIES. 

(** * Semantic agreement between RTL registers and LTL locations *)

Require Import LTL.
Module RegsetP := Properties(Regset).

Section AGREE.

Variable f: RTL.function.
Variable env: regenv.
Variable flive: PMap.t Regset.t.
Variable assign: reg -> loc.
Hypothesis REGALLOC: regalloc f flive (live0 f flive) env = Some assign.

(** Remember the core of the code transformation performed in module
  [Allocation]: every reference to register [r] is replaced by
  a reference to location [assign r].  We will shortly prove
  the semantic equivalence between the original code and the transformed code.
  The key tool to do this is the following relation between
  a register set [rs] in the original RTL program and a location set
  [ls] in the transformed LTL program.  The two sets agree if
  they assign identical values to matching registers and locations,
  that is, the value of register [r] in [rs] is the same as
  the value of location [assign r] in [ls].  However, this equality
  needs to hold only for live registers [r].  If [r] is dead at
  the current point, its value is never used later, hence the value
  of [assign r] can be arbitrary. *)

Definition agree (live: Regset.t) (rs: regset) (ls: locset) : Prop :=
  forall (r: reg), Regset.In r live -> rs#r = ls (assign r).

(** What follows is a long list of lemmas expressing properties
  of the [agree_live_regs] predicate that are useful for the 
  semantic equivalence proof.  First: two register sets that agree
  on a given set of live registers also agree on a subset of
  those live registers. *)

Lemma agree_increasing:
  forall live1 live2 rs ls,
  RegsetLat.ge live1 live2 -> agree live1 rs ls ->
  agree live2 rs ls.
Proof.
  unfold agree; intros. 
  apply H0. apply H. auto.
Qed.

Lemma agree_succ:
  forall n s rs ls live i,
  analyze f = Some live ->
  f.(RTL.fn_code)!n = Some i ->
  In s (RTL.successors_instr i) ->
  agree live!!n rs ls ->
  agree (transfer f s live!!s) rs ls.
Proof.
  intros.
  apply agree_increasing with (live!!n).
  eapply DS.fixpoint_solution. unfold analyze in H; eauto.
  unfold RTL.successors, Kildall.successors_list. 
  rewrite PTree.gmap. rewrite H0. simpl. auto.
  auto.
Qed.

(** Some useful special cases of [agree_increasing]. *)

Lemma agree_reg_live:
  forall r live rs ls,
  agree (reg_live r live) rs ls -> agree live rs ls.
Proof.
  intros. apply agree_increasing with (reg_live r live); auto.
  red. apply RegsetP.subset_add_2. apply RegsetP.subset_refl.
Qed.

Lemma agree_reg_list_live:
  forall rl live rs ls,
  agree (reg_list_live rl live) rs ls -> agree live rs ls.
Proof.
  induction rl; simpl; intros.
  assumption. 
  apply agree_reg_live with a. apply IHrl. assumption.
Qed.

Lemma agree_reg_sum_live:
  forall ros live rs ls,
  agree (reg_sum_live ros live) rs ls -> agree live rs ls.
Proof.
  intros. destruct ros; simpl in H.
  apply agree_reg_live with r; auto.
  auto.  
Qed.

(** Agreement over a set of live registers just extended with [r]
  implies equality of the values of [r] and [assign r]. *)

Lemma agree_eval_reg:
  forall r live rs ls,
  agree (reg_live r live) rs ls -> rs#r = ls (assign r).
Proof.
  intros. apply H. apply Regset.add_1. auto. 
Qed.

(** Same, for a list of registers. *)

Lemma agree_eval_regs:
  forall rl live rs ls,
  agree (reg_list_live rl live) rs ls ->
  rs##rl = List.map ls (List.map assign rl).
Proof.
  induction rl; simpl; intros.
  auto.
  f_equal.
  apply agree_eval_reg with live. 
  apply agree_reg_list_live with rl. auto.
  eapply IHrl. eexact H.
Qed.

(** Agreement is insensitive to the current values of the temporary
  machine registers. *)

Lemma agree_exten:
  forall live rs ls ls',
  agree live rs ls ->
  (forall l, Loc.notin l temporaries -> ls' l = ls l) ->
  agree live rs ls'.
Proof.
  unfold agree; intros. 
  rewrite H0. apply H. auto. eapply regalloc_not_temporary; eauto.
Qed.

(** If a register is dead, assigning it an arbitrary value in [rs]
    and leaving [ls] unchanged preserves agreement.  (This corresponds
    to an operation over a dead register in the original program
    that is turned into a no-op in the transformed program.) *)

Lemma agree_assign_dead:
  forall live r rs ls v,
  ~Regset.In r live ->
  agree live rs ls ->
  agree live (rs#r <- v) ls.
Proof.
  unfold agree; intros.
  case (Reg.eq r r0); intro.
  subst r0. contradiction.
  rewrite Regmap.gso; auto. 
Qed.

(** Setting [r] to value [v] in [rs]
  and simultaneously setting [assign r] to value [v] in [ls]
  preserves agreement, provided that all live registers except [r]
  are mapped to locations other than that of [r]. *)

Lemma agree_assign_live:
  forall live r rs ls v,
  (forall s,
     Regset.In s live -> s <> r -> assign s <> assign r) ->
  agree (reg_dead r live) rs ls ->
  agree live (rs#r <- v) (Locmap.set (assign r) v ls).
Proof.
  unfold agree; intros. rewrite Regmap.gsspec.
  destruct (peq r0 r).
  subst r0. rewrite Locmap.gss. auto.
  rewrite Locmap.gso. apply H0. apply Regset.remove_2; auto.
  eapply regalloc_noteq_diff. eauto. apply sym_not_equal. apply H. auto.  auto.
Qed.

(** This is a special case of the previous lemma where the value [v]
  being stored is not arbitrary, but is the value of
  another register [arg].  (This corresponds to a register-register move
  instruction.)  In this case, the condition can be weakened:
  it suffices that all live registers except [arg] and [res] 
  are mapped to locations other than that of [res]. *)

Lemma agree_move_live:
  forall live arg res rs (ls: locset),
  (forall r,
     Regset.In r live -> r <> res -> r <> arg -> 
     assign r <> assign res) ->
  agree (reg_live arg (reg_dead res live)) rs ls ->
  agree live (rs#res <- (rs#arg)) (Locmap.set (assign res) (ls (assign arg)) ls).
Proof.
  unfold agree; intros. rewrite Regmap.gsspec. destruct (peq r res). 
  subst r. rewrite Locmap.gss. apply H0.
  apply Regset.add_1; auto.
  destruct (Reg.eq r arg).
  subst r.
  replace (Locmap.set (assign res) (ls (assign arg)) ls (assign arg))
     with (ls (assign arg)).
  apply H0. apply Regset.add_1. auto.
  symmetry. destruct (Loc.eq (assign arg) (assign res)).
  rewrite <- e. apply Locmap.gss.
  apply Locmap.gso. eapply regalloc_noteq_diff; eauto.

  rewrite Locmap.gso. apply H0. apply Regset.add_2. apply Regset.remove_2. auto. auto.
  eapply regalloc_noteq_diff; eauto. apply sym_not_equal. apply H; auto.
Qed.

(** Yet another special case corresponding to the case of 
  a redundant move. *)

Lemma agree_redundant_move_live:
  forall live arg res rs (ls: locset),
  (forall r,
     Regset.In r live -> r <> res -> r <> arg -> 
     assign r <> assign res) ->
  agree (reg_live arg (reg_dead res live)) rs ls ->
  assign res = assign arg ->
  agree live (rs#res <- (rs#arg)) ls.
Proof.
  intros. 
  apply agree_exten with (Locmap.set (assign res) (ls (assign arg)) ls).
  eapply agree_move_live; eauto. 
  intros. symmetry. rewrite H1. destruct (Loc.eq l (assign arg)).
  subst l. apply Locmap.gss.
  apply Locmap.gso. eapply regalloc_noteq_diff; eauto. 
Qed.

(** This complicated lemma states agreement between the states after
  a function call, provided that the states before the call agree
  and that calling conventions are respected. *)

Lemma agree_postcall:
  forall live args ros res rs v (ls: locset),
  (forall r,
    Regset.In r live -> r <> res ->
    ~(In (assign r) Conventions.destroyed_at_call)) ->
  (forall r,
    Regset.In r live -> r <> res -> assign r <> assign res) ->
  agree (reg_list_live args (reg_sum_live ros (reg_dead res live))) rs ls ->
  agree live (rs#res <- v) (Locmap.set (assign res) v (postcall_locs ls)).
Proof.
  intros. 
  assert (agree (reg_dead res live) rs ls).
  apply agree_reg_sum_live with ros. 
  apply agree_reg_list_live with args. assumption.
  red; intros. rewrite Regmap.gsspec. destruct (peq r res). 
  subst r. rewrite Locmap.gss. auto.
  rewrite Locmap.gso. transitivity (ls (assign r)). 
  apply H2. apply Regset.remove_2; auto. 
  unfold postcall_locs.
  assert (~In (assign r) temporaries).
    apply Loc.notin_not_in. eapply regalloc_not_temporary; eauto.
  assert (~In (assign r) destroyed_at_call).
    apply H. auto. auto.
  caseEq (assign r); auto. intros m ASG. rewrite <- ASG. 
  destruct (In_dec Loc.eq (assign r) temporaries). contradiction.
  destruct (In_dec Loc.eq (assign r) destroyed_at_call). contradiction.
  auto.
  eapply regalloc_noteq_diff; eauto. apply sym_not_eq. auto.
Qed.

Lemma agree_postthreadcreate:
  forall live args rs (ls: locset)
  (ND : forall r,
    Regset.In r live ->
    ~(In (assign r) Conventions.destroyed_at_threadcreate))
  (AG : agree (reg_list_live args live) rs ls),
    agree live rs (postthreadcreate_locs ls).
Proof.
  intros. 
  assert (LL := agree_reg_list_live _ _ _ _ AG).
  unfold postthreadcreate_locs.
  red; intros.
  assert (~In (assign r) temporaries).
    apply Loc.notin_not_in. eby eapply regalloc_not_temporary.
  assert (~In (assign r) destroyed_at_threadcreate). by apply ND. 
  caseEq (assign r); auto. intros m ASG. rewrite <- ASG. 
  destruct (In_dec Loc.eq (assign r) temporaries). contradiction.
  destruct (In_dec Loc.eq (assign r) destroyed_at_threadcreate). contradiction.
  auto.
  by intros s <-; auto. 
Qed.

(** Agreement between the initial register set at RTL function entry
  and the location set at LTL function entry. *)

Lemma agree_init_regs:
  forall live rl vl,
  (forall r1 r2,
    In r1 rl -> Regset.In r2 live -> r1 <> r2 ->
    assign r1 <> assign r2) ->
  agree live (RTL.init_regs vl rl) 
             (LTL.init_locs vl (List.map assign rl)).
Proof.
  intro live.
  assert (agree live (Regmap.init Vundef) (Locmap.init Vundef)).
    red; intros. rewrite Regmap.gi. auto.
  induction rl; simpl; intros.
  auto.
  destruct vl. auto.
  assert (agree live (init_regs vl rl) (init_locs vl (map assign rl))).
  apply IHrl. intros. apply H0. tauto. auto. auto.
  red; intros. rewrite Regmap.gsspec. destruct (peq r a). 
  subst r. rewrite Locmap.gss. auto.
  rewrite Locmap.gso. apply H1; auto. 
  eapply regalloc_noteq_diff; eauto. 
Qed.

Lemma agree_parameters:
  forall vl,
  let params := f.(RTL.fn_params) in
  agree (live0 f flive)
        (RTL.init_regs vl params) 
        (LTL.init_locs vl (List.map assign params)).
Proof.
  intros. apply agree_init_regs. 
  intros. eapply regalloc_correct_3; eauto.
Qed.

Lemma agree_undef_temps:
  forall live rs ls,
  agree live rs ls -> agree live rs (undef_temps ls).
Proof.
  intros. apply agree_exten with ls; auto. 
  intros. apply Locmap.guo; auto. 
Qed.

End AGREE.

(** * Preservation of semantics *)

(* Relation that maps global environments... *)
Definition genv_rel : RTL.genv -> LTL.genv -> Prop :=
 (fun x y => Genv.genv_match (fun a b => transf_fundef a = OK b) y x).

(** We now show that the LTL code reflecting register allocation has
  the same semantics as the original RTL code.  We start with
  standard properties of translated functions and 
  global environments in the original and translated code. *)

Section PRESERVATION.

(* Assume fixed global environments that are related: *)
Variables (ge : RTL.genv) (tge : LTL.genv).
Hypothesis TRANSF: genv_rel ge tge.

Let lts := (mklts thread_labels (rtl_step ge)).
Let tlts := (mklts thread_labels (ltl_step tge)).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  exists tf,
  Genv.find_funct_ptr tge v = Some tf /\ transf_fundef f = OK tf.
Proof.
  intros v f H.
  pose proof (proj2 TRANSF v).
  destruct (Genv.find_funct_ptr ge v);
   destruct (Genv.find_funct_ptr tge v); try done.
  clarify; eexists; done.
Qed.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
Proof.
  intros v f H.
  destruct v as [| |p|]; try done; simpl in *.
  apply function_ptr_translated; done.
Qed.

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof. by intros; destruct TRANSF. Qed.

Lemma sig_preserved:
  forall f tf,
  transf_fundef f = OK tf ->
  LTL.funsig tf = RTL.funsig f.
Proof.
  intros [] ?; simpl; [|by intros; clarify].  
  intro H; monadInv H.
  unfold transf_function in *.
  destruct (type_function f); try done.
  destruct (analyze f); try done.
  by destruct (regalloc f t); clarify.
Qed.


(** The proof of semantic preservation is a simulation argument
  based on diagrams of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                   |t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  Hypotheses: the left vertical arrow represents a transition in the
  original RTL code.  The top horizontal bar is the [match_states]
  relation defined below.  It implies agreement between
  the RTL register map [rs] and the LTL location map [ls]
  over the pseudo-registers live before the RTL instruction at [pc].  

  Conclusions: the right vertical arrow is an [exec_instrs] transition
  in the LTL code generated by translation of the current function.
  The bottom horizontal bar is the [match_states] relation.
*)

Inductive match_stackframes: list RTL.stackframe -> list LTL.stackframe -> Prop :=
  | match_stackframes_nil:
      match_stackframes nil nil
  | match_stackframes_cons:
      forall s ts res f sp pc rs ls env live assign,
      match_stackframes s ts ->
      wt_function f env ->
      analyze f = Some live ->
      regalloc f live (live0 f live) env = Some assign ->
      (forall rv,
        agree assign (transfer f pc live!!pc)
              (rs#res <- rv)
              (Locmap.set (assign res) rv ls)) ->
      match_stackframes
        (RTL.Stackframe res (RTL.fn_code f) sp pc rs :: s)
        (LTL.Stackframe (assign res) (transf_fun f live assign) sp ls pc :: ts).

Inductive match_states: RTL.state -> LTL.state -> Prop :=
  | match_states_intro:
      forall s f sp pc rs ts ls live assign env
      (STACKS: match_stackframes s ts)
      (WT: wt_function f env)
      (ANL: analyze f = Some live)
      (ASG: regalloc f live (live0 f live) env = Some assign)
      (AG: agree assign (transfer f pc live!!pc) rs ls),
      match_states (RTL.State s (RTL.fn_code f) sp pc rs)
                   (LTL.State ts (transf_fun f live assign) sp pc ls)
  | match_states_call:
      forall s f args ts tf,
      match_stackframes s ts ->
      transf_fundef f = OK tf ->
      match_states (RTL.Callstate s f args)
                   (LTL.Callstate ts tf args)
  | match_states_return:
      forall s v ts,
      match_stackframes s ts ->
      match_states (RTL.Returnstate s v)
                   (LTL.Returnstate ts v)
  | match_states_blocked:
      forall s efsig ts,
      match_stackframes s ts ->
      match_states (RTL.Blockedstate s efsig)
                   (LTL.Blockedstate ts efsig).


(** The simulation proof is by case analysis over the RTL transition
  taken in the source program. *)

Ltac CleanupHyps :=
  match goal with
  | H: (match_states _ _) |- _ =>
      inv H; CleanupHyps
  | H1: (PTree.get _ _ = Some _),
    H2: (agree _ (transfer _ _ _) _ _) |- _ =>
      unfold transfer in H2; rewrite H1 in H2; simpl in H2; CleanupHyps
  | _ => idtac
  end.

Ltac WellTypedHyp :=
  match goal with
  | H1: (PTree.get _ _ = Some _),
    H2: (wt_function _ _) |- _ =>
      let R := fresh "WTI" in (
      generalize (wt_instrs _ _ H2 _ _ H1); intro R)
  | _ => idtac
  end.

Ltac TranslInstr :=
  match goal with
  | H: (PTree.get _ _ = Some _) |- _ =>
      simpl; rewrite PTree.gmap; rewrite H; simpl; auto
  end.

Ltac MatchStates :=
  match goal with
  | |- match_states (RTL.State _ _ _ _ _) (LTL.State _ _ _ _ _) =>
      eapply match_states_intro; eauto; MatchStates
  | H: (PTree.get ?pc _ = Some _) |- agree _ _ _ _ =>
      eapply agree_succ with (n := pc); eauto; MatchStates
  | |- In _ (RTL.successors_instr _) =>
      unfold RTL.successors_instr; auto with coqlib
  | _ => idtac
  end.

Lemma transl_find_function:
  forall ros f args lv rs ls alloc,
  RTL.find_function ge ros rs = Some f ->
  agree alloc (reg_list_live args (reg_sum_live ros lv)) rs ls ->
  exists tf,
    LTL.find_function tge (sum_left_map alloc ros) ls = Some tf /\
    transf_fundef f = OK tf.
Proof.
  intros; destruct ros; simpl in *.
  assert (rs#r = ls (alloc r)).
    eapply agree_eval_reg. eapply agree_reg_list_live; eauto.
  rewrite <- H1. apply functions_translated. auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  apply function_ptr_translated. auto. discriminate.
Qed.

Theorem my_forward_sim:
  lockstep_forward_sim lts tlts true match_states.
Proof.
  intros s1 s1' lab s2 STEP; simpl.
  (rtl_step_cases (destruct STEP) Case); intros; CleanupHyps; WellTypedHyp.

  Case "exec_Inop".
  left; econstructor; split.
  eapply exec_Lnop. TranslInstr. MatchStates.

  Case "exec_Iop".
  generalize (PTree.gmap (transf_instr f live assign) pc (RTL.fn_code f)).
  rewrite H; simpl. 
  caseEq (Regset.mem res live!!pc); intro LV;
  rewrite LV in AG.
  generalize (Regset.mem_2 LV). intro LV'.
  generalize (regalloc_correct_1 f env live _ _ _ _ ASG H).
  unfold correct_alloc_instr, is_redundant_move.
  caseEq (is_move_operation op args).
  (* Special case for moves *)
  intros arg IMO CORR.
  generalize (is_move_operation_correct _ _ IMO).
  intros [EQ1 EQ2]. subst op; subst args. 
  injection H0; intro.
  destruct (Loc.eq (assign arg) (assign res)); intro CODE.
  (* sub-case: redundant move *)
  left; econstructor; split. eapply exec_Lnop; eauto.
  MatchStates. 
  rewrite <- H1. eapply agree_redundant_move_live; eauto.
  (* sub-case: non-redundant move *)
  left; econstructor; split. eapply exec_Lop; eauto. simpl. eauto.
  MatchStates.
  rewrite <- H1. set (ls1 := undef_temps ls).
  replace (ls (assign arg)) with (ls1 (assign arg)).
  eapply agree_move_live; eauto.
  unfold ls1. eapply agree_undef_temps; eauto.
  unfold ls1. simpl. apply Locmap.guo. eapply regalloc_not_temporary; eauto. 
  (* Not a move *)
  intros INMO CORR CODE.
  assert (eval_operation tge sp op (map ls (map assign args)) = Some v).
    replace (map ls (map assign args)) with (rs##args).
    rewrite <- H0. apply eval_operation_preserved. exact symbols_preserved. 
    eapply agree_eval_regs; eauto.
  left; econstructor; split. eapply exec_Lop; eauto. MatchStates. 
  apply agree_assign_live with f env live; auto.
  eapply agree_undef_temps; eauto.
  eapply agree_reg_list_live; eauto.
  (* Result is not live, instruction turned into a nop *)
  intro CODE. left; econstructor; split. eapply exec_Lnop; eauto.
  MatchStates. apply agree_assign_dead; auto. 
  red; intro. exploit Regset.mem_1; eauto. congruence.

  Case "exec_Iload".
  caseEq (Regset.mem dst live!!pc); intro LV;
  rewrite LV in AG.
  (* dst is live *)
  exploit Regset.mem_2; eauto. intro LV'.
  assert (eval_addressing tge sp addr (map ls (map assign args)) = Some (Vptr a)).
    replace (map ls (map assign args)) with (rs##args).
    rewrite <- H1. apply eval_addressing_preserved. exact symbols_preserved.
    eapply agree_eval_regs; eauto.
  left; econstructor; split.
  eapply exec_Lload; eauto. TranslInstr. rewrite LV; auto.
  generalize (regalloc_correct_1 f env live _ _ _ _ ASG H).
  unfold correct_alloc_instr. intro CORR.
  MatchStates. 
  eapply agree_assign_live; eauto.
  eapply agree_undef_temps; eauto.
  eapply agree_reg_list_live; eauto.
  (* dst is dead *)
  right; split; [done|split; [done|]]; econstructor; split.
  eapply exec_Lnop. TranslInstr. rewrite LV; auto.
  intros l0 s0.
  destruct l0 as [[]|[]| | | | | |]; simpl; try done; intros [EQ1 [EQ2 ?]] STEP'; subst.
  inv STEP'; try (by destruct sp); try (by inv ASME).
  rewrite H in *; clarify.
  MatchStates. apply agree_assign_dead; auto.
  red; intro; exploit Regset.mem_1; eauto. congruence.

  Case "exec_Istore".
  assert (eval_addressing tge sp addr (map ls (map assign args)) = Some (Vptr a)).
    replace (map ls (map assign args)) with (rs##args).
    rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
    eapply agree_eval_regs; eauto.
  assert (ESRC: rs#src = ls (assign src)).
    eapply agree_eval_reg. eapply agree_reg_list_live. eauto.
  left; econstructor; split.
  eapply exec_Lstore; eauto. TranslInstr.
  rewrite <- ESRC. eauto.
  MatchStates. eapply agree_reg_live. eapply agree_reg_list_live. 
  eapply agree_undef_temps; eauto.

  Case "exec_Icall".
  exploit transl_find_function; eauto.  intros [tf [TFIND TF]].
  generalize (regalloc_correct_1 f0 env live _ _ _ _ ASG H).
  unfold correct_alloc_instr. intros [CORR1 [CORR2 CORR3]].
  assert (rs##args = map ls (map assign args)).
    eapply agree_eval_regs; eauto. 
  left; econstructor; split. 
  eapply exec_Lcall; eauto. TranslInstr.
  rewrite (sig_preserved _ _ TF). eauto.
  rewrite H1. 
  econstructor; eauto.
  econstructor; eauto.
  intros. eapply agree_succ with (n := pc); eauto.
  simpl. auto.
  eapply agree_postcall; eauto.

  (* Case "exec_Itailcall". *)
  (* exploit transl_find_function; eauto.  intros [tf [TFIND TF]]. *)
  (* assert (rs##args = map ls (map assign args)). *)
  (*   eapply agree_eval_regs; eauto.  *)
  (* left; econstructor; split.  *)
  (* eapply exec_Ltailcall; eauto. TranslInstr. *)
  (* rewrite (sig_preserved _ _ TF). eauto. *)
  (* rewrite H1. econstructor; eauto. *)

  Case "exec_Icond_true".
  assert (COND: eval_condition cond (map ls (map assign args)) = Some true).
    replace (map ls (map assign args)) with (rs##args). auto.
    eapply agree_eval_regs; eauto.
  left; econstructor; split.
  eapply exec_Lcond_true; eauto. TranslInstr.
  MatchStates. eapply agree_reg_list_live. eapply agree_undef_temps; eauto.
  
  Case "exec_Icond_false".
  assert (COND: eval_condition cond (map ls (map assign args)) = Some false).
    replace (map ls (map assign args)) with (rs##args). auto.
    eapply agree_eval_regs; eauto.
  left; econstructor; split.
  eapply exec_Lcond_false; eauto. TranslInstr.
  MatchStates. eapply agree_reg_list_live. eapply agree_undef_temps; eauto.

  Case "exec_Ireturn".
  left; econstructor; split.
  eapply exec_Lreturn; eauto. TranslInstr; eauto.
  replace (regmap_optget or Vundef rs)
     with (locmap_optget (option_map assign or) Vundef ls).
  econstructor; eauto.
  inv WTI. destruct or; simpl in *.
  symmetry; eapply agree_eval_reg; eauto. 
  auto.

  Case "exec_Ithread_create".
  generalize (regalloc_correct_1 f env live _ _ _ _ ASG H).
  unfold correct_alloc_instr; intro CORR.
  left; econstructor; split. 
  rewrite (agree_eval_reg _ _ _ _ _ AG). 
  eapply exec_Lthreadcreate.
  - by TranslInstr.
  - by apply agree_reg_live in AG; rewrite <- (agree_eval_reg _ _ _ _ _ AG).
  - econstructor; try edone.
    eapply agree_succ with (n := pc); eauto. 
      unfold RTL.successors_instr; auto with coqlib.
  eby eapply agree_postthreadcreate with (args := fn :: arg :: nil). 

  Case "exec_Iatomic".
  generalize (PTree.gmap (transf_instr f live assign) pc (RTL.fn_code f)).
  rewrite H; simpl. 
  assert (CORR := regalloc_correct_1 f env live _ _ _ _ ASG H).
  unfold correct_alloc_instr, is_redundant_move in CORR.
  left; econstructor; split.
  eapply exec_Latomic. by TranslInstr.
  eby rewrite (agree_eval_regs _ _ _ _ _ AG) in ASME.
  edone. edone.
  MatchStates.
  apply agree_assign_live with f env live; auto. 
  eapply agree_reg_list_live, agree_undef_temps; eauto.

  Case "exec_Ifence".
  left; econstructor; split.
  - by eapply exec_Lfence; TranslInstr.
  by MatchStates.

  Case "exec_function_internal_empty".
  generalize H6. simpl.  unfold transf_function.
  caseEq (type_function f); simpl; try congruence. intros env TYP.
  assert (WTF: wt_function f env). apply type_function_correct; auto.
  caseEq (analyze f); simpl; try congruence. intros live ANL.
  caseEq (regalloc f live (live0 f live) env); simpl; try congruence.
  intros alloc ALLOC EQ. inv EQ. simpl in *.
  left; econstructor; split.
  eapply exec_function_internal_empty; simpl; eauto.
  simpl. econstructor; eauto.
  change (transfer f (RTL.fn_entrypoint f) live !! (RTL.fn_entrypoint f))
    with (live0 f live).
  eapply agree_parameters; eauto.

  Case "exec_function_internal_nonempty".
  generalize H10. simpl.  unfold transf_function.
  caseEq (type_function f); simpl; try congruence. intros env TYP.
  assert (WTF: wt_function f env). apply type_function_correct; auto.
  caseEq (analyze f); simpl; try congruence. intros live ANL.
  caseEq (regalloc f live (live0 f live) env); simpl; try congruence.
  intros alloc ALLOC EQ. inv EQ. simpl in *.
  left; econstructor; split.
  eapply exec_function_internal_nonempty; simpl; eauto.
  simpl. econstructor; eauto.
  change (transfer f (RTL.fn_entrypoint f) live !! (RTL.fn_entrypoint f))
    with (live0 f live).
  eapply agree_parameters; eauto.

  Case "exec_function_external_call".
  injection H7; intro EQ; inv EQ.
  left; econstructor; split.
  eapply exec_function_external_call; eauto.
  econstructor; eauto.

  Case "exec_function_external_return".
  by left; eexists; split; constructor.

  Case "exec_return".
  inv H3. 
  by left; eexists; split; econstructor; eauto.

  Case "exec_return_exit".
  inv H3.
  by left; eexists; split; vauto.
Qed.

Lemma init_sim_succ:
  forall {p vals tinit},
    ltl_init tge p vals = Some tinit ->
    exists sinit, rtl_init ge p vals = Some sinit /\ match_states sinit tinit.
Proof.
  intros p vals tinit INIT. unfold rtl_init, ltl_init in *. 
  pose proof TRANSF as (MG & MF).
  specialize (MF p).
  repeat (destruct Genv.find_funct_ptr); try done; [].
  destruct f; destruct f0; try done. pose proof MF as MF'. monadInv MF. 
  destruct f; destruct f0; try done. 
  unfold transf_function in EQ. 
  destruct type_function; try done; destruct analyze; try done; destruct regalloc; try done.
  inv EQ. simpl in *. destruct beq_nat; try done. inv INIT.
  eexists. split. edone. constructor. constructor. done.
Qed.

Lemma init_sim_fail:
  forall {p vals},
    ltl_init tge p vals = None ->
    rtl_init ge p vals = None.
Proof.
  intros p vals INIT. unfold ltl_init, rtl_init in *. 
  pose proof TRANSF as (MG & MF).
  specialize (MF p).
  destruct (Genv.find_funct_ptr tge p) as [[[]|]|]; try done;
    destruct (Genv.find_funct_ptr ge  p) as [[[]|]|]; try done; simpl in *;
      monadInv MF. 
  unfold transf_function in EQ. 
  destruct type_function; try done; destruct analyze; try done; destruct regalloc; try done.
  inv EQ. simpl in *. by destruct beq_nat.
Qed.

Definition bsim_rel t s := match_states s t.
Definition bsim_order (t t' : LTL.state) := False.

End PRESERVATION.

Definition alloc_match_prg (p  : rtl_sem.(SEM_PRG))
                           (p' : ltl_sem.(SEM_PRG)) : Prop := 
  transf_program p = OK p'.

(** The whole-system backward simulation for the [Allocation]
    phase. *)
Theorem alloc_sim :
  forall Mm (P: MM_pure_load_condition Mm),  
    Sim.sim Mm Mm rtl_sem ltl_sem alloc_match_prg.
Proof.
  intros; eapply (MCsim.sim (fun _ => P) rtl_sem ltl_sem genv_rel 
    (fun _ _ => bsim_rel) (fun _ _ => bsim_order)); intros; simpl in *.
  - destruct GENVR as [GR FR]. rewrite GR.
    by rewrite (transform_partial_program_main _ _ MP).
  - eapply Genv.exists_matching_genv_and_mem_rev 
      with (match_var := fun a b => a = b), INIT.
    apply transform_partial_program_match, MP.
  - destruct (init_sim_succ _ _ GENVR INIT) as [si [INIT' MS]].
    by exists si.
  - eby eapply init_sim_fail.
  - eapply lockstep_forward_to_backward_sim. 
          apply rtl_sem.(SEM_receptive).
        apply ltl_sem.(SEM_determinate).
      apply rtl_sem.(SEM_progress_dec).
    by apply my_forward_sim.
Qed.

