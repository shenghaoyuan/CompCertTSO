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

(** Correctness of instruction selection *)

Require Import Coqlib.
Require Import Classical.
Require Import Maps.
Require Import Ast.
Require Import Integers.
Require Import Floats.
Require Import Pointers.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Cminor.
Require Import CminorP.
Require Import Op.
Require Import CminorSel.
Require Import SelectOp.
Require Import Cminorops.
Require Import Selection.
Require Import SelectOpproof. 
Require Import Memcomp Traces.
Require Import Simulations MCsimulation.
Require Import Libtactics.

Open Local Scope cminorsel_scope.

(** * Correctness of the instruction selection functions for expressions *)

Section CMCONSTR.

Variable ge: genv.
Variable sp: option pointer. (* was val *)
Variable e: env.

(** Conversion of condition expressions. *)

Hint Constructors eval_condexpr : myhints.
Hint Constructors eval_exprlist : myhints.

Lemma negate_condexpr_correct:
  forall t a b,
  eval_condexpr ge sp e t a b ->
  eval_condexpr ge sp e t (negate_condexpr a) (negb b).
Proof.
  induction 1; simpl; try destruct vb1;
    eauto using eval_negate_condition with myhints.
Qed.

Scheme expr_ind2 := Induction for expr Sort Prop
  with exprlist_ind2 := Induction for exprlist Sort Prop.

Fixpoint forall_exprlist (P: expr -> Prop) (el: exprlist) {struct el}: Prop :=
  match el with
  | Enil => True
  | Econs e el' => P e /\ forall_exprlist P el'
  end.

Lemma expr_induction_principle:
  forall (P: expr -> Prop),
  (forall i : ident, P (Evar i)) ->
  (forall (o : operation) (e : exprlist),
     forall_exprlist P e -> P (Eop o e)) ->
  (forall (m : memory_chunk) (a : Op.addressing) (e : exprlist),
     forall_exprlist P e -> P (Eload m a e)) ->
  (forall (c : condexpr) (e : expr),
     P e -> forall e0 : expr, P e0 -> P (Econdition c e e0)) ->
  (forall e : expr, P e -> forall e0 : expr, P e0 -> P (Ediscard e e0)) ->
  forall e : expr, P e.
Proof.
  intros; apply expr_ind2 with (P := P) (P0 := forall_exprlist P); simpl; auto.
Qed.

Lemma eval_base_condition_of_expr:
  forall t a v b,
  eval_expr ge sp e t a v ->
  Val.bool_of_val v b ->
  eval_condexpr ge sp e t
                (CEcond (Ccompimm Cne Int.zero) (a ::: Enil))
                b.
Proof.
  intros; eapply eval_CEcond; eauto using app_nil_end with myhints evalexpr.
  inv H0; simpl; auto. rewrite Int.eq_false; auto.
Qed.

Lemma is_compare_neq_zero_correct:
  forall c v b,
  is_compare_neq_zero c = true ->
  eval_condition c (v :: nil) = Some b ->
  Val.bool_of_val v b.
Proof.
  intros.
  destruct c; simpl in H; try done;
  destruct c; simpl in H; try done;
  generalize (Int.eq_spec i Int.zero); rewrite H; intros; clarify. 

  destruct v; inv H0; vauto. 
  generalize (Int.eq_spec i Int.zero); destruct (Int.eq i Int.zero); intros; vauto. 

  destruct v; inv H0; vauto. 
  generalize (Int.eq_spec i Int.zero); destruct (Int.eq i Int.zero); intros; vauto. 
Qed.

Lemma is_compare_eq_zero_correct:
  forall c v b,
  is_compare_eq_zero c = true ->
  eval_condition c (v :: nil) = Some b ->
  Val.bool_of_val v (negb b).
Proof.
  intros. apply is_compare_neq_zero_correct with (negate_condition c).
  destruct c; simpl in H; simpl; try discriminate;
  destruct c; simpl; try discriminate; auto.
  apply eval_negate_condition; auto.
Qed.

Lemma eval_condition_of_expr:
  forall a t v b,
  eval_expr ge sp e t a v ->
  Val.bool_of_val v b ->
  eval_condexpr ge sp e t (condexpr_of_expr a) b.
Proof.
  intro a0; pattern a0.
  apply expr_induction_principle; simpl; intros;
    try (eapply eval_base_condition_of_expr; eauto; fail).
  
  destruct o; try (eapply eval_base_condition_of_expr; eauto; fail).

  destruct e0. inv H0. inv EE. simpl in EVAL. inv EVAL.  
  inversion H1. 
  rewrite Int.eq_false; auto. constructor.
  subst i; rewrite Int.eq_true. constructor.
  eapply eval_base_condition_of_expr; eauto.

  inv H0. simpl in EVAL.
  assert (eval_condition c vl = Some b).
    destruct (eval_condition c vl); try discriminate.
    destruct b0; inv EVAL; inversion H1; congruence.
  assert (eval_condexpr ge sp e t (CEcond c e0) b).
    eapply eval_CEcond; eauto.
  destruct e0; auto. destruct e1; auto.
  simpl in H. destruct H.
  inv EE. inv EL.

  case_eq (is_compare_neq_zero c); intros. 
  rewrite <- app_nil_end in *. eapply H; eauto.
  apply is_compare_neq_zero_correct with c; auto.

  case_eq (is_compare_eq_zero c); intros.
  replace b with (negb (negb b)). apply negate_condexpr_correct.
  eapply H; eauto.
  rewrite <- app_nil_end in *.  eauto. apply is_compare_eq_zero_correct with c; auto.
  apply negb_involutive.

  rewrite <- app_nil_end in *. auto.

  inv H1. destruct vb1; eauto with evalexpr.
Qed.

Lemma eval_load:
  forall t tl a p c v
  (HT : Val.has_type v (type_of_chunk c))
  (TT : t = tl++((TEmem(MEread p  c v)) :: nil)),
  eval_expr ge sp e tl a (Vptr p) ->
  eval_expr ge sp e t (load c a) v.
Proof.
 intros. generalize H. unfold load.  unfold addressing. destruct (addressing_match a).  
 - inversion 1; inv EVAL; eauto with evalexpr.
 - intros. eapply eval_Eload with (p:=p); eauto with evalexpr. 
     by destruct p; simpl; rewrite  Int.add_zero. 
     by rewrite <- app_nil_end.  
Qed.

Lemma cast_and_conv: forall c v, 
  (cast_value_to_chunk c v) = (cast_value_to_chunk c (Val.conv v (type_of_chunk c))).
Proof.
  intros [] []; simpl; try done.
Qed.

Lemma eval_store:
  forall c a1 a2 p1 v2 k t1 t2 t env
 (*  (HT : Val.has_type v2 (type_of_chunk c)) *)
  (TT : t = t1++t2++((TEmem(MEwrite p1 c (cast_value_to_chunk c v2)) :: nil))),
  eval_expr ge sp env t1 a1 (Vptr p1) ->
  eval_expr ge sp env t2 a2 v2 ->
  step ge (SKstmt (store c a1 a2) sp env k)
       t (SKstmt  Sskip sp env k).
Proof.
intros. 

assert (eval_exprlist ge sp env t1 (Econs a1 Enil) (Vptr p1::nil))
  by eauto using app_nil_end with evalexpr.

unfold store, addressing. destruct (addressing_match a1).  

 - by intros; inv H; inv EVAL; econstructor; eauto; rewrite cast_and_conv.

 - intros; clarify. eapply StepStore with (ptr:=p1); eauto. 
     by destruct p1; simpl; rewrite Int.add_zero.
   by rewrite cast_and_conv.
Qed.


(** Correctness of instruction selection for operators *)

Hint Resolve eval_cast8unsigned eval_cast8signed 
             eval_cast16unsigned eval_cast16signed
             eval_negint eval_notint eval_notbool
             eval_negf eval_singleoffloat
             eval_intoffloat eval_intuoffloat
             eval_floatofint eval_floatofintu : evhints.
Hint Constructors Val.bool_of_val : evhints.

Hint Resolve eval_add eval_add_ptr_2 eval_add_ptr
  eval_sub eval_sub_ptr_int eval_sub_ptr_ptr
  eval_mul eval_divs eval_divu eval_mods eval_modu
  eval_and eval_or eval_xor eval_shl eval_shr eval_shru
  eval_addf eval_subf eval_mulf eval_divf
  eval_comp_int eval_comp_int_ptr eval_comp_ptr_int
  eval_comp_ptr_ptr3 eval_compu eval_compf : evhints.

Lemma eval_sel_unop:
  forall t op a1 v1 v,
  eval_expr ge sp e t a1 v1 ->
  eval_unop op v1 = Some v ->
  eval_expr ge sp e t (sel_unop op a1) v.
Proof.
  destruct op; simpl; intros; FuncInv; clarify; eauto with evhints.  

  generalize (Int.eq_spec i Int.zero); destruct (Int.eq i Int.zero); intro; subst.
  change true with (negb false); eauto with evhints.
  change false with (negb true); eauto with evhints.
  change Vfalse with (Val.of_bool (negb true)); eauto with evhints.
  apply eval_notint; auto.
Qed.

Lemma eval_sel_binop:
  forall t1 t2 op a1 a2 v1 v2 v,
  eval_expr ge sp e t1 a1 v1 ->
  eval_expr ge sp e t2 a2 v2 ->
  eval_binop op v1 v2 = Some v ->
  eval_expr ge sp e (t1++t2) (sel_binop op a1 a2) v.
Proof.
  destruct op; simpl; intros; FuncInv; clarify; eauto with evhints; 
  try generalize (Int.eq_spec i0 Int.zero);
  repeat 
    (match goal with 
       | H: context[match ?a with true => _ | false => _ end] |- _ => destruct a as [] _eqn: ?
       | H: context[if ?a then _ else _] |- _ => destruct a
     end; simpl in *; clarify; eauto with evhints).
Qed.

End CMCONSTR.

(* Recognition of calls to built-in functions *)
(* This built-in treatment seems to be new in 1.7 *)
(*

Lemma expr_is_addrof_ident_correct:
  forall e id,
  expr_is_addrof_ident e = Some id ->
  e = Cminor.Econst (Cminor.Oaddrsymbol id Int.zero).
Proof.
  intros e id. unfold expr_is_addrof_ident. 
  destruct e; try congruence.
  destruct c; try congruence.
  predSpec Int.eq Int.eq_spec i0 Int.zero; congruence.
Qed.

Lemma expr_is_addrof_builtin_correct:
  forall ge sp e m a v ef fd,
  expr_is_addrof_builtin ge a = Some ef ->
  Cminor.eval_expr ge sp e m a v ->
  Genv.find_funct ge v = Some fd ->
  fd = External ef.
Proof.
  intros until fd; unfold expr_is_addrof_builtin.
  case_eq (expr_is_addrof_ident a); intros; try congruence.
  exploit expr_is_addrof_ident_correct; eauto. intro EQ; subst a.
  inv H1. inv H4. 
  destruct (Genv.find_symbol ge i); try congruence.
  inv H3. rewrite Genv.find_funct_find_funct_ptr in H2. rewrite H2 in H0. 
  destruct fd; try congruence. 
  destruct (ef_inline e0); congruence.
Qed.
*)

(** * Semantic preservation for instruction selection. *)

Section PRESERVATION.

Variable prog: Cminor.program.
Let tprog := sel_program prog.

Variables (ge : Cminor.cm_sem.(SEM_GE)) (tge : CminorSel.genv).

Definition genv_rel : Cminor.cm_sem.(SEM_GE) -> CminorSel.genv -> Prop :=
 (fun x y => Genv.genv_match (fun a b => sel_fundef a = b) y x).

Hypothesis TRANSF: genv_rel ge tge.

(** Relationship between the global environments for the original
  CminorSel program and the generated RTL program. *)

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof. by intros; destruct TRANSF. Qed.

Lemma functions_translated:
  forall (v: val) (f: Cminor.fundef),
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (sel_fundef f).
Proof.  
  destruct v; unfold Genv.find_funct; simpl; intros; try done.
  pose proof (proj2 TRANSF p); do 2 destruct Genv.find_funct_ptr; clarify. 
Qed.
(*
Lemma function_ptr_translated:
  forall (b: block) (f: Cminor.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr tge b = Some (sel_fundef ge f).
Proof.  
  intros. 
  exact (Genv.find_funct_ptr_transf (sel_fundef ge) _ _ H).
Qed.
*)
Lemma sig_function_translated:
  forall f,
  funsig (sel_fundef f) = Cminor.funsig f.
Proof. by destruct f. Qed.
(*
Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros; unfold ge, tge, tprog, sel_program. 
  apply Genv.find_var_info_transf.
Qed.
*)
(** Semantic preservation for expressions. *)

Hint Resolve eval_sel_unop eval_sel_binop eval_load eval_condition_of_expr : evalexpr.

Lemma sel_expr_correct:
  forall sp e t a v,
  CminorP.cmp_eval_expr ge sp e t a v ->
  eval_expr tge sp e t (sel_expr a) v.
Proof.
  induction 1; intros; simpl; clarify; try destruct b1; eauto with evalexpr.
  (* Econst *)
  destruct cst; simpl; simpl in EC; (econstructor; [constructor|simpl;auto]).
  rewrite symbols_preserved. auto.
Qed.

Hint Resolve sel_expr_correct: evalexpr.

Lemma sel_exprlist_correct:
  forall sp e t a v,
  CminorP.cmp_eval_exprlist ge sp e t a v ->
  eval_exprlist tge sp e t (sel_exprlist a) v.
Proof.
  induction 1; intros; simpl; subst; eauto with evalexpr. 
Qed.

Hint Resolve sel_exprlist_correct: evalexpr.

(** Semantic preservation for terminating function calls and statements. *)

Fixpoint sel_cont (k: Cminor.cont) : CminorSel.cont :=
  match k with
  | Cminor.Kstop => Kstop
  | Cminor.Kseq s1 k1 => Kseq (sel_stmt s1) (sel_cont k1)
  | Cminor.Kblock k1 => Kblock (sel_cont k1)
  | Cminor.Kcall id f sp e k1 =>
      Kcall id (sel_fundef f) sp e (sel_cont k1)
  end.

Inductive match_states: Cminor.state -> CminorSel.state -> Prop :=
  | match_state: forall s k s' k' sp env,
      s' = sel_stmt s ->
      k' = sel_cont k ->
      match_states
        (Cminor.SKstmt s sp env k)
        (SKstmt s' sp env k')
  | match_callstate: forall args k k',
      k' = sel_cont k ->
      match_states
        (Cminor.SKcall args k)
        (SKcall args k')
  | match_externalstate: forall efsig k k',
      k' = sel_cont k ->
      match_states
        (Cminor.SKexternal efsig k)
        (SKexternal efsig k')
  | match_returnstate: forall v k k',
      k' = sel_cont k ->
      match_states
        (Cminor.SKreturn v k)
        (SKreturn v k').


Remark call_cont_commut:
  forall k, call_cont (sel_cont k) = sel_cont (Cminor.call_cont k).
Proof.
  induction k; simpl; auto.
Qed.

Remark find_label_commut:
  forall lbl s k,
  find_label lbl (sel_stmt s) (sel_cont k) =
  option_map (fun sk => (sel_stmt (fst sk), sel_cont (snd sk)))
             (Cminor.find_label lbl s k).
Proof.
  induction s; intros; simpl; auto.
  unfold store. destruct (addressing m (sel_expr e)); auto.
(*  destruct (expr_is_addrof_builtin ge e); auto.*)
  change (Kseq (sel_stmt s2) (sel_cont k))
    with (sel_cont (Cminor.Kseq s2 k)).
  rewrite IHs1. rewrite IHs2. 
  destruct (Cminor.find_label lbl s1 (Cminor.Kseq s2 k)); auto.
  rewrite IHs1. rewrite IHs2. 
  destruct (Cminor.find_label lbl s1 k); auto.
  change (Kseq (Sloop (sel_stmt s)) (sel_cont k))
    with (sel_cont (Cminor.Kseq (Cminor.Sloop s) k)).
  auto.
  change (Kblock (sel_cont k))
    with (sel_cont (Cminor.Kblock k)).
  auto.
  destruct o; auto.
  destruct (ident_eq lbl l); auto.
Qed.

(*
Definition measure (s: Cminor.state) : nat :=
  match s with
  | Cminor.SKexpr _ _ _ _ => 0%nat  (* dummy *)
  | Cminor.SKval _ _ _ _ => 0%nat   (* dummy *)
  | Cminor.SKcall _ _ => 0%nat
  | Cminor.SKstmt _ _ _ _ => 1%nat
  | Cminor.SKexternal _ _ => 2%nat   (* "2" just copied from SKreturn *)
  | Cminor.SKreturn _ _ => 2%nat
  end.

*)

Definition sel_option_fundef (ofd: option Cminor.fundef) : option fundef :=
  match ofd with
  | Some fd => Some (sel_fundef fd)
  | None => None
  end.

Lemma get_fundef_commut: forall (k:Cminor.cont),
  (CminorSel.get_fundef (sel_cont (Cminor.call_cont k))
  = sel_option_fundef (Cminor.get_fundef (Cminor.call_cont k))).
Proof. by induction k. Qed.

Hint Constructors match_states.

Lemma sel_aop_correct:
  forall aop vargs p rmwi v'
    (AS : sem_atomic_statement aop  vargs = Some (p, rmwi)),
      atomic_statement_mem_event (sel_aop aop) vargs v'
        (MErmw p Mint32 v' rmwi).
Proof.
  intros.
  destruct aop; destruct vargs as [|[] vargs]; try done.
  (* CAS *)
  do 3 (destruct vargs; try done); simpl in AS. 
  destruct Val.eq_dec; [done|]. 
  destruct (Val.has_type v0 Tint) as [] _eqn : HT1; [|done].
  destruct Val.eq_dec; [done|]. 
  destruct (Val.has_type v Tint) as [] _eqn : HT2; [|done].
  inv AS. eby econstructor.
  (* Locked increment *)
  destruct vargs; [|done].
  inv AS. eby econstructor.
Qed.

Lemma sel_step_correct:
  forall S1 t S2, CminorP.cmp_step ge S1 t S2 ->
  forall T1, match_states S1 T1 ->
  (exists T2, step tge T1 t T2 /\ match_states S2 T2).
Proof.
  induction 1; intros T1 ME; inv ME; simpl;
  try (econstructor; split; [econstructor |]; eauto with evalexpr; fail).

  (* store *)
  eauto 10 using eval_store, sel_expr_correct.

  (* Scall *)
  econstructor; split. 
  - econstructor; eauto using sel_expr_correct, sel_exprlist_correct.

  destruct TRANSF.   unfold Genv.find_funct in *. destruct vf; try discriminate.  
  specialize (H0 p); rewrite GFF in H0. 
  destruct (Genv.find_funct_ptr tge p)  as [] _eqn : K.
  inv H0. instantiate (1:=sel_fundef fd). 
  eapply sig_function_translated. 
  eapply sig_function_translated. 
  eby eapply functions_translated.

  - by eauto.

  (* Satomic none *)
  eexists; split. 
  econstructor; eauto using sel_exprlist_correct, sel_aop_correct.
  vauto.  

  (* Satomic some *)
  eexists; split. 
  econstructor; eauto using sel_exprlist_correct, sel_aop_correct.
  vauto.

  (* Sifthenelse *)
  exists (SKstmt (if b then sel_stmt s1 else sel_stmt s2) sp env (sel_cont k)); split.
  - by econstructor; eauto with evalexpr.
  - by destruct b; eauto.

  (* Sgoto *)
  econstructor. split. 
  econstructor. simpl; eauto. 
  - by rewrite call_cont_commut, get_fundef_commut; unfold sel_option_fundef; rewrite GFD.
  - by simpl; rewrite call_cont_commut, find_label_commut, FL; simpl; eauto.
  - by eauto.

  (* Sreturn None *)
  econstructor; split.
  - by econstructor; try rewrite call_cont_commut, CC; simpl; eauto with evalexpr.
  - by eauto.

  (* Sreturn Some *)
  econstructor; split.
  - econstructor; 
      try (eby rewrite call_cont_commut;
           destruct (Cminor.call_cont k); simpl in *; clarify); eauto with evalexpr.
  - by eauto.

  (* SKreturn *)
  econstructor; split.
  - by econstructor; try rewrite call_cont_commut, CC; simpl; eauto with evalexpr.
  - by eauto.
Qed.


(** Gluing the CminorP cmp_step_correct and above sel_step_correct
simulations: forward simulation of compound cm_steps (from clean via
unclean to clean) to CminorSel step. *)

Definition match_states_clean (st:Cminor.state) (st':CminorSel.state) : Prop :=
  clean st /\ match_states st st'.

Lemma cmp_step_correct_foo:
  forall st1 t st2 st1'
  (VIA: cm_via_unclean ge st1 t st2)
  (MATCH_CLEAN: match_states_clean st1 st1'),
  (exists st2', step tge st1' t st2' /\ match_states_clean st2 st2').
Proof.
  intros; destruct MATCH_CLEAN.
  assert (cmp_step ge st1 t st2) by (eapply cmp_step_correct; eauto).
  assert (X: exists st2', step tge st1' t st2' /\ match_states st2 st2')
    by (eapply sel_step_correct; eauto).
  destruct X as (st2' & ? & ?).
  eexists; repeat first [by eauto using cmp_step_to_clean | split].
Qed.


(** Now we need to build a small-step simulation out of that, from our
original small-step Cminor semantics to a small-step CminorSel
semantics constructed from its trace-set semantics.  We do so in
two steps: first lift cmp_step_correct to a simulation between
constructed small-step LTSs (cmp_small_step_correct), and then stick a
simulation from small-step Cminor to constructed small-step Cminor on
the front. *)

Lemma small_step_cs_intro : forall s te s',
  small_step_Recep CminorSel.state (step tge) s te s' ->
  small_step_cs tge s te s'.
Proof. done. Qed.
Hint Resolve small_step_cs_intro.


(** Lift match_states_clean to a relation between the constructed small-step LTSs 
(Cminor.small_step_cm, constructed from Cminor.cm_via_unclean, and
small_step_cs, constructed from CminorSel.step *)
Inductive match_small_step : small_step_state Cminor.state -> small_step_state CminorSel.state -> Prop :=
  | Match: forall st st' t
      (M: match_states_clean st st'),
   match_small_step (SSState Cminor.state st t) (SSState CminorSel.state st' t)
  | MatchStuck: forall st, match_small_step (SSStuck _) st.

Hint Constructors small_step_Recep.
Hint Constructors match_small_step.

(** Check that that is a small-step simulation. *)
Lemma cmp_small_step_correct:
  forall st1 st2 st1' te
  (S: small_step_cm ge st1 te st2)
  (M: match_small_step st1 st1'),
  (exists st2',
    small_step_cs tge st1' te st2' /\
    match_small_step st2 st2').
Proof.
intros [st1 t1|] [st2 t2|] [st1' t1'|]; intros; inv M; inv S; 
try destruct TS as (stB & te' & tb & X);
exploit cmp_step_correct_foo; try eassumption; intros (stB' & ? & ?);
eauto 10; 
assert (te <> TEtau) by (destruct te; destruct te0; clarify);
destruct (classic (exists stB, exists tb, step tge st1' (t1' ++ te :: tb) stB)) as [(? & [|] & ?)|]; 
  eauto 8.
Qed.

(** Now that has to be glued onto the CminorP.v  [cm_small_step_correct]. *)


Inductive match_all : Cminor.state -> small_step_state CminorSel.state -> Prop :=
  | Match_all: forall st st' st'' 
      (M1: match_cm ge st st')
      (M2: match_small_step st' st''),
    match_all st st''
  | Match_all_stuck : forall st st'
      (STUCK: cm_ev_stuck ge st),
    match_all st st'.

Hint Constructors match_all.

Lemma small_step_correct_all:
  forall st1 te st2 st1'' 
  (S: cm_step ge st1 te st2)
  (M: match_all st1 st1''),
  (cm_ev_stuck ge st1) \/ 
  (exists st2'', 
      ( (te=TEtau /\ st2''=st1'' /\ (measure st2 < measure st1)%nat) \/
        (small_step_cs tge st1'' te st2'')) /\
      match_all st2 st2'').
Proof. 
  intros; inv M; eauto.
  rename st' into st1'.
  exploit cm_small_step_correct; try eassumption; [].
  intros (? & [(? & ? & ?)|?] & [?|?]); clarify; eauto 10;
  exploit cmp_small_step_correct; try eassumption; intros (? & ? & ?); eauto 10. 
Qed.

Let lts := mklts thread_labels (cm_step ge).
Let tlts := mklts thread_labels (small_step_cs tge).

Lemma cm_ev_stuckE :
  forall s, cm_ev_stuck ge s ->ev_stuck_or_error lts s.
Proof.
  induction 1; vauto. 
  econstructor 4; simpl; eauto.
  - by inv H.
  intros [|[]| | | | | |]; try done; intros; eauto using te_read_read.
Qed.

Hint Resolve cm_ev_stuckE.

Definition bsim_rel := bsr lts tlts match_all.
Definition bsim_order := bsc tlts.

Lemma my_backward_sim:
  backward_sim lts tlts false bsim_rel bsim_order.
Proof.
  eapply (@forward_to_backward_sim thread_labels lts tlts 
            (cm_receptive ge) (cms_determinate tge) (cm_progress_dec ge)
            match_all (fun x y => measure x < measure y)%nat). 
  split; [by apply well_founded_lt_compat with measure|]. 
  intros; exploit small_step_correct_all; try eassumption; []; intros. 
  repeat match goal with 
           H: exists x, _ |- _ => destruct H; clarify
         | H: _ /\ _ |- _ => destruct H; clarify
         | H: _ \/ _ |- _ => destruct H; clarify
         end; eauto 10 using step_weakstep.
Qed.

Lemma init_sim_succ:
  forall {p vals tinit},
    cms_init tge p vals = Some tinit ->
    exists sinit, cm_init ge p vals = Some sinit /\ match_all sinit tinit.
Proof.
  intros p vals tinit INIT. unfold cms_init, cm_init in *.
  pose proof TRANSF as (MG & MF).
  specialize (MF p).
  repeat (destruct Genv.find_funct_ptr); clarify; [].
  destruct f0; [|done]. simpl in INIT.
  destruct beq_nat; [|done]. inv INIT.
  eexists; split; try done; vauto.
  econstructor; vauto; econstructor; vauto. 
Qed.

Lemma init_sim_fail:
  forall p vals,
    cms_init tge p vals = None ->
    cm_init ge p vals = None.
Proof.
  intros p vals INIT. unfold cms_init, cm_init in *.
  pose proof TRANSF as (MG & MF).
  specialize (MF p).
  repeat (destruct Genv.find_funct_ptr); clarify. 
  destruct f0; [|done]; simpl in INIT.
  by destruct beq_nat.
Qed.

End PRESERVATION.



Definition full_genv_rel ge tge :=
  genv_rel ge tge /\ (forall (b : Z) (ofs : int),
       match Genv.find_funct_ptr ge (Ptr b ofs) with
       | Some _ => b = 0%Z
       | None => True
       end).

Definition sel_match_prg p p' :=
   sel_program p = p'.

Theorem sel_sim Mm : Sim.sim Mm Mm cm_sem cms_sem sel_match_prg.
Proof.
  intros; eapply (MCsim.sim (false_pure_load_cond Mm) cm_sem cms_sem full_genv_rel
            bsim_rel (fun _ => bsim_order));
    intros; simpl in *.

  - by destruct GENVR as [[GR FR] _]; rewrite GR, <- MP.
  - destruct (Genv.exists_matching_genv_and_mem_rev
                  (transform_program_match MP) INIT) 
      as [sge [INIT' GEM]].
    exists sge; repeat (split; try done).
    intros b ofs. 
    destruct (Genv.find_funct_ptr sge (Ptr b ofs)) as [] _eqn:FF; try done.
    pose proof (Genv.find_funct_mem_restr INIT' FF) as B.
    unfold low_mem_restr in B. by destruct zeq.
  - destruct GENVR.
    exploit init_sim_succ; try eassumption; []; intros (? & ? & ?).
    eexists; split; try edone.
    by eexists; split; try edone; vauto.
  - eby destruct GENVR; eapply init_sim_fail.
  - by destruct GENR; apply my_backward_sim.
Qed.
