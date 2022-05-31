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

(** Correctness proof for x86 generation: main proof. *)

Require Import Coqlib.
Require Import Maps.
Require Import Errors.
Require Import Ast.
Require Import Integers.
Require Import Floats.
Require Import Pointers.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import TSOmachine.
Require Import Simulations.
Require Import TSOsimulation.
Require Import Op.
Require Import Locations.
Require Import Mach.
Require Import Machconcr.
Require Import Machtyping.
Require Import Asm.
Require Import Asmgen.
Require Import Asmgenretaddr.
Require Import Asmgenproof1.
Require Import Memcomp Traces.
Require Import Libtactics.

Definition genv_rel : Mach.genv -> Asm.genv -> Prop :=
 (fun x y => Genv.genv_match (fun a b => transf_fundef a = OK b) y x).

Section PRESERVATION.

Variable ge: Mach.genv.
Variable tge: Asm.genv.
Hypothesis TRANSF: genv_rel ge tge.

Let lts := (mklts thread_labels (Machconcr.mc_step ge)).
Let tlts := (mklts thread_labels (Asm.x86_step tge)).

Definition wt_genv := 
  forall f, match (Genv.find_funct ge f) with 
    | Some x => wt_fundef x 
    | None => True
    end.

Hypothesis WTGENV : wt_genv.

Lemma symbols_preserved: 
  forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof. by intros; destruct TRANSF. Qed.

Lemma function_ptr_translated:
  forall {v f}
    (H: Genv.find_funct_ptr ge v = Some f),
  exists tf, Genv.find_funct_ptr tge v = Some tf /\ transf_fundef f = Errors.OK tf.
Proof.
  intros; pose proof (proj2 TRANSF v).
  destruct (Genv.find_funct_ptr ge v);
  destruct (Genv.find_funct_ptr tge v); clarify; vauto. 
Qed.

Lemma functions_transl:
  forall f tf b,
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    transf_function f = OK tf ->
    Genv.find_funct_ptr tge b = Some (Internal tf).
Proof.
  intros.  destruct (function_ptr_translated H) as [tf' [-> B]].
  monadInv B. rewrite H0 in EQ; inv EQ; auto.  
Qed.

Lemma functions_transl_no_overflow:
  forall f sig tf b,
  Genv.find_funct_ptr ge b = Some (Internal f) ->
  transf_function f = OK (sig,tf) ->
  code_size tf <= Int.max_unsigned.
Proof.
  intros.
  destruct (function_ptr_translated H) as [tf' [A B]].
  monadInv B. rewrite H0 in EQ; inv EQ.  simpl. monadInv H0. 
  destruct zlt; simpl in *; clarify. simpl. omega.
Qed.

Hint Immediate functions_transl_no_overflow : x86gen.

(** [transl_code_at_pc pc fn c] holds if the code pointer [pc] points
  within the PPC code generated by translating Mach function [fn],
  and [c] is the tail of the generated code at the position corresponding
  to the code pointer [pc]. *) 

Inductive transl_code_at_pc: val -> Mach.function -> Mach.code -> 
                                    Asm.code -> Asm.code -> Prop :=
  transl_code_at_pc_intro:
    forall b ofs f c sig tf tc
      (GFUN: Genv.find_funct_ptr ge (Ptr 0 (Int.repr b)) = Some (Internal f))
      (HTF: transf_function f = OK (sig,tf))
      (HTF: transl_code f c = OK tc)
      (GOFS: code_tail (Int.unsigned ofs) tf tc),
    transl_code_at_pc (Vptr (Ptr b ofs)) f c tf tc.

Hint Resolve transl_code_at_pc_intro: x86gen.

(** Correctness of the return addresses predicted by
    [PPCgen.return_address_offset]. *)

Lemma return_address_offset_correct:
  forall b ofs f c tf tc ofs',
  transl_code_at_pc (Vptr (Ptr b ofs)) f c tf tc ->
  return_address_offset f c ofs' ->
  ofs' = ofs.
Proof.
  intros; inv H; inv H0. 
  rewrite HTF, HTF0 in *; clarify. 
  rewrite (code_tail_unique H GOFS); apply Int.repr_unsigned.
  by rewrite TF in *. by rewrite TC in *.
Qed.

(** The following lemmas show that the translation from Mach to PPC
  preserves labels, in the sense that the following diagram commutes:
<<
                          translation
        Mach code ------------------------ Asm instr sequence
            |                                          |
            | Mach.find_label lbl       find_label lbl |
            |                                          |
            v                                          v
        Mach code tail ------------------- Asm instr seq tail
                          translation
>>
  The proof demands many boring lemmas showing that Asm constructor
  functions do not introduce new labels.
*)


(** A valid branch in a piece of Mach code translates to a valid ``go to''
  transition in the generated PPC code. *)

(* Lemma find_label_goto_label: *)
(*   forall f tf lbl rs c' b ofs, *)
(*   Genv.find_funct_ptr ge (Ptr 0 (Int.repr b)) = Some (Internal f) -> *)
(*   transf_function f = OK tf -> *)
(*   rs EIP = Vptr (Ptr b ofs) -> *)
(*   Mach.find_label lbl f.(fn_code) = Some c' -> *)
(*   exists rs', *)
(*     goto_label tge lbl rs = Rtau (mkstate rs' XPEdone) *)
(*   /\ transl_code_at_pc (rs' EIP) f c' *)
(*   /\ forall r, r <> EIP -> rs'#r = rs#r. *)
(* Proof. *)
(*   intros. exploit (transl_find_label lbl f tf); eauto. rewrite H2.  *)
(*   intros [tc [A B]]. *)
(*   exploit label_pos_code_tail; eauto. instantiate (1 := 0). *)
(*   intros [pos' [P [Q R]]]. *)
(*   exists tc; exists (rs#PC <- (Vptr b (Int.repr pos'))). *)
(*   split. unfold goto_label. rewrite P. rewrite H1. auto. *)
(*   split. rewrite Pregmap.gss. constructor; auto.  *)
(*   rewrite Int.unsigned_repr. replace (pos' - 0) with pos' in Q. *)
(*   auto. omega. *)
(*   generalize (transf_function_no_overflow _ _ H0). omega. *)
(*   intros. apply Pregmap.gso; auto. *)
(* Qed. *)

(* Lemma find_label_goto_label: *)
(*   forall f lbl rs c' b ofs, *)
(*   Genv.find_funct_ptr ge (Ptr 0 (Int.repr b)) = Some (Internal f) -> *)
(*   rs EIP = Vptr (Ptr b ofs) -> *)
(*   Mach.find_label lbl f.(fn_code) = Some c' -> *)
(*   exists rs', *)
(*     goto_label tge lbl rs = Rtau (mkstate rs' XPEdone) *)
(*   /\ transl_code_at_pc (rs' EIP) f c' *)
(*   /\ forall r, r <> EIP -> rs'#r = rs#r. *)
(* Proof. *)
(*   intros. *)
(*   generalize (transl_find_label lbl f). *)
(*   rewrite H1; simpl. intro. *)
(*   generalize (label_pos_code_tail lbl (transl_function f) 0 *)
(*                  (transl_code f c') H2). *)
(*   intros [pos' [A [B C]]]. *)
(*   exists (rs#EIP <- (Vptr (Ptr b (Int.repr pos')))). *)
(*   split; [by unfold goto_label; rewrite H0, (functions_transl H), A|]. *)
(*   split.  *)
(*     rewrite Pregmap.gss; constructor; try done. *)
(*     rewrite Int.unsigned_repr.  *)
(*       by replace (pos' - 0) with pos' in B; [auto|omega]. *)
(*     by generalize (functions_transl_no_overflow _ _ H); omega. *)
(*   by intros; apply Pregmap.gso; auto. *)
(* Qed. *)

(** * Proof of semantic preservation *)

(** Semantic preservation is proved using simulation diagrams
  of the following form.
<<
           st1 --------------- st2
            |                   |
           t|                  *|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The invariant is the [match_states] predicate below, which includes:
- The PPC code pointed by the PC register is the translation of
  the current Mach code sequence.
- Mach register values and PPC register values agree.
*)

Inductive match_stack: list Machconcr.stackframe -> Prop :=
  | match_stack_nil:
      match_stack nil
  | match_stack_cons: forall fb sp ra c s f tf tc b ofs,
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      wt_function f ->
      incl c f.(fn_code) ->
      transl_code_at_pc (Vptr ra) f c tf tc ->
      ra <> nullptr ->
      ra = Ptr (Int.unsigned b) ofs ->
      fb = Ptr 0 b ->
      match_stack s ->
      match_stack (Stackframe fb sp ra c :: s).

Inductive match_states: Machconcr.state -> Asm.state -> Prop :=
  | match_states_intro:
      forall s fb sp c ms stkr rs f tf tc b ofs
        (STACKS: match_stack s)
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
        (WTF: wt_function f)
        (INCL: incl c f.(fn_code))
        (ErsEIP: rs EIP = Vptr (Ptr (Int.unsigned b) ofs))
        (Efb: fb = Ptr 0 b)
        (AT: transl_code_at_pc (rs EIP) f c tf tc)
        (AG: agree ms (Vptr sp) rs),
      match_states (Machconcr.State s fb sp c stkr ms)
                   (State rs XPEdone stkr)

  | match_states_call:
      forall s sp ms stkr rs b ofs
        (STACKS: match_stack s)
        (AG: agree ms (Vptr sp) rs)
        (AT: rs EIP = Vptr (Ptr (Int.unsigned ofs) Int.zero)),
(*        (NO: no stack overflow: check that ESP in inside stkr) *)
      match_states (Machconcr.Callstate s (Ptr b ofs) sp stkr ms)
                   (State rs XPEdone stkr)

  | match_states_return_internal:
      forall s ms sp stkr (rs : regset) f c ofs b (* tf *) tc sig
        (STACKS: match_stack s)
        (AG: agree ms (Vptr sp) rs)

        (INCL: incl c f.(fn_code))
(*        (AT : transl_code_at_pc (rs EIP) f c tf tc) *)

        (AT2: rs EIP = Vptr (Ptr b ofs))
        (AT3: Genv.find_funct_ptr tge (Ptr 0 (Int.repr b)) = Some (Internal (sig,tc)))
        (AT4: find_instr (Int.unsigned ofs) tc = Some (Xret (Cint Int.zero))),

      match_states (Machconcr.Returnstate s sp stkr ms)
                   (State rs XPEdone stkr)

  | match_states_blocked:
      forall s ms sp rs b ofs ef efsig stkr
        (STACKS: match_stack s)
        (AG: agree ms (Vptr sp) rs)
        (AT2: rs EIP = Vptr (Ptr b ofs))
        (AT3: Genv.find_funct_ptr tge (Ptr 0 (Int.repr b)) = Some (External ef))
        (Eefsig : efsig = ef.(ef_sig)),
      match_states (Machconcr.Blockedstate s sp stkr ms efsig)
                   (Asm.Blockedstate rs stkr efsig)

  | match_states_return_external:
      forall s ms sp stkr (rs : regset) ofs b ef
        (STACKS: match_stack s)
        (AG: agree ms (Vptr sp) rs)

        (AT2: rs EIP = Vptr (Ptr b ofs))
        (AT3: Genv.find_funct_ptr tge (Ptr 0 (Int.repr b)) = Some (External ef)),

      match_states (Machconcr.Returnstate s sp stkr ms)
                   (Asm.ReturnExternal rs stkr)

  | match_initstate:
      forall f args args'
      (LD: Val.lessdef_list args args'),
      match_states (Machconcr.Initstate f args)
                   (Asm.Initstate f args')
  | match_initargsstate:
      forall ms sp rs f args args' locs stkr
        (LD: Val.lessdef_list args args')
        (AG: agree ms (Vptr sp) rs),
      match_states (Machconcr.Initargsstate f args locs sp stkr ms)
                   (Asm.Initargsstate f args' locs stkr rs)
  | match_freestackstate:
      forall stkr,
      match_states (Machconcr.Freestackstate stkr)
                   (Asm.Freestackstate stkr)
  | match_exitstate:
      match_states (Machconcr.Exitstate)
                   (Asm.Exitstate)

  | match_states_error:
      forall s,
      match_states Machconcr.Errorstate s.

(** All the Machconcr transitions correspond to at least one x86
transition. We do not need a fancy measure relation. *)

Definition bsim_rel := @bsr _ lts tlts match_states.
Definition bsim_order := @bsc _ tlts.

Lemma init_fun_funsig_eq:
  forall pfn fn,
  Genv.find_funct_ptr ge pfn = Some fn ->
  exists tfn, 
    Genv.find_funct_ptr tge pfn = Some tfn /\
    Mach.funsig fn = funsig tfn.
Proof.
  intros. assert (E := proj2 TRANSF pfn).
  destruct (Genv.find_funct_ptr ge). clarify.
  destruct Genv.find_funct_ptr; [|done].
  destruct fn; simpl in E. 
  - unfold transf_function in E.
    destruct transl_code; try done. simpl in E.
    destruct zlt; try done; simpl in E.
    inv E.
    eexists. eauto.
  - inv E. 
    eauto.
  done.
Qed.

Hypothesis find_function_block_0:
  forall b ofs, 
    match Genv.find_funct_ptr ge (Ptr b ofs) with
      | Some _ => b = 0
      | None => True
    end.

(** Some useful tactics *)

Ltac rgss := rewrite Pregmap.gss.
Ltac rgso := rewrite Pregmap.gso; [|auto with x86gen].

(* Important simplification tactic, but can loop forever when 
   the goal has unification variables. *) 
Ltac gs_simpl := 
  repeat (first [rewrite nextinstr_inv; [|done] | rewrite Pregmap.gso; [|done||congruence]
                |rewrite Pregmap.gss]; try done).

(* A weaker version that avoids looping. *) 
Ltac gs_simpl_safe := 
  repeat (first [rewrite nextinstr_inv; [|done] | rewrite Pregmap.gso; [|done||congruence]];
          try done).

Ltac des_teed := destruct thread_event_eq_dec; [auto|vauto].

Ltac unfold_step := simpl; unfold x86_step, xstep_fn, exec_pex_instr.

Ltac try_destruct_args :=
  match goal with
  | args: list mreg,
    Htc: transl_code _ _ = OK _ |- _ =>
      destruct args; monadInv Htc; try destruct args; clarify
  | _ => idtac
  end.

Ltac find_current_instruction :=
  match goal with
  | AT: transl_code_at_pc ?reip _ _ _ _ |- _ => 
      let Heip := fresh "Heip" in 
        destruct reip as [] _eqn: Heip; inv AT; clarify'; try_destruct_args
  end.

Ltac reduce_weakstep_2 :=
  match goal with
  | GOFS: code_tail _ _ _ |- _ =>
     rewrite (find_instr_tail _ _ _ _ GOFS); simpl
  end.

Lemma nextinstr1: 
  forall rs, (nextinstr rs) EIP = Val.add (rs EIP) Vone.
Proof.
  by intros; unfold nextinstr; rewrite Pregmap.gss.
Qed.

Lemma val_incr_pointer:
  forall b ofs, Val.add (Vptr (Ptr b ofs)) Vone = Vptr (Ptr b (Int.add ofs Int.one)).
Proof. done. Qed.

Ltac reduce_internal Heip th :=
  match goal with
  | GFUN: Genv.find_funct_ptr _ _ = _,
    HTF: transf_function _ = OK ?sf |- _ =>
      eapply th; unfold_step;
      repeat first [rewrite nextinstr1 | rewrite Pregmap.gso; [|done]];
      try (rewrite Heip, ?val_incr_pointer, (functions_transl _ _ _ GFUN HTF));
      try reduce_weakstep_2
  end. 

Ltac reduce_weakstep Heip :=
  reduce_internal Heip step_weakstep.

Ltac reduce_step_weakstep Heip :=
  reduce_internal Heip steptau_weakstep; des_teed; reduce_internal Heip step_weakstep.

Ltac adjust_nextinstr :=
  match goal with
  | GOFS: code_tail _ _ _ |- _ =>
     eapply code_tail_next_int in GOFS; [|eby eapply functions_transl_no_overflow]
  end.


(** We show the simulation diagram by case analysis on the Mach transition
  on the left.  Since the proof is large, we break it into one lemma
  per transition. *)

Lemma exec_Mlabel_correct:
  forall s f sp lbl c stkr rs t
    (MS: match_states (Machconcr.State s f sp (Mlabel lbl :: c) stkr rs) t),
  (exists t' : St tlts,
     weakstep tlts t TEtau t' /\
     match_states (Machconcr.State s f sp c stkr rs) t').
Proof.
  intros; inv MS.
  find_current_instruction. monadInv HTF0. eexists; split. reduce_weakstep Heip. des_teed.

  eapply match_states_intro; eauto.
  eapply incl_cons_inv; eauto.

  unfold nextinstr; rewrite Heip; rewrite Pregmap.gss; simpl. reflexivity.
  unfold nextinstr; rewrite Heip; rewrite Pregmap.gss; simpl.
  eapply transl_code_at_pc_intro; eauto. eapply code_tail_next_int; eauto.
  eapply functions_transl_no_overflow; eauto.
  eapply agree_nextinstr; auto. 
Qed.

Lemma exec_Mgetstack_correct:
  forall v ty s f sp ofs dst c stkr rs t ptr chunk
    (Eptr : ptr = (sp + ofs)%pointer)
    (Echunk : chunk = chunk_of_ty ty)
    (HT : Val.has_type v (type_of_chunk chunk))
    (MS: match_states
          (Machconcr.State s f sp (Mgetstack ofs ty dst :: c) stkr rs) t),
   exists t' : state,
     weakstep tlts t (TEmem (MEread ptr chunk v)) t' /\
     (forall v' : val,
      Val.lessdef v' v ->
      exists s'' : Machconcr.state,
        mc_step ge
          (Machconcr.State s f sp (Mgetstack ofs ty dst :: c) stkr rs)
          (TEmem (MEread ptr chunk v')) s'' /\ match_states s'' t').
Proof.
  intros; inv MS.
  find_current_instruction. 
  monadInv HTF0. destruct ty. 
  (* the int case *)
  monadInv EQ0. eexists; split.
  reduce_weakstep Heip.

  unfold read_ea, ea, ea_rm_index, ea_rm_base, value_of_imm.
  rewrite nextinstr_inv; auto with x86gen.  
  rewrite (agree_sp _ _ _ AG); simpl; rewrite Ptr.add_zero_r.  
  destruct Ptr.eq_dec; clarify. (* destruct memory_chunk_eq_dec; [|done]. *)
  by simpl in HT; rewrite HT.
  
  intros. eexists. split. econstructor; try done. simpl. simpl in HT.
  eby eapply Val.has_type_lessdef. 

  eapply match_states_intro; eauto.
  eapply incl_cons_inv; eauto.
  by unfold nextinstr; rewrite Heip; rgso; rgss; simpl.
  unfold nextinstr; rewrite Heip; rgso; rgss; simpl.
  eapply transl_code_at_pc_intro; eauto. eapply code_tail_next_int; eauto.
  eapply functions_transl_no_overflow; eauto.
  eapply agree_set_mreg; eauto. rewrite (ireg_of_eq _ _ EQ1).
  by rewrite Pregmap.gss.
  intros.  rewrite Pregmap.gso. rewrite nextinstr_inv; auto with x86gen. 
  rewrite (ireg_of_eq _ _ EQ1) in H1. auto.
  (* float case *)
  unfold loadind in EQ0.
  destruct (preg_of dst) as [] _eqn:Hdst; monadInv EQ0.
  (* xmm reg *)
  eexists; split.
  reduce_weakstep Heip.
  unfold read_ea, ea, ea_rm_index, ea_rm_base, value_of_imm.
  rewrite nextinstr_inv; auto with x86gen.  
  rewrite (agree_sp _ _ _ AG); simpl; rewrite Ptr.add_zero_r.  
  destruct Ptr.eq_dec; [|done]. (* destruct memory_chunk_eq_dec; [|done]. *)
  simpl in HT; rewrite HT. reflexivity. 
  
  intros. eexists. split. econstructor; try done. simpl; simpl in HT.
  eby eapply Val.has_type_lessdef. 

  eapply match_states_intro; eauto.
  eapply incl_cons_inv; eauto.
  unfold nextinstr; rewrite Heip; rgso; rgss; simpl; reflexivity. 
  unfold nextinstr; rewrite Heip; rgso; rgss; simpl.  
  eapply transl_code_at_pc_intro; eauto. eapply code_tail_next_int; eauto.
  eapply functions_transl_no_overflow; eauto.
  eapply agree_set_mreg; eauto. rewrite Hdst. by rewrite Pregmap.gss.
  intros. rgso. rewrite nextinstr_inv; auto with x86gen. 
  rewrite Hdst in H1; auto. 
  (* SP reg *)
  eexists; split.
  reduce_weakstep Heip.
  unfold read_ea, ea, ea_rm_index, ea_rm_base, value_of_imm.
  rewrite (agree_sp _ _ _ AG); simpl; rewrite Ptr.add_zero_r.  
  destruct Ptr.eq_dec; [|done]. (* destruct memory_chunk_eq_dec; [|done]. *)
  simpl in HT; rewrite HT. reflexivity. 
  
  intros. eexists. split. econstructor; try done. simpl; simpl in HT.
  eby eapply Val.has_type_lessdef. 

  eapply match_states_intro; eauto.
  eapply incl_cons_inv; eauto.
  unfold nextinstr; rewrite Heip; rgso; rgss; simpl; reflexivity. 
  unfold nextinstr; rewrite Heip; rgso; rgss; simpl.  
  eapply transl_code_at_pc_intro; eauto. eapply code_tail_next_int; eauto.
  eapply functions_transl_no_overflow; eauto.
  eapply agree_set_mreg; eauto. rewrite Hdst. by rewrite Pregmap.gss.
  intros. rgso. rewrite nextinstr_inv; auto with x86gen. 
  rewrite Hdst in H1; auto. 
Qed.

(* move elsewhere *)
Lemma conv_lessdef_2:
  forall v ty,
    Val.lessdef (Val.conv v ty) v.
Proof.
  intros. destruct ty; destruct v; simpl; auto. 
Qed.

Lemma lessdef_trans:
  forall v1 v2 v3,
    Val.lessdef v1 v2 ->
    Val.lessdef v2 v3 ->
    Val.lessdef v1 v3.
Proof.
  intros; destruct v2; try inv H; try inv H0; auto.
Qed.

Lemma exec_Msetstack_correct:
  forall t s f sp src ofs ty c stkr rs ptr chunk v
    (Eptr : ptr = (sp + ofs)%pointer)
    (Echunk : chunk = chunk_of_ty ty)
    (Ev : v = Val.conv (rs src) (type_of_chunk chunk))
    (HT : Val.has_type v (type_of_chunk chunk))
    (MS : match_states
           (Machconcr.State s f sp (Msetstack src ofs ty :: c) stkr rs) t),
   (exists t' : state,
      exists v' : val,
        Val.lessdef (cast_value_to_chunk chunk v) v' /\
        weakstep tlts t (TEmem (MEwrite ptr chunk v')) t' /\
        match_states (Machconcr.State s f sp c stkr rs) t').
Proof.
  intros; inv MS.
  find_current_instruction. 
  monadInv HTF0. destruct ty.
  (* int case *)
  monadInv EQ0.
  exists (State (nextinstr rs0) XPEdone stkr); 
    exists (cast_value_to_chunk (chunk_of_ty Tint) (rs0 x0)); split.
  apply cast_value_to_chunk_lessdef.
  inversion AG. 
    specialize (agree_mregs src). rewrite <- (ireg_of_eq _ _ EQ1).
    generalize (conv_lessdef_2 (rs src) Tint); intro.
    eapply lessdef_trans. apply H. apply agree_mregs.
  split.
  reduce_weakstep Heip.
  unfold write_ea, ea, ea_rm_index, ea_rm_base, value_of_imm.
  rewrite nextinstr_inv; auto with x86gen.  
  rewrite (agree_sp _ _ _ AG). simpl. rewrite Ptr.add_zero_r.
  simpl in HT.  rewrite nextinstr_inv. 2: auto with x86gen.
  des_teed.
 
  eapply match_states_intro; eauto.
  eapply incl_cons_inv; eauto.
  unfold nextinstr; rewrite Heip. simpl. rgss. reflexivity. 
  unfold nextinstr; rewrite Heip. simpl. rgss. 
  eapply transl_code_at_pc_intro; eauto. eapply code_tail_next_int; eauto.
  eapply functions_transl_no_overflow; eauto.
  eapply agree_nextinstr. auto.
  (* float case *)
  unfold storeind in EQ0; destruct (preg_of src) as [] _eqn:Hpsrc; monadInv EQ0.
  (* xmm *)
  exists (State (nextinstr rs0) XPEdone stkr). 
  exists (cast_value_to_chunk (chunk_of_ty Tfloat) (rs0 f)); split.
  apply cast_value_to_chunk_lessdef.  
  inversion AG.
    specialize (agree_mregs src). rewrite <- Hpsrc.
    generalize (conv_lessdef_2 (rs src) Tfloat); intro.
    eapply lessdef_trans. apply H. apply agree_mregs.
  split.
  reduce_weakstep Heip.
  unfold write_ea, ea, ea_rm_index, ea_rm_base, value_of_imm.
  rewrite nextinstr_inv; auto with x86gen.  
  rewrite (agree_sp _ _ _ AG). simpl. rewrite Ptr.add_zero_r.
  simpl in HT.  rewrite nextinstr_inv; [| auto with x86gen].
  des_teed.
  eapply match_states_intro; eauto.
  eapply incl_cons_inv; eauto.
  unfold nextinstr; rewrite Heip. simpl. rgss. reflexivity. 
  unfold nextinstr; rewrite Heip. simpl. rgss. 
  eapply transl_code_at_pc_intro; eauto. eapply code_tail_next_int; eauto.
  eapply functions_transl_no_overflow; eauto.
  eapply agree_nextinstr. auto.
  (* ST0 *)
  exists (State (nextinstr rs0) XPEdone stkr). 
  exists (cast_value_to_chunk (chunk_of_ty Tfloat) (rs0 ST0)); split.
  apply cast_value_to_chunk_lessdef.  
  inversion AG.
    specialize (agree_mregs src). rewrite <- Hpsrc.
    generalize (conv_lessdef_2 (rs src) Tfloat); intro.
    eapply lessdef_trans. apply H. apply agree_mregs.
  split. 
  reduce_weakstep Heip.
  unfold write_ea, ea, ea_rm_index, ea_rm_base, value_of_imm.
  rewrite nextinstr_inv; auto with x86gen.  
  rewrite (agree_sp _ _ _ AG). simpl. rewrite Ptr.add_zero_r.
  des_teed. 
  eapply match_states_intro; eauto.
  eapply incl_cons_inv; eauto.
  unfold nextinstr; rewrite Heip. simpl. rgss. reflexivity. 
  unfold nextinstr; rewrite Heip. simpl. rgss. 
  eapply transl_code_at_pc_intro; eauto. eapply code_tail_next_int; eauto.
  eapply functions_transl_no_overflow; eauto.
  eapply agree_nextinstr. auto.
Qed.

Lemma exec_Mgetparam_correct:
  forall ptr sp ofs chunk ty v s f fb dst c stkr rs t
    (FF : Genv.find_funct_ptr ge fb = Some (Internal f))
    (Eptr : ptr = (sp + parent_offset f + ofs)%pointer)
    (Echunk : chunk = chunk_of_ty ty)
    (HT : Val.has_type v (type_of_chunk chunk))
    (MS : match_states
          (Machconcr.State s fb sp (Mgetparam ofs ty dst :: c) stkr rs) t),
   (exists t' : state,
      weakstep tlts t (TEmem (MEread ptr chunk v)) t' /\
      (forall v' : val,
       Val.lessdef v' v ->
       exists s'' : Machconcr.state,
         mc_step ge
           (Machconcr.State s fb sp (Mgetparam ofs ty dst :: c) stkr rs)
           (TEmem (MEread ptr chunk v')) s'' /\ match_states s'' t')).
Proof.
  intros; inv MS.

  find_current_instruction. monadInv HTF0. destruct ty.
  (* the int case *)
  monadInv EQ0.
  econstructor. split.
  reduce_weakstep Heip.
  simpl.
  unfold read_ea, ea, ea_rm_index, ea_rm_base, value_of_imm.
  rewrite nextinstr_inv; auto with x86gen.  
  rewrite (agree_sp _ _ _ AG). simpl. rewrite Ptr.add_zero_r. unfold parent_offset.
  clarify'. 
  rewrite <- Ptr.add_add_r, Int.add_commut.
  destruct Ptr.eq_dec; [|done]. (* destruct memory_chunk_eq_dec; [|done]. *)
  simpl in HT. rewrite HT. reflexivity.
  
  intros. eexists. split. econstructor; try done.
  clarify'. simpl. simpl in HT.
  eby eapply Val.has_type_lessdef.

  eapply match_states_intro; eauto.
  eapply incl_cons_inv; eauto.
  unfold nextinstr; rewrite Heip. rewrite Pregmap.gso; auto with x86gen. rewrite Pregmap.gss. eby simpl.
  unfold nextinstr; rewrite Heip. rewrite Pregmap.gso; auto with x86gen. rewrite Pregmap.gss. simpl.
  eapply transl_code_at_pc_intro; eauto. eapply code_tail_next_int; eauto.
  eapply functions_transl_no_overflow; eauto.
  eapply agree_set_mreg; eauto. rewrite (ireg_of_eq _ _ EQ1).
  by rewrite Pregmap.gss.
  intros. rewrite Pregmap.gso. rewrite nextinstr_inv; auto with x86gen.
  rewrite (ireg_of_eq _ _ EQ1) in H1. auto.
  (* float case *)
  unfold loadind in EQ0.
  destruct (preg_of dst) as [] _eqn:Hdst; monadInv EQ0.
  (* xmm reg *)
  eexists; split.
  reduce_weakstep Heip.
  unfold read_ea, ea, ea_rm_index, ea_rm_base, value_of_imm.
  rewrite nextinstr_inv; auto with x86gen.  
  rewrite (agree_sp _ _ _ AG); simpl. 
  rewrite Ptr.add_zero_r. unfold parent_offset. rewrite <- Ptr.add_add_r, Int.add_commut. 
  destruct Ptr.eq_dec; [|done]. (* destruct memory_chunk_eq_dec; [|done]. *)
  simpl in HT; rewrite HT. reflexivity. 
  intros. eexists. split. econstructor; try done.
  clarify'. simpl. simpl in HT.
  eby eapply Val.has_type_lessdef.
  eapply match_states_intro; eauto.
  eapply incl_cons_inv; eauto.
  unfold nextinstr; rewrite Heip. rgso. rgss. eby simpl.
  unfold nextinstr; rewrite Heip. rgso. rgss. simpl.
  eapply transl_code_at_pc_intro; eauto. eapply code_tail_next_int; eauto.
  eapply functions_transl_no_overflow; eauto.
  eapply agree_set_mreg; eauto. rewrite Hdst. 
  by rgss. 
  intros. rewrite Pregmap.gso. rewrite nextinstr_inv; auto with x86gen.
  rewrite <- Hdst. auto. 
  (* ST0 reg *)
  eexists; split.
  reduce_weakstep Heip.
  unfold read_ea, ea, ea_rm_index, ea_rm_base, value_of_imm.
  rewrite (agree_sp _ _ _ AG); simpl. 
  rewrite Ptr.add_zero_r. unfold parent_offset. rewrite <- Ptr.add_add_r, Int.add_commut. 
  destruct Ptr.eq_dec; [|done]. (* destruct memory_chunk_eq_dec; [|done]. *)
  simpl in HT; rewrite HT. reflexivity. 
  intros. eexists. split. econstructor; try done.
  clarify'. simpl. simpl in HT.
  eby eapply Val.has_type_lessdef.
  eapply match_states_intro; eauto.
  eapply incl_cons_inv; eauto.
  unfold nextinstr; rewrite Heip. rgso. rgss. eby simpl.
  unfold nextinstr; rewrite Heip. rgso. rgss. simpl.
  eapply transl_code_at_pc_intro; eauto. eapply code_tail_next_int; eauto.
  eapply functions_transl_no_overflow; eauto.
  eapply agree_set_mreg; eauto. rewrite Hdst. 
  by rgss. 
  intros. rewrite Pregmap.gso. rewrite nextinstr_inv; auto with x86gen.
  rewrite <- Hdst. auto. 
Qed.

Lemma transl_addressing_mode_correct:
  forall addr args (am: xmem) (ms: mreg -> val) (rs: regset) v (sp: pointer)
    (AG: agree ms (Vptr sp) rs)
    (Hta: transl_addressing addr args = OK am)
    (Hea: eval_addressing ge (Some sp) addr ms ## args = Some v),
    ea tge rs am = v.
Proof.
  assert (A: forall n, Int.add Int.zero n = n) by
    (intros; rewrite Int.add_commut; apply Int.add_zero).

  unfold transl_addressing; intros.
  destruct addr; repeat (destruct args; try done); simpl in Hea;
  unfold ea, ea_rm_index, ea_rm_base, value_of_imm; monadInv Hta.

  Case "Aindexed".
  destruct (ms m) as [] _eqn:Hms; (try destruct p); inv Hea;
  generalize (ireg_val _ _ _ _ _ AG EQ); intro Hld; rewrite Hms in Hld; inv Hld; simpl;
  rewrite ?(Int.add_commut Int.zero), Int.add_zero; auto.

  Case "Aindexed2".
  destruct (ms m) as [] _eqn:Hms; (try destruct p); inv Hea;
  generalize (ireg_val _ _ _ _ _ AG EQ); intro Hld; rewrite Hms in Hld; inv Hld;
  destruct (ms m0) as [] _eqn:Hms0; (try destruct p); inv H0;
  generalize (ireg_val _ _ _ _ _ AG EQ1); intro Hld; rewrite Hms0 in Hld; inv Hld; simpl.
  by (rewrite Int.add_permut, Int.add_assoc).
  by (rewrite Int.add_assoc).
  by (rewrite Int.add_commut, <- Int.add_assoc; decEq; decEq; decEq; rewrite Int.add_commut).

  Case "Ascaled".
  destruct (ms m) as [] _eqn:Hms; (try destruct p); clarify. 
  assert (Hld := ireg_val _ _ _ _ _ AG EQ); rewrite Hms in Hld; inv Hld; simpl.
  rewrite A.
  unfold transl_scale, Int.unsigned in EQ1;
  destruct i as [[|[|[|[|[]|]|]|]|]]; inv EQ1; unfold index_of_s; simpl; try done.
  by rewrite <- (Int.mul_one i1) at 1.

  Case "Aindexed2scaled".
  destruct (ms m) as [] _eqn:Hms; (try destruct p); clarify;
  destruct (ms m0) as [] _eqn:Hms0; (try destruct p); clarify;
  assert (Hld := ireg_val _ _ _ _ _ AG EQ); rewrite Hms in Hld; inv Hld; simpl;
  assert (Hld := ireg_val _ _ _ _ _ AG EQ1); rewrite Hms0 in Hld; inv Hld; simpl.
  - rewrite <- Int.add_assoc, (Int.add_commut _ (Int.mul i2 i)), Int.add_assoc.
    destruct i as [[|[|[|[|[]|]|]|]|]]; inv EQ0; unfold index_of_s; simpl; try done.
    by rewrite <- (Int.mul_one i2) at 1.
  - rewrite (Int.add_commut (Int.mul i2 i)), <- Int.add_assoc.
    destruct i as [[|[|[|[|[]|]|]|]|]]; inv EQ0; unfold index_of_s; simpl; try done.
    by rewrite <- (Int.mul_one i2) at 1.

  Case "Aindexed2scaledrev".
  destruct (ms m) as [] _eqn:Hms; (try destruct p); clarify; 
  destruct (ms m0) as [] _eqn:Hms0; (try destruct p); clarify; 
  assert (Hld := ireg_val _ _ _ _ _ AG EQ); rewrite Hms0 in Hld; inv Hld; simpl;
  assert (Hld := ireg_val _ _ _ _ _ AG EQ1); rewrite Hms in Hld; inv Hld; simpl.
  - rewrite <- Int.add_assoc, (Int.add_commut _ (Int.mul i1 i)), Int.add_assoc.
    destruct i as [[|[|[|[|[]|]|]|]|]]; inv EQ0; unfold index_of_s; simpl; try done.
    by rewrite <- (Int.mul_one i1) at 1.
  - rewrite (Int.add_commut (Int.mul i1 i)), <- Int.add_assoc.
    destruct i as [[|[|[|[|[]|]|]|]|]]; inv EQ0; unfold index_of_s; simpl; try done.
    by rewrite <- (Int.mul_one i1) at 1.

  Case "Aglobal".
  unfold get_symbol; rewrite symbols_preserved.
  by destruct Genv.find_symbol; simpl; clarify; rewrite !Ptr.add_zero_r.

  Case "Abased".
  destruct (ms m) as [] _eqn:Hms; clarify.
  unfold get_symbol; rewrite symbols_preserved.
  destruct Genv.find_symbol; simpl; clarify.
  assert (Hld := ireg_val _ _ _ _ _ AG EQ); rewrite Hms in Hld; inv Hld; simpl.
  by rewrite Ptr.add_zero_r, Ptr.add_add_r.

  Case "Abasedscaled".
  destruct (ms m) as [] _eqn:Hms; clarify.
  unfold get_symbol; rewrite symbols_preserved.
  destruct Genv.find_symbol; simpl; clarify.
  assert (Hld := ireg_val _ _ _ _ _ AG EQ); rewrite Hms in Hld; inv Hld; simpl.
  rewrite Ptr.add_zero_r, Ptr.add_add_r.
  unfold transl_scale, Int.unsigned in EQ1;
  destruct i as [[|[|[|[|[]|]|]|]|]]; inv EQ1; unfold index_of_s; simpl; try done.
  by rewrite <- (Int.mul_one i2) at 1.

  Case "Ainstack".
  by clarify; inv AG; rewrite agree_sp; simpl; rewrite Ptr.add_zero_r.
Qed.

Lemma ea_nextinstr:
  forall rs am, ea tge (nextinstr rs) am = ea tge rs am.
Proof.
  by intros rs [[[]|] [] ?]; simpl; unfold nextinstr; rewrite ?Pregmap.gso. 
Qed.


Lemma exec_Mload_correct:
  forall t s f sp chunk addr args dst c stkr rs rs' a v
    (EVAL : eval_addressing ge (Some sp) addr rs ## args = Some (Vptr a))
    (HT : Val.has_type v (type_of_chunk chunk))
    (Ers' : rs' = Regmap.set dst v (undef_temps rs))
    (MS : match_states
           (Machconcr.State s f sp (Mload chunk addr args dst :: c) stkr rs) t),
   (exists t' : state,
      weakstep tlts t (TEmem (MEread a chunk v)) t' /\
      (forall v' : val,
       Val.lessdef v' v ->
       exists s'' : Machconcr.state,
         mc_step ge
           (Machconcr.State s f sp (Mload chunk addr args dst :: c) stkr rs)
           (TEmem (MEread a chunk v')) s'' /\ match_states s'' t')).
Proof.
  intros; inv MS.
  
  destruct (rs0 EIP) as [] _eqn:Heip; inv AT; clarify'. 
  destruct chunk; monadInv HTF0; monadInv EQ0;
  assert (X := transl_addressing_mode_correct _ _ _ _ _ _ _ AG EQ1 EVAL);
      (eexists; split;  
         [by reduce_weakstep Heip; unfold read_ea; try rewrite ea_nextinstr;
             rewrite X; simpl in *; rewrite !dec_eq_true, HT|]);
      (eexists; split;
         [eby econstructor; simpl; try edone; eapply Val.has_type_lessdef|]);
      (eapply match_states_intro; eauto using incl_cons_inv;  
         [by unfold nextinstr; rewrite Heip; rgso; rgss; simpl
         |by unfold nextinstr; rewrite Heip; rgso; rgss; simpl; 
             eauto with x86gen
         |by first [rewrite <- (ireg_of_eq _ _ EQ0) | rewrite <- (freg_of_eq _ _ EQ0)]; 
             eapply agree_set_mreg; 
               [eby eapply agree_exten_temps|by rgss
                |by intros; rgso; apply nextinstr_inv; auto with x86gen]]).
Qed.

Lemma exec_Mstore_correct:
  forall t s f sp chunk addr args src c stkr rs a v
    (EVAL : eval_addressing ge (Some sp) addr rs ## args = Some (Vptr a))
    (Ev : v = Val.conv (rs src) (type_of_chunk chunk))
    (MS : match_states
           (Machconcr.State s f sp (Mstore chunk addr args src :: c) stkr rs) t),
   (exists t' : state,
      exists v' : val,
        Val.lessdef (cast_value_to_chunk chunk v) v' /\
        weakstep tlts t (TEmem (MEwrite a chunk v')) t' /\
        match_states (Machconcr.State s f sp c stkr (undef_temps rs)) t').
Proof.
  intros. inv MS.

  destruct (rs0 EIP) as [] _eqn:Heip; inv AT; clarify'. 
  destruct chunk; monadInv HTF0; monadInv EQ0;
  assert (X := transl_addressing_mode_correct _ _ _ _ _ _ _ AG EQ1 EVAL);
  rewrite <- ea_nextinstr in X;
  unfold mk_smallstore in *;
  match goal with 
   | H: context[(get_low_ireg ?x)] |- _ =>
       destruct (get_low_ireg x) as [lowreg|] _eqn: LOW_EQ; clarify
   | _ => idtac
  end;
  eexists; eexists (cast_value_to_chunk _ (nextinstr rs0 x1)); 
  (split; [(by apply cast_value_to_chunk_lessdef; first [rewrite <- (ireg_of_eq _ _ EQ0) | rewrite <- (freg_of_eq _ _ EQ0)];
             rewrite nextinstr_inv; auto with x86gen;
             inversion AG; eapply lessdef_trans; auto using conv_lessdef_2) |]); 
  try (split; 
         [by reduce_weakstep Heip; unfold write_ea; rewrite X; simpl in *;
             try (unfold nextinstr; rgso);
             try (revert LOW_EQ; destruct x1; simpl; intro LOW_EQ; clarify; simpl); 
             rewrite dec_eq_true|]);
  try (eapply match_states_intro; eauto using incl_cons_inv;
         [by unfold nextinstr; rewrite Heip; rgss; simpl
         |by unfold nextinstr; rewrite Heip; rgss; simpl; eauto with x86gen
         |by eapply agree_exten_temps; eauto; [];
             intros; apply nextinstr_inv; auto with x86gen]).

  Case "Mint8signed".
  split.
    reduce_internal Heip steptau_weakstep; [by des_teed | adjust_nextinstr].
    reduce_internal Heip steptau_weakstep; [by des_teed | adjust_nextinstr].
    reduce_weakstep Heip.
    unfold write_ea, nextinstr; simpl.
    repeat (rewrite Pregmap.gso; [|done]); rewrite Pregmap.gss.
    repeat (rewrite Pregmap.gso; [|done]); rewrite Pregmap.gss.
    rewrite ea_nextinstr in X; rewrite X; simpl; rewrite !Ptr.add_zero_r.
    repeat (rewrite Pregmap.gso; [|by destruct x1]); rewrite Pregmap.gss.
    by rewrite dec_eq_true.
  repeat (rewrite Pregmap.gso; [|done]); rewrite Pregmap.gss, Heip, ?val_incr_pointer.
  eapply match_states_intro; eauto using incl_cons_inv;
    repeat (rewrite Pregmap.gso; [|done]); try rewrite Pregmap.gss;
    eauto with x86gen.
  inv AG; constructor; [by rgso; rgso; rgso; rgso; rgso|done|].
  intro r; specialize (agree_mregs r); unfold undef_temps.
  by destruct r; simpl;
     (repeat (rewrite Pregmap.gso; [|done]); rewrite ?Pregmap.gss);
     (repeat (rewrite Regmap.gso; [|done]); rewrite ?Regmap.gss).

  Case "Mint8unsigned".
  split.
    reduce_internal Heip steptau_weakstep; [by des_teed | adjust_nextinstr].
    reduce_internal Heip steptau_weakstep; [by des_teed | adjust_nextinstr].
    reduce_weakstep Heip.
    unfold write_ea, nextinstr; simpl.
    repeat (rewrite Pregmap.gso; [|done]); rewrite Pregmap.gss.
    repeat (rewrite Pregmap.gso; [|done]); rewrite Pregmap.gss.
    rewrite ea_nextinstr in X; rewrite X; simpl; rewrite !Ptr.add_zero_r.
    repeat (rewrite Pregmap.gso; [|by destruct x1]); rewrite Pregmap.gss.
    by rewrite dec_eq_true.
  repeat (rewrite Pregmap.gso; [|done]); rewrite Pregmap.gss, Heip, ?val_incr_pointer.
  eapply match_states_intro; eauto using incl_cons_inv;
    repeat (rewrite Pregmap.gso; [|done]); try rewrite Pregmap.gss;
    eauto with x86gen.
  inv AG; constructor; [by rgso; rgso; rgso; rgso; rgso|done|].
  intro r; specialize (agree_mregs r); unfold undef_temps.
  by destruct r; simpl; 
     (repeat (rewrite Pregmap.gso; [|done]); rewrite ?Pregmap.gss);
     (repeat (rewrite Regmap.gso; [|done]); rewrite ?Regmap.gss).

  Case "Mint16signed".
  split.
    reduce_internal Heip steptau_weakstep; [by des_teed | adjust_nextinstr].
    reduce_internal Heip steptau_weakstep; [by des_teed | adjust_nextinstr].
    reduce_weakstep Heip.
    unfold write_ea, nextinstr; simpl.
    repeat (rewrite Pregmap.gso; [|done]); rewrite Pregmap.gss.
    repeat (rewrite Pregmap.gso; [|done]); rewrite Pregmap.gss.
    rewrite ea_nextinstr in X; rewrite X; simpl; rewrite !Ptr.add_zero_r.
    repeat (rewrite Pregmap.gso; [|by destruct x1]); rewrite Pregmap.gss.
    by rewrite dec_eq_true.
  repeat (rewrite Pregmap.gso; [|done]); rewrite Pregmap.gss, Heip, ?val_incr_pointer.
  eapply match_states_intro; eauto using incl_cons_inv;
    repeat (rewrite Pregmap.gso; [|done]); try rewrite Pregmap.gss;
    eauto with x86gen.
  inv AG; constructor; [by rgso; rgso; rgso; rgso; rgso|done|].
  intro r; specialize (agree_mregs r); unfold undef_temps.
  by destruct r; simpl; 
     (repeat (rewrite Pregmap.gso; [|done]); rewrite ?Pregmap.gss);
     (repeat (rewrite Regmap.gso; [|done]); rewrite ?Regmap.gss).

  Case "Mint16unsigned".
  split.
    reduce_internal Heip steptau_weakstep; [by des_teed | adjust_nextinstr].
    reduce_internal Heip steptau_weakstep; [by des_teed | adjust_nextinstr].
    reduce_weakstep Heip.
    unfold write_ea, nextinstr; simpl.
    repeat (rewrite Pregmap.gso; [|done]); rewrite Pregmap.gss.
    repeat (rewrite Pregmap.gso; [|done]); rewrite Pregmap.gss.
    rewrite ea_nextinstr in X; rewrite X; simpl; rewrite !Ptr.add_zero_r.
    repeat (rewrite Pregmap.gso; [|by destruct x1]); rewrite Pregmap.gss.
    by rewrite dec_eq_true.
  repeat (rewrite Pregmap.gso; [|done]); rewrite Pregmap.gss, Heip, ?val_incr_pointer.
  eapply match_states_intro; eauto using incl_cons_inv;
    repeat (rewrite Pregmap.gso; [|done]); try rewrite Pregmap.gss;
    eauto with x86gen.
  inv AG; constructor; [by rgso; rgso; rgso; rgso; rgso|done|].
  intro r; specialize (agree_mregs r); unfold undef_temps.
  by destruct r; simpl; 
     (repeat (rewrite Pregmap.gso; [|done]); rewrite ?Pregmap.gss);
     (repeat (rewrite Regmap.gso; [|done]); rewrite ?Regmap.gss).
Qed.

Lemma exec_Mcall_correct:
  forall t s fb sp sig ros c stkr rs f f' roffs
    (FF : find_function_ptr ge ros rs = Some f')
    (GFF : Genv.find_funct_ptr ge fb = Some (Internal f))
    (RA : return_address_offset f c roffs)
    (MS : match_states (Machconcr.State s fb sp (Mcall sig ros :: c) stkr rs) t)
    (RI : range_inside
           (Ptr.sub_int sp (Int.repr Stacklayout.fe_retaddrsize), Int.zero)
           stkr),
   (exists t' : state,
      exists v' : val,
        Val.lessdef (Vptr (Ptr (Int.unsigned (Ptr.offset fb)) roffs)) v' /\
        weakstep tlts t
          (TEmem
             (MEwrite (Ptr.sub_int sp (Int.repr Stacklayout.fe_retaddrsize))
                Mint32 v')) t' /\
        match_states
          (Callstate
             (Stackframe fb sp (Ptr (Int.unsigned (Ptr.offset fb)) roffs) c
              :: s) f' (Ptr.sub_int sp (Int.repr Stacklayout.fe_retaddrsize))
             stkr rs) t').
Proof.
  intros; inv MS.
  find_current_instruction.

  monadInv HTF0; clarify'.
  destruct ros as [reg | symb]; monadInv EQ0;
  inversion RA; rewrite ?HTF, ?EQ in *; clarify;
  (generalize GOFS; intro GOFS';
   apply code_tail_next_int in GOFS'; [|by eauto with x86gen];
   pose proof (code_tail_determinate _ _ _ _ H GOFS'); subst; clear H GOFS';
   rewrite Int.repr_unsigned in RA |- * ).

(* indirect call (Xcallreg) *)
  inversion FF. 
  exploit ireg_val; eauto. intro Hld. 
  destruct (rs reg); try destruct p; inv Hld; inv H0. 

  econstructor. eexists.
  split. apply Val.lessdef_refl.
  split. reduce_weakstep Heip. 
  rewrite (agree_sp _ _ _ AG). simpl.
  destruct range_inside_dec. unfold Stacklayout.fe_retaddrsize.
  rewrite Heip, <- H2. simpl.
  des_teed.
  eby destruct thread_event_eq_dec.
  (* match states *)
  simpl in FF. 
  eapply match_states_call; eauto.
  (* match stack *)
  econstructor; eauto with x86gen.
  eby eapply incl_cons_inv.
    destruct (rs reg); clarify. 
  (* the tricky part now *)
  simpl. unfold nullptr. intro; clarify.
  clear -GOFS H HTF FIND.
  revert H.
  change (1 mod Int.modulus) with 1. 
  change (0 mod Int.modulus) with 0. 
  rewrite Zmod_small.
  exploit code_tail_bounds; eauto. intro Hb.
  generalize (functions_transl_no_overflow _ _ _ _ FIND HTF); intro Hs.
  intro; omega.
  generalize (functions_transl_no_overflow _ _ _ _ FIND HTF); intro Hs.
  exploit code_tail_bounds; eauto. intro Hb.
  split. omega.
  unfold Int.max_unsigned in Hs. omega.
  (* agree *)
  constructor; intros; try done; gs_simpl. 
    rgso. rgso. eby eapply agree_mregs.
  by gs_simpl. 

(* direct call (Xcall) *)
  econstructor. eexists.
  split. apply Val.lessdef_refl.
  split. reduce_weakstep Heip. 
  rewrite (agree_sp _ _ _ AG). simpl. 
  destruct range_inside_dec. unfold Stacklayout.fe_retaddrsize.
  rewrite Heip.
  des_teed. 
  eby destruct thread_event_eq_dec.
  (* match states *)
  simpl in FF. 
  destruct f' as [b' ofs'].
  eapply match_states_call; eauto.
  (* match stack *)
  econstructor; eauto with x86gen.
  eby eapply incl_cons_inv.
  (* the tricky part now *)
  simpl. unfold nullptr. intro; clarify.
  clear -GOFS H HTF FIND.
  revert H.
  change (1 mod Int.modulus) with 1. 
  change (0 mod Int.modulus) with 0. 
  rewrite Zmod_small.
  exploit code_tail_bounds; eauto. intro Hb.
  generalize (functions_transl_no_overflow _ _ _ _ FIND HTF); intro Hs.
  intro; omega.
  generalize (functions_transl_no_overflow _ _ _ _ FIND HTF); intro Hs.
  exploit code_tail_bounds; eauto. intro Hb.
  split. omega.
  unfold Int.max_unsigned in Hs. omega.
  (* agree *)
  constructor; intros; try done; gs_simpl. 
    rgso. rgso. eby eapply agree_mregs.
  by gs_simpl; unfold code_pointer_from_function_ident; rewrite <- (proj1 TRANSF), FF.
Qed.

Ltac unfold_flags :=
  unfold write_int_result,
         write_result_flags_only,
         write_logical_result,
         write_logical_result_flags_only,
         write_result_erase_flags,
         write_arith_eflags, write_arith_eflags_ZF, 
         write_logical_eflags, erase_eflags, write_eflag.

Lemma exec_Mreturn_correct:
  forall t s fb sp c stkr rs sp' f'
    (H : Genv.find_funct_ptr ge fb = Some (Internal f'))
    (H0 : sp' = (sp + total_framesize f')%pointer)
    (INSIDE: range_inside (sp', Int.zero) stkr)
    (MS : match_states (Machconcr.State s fb sp (Mreturn :: c) stkr rs) t),
  (exists t' : state,
     weakstep tlts t TEtau t' /\ match_states (Returnstate s sp' stkr rs) t').
Proof.
  intros. inv MS.
  find_current_instruction. 
  monadInv HTF0. 
  destruct sp.
  eexists. split.
  reduce_internal Heip steptau_weakstep; [by des_teed | adjust_nextinstr].
  reduce_weakstep Heip.
  unfold write_int_result, add_with_carry_out; rewrite (agree_sp _ _ _ AG); 
    unfold_flags; simpl.

  destruct range_inside_dec. by des_teed.
  by elim n; revert INSIDE; clear; unfold total_framesize; rewrite Zplus_comm.
  
  eapply match_states_return_internal; eauto.
  (* AG *)
  eapply mkagree; try done.
  - by rgss; unfold total_framesize; rewrite Zplus_comm.
  eby intro; repeat rgso; eapply preg_val, agree_nextinstr.
  (* AT2 *)
  gs_simpl_safe; unfold nextinstr; rewrite Heip; rgss; simpl; auto. 
  (* AT3 *)
  eapply functions_transl; eauto. 
  (* AT4 *)
  exploit code_tail_next; eauto. intro GOFS1.
  eapply find_instr_tail. simpl.   
  rewrite Zmod_small; [|
    assert (1 mod Int.modulus = 1) by done; rewrite H; 
    generalize (code_tail_bounds _ _ _ _ GOFS); 
    generalize (functions_transl_no_overflow _ _ _ _ FIND HTF); 
    unfold Int.max_unsigned; omega].  
  rewrite Zmod_small; [|done].
  eauto.
Qed.

Lemma exec_function_internal_correct:
  forall t s fb stkr rs f sp sp'
    (H : Genv.find_funct_ptr ge fb = Some (Internal f))
    (H0 : sp' = Ptr.sub_int sp (total_framesize f))
    (H1 : range_inside (sp', Int.zero) stkr)
    (MS : match_states (Callstate s fb sp stkr rs) t),
  (exists t' : state,
     weakstep tlts t TEtau t' /\
     match_states (Machconcr.State s fb sp' (fn_code f) stkr rs) t').
Proof.
  intros. inv MS.   
  assert (FF := proj2 TRANSF (Ptr b ofs)).
  rewrite H in FF.
  pose proof (find_function_block_0 b ofs) as E; rewrite H in E; subst b.
  destruct (Genv.find_funct_ptr tge (Ptr 0 ofs)) as [] _eqn : E; [|done].
  monadInv FF. destruct x as [sig tc]. generalize EQ; intro EQ'. monadInv EQ'. destruct zlt; [|done]. inv EQ1.
  destruct sp.
  eexists; split.
  eapply steptau_weakstep. unfold_step.
  rewrite AT, Int.repr_unsigned, E.
  simpl. des_teed. 
  apply step_weakstep. simpl.
  unfold write_int_result, sub_with_borrow_out. rewrite (agree_sp _ _ _ AG).

  simpl in H1; unfold total_framesize in H1; rewrite Zplus_comm in H1. 
  destruct z0 as [] _eqn: ZZZ; simpl;
  unfold_flags; 
  unfold_step;
  (destruct range_inside_dec; [simpl; rewrite dec_eq_true|done]);
  by rewrite <- ZZZ.

  simpl.
  unfold sub_borrow.
  eapply match_states_intro; eauto.
  specialize (WTGENV (Vptr (Ptr 0 ofs))).
  unfold Genv.find_funct in WTGENV. rewrite H in WTGENV. by inv WTGENV.
  done.
  by gs_simpl_safe; rewrite nextinstr1, AT; simpl. 

  gs_simpl_safe; rewrite nextinstr1, AT; simpl. 
   eapply transl_code_at_pc_intro; eauto.
  rewrite Int.repr_unsigned. auto.

  simpl. 
  replace ((1 mod Int.modulus) mod Int.modulus) with (0 + 1) by done. 
  eapply code_tail_next. apply code_tail_0.

  eapply mkagree; try done.
  - by rgss; unfold total_framesize; rewrite Zplus_comm.
  eby intro; repeat rgso; eapply preg_val, agree_nextinstr.
Qed.

Lemma exec_return_correct:
  forall t s f sp ra c stkr rs sp'
    (H : sp' = (sp + Int.repr Stacklayout.fe_retaddrsize)%pointer)
    (MS : match_states (Returnstate (Stackframe f sp' ra c :: s) sp stkr rs) t),
  (exists t' : state,
     weakstep tlts t (TEmem (MEread sp Mint32 (Vptr ra))) t' /\
     (forall v' : val,
      Val.lessdef v' (Vptr ra) ->
      exists s'' : Machconcr.state,
        mc_step ge (Returnstate (Stackframe f sp' ra c :: s) sp stkr rs)
          (TEmem (MEread sp Mint32 v')) s'' /\ match_states s'' t')).
Proof.
  intros. inv MS. 
  eexists. split. eapply step_weakstep. unfold_step. 
  rewrite AT2. rewrite AT3. rewrite AT4. simpl.
  rewrite (agree_sp _ _ _ AG). simpl. destruct Ptr.eq_dec;[clear e|done].
  (* destruct memory_chunk_eq_dec;[clear e|done]. *)
  reflexivity.
  intros v' LD. inv LD. 
  (* good case, the ra is a pointer *)
  eexists. split. apply Machconcr.exec_return; auto.
  inv STACKS. destruct Val.eq_dec. inversion e. rewrite H0 in H8. rewrite H1 in H8. done. 
  eapply match_states_intro; eauto. 
  by rgso; rgss. 
  rgso; rgss. eauto. 
  apply mkagree.
  rewrite Pregmap.gss; auto. done.
  intro. rewrite Pregmap.gso; auto with x86gen. rewrite Pregmap.gso; auto with x86gen. 
  eapply preg_val. eauto.
  (* bad case, the ra is Undef *)
  eexists. split. eapply exec_return_fail; done. 
  vauto.
  (* external return *)
  destruct (Val.eq_dec (Vptr ra) (Vptr nullptr)); [by clarify; inv STACKS|].
  (* ra <> nullptr *)
  eexists. split.
  apply step_weakstep. unfold_step.
  rewrite (agree_sp _ _ _ AG).
   by unfold read_mem; rewrite !dec_eq_true; simpl; rewrite dec_eq_false; clarify.

  intros; inv H; eexists; split; vauto. 
  inv STACKS.
  eapply match_states_intro; eauto.
  rgso. rgss. eauto.
  rgso. rgss. eauto.
  unfold Stacklayout.fe_retaddrsize. 
  eapply mkagree; try done.
  - by rgss. 
  by intros; rgso; rgso; eauto with x86gen.
Qed.


Ltac destruct_code_tail_i_zero := 
  match goal with 
  | GOFS: code_tail _ _ (if Int.eq_dec ?i ?j then _ else _) |- _ =>
     destruct (Int.eq_dec i j) as [] _eqn:Hizero; clear Hizero
  | _ => idtac
  end.

Ltac try_destruct_args_cond :=
   match goal with
  | args: list mreg,
    Htc: transl_cond _ _ _ = OK _ |- _ =>
      destruct args; monadInv Htc
  | _ => idtac
  end.

Lemma unsigned_mod_mod :
  forall ofs sig tf c tc f p
   (GOFS : code_tail (Int.unsigned ofs) tf (c::tc))
   ( HTF : transf_function f = OK (sig, tf))
   (FIND : Genv.find_funct_ptr ge p = Some (Internal f)),
  (Int.unsigned ofs + 1 mod Int.modulus) mod Int.modulus = Int.unsigned ofs + 1.
Proof.
  intros.
  repeat rewrite Zmod_small; try done.
  generalize (code_tail_bounds _ _ _ _ GOFS).
  generalize (functions_transl_no_overflow _ _ _ _ FIND HTF).
  unfold Int.max_unsigned; omega.  
Qed.


(** * Translation of Conditionals *)

Definition b3_moredef (b1 : bool3) (b2: bool) :=
  match b1 with
    | b3_true    => b2
    | b3_false   => negb b2
    | b3_unknown => false
  end.

Lemma cmp_lt:
  forall i j, 
      (vi_eq (Val.of_bool (int_msb (Int.sub i j)))
        (word_signed_overflow_sub i j)) 
    = (if Int.lt i j then b3_false else b3_true).
Proof.
  assert (eq_and_hm:
    forall i,
      ((Int.eq (Int.and i (Int.repr Int.half_modulus)) Int.zero)) =
      (negb (Int.lt i Int.zero))).
    by intros; rewrite int_and_half_modulus; destruct Int.lt.

  intros [i I] [j J]; simpl.
  unfold word_signed_overflow_sub, int_msb; rewrite ?eq_and_hm.
  unfold Int.lt; change (Int.signed Int.zero) with 0.
  rewrite !negb_involutive.
  unfold Int.sub, Int.signed, Int.unsigned; simpl.

  rewrite Int.modulus_expand in *.

  destruct (zlt i Int.half_modulus); 
  destruct (zlt j Int.half_modulus); 
  destruct (zlt i j); try omegaContradiction;
  try (rewrite Zmod_too_small; [|omega]);
  try (rewrite Zmod_small; [|omega]);
  try (rewrite Zmod_too_big; [|omega]);
  rewrite ?Zminus_plus;
  try destruct (zlt (Int.half_modulus + Int.half_modulus + (i - j)));
  try destruct (zlt (i - j)); try omegaContradiction;
  by repeat (destruct (zlt); try omegaContradiction; []).
Qed.

Lemma cmp_ltu0:
  forall i j, Int.eq (sub_borrow i j) Int.zero = negb (Int.ltu i j).
Proof.
  by intros; unfold sub_borrow, Int.ltu; destruct zlt.
Qed.

Lemma cmp_ltu1:
  forall i j, Int.eq (sub_borrow i j) Int.one = Int.ltu i j.
Proof.
  by intros; unfold sub_borrow, Int.ltu; destruct zlt.
Qed.


Lemma transl_cond_float_correct:
  forall cond op args ms rs b stkr k fb ofs tf tc sig
    (Hec  : eval_condition cond ms ## args = Some b)
    (TRAN : transl_cond cond args k = OK tc)
    (FIND : Genv.find_funct_ptr tge (Ptr 0 fb) = Some (Internal (sig,tf)))
    (AG   : forall r : mreg, Val.lessdef (ms r) (rs (preg_of r)))
    (Heip : rs EIP = Vptr (Ptr (Int.unsigned fb) ofs))
    (GOFS : code_tail (Int.unsigned ofs) tf tc)
    (COND : cond = Ccompf op \/ cond = Cnotcompf op),
  exists rs',
     x86_step tge (State rs XPEdone stkr) TEtau (State rs' XPEdone stkr)
  /\ b3_moredef (read_cond rs' (testcond_for_cond cond)) b
  /\ rs' EIP = Val.add (rs EIP) Vone
  /\ forall r, nontemp_preg r = true -> rs' # r = rs # r.
Proof.
  intros; destruct COND; clarify; simpl in *; 
  repeat (destruct args; clarify); simpl in *;
    monadInv TRAN; clarify; simpl in *;
  generalize (AG m); rewrite (freg_of_eq _ _ EQ); intro L1; 
  generalize (AG m0); rewrite (freg_of_eq _ _ EQ1); intro L2;
  destruct (ms m); clarify; inv L1;
  destruct (ms m0); clarify; inv L2;
  destruct op; simpl; clarify;
    (eexists; split;
        [by unfold_step; rewrite Heip, Int.repr_unsigned, FIND;
            reduce_weakstep_2; unfold_flags; des_teed |];
     split;
       [|by unfold write_eflag, nextinstr; gs_simpl; rewrite Heip; 
            split; [|intros; destruct r; gs_simpl]]);
     try done;
     unfold write_eflag; gs_simpl;
     rewrite <- ?H1, <- ?H2; simpl; rewrite Float.unordered_internal;
     try (by unfold Float.cmp; destruct Float.internal_cmp);
     rewrite <- (Float.cmp_swap _ f0);
     try (by unfold Float.cmp; destruct Float.internal_cmp).
Qed.


Lemma transl_cond_mask_correct:
  forall cond i args ms rs b stkr k fb ofs tf tc sig
    (Hec  : eval_condition cond ms ## args = Some b)
    (TRAN : transl_cond cond args k = OK tc)
    (FIND : Genv.find_funct_ptr tge (Ptr 0 fb) = Some (Internal (sig,tf)))
    (AG   : forall r : mreg, Val.lessdef (ms r) (rs (preg_of r)))
    (Heip : rs EIP = Vptr (Ptr (Int.unsigned fb) ofs))
    (GOFS : code_tail (Int.unsigned ofs) tf tc)
    (COND : cond = Cmaskzero i \/ cond = Cmasknotzero i),
  exists rs',
     x86_step tge (State rs XPEdone stkr) TEtau (State rs' XPEdone stkr)
  /\ b3_moredef (read_cond rs' (testcond_for_cond cond)) b
  /\ rs' EIP = Val.add (rs EIP) Vone
  /\ forall r, nontemp_preg r = true -> rs' # r = rs # r.
Proof.
  intros; destruct COND; clarify; simpl in *; 
  repeat (destruct args; clarify); simpl in *;
    monadInv TRAN; clarify; simpl in *;
  generalize (AG m); rewrite (ireg_of_eq _ _ EQ); intro L1;
  destruct (ms m); clarify; inv L1;
    (eexists; split;
        [by unfold_step; rewrite Heip, Int.repr_unsigned, FIND;
            reduce_weakstep_2; unfold_flags; des_teed |];
     split;
       [|by unfold write_eflag, nextinstr; gs_simpl; rewrite Heip; 
            split; [|intros; destruct r; gs_simpl]]);
  by unfold write_eflag; gs_simpl; rewrite <- ?H1; simpl; destruct Int.eq.
Qed.

Lemma eq_sub_zero_eq:
  forall i i', Int.eq (Int.sub i i') Int.zero = Int.eq i i'.
Proof. 
  by intros; rewrite <- (Int.translate_eq _ Int.zero i'), <- Int.sub_add_l,
                  Int.add_commut, Int.sub_add_l, Int.sub_idem, 
                  !(Int.add_commut Int.zero), !Int.add_zero.
Qed.

Lemma Ptr_eq_simpl:
  forall a b c d, Ptr.eq (Ptr a b) (Ptr c d) = (if zeq a c then Int.eq b d else false).
Proof.
  intros; unfold Ptr.eq; destruct Ptr.eq_dec; clarify; 
  destruct zeq; clarify; rewrite ?Int.eq_true, ?Int.eq_false; clarify; congruence.
Qed.

Lemma transl_cond_int_correct:
  forall cond op i args ms rs b stkr k fb ofs tf tc sig
    (Hec  : eval_condition cond ms ## args = Some b)
    (TRAN : transl_cond cond args k = OK tc)
    (FIND : Genv.find_funct_ptr tge (Ptr 0 fb) = Some (Internal (sig,tf)))
    (AG   : forall r : mreg, Val.lessdef (ms r) (rs (preg_of r)))
    (Heip : rs EIP = Vptr (Ptr (Int.unsigned fb) ofs))
    (GOFS : code_tail (Int.unsigned ofs) tf tc)
    (COND : cond = Ccomp op \/ cond = Ccompu op 
            \/ cond = Ccompimm op i \/ cond = Ccompuimm op i),
  exists rs',
     x86_step tge (State rs XPEdone stkr) TEtau (State rs' XPEdone stkr)
  /\ b3_moredef (read_cond rs' (testcond_for_cond cond)) b
  /\ rs' EIP = Val.add (rs EIP) Vone
  /\ forall r, nontemp_preg r = true -> rs' # r = rs # r.
Proof.
  intros; destruct COND as [|[|[]]]; clarify; simpl in *; 
  repeat (destruct args; clarify); simpl in *;
    monadInv TRAN; clarify; simpl in *;
  generalize (AG m); rewrite (ireg_of_eq _ _ EQ); intro L1;
  try (generalize (AG m0); rewrite (ireg_of_eq _ _ EQ1); intro L2);
  try (destruct Int.eq_dec; clarify);
  (eexists; split; 
        [by unfold_step; rewrite Heip, Int.repr_unsigned, FIND;
            reduce_weakstep_2; unfold_flags; unfold sub_with_borrow_out; simpl;
            rewrite dec_eq_true |]);
  try (destruct (ms m) as [| | |[]]; clarify; inv L1);
  try (destruct (ms m0) as [| | |[]]; clarify; inv L2);
  try (destruct zeq; clarify);
  unfold nextinstr; gs_simpl; simpl;
  try (split; [|abstract (split; [by rewrite Heip|by intros; destruct r; clarify; gs_simpl])]);
  rewrite ?eq_sub_zero_eq; destruct op; unfold eval_compare_null in *; clarify; 
  simpl; gs_simpl; simpl in *;
  rewrite ?Ptr_eq_simpl in *;
  rewrite ?zeq_true in *;
  try (rewrite zeq_false in *; [|by intro; clarify]); clarify;
  rewrite ?Int.and_idem, ?cmp_lt, ?cmp_ltu0, ?cmp_ltu1, ?Int.ltu0i, ?Int.ltui0;
  try (by destruct Int.eq; simpl in *; clarify);
  try (by destruct Int.lt; simpl in *; clarify);
  try (by destruct Int.ltu; simpl in *; clarify).

  abstract (by rewrite (Int.lt_not i0), Int.eq_sym; destruct Int.eq; destruct Int.lt).
  abstract (by rewrite (Int.lt_not i0), Int.eq_sym; destruct Int.eq; destruct Int.lt).

  abstract (by rewrite (Int.lt_not i0) in *; destruct Int.eq; destruct Int.lt; simpl in *; clarify).
  abstract (by rewrite (Int.lt_not i0) in *; destruct Int.eq; destruct Int.lt; simpl in *; clarify).

  abstract (by rewrite (Int.ltu_not i0), Int.eq_sym; destruct Int.eq; destruct Int.ltu).
  abstract (by rewrite (Int.ltu_not i0), Int.eq_sym; destruct Int.eq; destruct Int.ltu).

  abstract (by rewrite (Int.ltu_not i0) in *; destruct Int.eq; destruct Int.ltu; simpl in *; clarify).
  abstract (by rewrite (Int.ltu_not i0) in *; destruct Int.eq; destruct Int.ltu; simpl in *; clarify).

  abstract (by rewrite (Int.lt_not i0), Int.eq_sym; destruct Int.eq; destruct Int.lt).
  abstract (by rewrite (Int.lt_not i0), Int.eq_sym; destruct Int.eq; destruct Int.lt).

  abstract (by rewrite (Int.ltu_not i0), Int.eq_sym; destruct Int.eq; destruct Int.ltu).
  abstract (by rewrite (Int.ltu_not i0), Int.eq_sym; destruct Int.eq; destruct Int.ltu).
Qed.

Lemma transl_cond_correct:
  forall cond args c ms rs sp b stkr lbl fb s
    (Hec : eval_condition cond ms ## args = Some b)
    (MS  : match_states
             (Machconcr.State s fb sp (Mcond cond args lbl :: c) stkr ms) 
             (State rs XPEdone stkr)),
  exists rs',
     x86_step tge (State rs XPEdone stkr) TEtau (State rs' XPEdone stkr)
  /\ b3_moredef (read_cond rs' (testcond_for_cond cond)) b
  /\ rs' EIP = Val.add (rs EIP) Vone
  /\ forall r, nontemp_preg r = true -> rs' # r = rs # r.
Proof.
  intros.
  set (X := Val.add (rs EIP) Vone).
  inv MS; clarify; rewrite ErsEIP in AT; inv AT.
  eapply (functions_transl _ _ _ FIND) in HTF.
  monadInv HTF0; inv AG.
  destruct cond;
    try solve [ eapply transl_cond_int_correct with (i := Int.zero); eauto
              | eapply transl_cond_int_correct; eauto
              | eapply transl_cond_float_correct; eauto
              | eapply transl_cond_mask_correct; eauto].
Qed.

Lemma transl_cmp_correct:
  forall cond args c ms rs sp b stkr m fb s
    (Hec : eval_condition cond ms ## args = Some b)
    (MS  : match_states
             (Machconcr.State s fb sp (Mop (Ocmp cond) args m :: c) stkr ms) 
             (State rs XPEdone stkr)),
  exists rs',
     x86_step tge (State rs XPEdone stkr) TEtau (State rs' XPEdone stkr)
  /\ b3_moredef (read_cond rs' (testcond_for_cond cond)) b
  /\ rs' EIP = Val.add (rs EIP) Vone
  /\ forall r, nontemp_preg r = true -> rs' # r = rs # r.
Proof.
  intros.
  set (X := Val.add (rs EIP) Vone).
  inv MS; clarify; rewrite ErsEIP in AT; inv AT.
  eapply (functions_transl _ _ _ FIND) in HTF.
  monadInv HTF0; inv AG.
  destruct cond;
    try solve [ eapply transl_cond_int_correct with (i := Int.zero); eauto
              | eapply transl_cond_int_correct; eauto
              | eapply transl_cond_float_correct; eauto
              | eapply transl_cond_mask_correct; eauto].
Qed.

Lemma exec_Mcond_true_correct:
  forall t s fb f sp cond args lbl c stkr rs c' 
    (Hec : eval_condition cond rs ## args = Some true)
    (Hff : Genv.find_funct_ptr ge fb = Some (Internal f))
    (Hfl : Mach.find_label lbl (fn_code f) = Some c')
    (MS : match_states
           (Machconcr.State s fb sp (Mcond cond args lbl :: c) stkr rs) t),
  (exists t' : state,
     weakstep tlts t TEtau t' /\
     match_states (Machconcr.State s fb sp c' stkr (undef_temps rs)) t').
Proof.
  intros. inversion MS; subst. 
  rewrite FIND in Hff; inv Hff.
  rewrite ErsEIP in AT; inv AT; clear GFUN. monadInv HTF0.
  exploit transl_cond_correct; eauto; clear MS. intros [rs' [Hrs'1 [Hrs'2 [Hrs'3 Hrs'4]]]].
  generalize (transl_find_label lbl _ _ _ HTF); rewrite Hfl; intros [tc' [Htc'1 Htc'2]].
  destruct (label_pos_code_tail lbl tf 0 _ Htc'1) as [pos' [Hpos'1 Hpos'2]]. 
  destruct cond; repeat (destruct args; try done); monadInv EQ0;
  try destruct_code_tail_i_zero;
  try (eexists; split;
    [by eapply steptau_weakstep; [ apply Hrs'1 |]; adjust_nextinstr;
        reduce_weakstep Hrs'3; rewrite Hrs'3, ErsEIP, val_incr_pointer;
        rewrite Int.repr_unsigned, (functions_transl _ _ _ FIND HTF);
        rewrite (find_instr_tail _ _ _ _ GOFS); unfold exec_instr;
        unfold testcond_for_cond in Hrs'2; destruct read_cond; clarify; 
        unfold goto_label; rewrite Hrs'3, ErsEIP, val_incr_pointer;
        rewrite Int.repr_unsigned, (functions_transl _ _ _ FIND HTF);
        rewrite Hpos'1; des_teed|]);
  try (
    eapply match_states_intro; eauto;
    [ eapply find_label_incl; eauto
    | rgss; reflexivity
    | rgss;
      eapply transl_code_at_pc_intro; try rewrite Int.repr_unsigned; eauto;
      destruct Hpos'2 as [Hpos'21 Hpos'22]; rewrite Zminus_0_r in Hpos'21;
      rewrite Int.unsigned_repr; auto;
      generalize (functions_transl_no_overflow f sig tf _ FIND HTF); omega 
    | eapply agree_set_other; auto; eapply agree_exten_temps; eauto ]).
Qed.

Lemma exec_Mcond_false_correct:
  forall t s f sp cond args lbl c stkr rs
    (Hec : eval_condition cond rs ## args = Some false)
    (MS : match_states
         (Machconcr.State s f sp (Mcond cond args lbl :: c) stkr rs) t),
   (exists t' : state,
      weakstep tlts t TEtau t' /\
      match_states (Machconcr.State s f sp c stkr (undef_temps rs)) t').
Proof.
  intros; inversion MS; subst.
  rewrite ErsEIP in AT; inv AT; clear GFUN. monadInv HTF0.
  exploit transl_cond_correct; eauto. intros [rs' [Hrs'1 [Hrs'2 [Hrs'3 Hrs'4]]]].
  destruct cond; repeat (destruct args; try discriminate); monadInv EQ0;
  try destruct_code_tail_i_zero;
  eexists; ( split;
    [by eapply steptau_weakstep; [ apply Hrs'1 |]; adjust_nextinstr;
        reduce_weakstep Hrs'3; rewrite Hrs'3, ErsEIP, val_incr_pointer;
        rewrite Int.repr_unsigned, (functions_transl _ _ _ FIND HTF);
        rewrite (find_instr_tail _ _ _ _ GOFS); unfold exec_instr;
        unfold testcond_for_cond in Hrs'2; destruct read_cond; clarify; 
        des_teed |]); 
  try (
    eapply match_states_intro; eauto;
    [ eby eapply incl_cons_inv
    | by unfold nextinstr; rewrite Hrs'3, ErsEIP; rgss; simpl
    | unfold nextinstr; rewrite Hrs'3, ErsEIP; rgss; simpl;
      eapply transl_code_at_pc_intro; try rewrite Int.repr_unsigned; eauto with x86gen
    | eapply agree_nextinstr; auto; eapply agree_exten_temps; eauto ]).
Qed.

(** * Plain operations *)

(** Binary floating-point ops (double-precision) *)

Lemma exec_binopf_correct:
  forall t s f sp op args res c stkr rs v 
   (EVAL : eval_operation ge (Some sp) op rs ## args = Some v)
   (MS : match_states (Machconcr.State s f sp (Mop op args res :: c) stkr rs) t)
   (OP:  op = Oaddf \/ op = Osubf \/ op = Omulf \/ op = Odivf),
 (exists t' : state,
    weakstep tlts t TEtau t' /\
    match_states
      (Machconcr.State s f sp c stkr (Regmap.set res v (undef_op op rs)))
      t').
Proof.
  intros; inv MS; inv AG.
  destruct OP as [|[|[]]]; clarify;
  (find_current_instruction; destruct args; monadInv EQ0;
   eexists; split;
    [eapply steptau_weakstep; unfold_step;
      [by rewrite Heip, (functions_transl _ _ _ GFUN HTF), 
          (find_instr_tail _ _ _ _ GOFS); simpl; rewrite dec_eq_true
      |by apply step_weakstep; simpl; unfold x86_step, xstep_fn; simpl; des_teed]
    |];
   eapply match_states_intro; eauto using incl_cons_inv;
   try (rgso; unfold nextinstr; rewrite Heip; simpl; rgss; simpl; try done); 
   [by eauto using transl_code_at_pc_intro, code_tail_next_int, functions_transl_no_overflow|]
  );
  apply assertion_inversion_1 in EQ1; subst; simpl in EVAL;
  generalize (agree_mregs res), (agree_mregs m0);
  rewrite (freg_of_eq _ _ EQ0), (freg_of_eq _ _ EQ2);
  intros X1 X2;
  destruct (rs res); clarify; destruct (rs m0); clarify;
  (eapply agree_set_mreg; [eby eapply agree_exten_temps; [eapply agree_nextinstr|]| |];
   [rewrite (freg_of_eq res x1); [by rgss; inv X1; inv X2|done]|]); 
  by intros; rgso; [|unfold freg_of in *; destruct (preg_of res); clarify]. 
Qed.

(** Binary boolean ops (and, or, xor) *)

Lemma exec_boolop_correct:
  forall t s f sp op args res c stkr rs v 
   (EVAL : eval_operation ge (Some sp) op rs ## args = Some v)
   (MS : match_states (Machconcr.State s f sp (Mop op args res :: c) stkr rs) t)
   (OP:  op = Oand \/ op = Oor \/ op = Oxor),
 (exists t' : state,
    weakstep tlts t TEtau t' /\
    match_states
      (Machconcr.State s f sp c stkr (Regmap.set res v (undef_op op rs)))
      t').
Proof.
  intros; inv MS; destruct OP as [|[]]; clarify;
  find_current_instruction; destruct args; monadInv EQ0;
  (eexists; split;
    [by reduce_internal Heip steptau_weakstep; [des_teed|]; 
        apply step_weakstep; simpl; unfold x86_step, xstep_fn; 
        unfold write_logical_result, write_logical_eflags;
        rewrite exec_pexstorei_split; [|by destruct res; inv EQ0]; simpl; des_teed |];
  eapply match_states_intro; eauto using incl_cons_inv;
   try (unfold nextinstr; rgso; rewrite !write_eflag_EIP, Heip; simpl; rgss; try done);
   eauto using transl_code_at_pc_intro, code_tail_next_int, functions_transl_no_overflow;
  (* step 0: invert the assertion and conclude m = res *)
  assert (m = res) by (eapply assertion_inversion_1; apply EQ1); subst m; clear EQ1;
  simpl in EVAL;
  (* step 1: prove relationship between x1-res *)
  inversion AG;
  generalize (agree_mregs res), (agree_mregs m0);
  rewrite (ireg_of_eq _ _ EQ0), (ireg_of_eq _ _ EQ2); intros X1 X2;
  assert (X3: preg_of res = x1) by (unfold ireg_of in EQ0; destruct preg_of; clarify);
  (* step 2: destructions *)
  destruct (rs res); clarify; destruct (rs m0); clarify;
  eapply agree_set_mreg; 
    [by eapply agree_exten_temps; [|done];
     eapply agree_eflag; eapply agree_eflag; eapply agree_eflag; 
     eapply agree_eflag; eapply agree_eflag; eapply agree_eflag; eapply agree_nextinstr; eauto
    |by rewrite X3; unfold write_eflag, nextinstr; repeat first [rgss | rgso]; inv X1; inv X2
    |by intros; rgso; rewrite <- X3]). 
Qed.

Lemma exec_boolopimm_correct:
  forall t s f sp op args res c stkr rs v i 
   (EVAL : eval_operation ge (Some sp) op rs ## args = Some v)
   (MS : match_states (Machconcr.State s f sp (Mop op args res :: c) stkr rs) t)
   (OP:  op = Oandimm i \/ op = Oorimm i \/ op = Oxorimm i),
 (exists t' : state,
    weakstep tlts t TEtau t' /\
    match_states
      (Machconcr.State s f sp c stkr (Regmap.set res v (undef_op op rs)))
      t').
Proof.
  intros; inv MS; destruct OP as [|[]]; clarify;
  find_current_instruction; monadInv EQ0;
  (eexists; split;
    [by reduce_internal Heip steptau_weakstep; [des_teed|]; 
        apply step_weakstep; simpl; unfold x86_step, xstep_fn; 
        unfold write_logical_result, write_logical_eflags;
        rewrite exec_pexstorei_split; [|by destruct res; inv EQ0]; simpl; des_teed |];
  eapply match_states_intro; eauto using incl_cons_inv;
   try (unfold nextinstr; rgso; rewrite !write_eflag_EIP, Heip; simpl; rgss; try done);
   eauto using transl_code_at_pc_intro, code_tail_next_int, functions_transl_no_overflow;
  (* step 0: invert the assertion and conclude m = res *)
  assert (m = res) by (eapply assertion_inversion_1; apply EQ1); subst m; clear EQ1;
  simpl in EVAL;
  (* step 1: prove relationship between x1-res *)
  inversion AG;
  generalize (agree_mregs res);
  rewrite (ireg_of_eq _ _ EQ0); intros X1;
  assert (X3: preg_of res = x1) by (unfold ireg_of in EQ0; destruct preg_of; clarify);
  (* step 2: destructions *)
  destruct (rs res); clarify;
  eapply agree_set_mreg; 
    [by eapply agree_exten_temps; [|done];
     eapply agree_eflag; eapply agree_eflag; eapply agree_eflag; 
     eapply agree_eflag; eapply agree_eflag; eapply agree_eflag; eapply agree_nextinstr; eauto
    |by rewrite X3; unfold write_eflag, nextinstr; repeat first [rgss | rgso]; inv X1
    |by intros; rgso; rewrite <- X3]). 
Qed.

(** Shifts and rotations *)

Lemma ltu32_fits_in_8bit:
  forall i, Int.ltu i (Int.repr 32) -> Int.zero_ext 8 i = i.
Proof.
  unfold Int.ltu; intros.
  apply Int.unsigned_eq; rewrite Int.zero_ext_mod, Zmod_small; try done.
  revert H; case zlt; try done.
  change (Int.unsigned (Int.repr 32)) with 32.
  change (two_p 8) with 256.
  intros; pose proof (Int.unsigned_range i); omega.
Qed.

Lemma exec_shiftop_correct:
  forall t s f sp op args res c stkr rs v 
   (EVAL : eval_operation ge (Some sp) op rs ## args = Some v)
   (MS : match_states (Machconcr.State s f sp (Mop op args res :: c) stkr rs) t)
   (OP:  op = Oshl \/ op = Oshr \/ op = Oshru),
 (exists t' : state,
    weakstep tlts t TEtau t' /\
    match_states
      (Machconcr.State s f sp c stkr (Regmap.set res v (undef_op op rs)))
      t').
Proof.
  intros; inv MS; destruct OP as [|[]]; clarify;
  find_current_instruction; destruct args; monadInv EQ0;
  (* step 0: invert the assertion and conclude m = res *)
  assert (m = res) by (eapply assertion_inversion_1; apply EQ1); subst m; clear EQ1; clear x0;
  (* step 1: prove relationship between x1-res and x2-m0 *)
  inversion AG;
  generalize (agree_mregs res), (agree_mregs m0);
  rewrite (ireg_of_eq _ _ EQ0), (ireg_of_eq _ _ EQ2); intros X1 X2;
  assert (X3: preg_of res = x1) by (unfold ireg_of in EQ0; destruct preg_of; clarify);
  (* step 2: destruct the registers *)
  simpl in EVAL;
  destruct (rs res); clarify; destruct (rs m0); clarify;
  destruct (Int.ltu i0 (Int.repr 32)) as [] _eqn: LTU; clarify;
(  unfold mk_shift in *;
  destruct (ireg_eq x2 ECX); clarify;
  [eexists; split;
    [by reduce_internal Heip steptau_weakstep; [des_teed|]; 
        apply step_weakstep; simpl; unfold x86_step, xstep_fn; 
        unfold write_result_erase_flags, write_logical_eflags, erase_eflags;
        rewrite exec_pexstorei_split; [|by destruct res; inv EQ0]; simpl; des_teed |];
  eapply match_states_intro; eauto using incl_cons_inv;
   try (unfold nextinstr; rgso; rewrite !write_eflag_EIP, Heip; simpl; rgss; try done);
   eauto with x86gen;
  eapply agree_set_mreg; 
    [by eapply agree_exten_temps; [|done];
     eapply agree_eflag; eapply agree_eflag; eapply agree_eflag; 
     eapply agree_eflag; eapply agree_eflag; eapply agree_eflag; eapply agree_nextinstr; eauto
    |by rewrite X3; unfold write_eflag, nextinstr; repeat first [rgss | rgso]; inv X1; inv X2; 
     simpl; rewrite (ltu32_fits_in_8bit _ LTU); rewrite LTU
    |by intros; rgso; [|rewrite <- X3]]
 |monadInv EQ4; destruct (ireg_eq x1 ECX); simpl in *; try done;
  eexists; split;
  [by reduce_internal Heip steptau_weakstep; [by des_teed|adjust_nextinstr]; 
      reduce_internal Heip steptau_weakstep; [by des_teed|];
      apply step_weakstep; simpl; unfold x86_step, xstep_fn;
      unfold write_result_erase_flags, erase_eflags;
      rewrite exec_pexstorei_split; 
      [simpl; des_teed|by revert X3; clear; destruct res; destruct x1; clarify]|]];
  eapply match_states_intro; eauto using incl_cons_inv;
   try (unfold nextinstr, write_eflag; gs_simpl_safe; rgss; 
        gs_simpl_safe; rgss; rewrite Heip, ?val_incr_pointer); try done; 
   [by eauto 6 with x86gen|];
  econstructor; eauto;
    [by unfold write_eflag, nextinstr; repeat first [rgss | rgso]; 
        [|destruct x1; try done; destruct res]
    |intros; destruct (mreg_eq r res); 
     [by subst; rewrite Regmap.gss; rewrite X3; repeat first [rgss | rgso]; 
         inv X1; inv X2; simpl; rewrite !(ltu32_fits_in_8bit _ LTU), LTU
     |rewrite Regmap.gso; [|congruence]; specialize (agree_mregs r); 
      by unfold undef_temps; destruct r; simpl in *; 
         repeat (first [rewrite Regmap.gss|rewrite Pregmap.gss 
                       |rewrite Regmap.gso|rewrite Pregmap.gso]; try done); 
         destruct x1; try done; destruct res; clarify]]).
Qed.

Lemma exec_shiftopimm_correct:
  forall t s f sp op args res c stkr rs v i 
   (EVAL : eval_operation ge (Some sp) op rs ## args = Some v)
   (MS : match_states (Machconcr.State s f sp (Mop op args res :: c) stkr rs) t)
   (OP:  op = Oshlimm i \/ op = Oshrimm i \/ op = Oshruimm i \/ op = Ororimm i),
 (exists t' : state,
    weakstep tlts t TEtau t' /\
    match_states
      (Machconcr.State s f sp c stkr (Regmap.set res v (undef_op op rs)))
      t').
Proof.
  intros; inv MS; destruct OP as [|[|[]]]; clarify;
  find_current_instruction; monadInv EQ0;
  (* step 0: invert the assertion and conclude m = res *)
  assert (m = res) by (eapply assertion_inversion_1; apply EQ1); subst m; clear EQ1; clear x0;
  (* step 1: prove relationship between x1-res and x2-m0 *)
  inversion AG;
  generalize (agree_mregs res);
  rewrite (ireg_of_eq _ _ EQ0); intros X1;
  assert (X3: preg_of res = x1) by (unfold ireg_of in EQ0; destruct preg_of; clarify);
  (* step 2: destruct the registers *)
  simpl in EVAL;
  destruct (rs res); clarify;
  destruct (Int.ltu i (Int.repr 32)) as [] _eqn: LTU; clarify;
(  unfold mk_shift in *;
  eexists; split;
    [by reduce_internal Heip steptau_weakstep; [des_teed|]; 
        apply step_weakstep; simpl; unfold x86_step, xstep_fn; 
        unfold write_result_erase_flags, write_logical_eflags, erase_eflags;
        rewrite exec_pexstorei_split; [|by destruct res; inv EQ0]; simpl; des_teed |];
  eapply match_states_intro; eauto using incl_cons_inv;
   try (unfold nextinstr; rgso; rewrite !write_eflag_EIP, Heip; simpl; rgss; try done);
   eauto using transl_code_at_pc_intro, code_tail_next_int, functions_transl_no_overflow;
  eapply agree_set_mreg; 
    [by eapply agree_exten_temps; [|done];
     eapply agree_eflag; eapply agree_eflag; eapply agree_eflag; 
     eapply agree_eflag; eapply agree_eflag; eapply agree_eflag; eapply agree_nextinstr; eauto
    |by rewrite X3; unfold write_eflag, nextinstr; repeat first [rgss | rgso]; inv X1;
     simpl; rewrite LTU
    |by intros; rgso; [|rewrite <- X3]]
).
Qed.

(** Casts between integer types *)

Lemma exec_cast_correct:
  forall t s f sp op args res c stkr rs v 
   (EVAL : eval_operation ge (Some sp) op rs ## args = Some v)
   (MS : match_states (Machconcr.State s f sp (Mop op args res :: c) stkr rs) t)
   (OP:  op = Ocast8signed \/ op = Ocast8unsigned \/ op = Ocast16signed \/ op = Ocast16unsigned),
 (exists t' : state,
    weakstep tlts t TEtau t' /\
    match_states
      (Machconcr.State s f sp c stkr (Regmap.set res v (undef_op op rs)))
      t').
Proof.
  intros; inv MS; destruct OP as [|[|[]]]; clarify;
  find_current_instruction; monadInv EQ0; simpl in *; clarify; unfold mk_intconv in *; 
  (destruct (get_low_ireg x0) as [lowreg|] _eqn: LOW_EQ; clarify;
    [eexists; split; [by reduce_weakstep Heip; rewrite dec_eq_true|];
     eapply match_states_intro; eauto using incl_cons_inv;
     try (unfold nextinstr; rgso; rgss; rewrite Heip; simpl); try done;
     eauto with x86gen;
     rewrite <- (ireg_of_eq res _ EQ0);
     eapply agree_set_mreg; 
       [eby eapply agree_exten_temps
       |by rgss; unfold do_extend, nextinstr; rgso;
           inversion AG; assert (Hm := agree_mregs m); 
           rewrite (ireg_of_eq m x0) in Hm; [|done];
           destruct x0; simpl in *; clarify; simpl; destruct (rs m); inv Hm
       |by intros; rgso; rewrite nextinstr_inv; try done;
           destruct r'; try destruct i0; inv H; auto with x86gen]
    |eexists; split;
       [by reduce_internal Heip steptau_weakstep; [by des_teed|adjust_nextinstr];
           reduce_weakstep Heip; des_teed
       |]]);
    (eapply match_states_intro; eauto using incl_cons_inv;
      repeat first [(rewrite Pregmap.gso; [|done]) | rewrite nextinstr1 
        | rewrite Heip, ?val_incr_pointer ]; 
     eauto with x86gen;
     assert (FOO: preg_of res = x1) by (by destruct res; inv EQ0);
      eapply agree_set_mreg; 
       [eapply agree_exten_temps with (rs' := rs0 # EDX <- (rs0 x0)); eauto;
        by destruct r as [[]| | | |]; intros; clarify; try rgss; rgso
       |by rewrite FOO; unfold nextinstr; repeat first [rgss | rgso]; inversion AG; 
           assert (Hm:= agree_mregs m); rewrite (ireg_of_eq m x0) in Hm; [inv Hm|done]
       |by rewrite FOO; unfold nextinstr; intros; destruct (preg_eq r' EDX); [subst|];
           repeat first [ rgss | rgso ]]).
Qed.

(** Division and modulus *)

Lemma exec_divs_body_correct:
  forall (rs: regset) (arg: ireg) f c stkr sig b ofs tf
  (NEQ : arg <> EDX)
  (HTF : transf_function f = OK (sig, tf)) 
  (GFUN : Genv.find_funct_ptr ge (Ptr 0 (Int.repr b)) = Some (Internal f))
  (Heip : rs # EIP = Vptr (Ptr b ofs))
  (GOFS : code_tail (Int.unsigned ofs) tf (Xcltd :: Xmonop Xidiv (Xr arg) :: c)),
   exists rs',
     weakstep tlts (State rs XPEdone stkr) TEtau (State rs' XPEdone stkr) /\
     rs' EAX = Val.divs (rs EAX) (rs arg) /\
     rs' EIP = Vptr (Ptr b (Int.add (Int.add ofs Int.one) Int.one)) /\
     rs' ESP = rs ESP /\
     (forall r,
        important_preg r -> 
        r <> EAX -> r <> EDX ->
        rs' r = rs r).
Proof.
  intros; eexists; split.
    by reduce_internal Heip steptau_weakstep; [by des_teed|adjust_nextinstr];
       reduce_weakstep Heip; des_teed;
       gs_simpl_safe; destruct Val.eq_dec as [_|NEQ'];
       [|elim NEQ'; unfold nextinstr; repeat first [rgss | rgso]; congruence].
  unfold nextinstr; gs_simpl; rewrite Heip.
  by repeat split; intros; repeat rgso.
Qed.

Lemma exec_mods_body_correct:
  forall (rs: regset) (arg: ireg) f c stkr sig b ofs tf
  (NEQ : arg <> EDX)
  (HTF : transf_function f = OK (sig, tf)) 
  (GFUN : Genv.find_funct_ptr ge (Ptr 0 (Int.repr b)) = Some (Internal f))
  (Heip : rs # EIP = Vptr (Ptr b ofs))
  (GOFS : code_tail (Int.unsigned ofs) tf (Xcltd :: Xmonop Xidiv (Xr arg) :: c)),
   exists rs',
     weakstep tlts (State rs XPEdone stkr) TEtau (State rs' XPEdone stkr) /\
     rs' EDX = Val.mods (rs EAX) (rs arg) /\
     rs' EIP = Vptr (Ptr b (Int.add (Int.add ofs Int.one) Int.one)) /\
     rs' ESP = rs ESP /\
     (forall r,
        important_preg r -> 
        r <> EAX -> r <> EDX ->
        rs' r = rs r).
Proof.
  intros; eexists; split.
    by reduce_internal Heip steptau_weakstep; [by des_teed|adjust_nextinstr];
       reduce_weakstep Heip; des_teed;
       gs_simpl_safe; destruct Val.eq_dec as [_|NEQ'];
       [|elim NEQ'; unfold nextinstr; repeat first [rgss | rgso]; congruence].
  unfold nextinstr; gs_simpl; rewrite Heip.
  by repeat split; intros; repeat rgso.
Qed.

Lemma exec_divu_body_correct:
  forall (rs: regset) (arg: ireg) f c stkr sig b ofs tf
  (NEQ : arg <> EDX)
  (HTF : transf_function f = OK (sig, tf)) 
  (GFUN : Genv.find_funct_ptr ge (Ptr 0 (Int.repr b)) = Some (Internal f))
  (Heip : rs # EIP = Vptr (Ptr b ofs))
  (GOFS : code_tail (Int.unsigned ofs) tf
             (Xxor_self EDX :: Xmonop Xdiv (Xr arg) :: c)),
   exists rs',
     weakstep tlts (State rs XPEdone stkr) TEtau (State rs' XPEdone stkr) /\
     rs' EAX = Val.divu (rs EAX) (rs arg) /\
     rs' EIP = Vptr (Ptr b (Int.add (Int.add ofs Int.one) Int.one)) /\
     rs' ESP = rs ESP /\
     (forall r,
        important_preg r -> 
        r <> EAX -> r <> EDX ->
        rs' r = rs r).
Proof.
  intros; eexists; split.
     reduce_internal Heip steptau_weakstep; [by des_teed|].
     reduce_internal Heip steptau_weakstep;
       [by unfold write_logical_result, write_int_rm; simpl; des_teed|adjust_nextinstr].
     reduce_weakstep Heip.
     unfold_flags; gs_simpl_safe; rewrite nextinstr1, Heip, val_incr_pointer.
     rewrite (functions_transl _ _ _ GFUN HTF), (find_instr_tail _ _ _ _ GOFS). 
     unfold exec_instr, write_monop, read_int_rm; rewrite dec_eq_true.
     by gs_simpl_safe; destruct Val.eq_dec as [_|NEQ'];
        [|elim NEQ'; unfold nextinstr; repeat first [rgss | rgso]]. 
  unfold nextinstr; gs_simpl; rewrite Heip.
  by repeat split; intros; repeat rgso.
Qed.

Lemma exec_modu_body_correct:
  forall (rs: regset) (arg: ireg) f c stkr sig b ofs tf
  (NEQ : arg <> EDX)
  (HTF : transf_function f = OK (sig, tf)) 
  (GFUN : Genv.find_funct_ptr ge (Ptr 0 (Int.repr b)) = Some (Internal f))
  (Heip : rs # EIP = Vptr (Ptr b ofs))
  (GOFS : code_tail (Int.unsigned ofs) tf
             (Xxor_self EDX :: Xmonop Xdiv (Xr arg) :: c)),
   exists rs',
     weakstep tlts (State rs XPEdone stkr) TEtau (State rs' XPEdone stkr) /\
     rs' EDX = Val.modu (rs EAX) (rs arg) /\
     rs' EIP = Vptr (Ptr b (Int.add (Int.add ofs Int.one) Int.one)) /\
     rs' ESP = rs ESP /\
     (forall r,
        important_preg r -> 
        r <> EAX -> r <> EDX ->
        rs' r = rs r).
Proof.
  intros; eexists; split.
     reduce_internal Heip steptau_weakstep; [by des_teed|].
     reduce_internal Heip steptau_weakstep;
       [by unfold write_logical_result, write_int_rm; simpl; des_teed|adjust_nextinstr].
     reduce_weakstep Heip.
     unfold_flags; gs_simpl_safe; rewrite nextinstr1, Heip, val_incr_pointer.
     rewrite (functions_transl _ _ _ GFUN HTF), (find_instr_tail _ _ _ _ GOFS). 
     unfold exec_instr, write_monop, read_int_rm; rewrite dec_eq_true.
     by gs_simpl_safe; destruct Val.eq_dec as [_|NEQ'];
        [|elim NEQ'; unfold nextinstr; repeat first [rgss | rgso]]. 
  unfold nextinstr; gs_simpl; rewrite Heip.
  by repeat split; intros; repeat rgso.
Qed.


Lemma exec_mk_div_correct:
  forall op1 op2 compf f (arg res: ireg) c stkr rs b ofs k sig tf tc
  (HTF : transf_function f = OK (sig, tf)) 
  (GFUN : Genv.find_funct_ptr ge (Ptr 0 (Int.repr (Int.unsigned b))) = Some (Internal f))
  (Heip : rs # EIP = Vptr (Ptr (Int.unsigned b) ofs))
  (GOFS : code_tail (Int.unsigned ofs) tf tc)
  (TRANSL: transl_code f c = OK k)
  (NEres : ESP <> res)
  (NEarg : ESP <> arg)
  (DIV : mk_div op1 op2 res arg k = OK tc)
  (EXEC_BODY:
     forall (rs: regset) (arg: ireg) f c stkr sig b ofs tf,
      arg <> EDX ->
      transf_function f = OK (sig, tf) ->
      Genv.find_funct_ptr ge (Ptr 0 (Int.repr b)) = Some (Internal f) ->
      rs # EIP = Vptr (Ptr b ofs) ->
      code_tail (Int.unsigned ofs) tf (op1 :: Xmonop op2 (Xr arg) :: c) ->
   exists rs',
     weakstep tlts (State rs XPEdone stkr) TEtau (State rs' XPEdone stkr) /\
     rs' EAX = compf (rs EAX) (rs arg) /\
     rs' EIP = Vptr (Ptr b (Int.add (Int.add ofs Int.one) Int.one)) /\
     rs' ESP = rs ESP /\
     (forall r,
        important_preg r -> 
        r <> EAX -> r <> EDX ->
        rs' r = rs r)),
   exists rs', exists ofs',
     weakstep tlts (State rs XPEdone stkr) TEtau (State rs' XPEdone stkr) /\
     transl_code_at_pc (rs' EIP) f c tf k /\
     rs' res = compf (rs res) (rs arg) /\
     rs' EIP = Vptr (Ptr (Int.unsigned b) ofs') /\
     rs' ESP = rs ESP /\
     (forall r, nontemp_preg r -> r <> res -> rs' r = rs r).
Proof.
  intros.
  unfold mk_div in *.
  destruct (ireg_eq res EAX); clarify; 
    [destruct (ireg_eq arg EDX); clarify; simpl in *
    |simpl in *; monadInv DIV;  apply assertion_inversion_2 in EQ; 
     destruct (ireg_eq arg EAX); clarify; simpl in *].

  SCase 1.
    exploit (EXEC_BODY ((nextinstr rs) # ECX <- (rs EDX)) ECX);
      eauto with x86gen.
    - by gs_simpl; rewrite nextinstr1, Heip.
    unfold nextinstr; gs_simpl_safe; intros (rs' & WS & Eres & Eip & Esp & Eother).
    eexists; eexists; split.  
      reduce_internal Heip steptau_weakstep; [by des_teed|].
      by gs_simpl_safe; eapply WS.
    rewrite Eip, Eres, Esp, ?val_incr_pointer; repeat split; eauto with x86gen; gs_simpl.
    intros r' NT Nres.
    destruct (preg_eq r' EDX); clarify. 
    rewrite Eother; try done.
      by rgso; rgso.
    by destruct r'.

  SCase 2.
    exploit (EXEC_BODY rs arg);
      eauto with x86gen.
    intros (rs' & WS & Eres & Eip & Esp & Eother).
    eexists; eexists; split; [by eapply WS|].
    rewrite Eip, Eres, Esp, ?val_incr_pointer; repeat split; eauto with x86gen; gs_simpl.
    intros r' NT Nres.
    destruct (preg_eq r' EDX); clarify. 
    rewrite Eother; try done.
    by destruct r'.

  SCase 3.
    exploit 
      (EXEC_BODY 
        ((nextinstr (nextinstr rs) # ECX <- (rs EAX)) # EAX <- (rs res)) ECX);
      eauto with x86gen.
    - by unfold nextinstr; gs_simpl; rewrite Heip.
    gs_simpl_safe; intros (rs' & WS & Eres & Eip & Esp & Eother).
    eexists; eexists 
      (Int.add (Int.add (Int.add (Int.add (Int.add (Int.add ofs 
       Int.one) Int.one) Int.one) Int.one) Int.one) Int.one); split.  
      reduce_internal Heip steptau_weakstep; [by des_teed|adjust_nextinstr].
      reduce_internal Heip steptau_weakstep; [by des_teed|adjust_nextinstr].
      gs_simpl_safe; eapply weakstep_taustar; [eby eapply WS|];
       eapply weaksteptau_taustar; simpl; adjust_nextinstr; adjust_nextinstr.
      reduce_internal Eip steptau_weakstep; [by des_teed|adjust_nextinstr].
      by reduce_weakstep Eip; des_teed. 
    unfold nextinstr; gs_simpl.
    rewrite Eip, Eres, Esp, ?val_incr_pointer; repeat split; eauto 10 with x86gen; gs_simpl.
    intros r' NT Nres.
    destruct (preg_eq r' EDX); clarify. 
    destruct (preg_eq r' EAX); clarify. 
    unfold nextinstr in *.
    gs_simpl; repeat (rgso; []).
    destruct r' as [ii | ff | | |]; try done.
    - exploit (Eother ii); try done; gs_simpl.
      by destruct ii; clarify; gs_simpl. 
    - by exploit (Eother ff); try done; gs_simpl.

  SCase 4.
    exploit (EXEC_BODY 
        ((nextinstr (nextinstr (nextinstr rs) # XMM7 <- (rs EAX)) # ECX <- (rs arg))
           # EAX <- (rs res)) ECX);
    eauto with x86gen.
    - by unfold nextinstr; gs_simpl; rewrite Heip.
    gs_simpl_safe; intros (rs' & WS & Eres & Eip & Esp & Eother).
    eexists; exists
     (Int.add (Int.add (Int.add (Int.add (Int.add (Int.add (Int.add (Int.add ofs 
      Int.one) Int.one) Int.one) Int.one) Int.one) Int.one) Int.one) Int.one); split.  
      reduce_internal Heip steptau_weakstep; [by des_teed|adjust_nextinstr].
      reduce_internal Heip steptau_weakstep; [by des_teed|adjust_nextinstr].
      reduce_internal Heip steptau_weakstep; [by des_teed|adjust_nextinstr].
      gs_simpl_safe; eapply weakstep_taustar; [eby eapply WS|];
      eapply weaksteptau_taustar; simpl; adjust_nextinstr; adjust_nextinstr.
      reduce_internal Eip steptau_weakstep; [by des_teed|adjust_nextinstr].
      reduce_internal Eip steptau_weakstep; [by des_teed|adjust_nextinstr].
      by reduce_weakstep Eip; des_teed.
    unfold nextinstr; gs_simpl.
    rewrite Eip, Eres, Esp, ?val_incr_pointer; repeat split; eauto 10 with x86gen; gs_simpl.
    intros r' NT Nres.
    destruct (preg_eq r' EDX); clarify. 
    destruct (preg_eq r' EAX); clarify. 
    unfold nextinstr in *.
    gs_simpl; repeat (rgso; []).
    destruct (preg_eq r' arg); clarify. 
      by rgss; rewrite Eother; try done; gs_simpl.
    exploit (Eother r'); try done.
    - by destruct r'.
    by repeat (rgso; []).
Qed.


Lemma exec_mk_mod_correct:
  forall op1 op2 compf f (arg res: ireg) c stkr rs b ofs k sig tf tc
  (HTF : transf_function f = OK (sig, tf)) 
  (GFUN : Genv.find_funct_ptr ge (Ptr 0 (Int.repr (Int.unsigned b))) = Some (Internal f))
  (Heip : rs # EIP = Vptr (Ptr (Int.unsigned b) ofs))
  (GOFS : code_tail (Int.unsigned ofs) tf tc)
  (TRANSL: transl_code f c = OK k)
  (NEres : ESP <> res)
  (NEarg : ESP <> arg)
  (DIV : mk_mod op1 op2 res arg k = OK tc)
  (EXEC_BODY:
     forall (rs: regset) (arg: ireg) f c stkr sig b ofs tf,
      arg <> EDX ->
      transf_function f = OK (sig, tf) ->
      Genv.find_funct_ptr ge (Ptr 0 (Int.repr b)) = Some (Internal f) ->
      rs # EIP = Vptr (Ptr b ofs) ->
      code_tail (Int.unsigned ofs) tf (op1 :: Xmonop op2 (Xr arg) :: c) ->
   exists rs',
     weakstep tlts (State rs XPEdone stkr) TEtau (State rs' XPEdone stkr) /\
     rs' EDX = compf (rs EAX) (rs arg) /\
     rs' EIP = Vptr (Ptr b (Int.add (Int.add ofs Int.one) Int.one)) /\
     rs' ESP = rs ESP /\
     (forall r,
        important_preg r -> 
        r <> EAX -> r <> EDX ->
        rs' r = rs r)),
   exists rs', exists ofs',
     weakstep tlts (State rs XPEdone stkr) TEtau (State rs' XPEdone stkr) /\
     transl_code_at_pc (rs' EIP) f c tf k /\
     rs' res = compf (rs res) (rs arg) /\
     rs' EIP = Vptr (Ptr (Int.unsigned b) ofs') /\
     rs' ESP = rs ESP /\
     (forall r, nontemp_preg r -> r <> res -> rs' r = rs r).
Proof.
  intros.
  unfold mk_mod in *.
  destruct (ireg_eq res EAX); clarify; 
    [destruct (ireg_eq arg EDX); clarify; simpl in *
    |simpl in *; monadInv DIV;  apply assertion_inversion_2 in EQ; 
     destruct (ireg_eq arg EDX); clarify; simpl in *].

  SCase 1.
    exploit (EXEC_BODY ((nextinstr rs) # ECX <- (rs EDX)) ECX);
      eauto with x86gen.
    - by gs_simpl; rewrite nextinstr1, Heip.
    unfold nextinstr; gs_simpl_safe; intros (rs' & WS & Eres & Eip & Esp & Eother).
    eexists; eexists 
     (Int.add (Int.add (Int.add (Int.add ofs 
      Int.one) Int.one) Int.one) Int.one); split.  
      reduce_internal Heip steptau_weakstep; [by des_teed|adjust_nextinstr].
      gs_simpl_safe; eapply weakstep_taustar; [eby eapply WS|];
       eapply weaksteptau_taustar; simpl; adjust_nextinstr; adjust_nextinstr.
      by reduce_weakstep Eip; des_teed.
    unfold nextinstr; gs_simpl.
    rewrite Eip, Eres, Esp, ?val_incr_pointer; repeat split; eauto 10 with x86gen; gs_simpl.
    intros r' NT Nres.
    destruct (preg_eq r' EDX); clarify. 
    rgso; rgso; rewrite Eother; try done.
      by rgso; rgso.
    by destruct r'.

  SCase 2.
    exploit (EXEC_BODY rs arg);
      eauto with x86gen.
    intros (rs' & WS & Eres & Eip & Esp & Eother).
    eexists; eexists (Int.add (Int.add (Int.add ofs Int.one) Int.one) Int.one); split.  
      gs_simpl_safe; eapply weakstep_taustar; [eby eapply WS|];
       eapply weaksteptau_taustar; simpl; adjust_nextinstr; adjust_nextinstr.
      by reduce_weakstep Eip; des_teed.
    unfold nextinstr; gs_simpl.
    rewrite Eip, Eres, Esp, ?val_incr_pointer; repeat split; eauto with x86gen; gs_simpl.
    intros r' NT Nres.
    destruct (preg_eq r' EDX); clarify. 
    rgso; rgso; rewrite Eother; try done.
    by destruct r'.

  SCase 3.
    exploit 
      (EXEC_BODY
        ((nextinstr
           (nextinstr (nextinstr rs) # XMM7 <- (rs EAX)) # ECX <- (rs EDX))
        # EAX <- (rs res)) ECX);
      eauto with x86gen.
    - by unfold nextinstr; gs_simpl; rewrite Heip.
    gs_simpl_safe; intros (rs' & WS & Eres & Eip & Esp & Eother).
    eexists; eexists 
      (Int.add (Int.add (Int.add (Int.add (Int.add (Int.add (Int.add ofs 
       Int.one) Int.one) Int.one) Int.one) Int.one) Int.one) Int.one); split.  
      reduce_internal Heip steptau_weakstep; [by des_teed|adjust_nextinstr].
      reduce_internal Heip steptau_weakstep; [by des_teed|adjust_nextinstr].
      reduce_internal Heip steptau_weakstep; [by des_teed|adjust_nextinstr].
      gs_simpl_safe; eapply weakstep_taustar; [eby eapply WS|];
       eapply weaksteptau_taustar; simpl; adjust_nextinstr; adjust_nextinstr.
      reduce_internal Eip steptau_weakstep; [by des_teed|adjust_nextinstr].
      by reduce_weakstep Eip; des_teed. 
    unfold nextinstr; gs_simpl.
    rewrite Eip, Eres, Esp, ?val_incr_pointer; repeat split; eauto 10 with x86gen; gs_simpl.
    intros r' NT Nres.
    destruct (preg_eq r' EDX); clarify. 
    destruct (preg_eq r' EAX); clarify. 
    destruct (preg_eq r' XMM7); clarify. 
    unfold nextinstr in *.
    gs_simpl; repeat (rgso; []).
    destruct r' as [ii | ff | | |]; try done.
    - exploit (Eother ii); try done; gs_simpl.
      by destruct ii; clarify; gs_simpl. 
    - by exploit (Eother ff); try done; gs_simpl.

  SCase 4.
    exploit (EXEC_BODY 
        ((nextinstr (nextinstr (nextinstr rs) # XMM7 <- (rs EAX)) # ECX <- (rs arg))
           # EAX <- (rs res)) ECX);
    eauto with x86gen.
    - by unfold nextinstr; gs_simpl; rewrite Heip.
    gs_simpl_safe; intros (rs' & WS & Eres & Eip & Esp & Eother).
    eexists; exists
     (Int.add (Int.add (Int.add (Int.add (Int.add (Int.add (Int.add (Int.add ofs 
      Int.one) Int.one) Int.one) Int.one) Int.one) Int.one) Int.one) Int.one); split.  
      reduce_internal Heip steptau_weakstep; [by des_teed|adjust_nextinstr].
      reduce_internal Heip steptau_weakstep; [by des_teed|adjust_nextinstr].
      reduce_internal Heip steptau_weakstep; [by des_teed|adjust_nextinstr].
      gs_simpl_safe; eapply weakstep_taustar; [eby eapply WS|];
      eapply weaksteptau_taustar; simpl; adjust_nextinstr; adjust_nextinstr.
      reduce_internal Eip steptau_weakstep; [by des_teed|adjust_nextinstr].
      reduce_internal Eip steptau_weakstep; [by des_teed|adjust_nextinstr].
      by reduce_weakstep Eip; des_teed.
    unfold nextinstr; gs_simpl.
    rewrite Eip, Eres, Esp, ?val_incr_pointer; repeat split; eauto 10 with x86gen; gs_simpl.
    intros r' NT Nres.
    destruct (preg_eq r' EDX); clarify. 
    destruct (preg_eq r' EAX); clarify. 
    unfold nextinstr in *.
    gs_simpl; repeat (rgso; []).
    destruct (preg_eq r' arg); clarify. 
      by rgss; rewrite Eother; try done; gs_simpl.
    exploit (Eother r'); try done.
    - by destruct r'.
    by repeat (rgso; []).
Qed.


Lemma exec_div_correct:
  forall t s f sp op args res c stkr rs v 
   (EVAL : eval_operation ge (Some sp) op rs ## args = Some v)
   (MS : match_states (Machconcr.State s f sp (Mop op args res :: c) stkr rs) t)
   (OP:  op = Odiv \/ op = Odivu),
 (exists t' : state,
    weakstep tlts t TEtau t' /\
    match_states
      (Machconcr.State s f sp c stkr (Regmap.set res v (undef_op op rs)))
      t').
Proof.
  intros; inv MS; clarify.
  destruct OP as []; clarify;
   [ assert (EXEC_BODY := exec_divs_body_correct) 
   | assert (EXEC_BODY := exec_divu_body_correct)];
  find_current_instruction; destruct args; clarify; monadInv EQ0;
  apply assertion_inversion_1 in EQ1; subst; simpl in EVAL;
    inversion AG;
    assert (L1 := agree_mregs res); destruct (rs res); clarify;
    assert (L2 := agree_mregs m0); destruct (rs m0); clarify;
    clear agree_sp agree_sp_def agree_mregs;
  (exploit (exec_mk_div_correct); eauto;
   [by intro; clarify; destruct res; clarify 
   |by intro; clarify; destruct m0; clarify|];
  intros (rs' & ofs' & WS & TRANSL & Eres & Eip & Esp & Eother);
  eexists; split; [by eapply WS|];
  econstructor; eauto using incl_cons_inv;
  eapply agree_set_undef_mreg; eauto;
  rewrite (ireg_of_eq _ _ EQ0), (ireg_of_eq _ _ EQ2) in *; try done;
  by rewrite Eres; inv L1; inv L2; simpl; destruct Int.eq; clarify).
Qed.

Lemma exec_mod_correct:
  forall t s f sp op args res c stkr rs v 
   (EVAL : eval_operation ge (Some sp) op rs ## args = Some v)
   (MS : match_states (Machconcr.State s f sp (Mop op args res :: c) stkr rs) t)
   (OP:  op = Omod \/ op = Omodu),
 (exists t' : state,
    weakstep tlts t TEtau t' /\
    match_states
      (Machconcr.State s f sp c stkr (Regmap.set res v (undef_op op rs)))
      t').
Proof.
  intros; inv MS; clarify.
  destruct OP as []; clarify;
   [ assert (EXEC_BODY := exec_mods_body_correct) 
   | assert (EXEC_BODY := exec_modu_body_correct)];
  find_current_instruction; destruct args; clarify; monadInv EQ0;
  apply assertion_inversion_1 in EQ1; subst; simpl in EVAL;
    inversion AG;
    assert (L1 := agree_mregs res); destruct (rs res); clarify;
    assert (L2 := agree_mregs m0); destruct (rs m0); clarify;
    clear agree_sp agree_sp_def agree_mregs;
  (exploit (exec_mk_mod_correct); eauto;
   [by intro; clarify; destruct res; clarify 
   |by intro; clarify; destruct m0; clarify|];
  intros (rs' & ofs' & WS & TRANSL & Eres & Eip & Esp & Eother);
  eexists; split; [by eapply WS|];
  econstructor; eauto using incl_cons_inv;
  eapply agree_set_undef_mreg; eauto;
  rewrite (ireg_of_eq _ _ EQ0), (ireg_of_eq _ _ EQ2) in *; try done;
  by rewrite Eres; inv L1; inv L2; simpl; destruct Int.eq; clarify).
Qed.

Lemma exec_castf_correct:
  forall t s f sp op args res c stkr rs v 
   (EVAL : eval_operation ge (Some sp) op rs ## args = Some v)
   (MS : match_states (Machconcr.State s f sp (Mop op args res :: c) stkr rs) t)
   (OP:  op = Osingleoffloat \/ op = Ointoffloat \/ op = Ofloatofint \/ op = Ofloatofintu),
 (exists t' : state,
    weakstep tlts t TEtau t' /\
    match_states
      (Machconcr.State s f sp c stkr (Regmap.set res v (undef_op op rs)))
      t').
Proof.
  intros; inversion MS; destruct OP as [|[|[]]]; clarify;
  find_current_instruction; monadInv EQ0; simpl in *; clarify;
  (eexists; split; [by reduce_weakstep Heip; rewrite dec_eq_true|]);
   try (eapply match_states_intro; eauto using incl_cons_inv;  
        [by unfold nextinstr; rewrite Heip; rgso; rgss; simpl
        |by unfold nextinstr; rewrite Heip; rgso; rgss; simpl; 
            eauto with x86gen
        |];
        unfold ireg_of,freg_of in EQ1; 
        first [rewrite <- (ireg_of_eq _ _ EQ0) | rewrite <- (freg_of_eq _ _ EQ0)];
        rewrite nextinstr_commute; [|done]; eapply agree_nextinstr;
        eapply agree_set_mreg; [eby eapply agree_exten_temps| |];
        destruct (preg_of res); clarify; intros; gs_simpl; []);
   by inv AG; specialize (agree_mregs m); destruct (rs m); clarify; inv agree_mregs; simpl.
Qed.



Lemma exec_shrximm_correct:
  forall t s f sp op args res c stkr rs v i 
   (EVAL : eval_operation ge (Some sp) op rs ## args = Some v)
   (MS : match_states (Machconcr.State s f sp (Mop op args res :: c) stkr rs) t)
   (OP:  op = Oshrximm i),
 (exists t' : state,
    weakstep tlts t TEtau t' /\
    match_states
      (Machconcr.State s f sp c stkr (Regmap.set res v (undef_op op rs)))
      t').
Proof.
  intros; inv MS; find_current_instruction. 
  unfold mk_shrximm in EQ0; monadInv EQ0.
  apply assertion_inversion_1 in EQ1; subst.
  apply assertion_inversion in EQ2.
  simpl in EVAL.
  destruct (rs res) as [|ii| |] _eqn: Eres; clarify; [].

  assert (L1 := agree_mregs _ _ _ AG res); rewrite Eres in L1;
  rewrite (ireg_of_eq _ _ EQ0) in *; inv L1.

  destruct (Int.ltu i (Int.repr 31)) as [] _eqn: Ltu31; clarify; []. 
  rewrite (Int.shrx_shr _ _ Ltu31).

  assert (Ltu32: Int.ltu i (Int.repr 32))
    by (clear -Ltu31; unfold Int.ltu in *; rewrite Int.unsigned_repr in *; try done;
        destruct zlt; try done; destruct zlt; try done; omegaContradiction).

  destruct (Int.lt ii Int.zero) as [] _eqn: LTzero.

  Case "ii < 0".
  eexists; split.
    reduce_internal Heip steptau_weakstep; [by des_teed|unfold_flags; adjust_nextinstr].
    reduce_internal Heip steptau_weakstep; [by des_teed|adjust_nextinstr].
    reduce_internal Heip steptau_weakstep; [|adjust_nextinstr].
    - gs_simpl_safe; rgss; gs_simpl_safe; rgss; gs_simpl_safe. 
      rewrite <- H1; simpl (Val.and (Vint ii) (Vint ii)); rewrite Int.and_idem; unfold word_msb.
      replace ((vi_eq (Val.of_bool (int_msb ii)) Vfalse)) with b3_false by
        (by clear -LTzero; rewrite <- (Int.sub_zero_r ii);
             replace Vfalse with (word_signed_overflow_sub ii Int.zero);
             [rewrite cmp_lt, LTzero | unfold word_signed_overflow_sub; 
                           rewrite Int.sub_zero_r, xorb_nilpotent, andbF]).
      by simpl; des_teed.
    reduce_internal Heip steptau_weakstep; [by des_teed|].
    unfold write_result_erase_flags; unfold_flags.
    eapply step_weakstep; simpl; unfold x86_step, xstep_fn.
    rewrite exec_pexstorei_split; [|by clear -EQ0; intro; clarify; destruct res].
    by simpl; des_teed.
  gs_simpl; rewrite !nextinstr_commute; try done; unfold nextinstr; gs_simpl.
  rewrite (Int.add_commut Int.zero), Int.add_zero.
  eapply match_states_intro; eauto using incl_cons_inv.
  - by rgss; rewrite Heip, !val_incr_pointer. 
  - by rgss; rewrite Heip, !val_incr_pointer; eauto 10 with x86gen.
  eapply agree_set_undef_mreg; eauto with x86gen; rewrite (ireg_of_eq _ _ EQ0).
  - by gs_simpl; simpl; rewrite Ltu32.
  by intros; repeat (rgso; []).

  Case "ii >= 0".
  eexists; split.
    reduce_internal Heip steptau_weakstep; [by des_teed|unfold_flags; adjust_nextinstr].
    reduce_internal Heip steptau_weakstep; [by des_teed|adjust_nextinstr].
    reduce_internal Heip steptau_weakstep; [|adjust_nextinstr].
    - gs_simpl_safe; rgss; gs_simpl_safe; rgss; gs_simpl_safe. 
      rewrite <- H1; simpl (Val.and (Vint ii) (Vint ii)); rewrite Int.and_idem; unfold word_msb.
      replace ((vi_eq (Val.of_bool (int_msb ii)) Vfalse)) with b3_true by
        (by clear -LTzero; rewrite <- (Int.sub_zero_r ii);
             replace Vfalse with (word_signed_overflow_sub ii Int.zero);
             [rewrite cmp_lt, LTzero | unfold word_signed_overflow_sub; 
                           rewrite Int.sub_zero_r, xorb_nilpotent, andbF]).
      by simpl; des_teed.
    reduce_internal Heip steptau_weakstep; [by des_teed|].
    unfold write_result_erase_flags; unfold_flags.
    eapply step_weakstep; simpl; unfold x86_step, xstep_fn.
    rewrite exec_pexstorei_split; [|by clear -EQ0; intro; clarify; destruct res].
    by simpl; des_teed.
  gs_simpl; rewrite !nextinstr_commute; try done; unfold nextinstr; gs_simpl.
  rewrite (Int.add_commut Int.zero), Int.add_zero.
  eapply match_states_intro; eauto using incl_cons_inv.
  - by rgss; rewrite Heip, !val_incr_pointer. 
  - by rgss; rewrite Heip, !val_incr_pointer; eauto 10 with x86gen.
  eapply agree_set_undef_mreg; eauto with x86gen; rewrite (ireg_of_eq _ _ EQ0).
  - destruct (ireg_eq x1 ECX); clarify; gs_simpl.
    by rewrite <- H1; simpl; rewrite Ltu32.
  by intros; repeat (rgso; []).
Qed.

Tactic Notation "exec_op_cases" tactic(first) tactic(c) :=
    first; [
      c "exec_Omove" |
      c "exec_Ointconst" |
      c "exec_Ofloatconst" |
      c "exec_Ocast8signed" |
      c "exec_Ocast8unsigned" |
      c "exec_Ocast16signed" |
      c "exec_Ocast16unsigned" |
      c "exec_Oneg" |
      c "exec_Osub" |
      c "exec_Omul" |
      c "exec_Omulimm" |
      c "exec_Odiv" |
      c "exec_Odivu" |
      c "exec_Omod" |
      c "exec_Omodu" |
      c "exec_Oand" |
      c "exec_Oandimm" |
      c "exec_Oor" |
      c "exec_Oorimm" |
      c "exec_Oxor" |
      c "exec_Oxorimm" |
      c "exec_Oshl" |
      c "exec_Oshlimm" |
      c "exec_Oshr" |
      c "exec_Oshrimm" |
      c "exec_Oshrximm" |
      c "exec_Oshru" |
      c "exec_Oshruimm" |
      c "exec_Ororimm" |
      c "exec_Olea" |
      c "exec_Onegf" |
      c "exec_Oaddf" |
      c "exec_Osubf" |
      c "exec_Omulf" |
      c "exec_Odivf" |
      c "exec_Osingleoffloat" |
      c "exec_Ointoffloat" |
      c "exec_Ofloatofint" |
      c "exec_Ointuoffloat" |
      c "exec_Ofloatofintu" |
      c "exec_Ocmp"].


(** All the operations together *)

Lemma exec_Mop_correct:
  forall t s f sp op args res c stkr rs v 
   ( EVAL : eval_operation ge (Some sp) op rs ## args = Some v)
   (MS : match_states (Machconcr.State s f sp (Mop op args res :: c) stkr rs) t),
 (exists t' : state,
    weakstep tlts t TEtau t' /\
    match_states
      (Machconcr.State s f sp c stkr (Regmap.set res v (undef_op op rs)))
      t').
Proof.
  intros; (exec_op_cases (destruct op) Case).

Case "exec_Omove".
  inv MS; find_current_instruction.
  unfold mk_mov in EQ0. 
  destruct (preg_of res) as []  _eqn:Hres; destruct (preg_of m) as [] _eqn:Hm; inv EQ0.
  (* I32 *) 
  eexists; split.
  reduce_weakstep Heip. des_teed.
  eapply match_states_intro; eauto.
  eapply incl_cons_inv; eauto.
  unfold nextinstr; rewrite Heip; simpl; rgso; rgss; reflexivity.
  unfold nextinstr; rewrite Heip; simpl; rgso; rgss.
  eapply transl_code_at_pc_intro; eauto. eapply code_tail_next_int; eauto. 
  eapply functions_transl_no_overflow; eauto.
  unfold undef_op. rewrite nextinstr_inv; auto with x86gen. 
  eapply agree_set_mreg; eauto. rewrite Hres.
  rgss. simpl in EVAL. clarify. 
  rewrite <- Hm. eapply agree_mregs; eauto.
  intros. rewrite Hres in H0. rewrite Pregmap.gso;[ apply nextinstr_inv |]; auto with x86gen. 
  (* float case *)
  eexists; split.
  reduce_weakstep Heip. des_teed.
  eapply match_states_intro; eauto.
  eapply incl_cons_inv; eauto.
  unfold nextinstr; rewrite Heip; simpl; rgso; rgss; reflexivity.
  unfold nextinstr; rewrite Heip; simpl; rgso; rgss.
  eapply transl_code_at_pc_intro; eauto. eapply code_tail_next_int; eauto. 
  eapply functions_transl_no_overflow; eauto.
  unfold undef_op. rewrite nextinstr_inv; auto with x86gen. 
  eapply agree_set_mreg; eauto. rewrite Hres.
  rgss. simpl in EVAL. clarify. 
  rewrite <- Hm. eapply agree_mregs; eauto.
  intros. rewrite Hres in H0. rewrite Pregmap.gso;[ apply nextinstr_inv |]; auto with x86gen. 
  (* fp_stack *) 
  eexists; split.
  reduce_weakstep Heip; des_teed.
  eapply match_states_intro; eauto using incl_cons_inv.
  unfold nextinstr; rgso; rgss; rewrite Heip; simpl; reflexivity.
  unfold nextinstr; rgso; rgss; rewrite Heip; simpl.  
  eauto using transl_code_at_pc_intro, code_tail_next_int, functions_transl_no_overflow.
  unfold undef_op. inv EVAL. 
  eapply agree_set_mreg; eauto. 
  rewrite Hres. rgss. rewrite <- Hm. eapply agree_mregs; eauto. 
  intros. rewrite Hres in H0. rgso; apply nextinstr_inv; auto with x86gen.

  eexists; split.
  reduce_weakstep Heip; des_teed.
  eapply match_states_intro; eauto using incl_cons_inv.
  unfold nextinstr; rgso; rgss; rewrite Heip; simpl; reflexivity.
  unfold nextinstr; rgso; rgss; rewrite Heip; simpl.  
  eauto using transl_code_at_pc_intro, code_tail_next_int, functions_transl_no_overflow.
  unfold undef_op. inv EVAL. 
  eapply agree_set_mreg; eauto. 
  rewrite Hres. rgss. rewrite <- Hm. eapply agree_mregs; eauto. 
  intros. rewrite Hres in H0. rgso; apply nextinstr_inv; auto with x86gen.

Case "exec_Ointconst".
  inv MS; find_current_instruction.
  eexists; split.
  reduce_weakstep Heip; des_teed.
  simpl in EVAL; clarify.
 (* matchstates *)
  eapply match_states_intro; eauto.
  eapply incl_cons_inv; eauto.
  unfold nextinstr; rgso; rgss; rewrite Heip; simpl; reflexivity.
  unfold nextinstr; rgso; rgss; rewrite Heip; simpl. 
  eapply transl_code_at_pc_intro; eauto.
  eapply code_tail_next_int; eauto.
  eapply functions_transl_no_overflow; eauto. 

  unfold undef_op.
  rewrite <- (ireg_of_eq res x0 EQ1).
  eapply agree_set_undef_mreg. eauto.
  rgss; auto.
  intros. rgso. rewrite nextinstr_inv; auto. destruct r'; try destruct i0; inv H; auto with x86gen.

Case "exec_Ofloatconst".
  inv MS; find_current_instruction. 
  eexists; split.
  reduce_weakstep Heip. des_teed.
  simpl in EVAL; clarify.
  eapply match_states_intro; eauto.
  eapply incl_cons_inv; eauto.
  unfold nextinstr; rgso; rgss; rewrite Heip; simpl; reflexivity.
  unfold nextinstr; rgso; rgss; rewrite Heip; simpl. 
  eapply transl_code_at_pc_intro; eauto.
  eapply code_tail_next_int; eauto.
  eapply functions_transl_no_overflow; eauto. 
  unfold undef_op. rewrite <- (freg_of_eq res x0 EQ1).
  eapply agree_set_mreg. eapply agree_exten_temps. eauto.
  done. 
  rgss; done. 
  intros; rgso; rewrite nextinstr_inv; auto. destruct r'; try destruct i0; inv H; auto with x86gen. 

Case "exec_Ocast8signed".    by eapply exec_cast_correct; eauto; vauto.
Case "exec_Ocast8unsigned".  by eapply exec_cast_correct; eauto; vauto.
Case "exec_Ocast16signed".   by eapply exec_cast_correct; eauto; vauto.
Case "exec_Ocast16unsigned". by eapply exec_cast_correct; eauto; vauto.

Case "exec_Oneg".
  inv MS; find_current_instruction.
  monadInv EQ0. eexists; split.  
  reduce_internal Heip steptau_weakstep. des_teed.
  apply step_weakstep; simpl; unfold x86_step, xstep_fn.
  unfold write_int_result.
  rewrite exec_pexstorei_split; [|by destruct res; inv EQ0].
  simpl; des_teed; reflexivity. 

  eapply match_states_intro; eauto using incl_cons_inv. 
  rgso. rewrite !write_eflag_EIP. 
  unfold nextinstr; rewrite Heip; simpl; rgss; reflexivity.

  rgso. rewrite !write_eflag_EIP.
  unfold nextinstr; rgss; rewrite Heip; simpl. 
  eauto using transl_code_at_pc_intro, code_tail_next_int, functions_transl_no_overflow.
 
  assert (m = res) by (eapply assertion_inversion_1; apply EQ1). subst m. clear EQ1.
  
  inv EVAL. destruct (rs res) as [] _eqn:Hres; inv H0.
  generalize (ireg_val _ _ _ _ _ AG EQ0); intro Hres'; rewrite Hres in Hres'; inv Hres'. 
  rewrite <- (ireg_of_eq res x1);[|done]. unfold undef_op.

  eapply agree_set_mreg. eapply agree_exten_temps. 
  eapply agree_eflag; eapply agree_eflag; eapply agree_eflag; 
  eapply agree_eflag; eapply agree_eflag; eapply agree_eflag; eapply agree_nextinstr; eauto.

  vauto. 

  rgss; rewrite <- Int.sub_zero_l; auto. 
  by intros; rgso.  

Case "exec_Osub".
  inv MS; find_current_instruction; destruct args; monadInv EQ0.
  destruct (sub_with_borrow_out (rs0 x1) (rs0 x2)) as [[[s1 s2] s3] s4] _eqn:Hsbo.
  eexists; split.  
  reduce_internal Heip steptau_weakstep. des_teed. 
  apply step_weakstep; simpl; unfold x86_step, xstep_fn.  
  unfold write_int_result. rewrite Hsbo.  
  rewrite exec_pexstorei_split; [|by destruct res; inv EQ0].
  simpl. des_teed. 
  eapply match_states_intro; eauto using incl_cons_inv.
  by rgso; rewrite !write_eflag_EIP;
     unfold nextinstr; rewrite Heip; simpl; rgss.
  rgso; rewrite !write_eflag_EIP;
    unfold nextinstr; rgss; rewrite Heip; simpl. 
    eauto using transl_code_at_pc_intro, code_tail_next_int, functions_transl_no_overflow. 
  (* step 0: invert the assertion and conclude m = res *)
  assert (m = res) by (eapply assertion_inversion_1; apply EQ1); 
    subst m; clear EQ1; clear x0.
  inv EVAL; unfold sub_with_borrow_out in Hsbo.
  (* step 1: prove relationship between x1-res and x2-m0 *)
  inversion AG.
    generalize (agree_mregs res); intro Hres; rewrite (ireg_of_eq res x1) in Hres; [|done].
    generalize (agree_mregs m0); intro Hm0; rewrite (ireg_of_eq m0 x2) in Hm0; [|done].
    clear agree_sp; clear agree_sp_def; clear agree_mregs.
  rewrite <- (ireg_of_eq res x1);[|done]. unfold undef_op.
  (* step 2: destruct the registers *)
  destruct (rs res); destruct (rs m0); inv H0;
  destruct (rs0 x1); destruct (rs0 x2); inv Hsbo;
  try inv Hres; try inv Hm0;
  try (destruct p0; inv H1; inv H0);
  try (destruct p1; destruct p2; unfold zeq in H0; destruct Z_eq_dec; inv H1; inv H0);
  try (
    eapply agree_set_mreg; 
    try (eapply agree_exten_temps; [|reflexivity]; 
         eapply agree_eflag; eapply agree_eflag; eapply agree_eflag; 
         eapply agree_eflag; eapply agree_eflag; eapply agree_eflag; 
         eapply agree_nextinstr; eauto);
    [ rgss; auto | intros; rgso; auto]).

Case "exec_Omul".
  inv MS; find_current_instruction. destruct args; monadInv EQ0.
  eexists; split.  
  reduce_internal Heip steptau_weakstep. des_teed. 
  apply step_weakstep; simpl; unfold x86_step, xstep_fn. 
  unfold write_result_erase_flags, write_logical_eflags. 
  rewrite exec_pexstorei_split; [|by destruct res; inv EQ0].
  simpl. des_teed. 
  eapply match_states_intro; eauto using incl_cons_inv. 
  by unfold erase_eflags; rgso; rewrite !write_eflag_EIP;
    unfold nextinstr; rewrite Heip; simpl; rgss.
  unfold erase_eflags; rgso; rewrite !write_eflag_EIP;
    unfold nextinstr; rewrite Heip; rgss; simpl. 
    eauto using transl_code_at_pc_intro, code_tail_next_int, functions_transl_no_overflow.
  (* step 0: invert the assertion and conclude m = res *)
  assert (m = res) by (eapply assertion_inversion_1; apply EQ1); subst m; clear EQ1; clear x0.
  inv EVAL. 
  (* step 1: prove relationship between x1-res and x2-m0 *)
  inversion AG.
    generalize (agree_mregs res); intro Hres; rewrite (ireg_of_eq res x1) in Hres; [|done].
    generalize (agree_mregs m0); intro Hm0; rewrite (ireg_of_eq m0 x2) in Hm0; [|done].
    clear agree_sp; clear agree_sp_def; clear agree_mregs.
  rewrite <- (ireg_of_eq res x1);[|done]. unfold undef_op.
  (* step 2: destruct the registers *)
  destruct (rs res); destruct (rs m0); inv H0. unfold erase_eflags. 
  eapply agree_set_mreg. eapply agree_exten_temps; [|reflexivity].
  eapply agree_eflag; eapply agree_eflag; eapply agree_eflag; eapply agree_eflag;
  eapply agree_eflag; eapply agree_eflag; eapply agree_nextinstr; eauto.
  rgss; auto.
  rewrite (ireg_of_eq res x1); [by inv Hres; inv Hm0 | done].
  intros; rgso; auto. 

Case "exec_Omulimm".
  inv MS; find_current_instruction. monadInv EQ0.
  eexists; split.  
  reduce_internal Heip steptau_weakstep. des_teed. 
  apply step_weakstep; simpl; unfold x86_step, xstep_fn. 
  unfold write_result_erase_flags, write_logical_eflags. 
  rewrite exec_pexstorei_split; [|by destruct res; inv EQ0].
  simpl. des_teed. 
  eapply match_states_intro; eauto using incl_cons_inv.
  by unfold erase_eflags; rgso; rewrite !write_eflag_EIP;
    unfold nextinstr; rewrite Heip; simpl; rgss.
  unfold erase_eflags; rgso; rewrite !write_eflag_EIP;
    unfold nextinstr; rewrite Heip; rgss; simpl. 
    eauto using transl_code_at_pc_intro, code_tail_next_int, functions_transl_no_overflow.
  (* step 0: invert the assertion and conclude m = res *)
  assert (m = res) by (eapply assertion_inversion_1; apply EQ1); subst m; clear EQ1; clear x0.
  inv EVAL. 
  (* step 1: prove relationship between x1-res *)
  inversion AG.
    generalize (agree_mregs res); intro Hres; rewrite (ireg_of_eq res x1) in Hres; [|done].
    clear agree_sp; clear agree_sp_def; clear agree_mregs.
  rewrite <- (ireg_of_eq res x1);[|done]. unfold undef_op.
  (* step 2: destruct the registers *)
  destruct (rs res); inv H0. unfold erase_eflags.
  eapply agree_set_mreg. eapply agree_exten_temps; [|reflexivity].
  eapply agree_eflag; eapply agree_eflag; eapply agree_eflag; eapply agree_eflag; eapply agree_eflag; eapply agree_eflag. eapply agree_nextinstr; eauto.
  rgss; auto.
  rewrite (ireg_of_eq res x1); [by inv Hres | done].
  intros; rgso; auto. 

Case "exec_Odiv".   by eapply exec_div_correct; eauto; vauto.
Case "exec_Odivu".  by eapply exec_div_correct; eauto; vauto.
Case "exec_Omod".   by eapply exec_mod_correct; eauto; vauto.
Case "exec_Omodu".  by eapply exec_mod_correct; eauto; vauto.

Case "exec_Oand".    by eapply exec_boolop_correct; eauto; vauto.
Case "exec_Oandimm". by eapply exec_boolopimm_correct; eauto; vauto.
Case "exec_Oor".     by eapply exec_boolop_correct; eauto; vauto.
Case "exec_Oorimm".  by eapply exec_boolopimm_correct; eauto; vauto.
Case "exec_Oxor".    by eapply exec_boolop_correct; eauto; vauto.
Case "exec_Oxorimm". by eapply exec_boolopimm_correct; eauto; vauto.

Case "exec_Oshl".     by eapply exec_shiftop_correct; eauto; vauto.
Case "exec_Oshlimm".  by eapply exec_shiftopimm_correct; eauto; vauto.
Case "exec_Oshr".     by eapply exec_shiftop_correct; eauto; vauto.
Case "exec_Oshrimm".  by eapply exec_shiftopimm_correct; eauto; vauto.
Case "exec_Oshrximm". by eapply exec_shrximm_correct; eauto; vauto.
Case "exec_Oshru".    by eapply exec_shiftop_correct; eauto; vauto.
Case "exec_Oshruimm". by eapply exec_shiftopimm_correct; eauto; vauto.
Case "exec_Ororimm".  by eapply exec_shiftopimm_correct; eauto; vauto.

Case "exec_Olea". 
  inv MS; destruct (rs0 EIP) as [] _eqn:Heip; inv AT; clarify'; monadInv HTF0. 
  pose proof (transl_addressing_mode_correct _ _ _ _ _ _ _ AG EQ1 EVAL); subst.
  (eexists; split; [by reduce_weakstep Heip; rewrite dec_eq_true|]);
   try (eapply match_states_intro; eauto using incl_cons_inv;  
        [by unfold nextinstr; rewrite Heip; rgso; rgss; simpl
        |by unfold nextinstr; rewrite Heip; rgso; rgss; simpl; 
            eauto with x86gen
        |]).
   rewrite nextinstr_commute, <- (ireg_of_eq res x1 EQ0); [|done]; 
   eapply agree_nextinstr, agree_set_mreg; [eby eapply agree_exten_temps | |]; 
   intros; gs_simpl.

Case "exec_Onegf".  
  inv MS; find_current_instruction. monadInv EQ0.
  eexists; split.
  reduce_weakstep Heip. des_teed. 
  eapply match_states_intro; eauto using incl_cons_inv.
  unfold nextinstr; gs_simpl_safe; rgss; rewrite Heip; simpl; reflexivity.
  unfold nextinstr; gs_simpl_safe; rgss; rewrite Heip; simpl; eauto with x86gen.
  eapply agree_set_undef_mreg; eauto.
  rewrite (freg_of_eq _ _ EQ0); rgss; simpl in EVAL; destruct (rs m) as [] _eqn:Hm; inv EVAL;
    unfold Val.negf; apply assertion_inversion_1 in EQ1; subst;
    exploit freg_val; eauto; intro Hx1; instantiate; rewrite Hm in Hx1; destruct (rs0 x1); inv Hx1; auto.
  intros; rewrite (freg_of_eq _ _ EQ0) in H0; rgso; apply nextinstr_inv; auto with x86gen.

Case "exec_Oaddf". by eapply exec_binopf_correct; eauto; vauto.
Case "exec_Osubf". by eapply exec_binopf_correct; eauto; vauto.
Case "exec_Omulf". by eapply exec_binopf_correct; eauto; vauto.
Case "exec_Odivf". by eapply exec_binopf_correct; eauto; vauto.

Case "exec_Osingleoffloat". by eapply exec_castf_correct; eauto; vauto.
Case "exec_Ointoffloat".    by eapply exec_castf_correct; eauto; vauto.
Case "exec_Ofloatofint".    by eapply exec_castf_correct; eauto; vauto.

Case "exec_Ointuoffloat". 
  inv MS; find_current_instruction. monadInv EQ0.
  eexists; split.
  reduce_weakstep Heip. des_teed. 
  eapply match_states_intro; eauto using incl_cons_inv.
  unfold nextinstr; gs_simpl_safe; rgss; rewrite Heip; simpl; reflexivity.
  unfold nextinstr; gs_simpl_safe; rgss; rewrite Heip; simpl; eauto with x86gen.
  eapply agree_set_undef_mreg; eauto.
  rewrite (ireg_of_eq _ _ EQ1); gs_simpl_safe; rgss; simpl in EVAL;
    destruct (rs m) as [] _eqn:Hm; inv EVAL;
    unfold Val.intuoffloat; exploit freg_val; eauto; intro Hx1; instantiate;
    rewrite Hm in Hx1; destruct (rs0 x1); inv Hx1; auto.
  by intros; rewrite (ireg_of_eq _ _ EQ1) in H0; unfold nextinstr; repeat rgso.

Case "exec_Ofloatofintu".   by eapply exec_castf_correct; eauto; vauto.

Case "exec_Ocmp".
  simpl in EVAL. 
  destruct (eval_condition c0 rs ## args) as [b|] _eqn: EVAL'; clarify.
  inversion MS; subst.
  exploit transl_cmp_correct; try eassumption; clear MS;
    intros (rs' & STEP & MD & Heip & DIFF).
  rewrite ErsEIP in *.
  inv AT.
  monadInv HTF0.

  assert (X : exists icmp, icmp :: Xset (testcond_for_cond c0) x0 :: x = tc).
  by revert EQ2; clear;
     destruct c0; simpl; repeat (destruct args; try done); intro X; monadInv X;
     try destruct Int.eq_dec; eexists.
  destruct X as [icmp X]; subst tc.
  clear EQ2.
  eexists; split.
    eapply steptau_weakstep; [eapply STEP|].
    adjust_nextinstr. 
    by reduce_weakstep Heip; des_teed.
  eapply match_states_intro; eauto using incl_cons_inv.
  - by gs_simpl_safe; rewrite nextinstr1, Heip; simpl.
  - by gs_simpl_safe; rewrite nextinstr1, Heip; simpl; eauto with x86gen.
  gs_simpl.
  eapply agree_set_mreg.
  - eapply agree_nextinstr; 
    eapply agree_exten_temps with (rs' := rs' # ECX <- Vundef # EDX <- Vundef);
    eauto with x86gen.
    by intros; rewrite !Pregmap.gso; auto; intro; clarify.
  - rewrite (ireg_of_eq _ _ EQ1); rgss.
    unfold b3_moredef in *; destruct read_cond; clarify.
       by rewrite MD in *; clarify.
    by rewrite (negPf MD) in *; clarify.
  intros; rewrite (ireg_of_eq _ _ EQ1) in *.
  by rgso; rewrite <- nextinstr_commute, nextinstr_commute.
Qed.

(** All together *)

Lemma transf_step_correct:
   forward_sim_with_undefs2 lts tlts match_states (fun _ _ : St lts => False).
Proof.
  intros s t l s' STEP MS; simpl in *.
  (mc_step_cases (destruct STEP) Case). (* inversion MS; subst; right. *)

Case "exec_Initalloc". 
  inversion MS; subst; right.
  destruct (init_fun_funsig_eq _ _ FF) as [f [Hf1 Hf2]].
  eexists. split. 
  eapply step_weakstep. simpl. 
  unfold x86_step, xstep_fn, exec_pex_instr. 
  rewrite Hf1. rewrite <- Hf2.
  destruct zle; [|omegaContradiction]; 
    destruct Int.eq_dec; [|done]; destruct mobject_kind_eq_dec; done. 
  econstructor. done.
  econstructor.
  by rgss. done.
  intro; rewrite Regmap.gi; constructor. 

Case "exec_Initalloc_oom". 
  inv MS; right.
  exists (Initstate pfn args'). split; [|vauto].
  destruct (init_fun_funsig_eq _ _ FF) as [f [Hf1 Hf2]].
  apply step_weakstep; simpl; unfold x86_step, xstep_fn, exec_pex_instr. rewrite Hf1. 
  rewrite <- Hf2. 
  destruct zle; [vauto|]. destruct thread_event_eq_dec; vauto.

Case "exec_Initargmem". 
  inv MS; right. inv LD.
  exists (Initargsstate pfn vl2 locs stkr rs0).
  exists v2.
  split; auto.
  split.
  apply step_weakstep. simpl. unfold x86_step, xstep_fn. simpl. destruct pfn. 
  rewrite (agree_sp _ _ _ AG). des_teed.
  apply match_initargsstate; auto.
 
Case "exec_Initargreg". 
  inv MS; right; right. inv LD.
  exists (Initargsstate pfn vl2 locs stkr (rs0#(preg_of r)<-v2)). 
  split.
  apply step_weakstep; simpl; unfold x86_step, xstep_fn; simpl. destruct pfn.
  des_teed.  
  apply match_initargsstate. done.
  eapply agree_set_mreg; eauto. rgss; auto.
  by intros; rgso.
 
Case "exec_Initretaddr". 
  inv MS; right.
  destruct pfn.
  eexists; eexists. inv LD.
  split. apply Val.lessdef_refl.
  split. 
  apply step_weakstep; simpl; unfold x86_step, xstep_fn; simpl. rewrite (agree_sp _ _ _ AG). des_teed.
  subst. eapply match_states_call; eauto. apply match_stack_nil.
  by apply agree_set_other. by rewrite Pregmap.gss.

Case "exec_Mlabel".
  eby (right; right; eapply exec_Mlabel_correct).

Case "exec_Mgetstack".
  eby (right; eapply exec_Mgetstack_correct).

Case "exec_Msetstack".
  eby (right; eapply exec_Msetstack_correct).

Case "exec_Mgetparam".
 eby (right; eapply exec_Mgetparam_correct).

Case "exec_Mop".
  eby (right; right; eapply exec_Mop_correct).

Case "exec_Mload".
  eby (right; eapply exec_Mload_correct).

Case "exec_Mstore".
  eby (right; eapply exec_Mstore_correct).
  
Case "exec_Mcall".
  eby (subst; right; eapply exec_Mcall_correct).
   
Case "exec_Mcall_oom".
  right. inv MS. exists Exitstate. split; [|vauto].
  eapply step_weakstep. unfold_step. 
  rewrite ErsEIP; rewrite Int.repr_unsigned. 
  rewrite ErsEIP in AT; inv AT.
  rewrite (functions_transl _ _ _ FIND HTF). 
  monadInv HTF0.
  destruct ros as [reg | symb]; monadInv EQ0; rewrite (find_instr_tail _ _ _ _ GOFS); simpl.
  (* xcallreg todo *)  
  inv FF. 
  exploit ireg_val; eauto. intro Hld. 
  destruct (rs reg); try destruct p; inv Hld; inv H0. 
  rewrite (agree_sp _ _ _ AG). simpl. destruct range_inside_dec. 
  unfold Stacklayout.fe_retaddrsize in RI. vauto.
  by destruct thread_event_eq_dec.
  (* normal call *)
  rewrite (agree_sp _ _ _ AG). simpl. destruct range_inside_dec. 
  unfold Stacklayout.fe_retaddrsize in RI. vauto.
  by destruct thread_event_eq_dec.
  
Case "exec_Mgoto".
  inv MS; right; right.
  clarify'. 
  inv AT. monadInv HTF0.  
  generalize (transl_find_label lbl _ _ _ HTF); rewrite FL; intros [tc [Htc1 Htc2]].
  generalize (label_pos_code_tail lbl tf 0 _ Htc1); intros [pos [Hpos1 [Hpos2 Hpos3]]].
  eexists; split. 
  eapply step_weakstep.
  simpl; unfold x86_step, xstep_fn, exec_pex_instr; rewrite ErsEIP. 
  rewrite Int.repr_unsigned.
  generalize (functions_transl _ (sig,tf) _ FIND); intro Htge.
  rewrite Htge; auto.
  rewrite ErsEIP in H0. inv H0. 
  rewrite (find_instr_tail _ _ _ _ GOFS).
  simpl. unfold goto_label. rewrite ErsEIP.
  rewrite Int.repr_unsigned. rewrite (Htge HTF).
  rewrite Hpos1.
  destruct thread_event_eq_dec; [|done]. reflexivity.

  eapply match_states_intro; eauto.
  eapply find_label_incl; eauto.
  rewrite Pregmap.gss; reflexivity.
  rewrite Pregmap.gss. eapply transl_code_at_pc_intro; eauto. 
    rewrite Int.repr_unsigned; eauto. 
    simpl. 
    generalize (functions_transl_no_overflow _ _ _ _ GFUN HTF); intro Hpos4.
  assert (pos mod Int.modulus = pos). unfold Int.max_unsigned in Hpos4.
    assert (pos < Int.modulus). omega. destruct Hpos3. apply Zmod_small; omega.
  rewrite H. assert (pos - 0 = pos). omega. by rewrite H1 in Hpos2.
  apply agree_set_other; auto.

Case "exec_Mcond_true".
  eby (right; right; eapply exec_Mcond_true_correct). 

Case "exec_Mcond_false".
  eby (right; right; eapply exec_Mcond_false_correct). 

Case "exec_Mreturn".
  eby (right; right; eapply exec_Mreturn_correct). 

Case "exec_Mthreadcreate".
  right. inv MS.
  find_current_instruction. inversion H. monadInv HTF0.  
  eexists. exists  [inl val ((sp + Int.repr 4)%pointer, Mint32)].  
  split. vauto.
  split. 
  reduce_weakstep Heip.
  rewrite (agree_sp _ _ _ AG). des_teed.
  eapply match_states_intro; eauto.
  eapply incl_cons_inv; eauto.
  unfold nextinstr; rewrite Heip; rgss; simpl; reflexivity.
  unfold nextinstr; rewrite Heip; rgss; simpl. 
  eapply transl_code_at_pc_intro; eauto. 
  eapply code_tail_next_int; eauto.
  eapply functions_transl_no_overflow; eauto.
  apply agree_nextinstr; auto.

Case "exec_Matomic". 
  right; inv MS; destruct lab; inv ASME.
  (* fence *)
(*  find_current_instruction. inv H1.
  eexists; split.
  reduce_weakstep Heip. des_teed.
  eapply match_states_intro; eauto using incl_cons_inv.
  unfold nextinstr; rewrite Heip; rgss; simpl; reflexivity.
  unfold nextinstr; rewrite Heip; rgss; simpl. 
  eauto using transl_code_at_pc_intro, code_tail_next_int, functions_transl_no_overflow.
  apply (agree_set_mreg (undef_temps rs) (Vptr sp) (nextinstr rs0) res Vundef (nextinstr rs0)). eapply agree_exten_temps. eauto.
  intros; apply nextinstr_inv; destruct r; try destruct i; inv H; done.
  auto.
  auto. *)
  (* cas *)
  assert (Haddzero: forall p0, (p0 + Int.zero)%pointer = p0)
    by (destruct p0; simpl; rewrite Int.add_zero; auto).
  assert (HeraseflagsEIP: forall rs1, (erase_eflags rs1) EIP = rs1 EIP) 
    by (intro; unfold_flags; repeat rgso; auto).
  find_current_instruction. 
  destruct args; inv EQ0; destruct args. monadInv H0. 
  generalize (ireg_val _ _ _ _ _ AG EQ2); intro Hldx1.
  generalize (ireg_val _ _ _ _ _ AG EQ1); intro Hldx2.
  generalize (ireg_val _ _ _ _ _ AG EQ3); intro Hldx3.
  destruct (ireg_eq x0 EAX); monadInv EQ7.
  (* res = EAX *)
  destruct (ireg_eq EAX x2).
  (* res = EAX, x2 = EAX *)
  inv H1.
  destruct (Val.eq_dec v0 (rs0 EAX)) as [] _eqn:Hv0; clear Hv0.
    (* v0 = rs0 EAX *) 
  eexists; split.  
  reduce_weakstep Heip. 
  rewrite <- EQ1 in EQ0; inv EQ0.
  rewrite <- H0 in Hldx1. generalize Hldx1; intro H; inv H. simpl.
  rewrite Haddzero; rewrite Haddzero.
  destruct Ptr.eq_dec; [|done].
  (* destruct memory_chunk_eq_dec; [|done]. *)
  destruct (rs m1); clarify; destruct (rs m0); clarify;
  inversion Hldx2; inversion Hldx3; clarify;
  destruct rmw_instr_dec; try done; simpl; (destruct Val.eq_dec; [|done]); reflexivity. 
  intros. econstructor; split. econstructor; auto. 
  simpl. rewrite <- H0. eapply atomic_statement_mem_event_cas; auto. 
  eby eapply Val.has_type_lessdef. 
  eapply match_states_intro; eauto using incl_cons_inv.
  unfold erase_eflags, nextinstr, write_eflag. gs_simpl_safe. rgss. rewrite Heip; simpl; reflexivity. 
  unfold erase_eflags, nextinstr, write_eflag; gs_simpl_safe; rgss; rewrite Heip; simpl.
  eapply transl_code_at_pc_intro; eauto using code_tail_next_int, functions_transl_no_overflow.  
  eapply agree_set_undef_mreg; eauto.
  rewrite e in H. rewrite (ireg_of_eq _ _ EQ0).  
  unfold erase_eflags, nextinstr, write_eflag; gs_simpl_safe.
  by intros; unfold erase_eflags, nextinstr, write_eflag; repeat rgso. 
    (* v0 /= rs0 EAX *) 
  eexists; split.  
  reduce_weakstep Heip. 
  rewrite <- EQ1 in EQ0; inv EQ0.
  rewrite <- H0 in Hldx1. generalize Hldx1; intro H; inv H. simpl.
  rewrite Haddzero; rewrite Haddzero.
  destruct Ptr.eq_dec; [|done].
  (* destruct memory_chunk_eq_dec; [|done]. *)
  destruct (rs m1); clarify; destruct (rs m0); clarify;
  inversion Hldx2; inversion Hldx3; clarify;
  destruct rmw_instr_dec; try (rewrite HTv;
  destruct Val.eq_dec; [ by subst; rewrite <- H3 in n; elim n |]; reflexivity).
  vauto. vauto. vauto. vauto. 
  intros. econstructor; split. econstructor; auto. 
  simpl. rewrite <- H0. eapply atomic_statement_mem_event_cas; auto. 
  eby eapply Val.has_type_lessdef. 
  eapply match_states_intro; eauto using incl_cons_inv.
  unfold erase_eflags, nextinstr, write_eflag; gs_simpl_safe; rgss; rewrite Heip; simpl; reflexivity. 
  unfold erase_eflags, nextinstr, write_eflag; gs_simpl_safe; rgss; rewrite Heip; simpl.
  eapply transl_code_at_pc_intro; eauto using code_tail_next_int, functions_transl_no_overflow.  
  eapply agree_set_undef_mreg; eauto.
  by rewrite (ireg_of_eq _ _ EQ0); unfold erase_eflags, nextinstr, write_eflag; gs_simpl_safe; rgss.
  by intros; unfold erase_eflags, nextinstr, write_eflag; repeat rgso. 
  (* res = EAX, x2 /= EAX *)
  inv H1.
  apply assertion_inversion_2 in EQ4.
  apply assertion_inversion_2 in EQ5.
  destruct (Val.eq_dec v0 (rs0 x2)) as [] _eqn:Hv0; clear Hv0.
    (* v0 = rs0 EAX *)
  eexists 
    ((State
        (erase_eflags
           (nextinstr
              (rs0 # EIP <-
               (Vptr (Ptr (Int.unsigned b) (Int.add ofs Int.one)))) # EAX <-
              (rs0 x2))) # ZF <- Vtrue XPEdone stkr)); split.
  reduce_internal Heip steptau_weakstep. des_teed.
  apply step_weakstep; unfold_step. rgso. 
  unfold nextinstr; rewrite Heip; rgss; simpl.
  rewrite (functions_transl _ _ _ GFUN HTF). 
  rewrite (unsigned_mod_mod _ sig tf _ _ _ _ GOFS HTF FIND).
  exploit code_tail_next; eauto; intro GOFS1.
  rewrite (find_instr_tail _ _ _ _ GOFS1).
  simpl.
  rgso; [|intro; clarify]. rgso. rewrite <- H0 in Hldx1. inv Hldx1. 
  simpl. 
  rewrite Haddzero; rewrite Haddzero.
  destruct Ptr.eq_dec; [|done].
  (* destruct memory_chunk_eq_dec; [|done]. *)
  rgss. rgso. rgso; [|congruence]. rgso. 
  destruct (rs m1); clarify; destruct (rs m0); clarify;
  inversion Hldx2; inversion Hldx3; clarify;
  destruct rmw_instr_dec; try done; simpl; (destruct Val.eq_dec; [ | done ]); reflexivity.
  intros. 
  econstructor; split.
  econstructor; auto.  
  simpl. rewrite <- H0. eapply atomic_statement_mem_event_cas; auto. 
  eby eapply Val.has_type_lessdef. 
  eapply match_states_intro; eauto using incl_cons_inv.
  unfold erase_eflags, nextinstr, write_eflag; gs_simpl_safe; rgss; rgso; rgss;  simpl; reflexivity. 
  unfold erase_eflags, nextinstr, write_eflag; gs_simpl_safe; rgss; rgso; rgss; simpl.
  eapply transl_code_at_pc_intro; eauto using code_tail_next_int, functions_transl_no_overflow.  
  eapply agree_set_undef_mreg; eauto.
  by rewrite (ireg_of_eq _ _ EQ0); unfold erase_eflags, nextinstr, write_eflag; gs_simpl_safe; rgss; rewrite e in H.
  by intros; unfold erase_eflags, nextinstr, write_eflag; repeat rgso. 
   (* v0 /= rs0 EAX *)
  eexists 
     (State
        ((erase_eflags
            (nextinstr
               (rs0 # EIP <-
                (Vptr (Ptr (Int.unsigned b) (Int.add ofs Int.one)))) # EAX <-
               (rs0 x2))) # EAX <- v0) # ZF <- Vfalse XPEdone stkr); split.
  reduce_internal Heip steptau_weakstep. des_teed.
  apply step_weakstep; unfold_step. rgso. 
  unfold nextinstr; rewrite Heip; rgss; simpl.
  rewrite (functions_transl _ _ _ GFUN HTF). 
  rewrite (unsigned_mod_mod _ sig tf _ _ _ _ GOFS HTF FIND).
  exploit code_tail_next; eauto; intro GOFS1.
  rewrite (find_instr_tail _ _ _ _ GOFS1).
  simpl.
  rgso; [|intro; clarify]. rgso. rewrite <- H0 in Hldx1. inv Hldx1. 
  simpl. 
  rewrite Haddzero; rewrite Haddzero.
  destruct Ptr.eq_dec; [|done].
  (* destruct memory_chunk_eq_dec; [|done]. *)
  rgss. rgso. rgso; [|congruence]. rgso. 
  destruct (rs m1); clarify; destruct (rs m0); clarify;
  inversion Hldx2; inversion Hldx3; clarify;
  destruct rmw_instr_dec; try done; rewrite HTv;(
  destruct Val.eq_dec;[ congruence |]); reflexivity.
  intros. 
  econstructor; split.
  econstructor; auto.  
  simpl. rewrite <- H0. eapply atomic_statement_mem_event_cas; auto. 
  eby eapply Val.has_type_lessdef. 
  eapply match_states_intro; eauto using incl_cons_inv.
  unfold erase_eflags, nextinstr, write_eflag; gs_simpl_safe; rgss; rgso; rgss;  simpl; reflexivity. 
  unfold erase_eflags, nextinstr, write_eflag; gs_simpl_safe; rgss; rgso; rgss; simpl.
  eapply transl_code_at_pc_intro; eauto using code_tail_next_int, functions_transl_no_overflow.  
  eapply agree_set_undef_mreg; eauto.
  by rewrite (ireg_of_eq _ _ EQ0); unfold erase_eflags, nextinstr, write_eflag; gs_simpl_safe; rgss. 
  by intros; unfold erase_eflags, nextinstr, write_eflag; repeat rgso. 
  (* x0 /= EAX *)
  destruct (ireg_eq EAX x2).
  (* x0 /= EAX, EAX = x2 *)
  inv H1.
  destruct (Val.eq_dec v0 (rs0 EAX)).
    (* v0 = rs0 EAX *)
  eexists; split.
  reduce_internal Heip steptau_weakstep; [des_teed|adjust_nextinstr].
  apply weakstep_taustar with (s2 := 
      (State
        (erase_eflags
           ((rs0 # EIP <- (Val.add (rs0 EIP) Vone)) # XMM7 <- (rs0 EAX))
           # EIP <-
           (Val.add (rs0 # EIP <- (Val.add (rs0 EIP) Vone) EIP) Vone))
        # ZF <- Vtrue XPEdone stkr)). 
    reduce_weakstep Heip.
    rgso. unfold nextinstr; rgso.
    rewrite <- H0 in Hldx1. generalize Hldx1; intro H; inv H. simpl.
    rewrite Haddzero; rewrite Haddzero.
    destruct Ptr.eq_dec; [|done].
    (* destruct memory_chunk_eq_dec; [|done]. *)
    gs_simpl_safe.
    destruct (rs m1); clarify; destruct (rs m0); clarify;
    inversion Hldx2; inversion Hldx3; clarify;
    destruct rmw_instr_dec; try done; simpl; (destruct Val.eq_dec;[|congruence];
    rewrite Heip; simpl; reflexivity). 
  adjust_nextinstr.
  eapply taustar_step. unfold_step. rgso.
  rewrite HeraseflagsEIP. rgss. rewrite Heip; simpl. rgss. simpl.
  rewrite (functions_transl _ _ _ GFUN HTF).
  generalize GOFS; intro GOFStmp; simpl in GOFStmp;
  rewrite (find_instr_tail _ _ _ _ GOFStmp); clear GOFStmp. 
  simpl. des_teed.
  adjust_nextinstr.
  eapply taustar_step. unfold_step. unfold nextinstr. gs_simpl_safe. rgss.
  rgso. rewrite HeraseflagsEIP.
  rgss. simpl. rewrite (functions_transl _ _ _ GFUN HTF). simpl in GOFS.
  rewrite (find_instr_tail _ _ _ _ GOFS). simpl. des_teed. gs_simpl_safe.
  apply taustar_refl.
  intros. eexists; split.
  econstructor; auto.
  simpl. rewrite <- H0. eapply atomic_statement_mem_event_cas; auto. 
  eby eapply Val.has_type_lessdef. 
  eapply match_states_intro; eauto using incl_cons_inv.
  unfold erase_eflags, nextinstr, write_eflag. gs_simpl_safe. rgss. gs_simpl_safe. rgss. simpl. reflexivity. 
  unfold erase_eflags, nextinstr, write_eflag; gs_simpl_safe; rgss; gs_simpl_safe; rgss; simpl.  
  eapply transl_code_at_pc_intro; eauto 10 using code_tail_next_int, functions_transl_no_overflow.  
  eapply agree_set_undef_mreg; eauto.
  by rewrite (ireg_of_eq _ _ EQ0); gs_simpl_safe; rgss; unfold erase_eflags, write_eflag; gs_simpl_safe; rewrite e in H.
  intros. unfold erase_eflags, nextinstr, write_eflag; repeat rgso. auto.
    rewrite (ireg_of_eq _ _ EQ0) in H2; auto.
    (* v0 /= rs0 EAX *)
  eexists; split.
  reduce_internal Heip steptau_weakstep; [des_teed|adjust_nextinstr].
  apply weakstep_taustar with (s2 := 
    (State
        ((erase_eflags
            ((rs0 # EIP <- (Val.add (rs0 EIP) Vone)) # XMM7 <- (rs0 EAX))
            # EIP <-
            (Val.add (rs0 # EIP <- (Val.add (rs0 EIP) Vone) EIP) Vone))
         # EAX <- v0) # ZF <- Vfalse XPEdone stkr)).
    reduce_weakstep Heip.
    rgso. unfold nextinstr; rgso.
    rewrite <- H0 in Hldx1. generalize Hldx1; intro H; inv H. simpl.
    rewrite Haddzero; rewrite Haddzero.
    destruct Ptr.eq_dec; [|done].
    (* destruct memory_chunk_eq_dec; [|done]. *)
    gs_simpl_safe.
    destruct (rs m1); clarify; destruct (rs m0); clarify;
    inversion Hldx2; inversion Hldx3; clarify;
    destruct rmw_instr_dec; try done; rewrite HTv; (destruct Val.eq_dec; [congruence|]; rewrite Heip; simpl; reflexivity). 
  adjust_nextinstr.
  eapply taustar_step. unfold_step. rgso. rgso.
  rewrite HeraseflagsEIP. rgss. rewrite Heip; simpl. rgss. simpl.
  rewrite (functions_transl _ _ _ GFUN HTF).
  generalize GOFS; intro GOFStmp; simpl in GOFStmp;
  rewrite (find_instr_tail _ _ _ _ GOFStmp); clear GOFStmp. 
  simpl. des_teed.
  adjust_nextinstr.
  eapply taustar_step. unfold_step. unfold nextinstr. gs_simpl_safe. rgss.
  rgso. rgso. 
  rewrite HeraseflagsEIP.
  rgss. simpl. rewrite (functions_transl _ _ _ GFUN HTF). simpl in GOFS.
  rewrite (find_instr_tail _ _ _ _ GOFS). simpl. des_teed. gs_simpl_safe.
  apply taustar_refl.
  intros. eexists; split.
  econstructor; auto.
  simpl; rewrite <- H0; eapply atomic_statement_mem_event_cas; auto. 
  eby eapply Val.has_type_lessdef. 
  eapply match_states_intro; eauto using incl_cons_inv.
  unfold erase_eflags, nextinstr, write_eflag. gs_simpl_safe. rgss. gs_simpl_safe. rgss. simpl. reflexivity. 
  unfold erase_eflags, nextinstr, write_eflag; gs_simpl_safe; rgss; gs_simpl_safe; rgss; simpl.  
  eapply transl_code_at_pc_intro; eauto 10 using code_tail_next_int, functions_transl_no_overflow.  
  eapply agree_set_undef_mreg; eauto.
  by rewrite (ireg_of_eq _ _ EQ0); gs_simpl_safe; rgss; rgss. 
  intros. unfold erase_eflags, nextinstr, write_eflag; repeat rgso. auto.
    rewrite (ireg_of_eq _ _ EQ0) in H2; auto.
  (* x0 /= EAX, EAX /= x2 *)
  inv H1.
  apply assertion_inversion_2 in EQ4.
  apply assertion_inversion_2 in EQ5.
  destruct (Val.eq_dec v0 (rs0 x2)).
    (* v0 = rs0 x2 *)
  eexists; split.
  reduce_internal Heip steptau_weakstep; [des_teed|adjust_nextinstr].
  reduce_internal Heip steptau_weakstep; [des_teed|adjust_nextinstr].
  apply weakstep_taustar with (s2 := 
    (State
        (erase_eflags
           ((((rs0 # EIP <- (Val.add (rs0 EIP) Vone)) # XMM7 <- (rs0 EAX))
             # EIP <- (Val.add (Val.add (rs0 EIP) Vone) Vone)) # EAX <-
            (rs0 x2)) # EIP <-
           (Val.add (Val.add (Val.add (rs0 EIP) Vone) Vone) Vone)) # ZF <-
        Vtrue XPEdone stkr)).
    reduce_weakstep Heip.
    rgso; [|congruence]. unfold nextinstr. rgso. rgso. rgso.
    rewrite <- H0 in Hldx1. generalize Hldx1; intro H; inv H. simpl.
    rewrite Haddzero; rewrite Haddzero.
    destruct Ptr.eq_dec; [|done].
    (* destruct memory_chunk_eq_dec; [|done]. *)
    rgss. rgso. rgso. rgso. rgso;[|congruence]. rgso. rgso. rgso. 
    destruct (rs m1); clarify; destruct (rs m0); clarify;
    inversion Hldx2; inversion Hldx3; clarify;
    destruct rmw_instr_dec; try done; simpl; 
    (destruct Val.eq_dec; [|congruence]); 
    gs_simpl_safe; rgss; rgso; rgss; rewrite Heip; simpl; reflexivity.
  adjust_nextinstr.
  eapply taustar_step. unfold_step. rgso. rgso. 
  rewrite HeraseflagsEIP. rgss. rewrite Heip. simpl. 
  rewrite (functions_transl _ _ _ GFUN HTF).
  generalize GOFS; intro GOFStmp; simpl in GOFStmp;
  rewrite (find_instr_tail _ _ _ _ GOFStmp); clear GOFStmp. 
  simpl. des_teed.
  adjust_nextinstr.
  eapply taustar_step. unfold_step. unfold nextinstr. gs_simpl_safe. rgss. gs_simpl_safe.
  rewrite HeraseflagsEIP. rgss. simpl. 
  rewrite (functions_transl _ _ _ GFUN HTF). simpl in GOFS.
  rewrite (find_instr_tail _ _ _ _ GOFS). simpl. des_teed. gs_simpl_safe.
  apply taustar_refl.
  intros. eexists; split.
  econstructor; auto.
  simpl; rewrite <- H0; eapply atomic_statement_mem_event_cas; auto. 
  eby eapply Val.has_type_lessdef. 
  eapply match_states_intro; eauto using incl_cons_inv.
  unfold erase_eflags, nextinstr, write_eflag. gs_simpl_safe. rgss. gs_simpl_safe. rgss. simpl. reflexivity. 
  unfold erase_eflags, nextinstr, write_eflag; gs_simpl_safe; rgss; gs_simpl_safe; rgss; simpl.  
  eapply transl_code_at_pc_intro; eauto. 
  eapply code_tail_next_int. eapply functions_transl_no_overflow; eauto.
  eapply code_tail_next_int. eapply functions_transl_no_overflow; eauto.
  eapply code_tail_next_int. eapply functions_transl_no_overflow; eauto.
  eapply code_tail_next_int. eapply functions_transl_no_overflow; eauto.
  eapply code_tail_next_int. eapply functions_transl_no_overflow; eauto.
  apply GOFS.
  eapply agree_set_undef_mreg; eauto.
  by unfold erase_eflags, write_eflag; rewrite (ireg_of_eq _ _ EQ0); gs_simpl_safe; rgss; gs_simpl_safe; rgss; rewrite e in H.
  intros. unfold erase_eflags, nextinstr, write_eflag; repeat rgso. auto.
    rewrite (ireg_of_eq _ _ EQ0) in H2; auto.
    (* v0 /= rs0 x2 *)
  eexists; split.
  reduce_internal Heip steptau_weakstep; [des_teed|adjust_nextinstr].
  reduce_internal Heip steptau_weakstep; [des_teed|adjust_nextinstr].
  apply weakstep_taustar with (s2 := 
    (State
        ((erase_eflags
            ((((rs0 # EIP <-
                (Vptr (Ptr (Int.unsigned b) (Int.add ofs Int.one))))
               # XMM7 <- (rs0 EAX)) # EIP <-
              (Vptr
                 (Ptr (Int.unsigned b)
                    (Int.add (Int.add ofs Int.one) Int.one)))) # EAX <-
             (rs0 x2)) # EIP <-
            (Vptr
               (Ptr (Int.unsigned b)
                  (Int.add (Int.add (Int.add ofs Int.one) Int.one) Int.one))))
         # EAX <- v0) # ZF <- Vfalse XPEdone stkr)).
    reduce_weakstep Heip.
    rgso; [|congruence]. unfold nextinstr. rgso. rgso. rgso.
    rewrite <- H0 in Hldx1. generalize Hldx1; intro H; inv H. simpl.
    rewrite Haddzero; rewrite Haddzero.
    destruct Ptr.eq_dec; [|done].
    (* destruct memory_chunk_eq_dec; [|done]. *)
    rgss. rgso. rgso. rgso. rgso;[|congruence]. rgso. rgso. rgso. 
    destruct (rs m1); clarify; destruct (rs m0); clarify;
    inversion Hldx2; inversion Hldx3; clarify;
    destruct rmw_instr_dec; try done; rewrite HTv; 
    (destruct Val.eq_dec; [congruence|]); 
    gs_simpl_safe; rgss; rgso; rgss; rewrite Heip; simpl; reflexivity.
  adjust_nextinstr.
  eapply taustar_step. unfold_step. rgso. rgso. 
  rewrite HeraseflagsEIP. rgss. 
  rewrite (functions_transl _ _ _ GFUN HTF). simpl.
  generalize GOFS; intro GOFStmp; simpl in GOFStmp;
  rewrite (find_instr_tail _ _ _ _ GOFStmp); clear GOFStmp. 
  simpl. des_teed.
  adjust_nextinstr.
  eapply taustar_step. unfold_step. unfold nextinstr. gs_simpl_safe. rgss. gs_simpl_safe.
  rewrite HeraseflagsEIP. rgss. simpl. 
  rewrite (functions_transl _ _ _ GFUN HTF). simpl in GOFS.
  rewrite (find_instr_tail _ _ _ _ GOFS). simpl. des_teed. gs_simpl_safe.
  apply taustar_refl.
  intros. eexists; split.
  econstructor; auto.
  simpl; rewrite <- H0; eapply atomic_statement_mem_event_cas; auto. 
  eby eapply Val.has_type_lessdef. 
  eapply match_states_intro; eauto using incl_cons_inv.
  unfold erase_eflags, nextinstr, write_eflag. gs_simpl_safe. rgss. gs_simpl_safe. rgss. simpl. reflexivity. 
  unfold erase_eflags, nextinstr, write_eflag; gs_simpl_safe; rgss; gs_simpl_safe; rgss; simpl.  
  eapply transl_code_at_pc_intro; eauto. 
  eapply code_tail_next_int. eapply functions_transl_no_overflow; eauto.
  eapply code_tail_next_int. eapply functions_transl_no_overflow; eauto.
  eapply code_tail_next_int. eapply functions_transl_no_overflow; eauto.
  eapply code_tail_next_int. eapply functions_transl_no_overflow; eauto.
  eapply code_tail_next_int. eapply functions_transl_no_overflow; eauto.
  apply GOFS.
  eapply agree_set_undef_mreg; eauto.
  by unfold erase_eflags, write_eflag; rewrite (ireg_of_eq _ _ EQ0); gs_simpl_safe; rgss; gs_simpl_safe; rgss. 
  intros. unfold erase_eflags, nextinstr, write_eflag; repeat rgso. auto.
    rewrite (ireg_of_eq _ _ EQ0) in H2; auto.
  (* impossible case *)
  inv H0.

  (* lkinc *)
  find_current_instruction. monadInv EQ0.
  apply assertion_inversion_2 in EQ2.
  eexists; split. 
  reduce_internal Heip steptau_weakstep; [by des_teed|].
  exploit code_tail_next; eauto; intro GOFS1.
  eapply step_taustar_weakstep.
  unfold_step. unfold nextinstr; rgso; rgss; rewrite Heip; simpl.
  rewrite (functions_transl _ _ _ GFUN HTF). 
    erewrite (unsigned_mod_mod _ sig tf _ _ f0 (Ptr 0 b)); eauto.
    rewrite (find_instr_tail _ _ _ _ GOFS1); simpl.
    rgso;[|intro; clarify]; rgso. 
    inv H1.
    generalize (ireg_val _ _ _ _ _ AG EQ1); intro Hix0. 
    rewrite <- H0 in Hix0. inv Hix0. 
    simpl. 
    assert (Hp: (p + Int.zero + Int.zero)%pointer = p).
      by destruct p; simpl; rewrite !Int.add_zero.
    rewrite Hp; clear Hp.
    destruct Ptr.eq_dec; [|done].
    (* destruct memory_chunk_eq_dec; [|done]. *)
    rgss. destruct rmw_instr_dec; [|done].
    rewrite HTv. reflexivity.
  eapply taustar_step; [|apply taustar_refl].
  unfold_step. unfold nextinstr; rgso; rgss; rgso; rgss. simpl. 
  exploit code_tail_next; eauto; intro GOFS2.
  rewrite (functions_transl _ _ _ GFUN HTF). 
    erewrite (unsigned_mod_mod _ sig tf _ _ f0 (Ptr 0 b)); eauto.
    rewrite Zmod_small; 
      [|assert (1 mod Int.modulus = 1) by done; rewrite H;
        generalize (code_tail_bounds _ _ _ _ GOFS1);
        generalize (functions_transl_no_overflow _ _ _ _ FIND HTF);
        unfold Int.max_unsigned; omega].
    rewrite Zmod_small; [|done].
    rewrite (find_instr_tail _ _ _ _ GOFS2); simpl.
    des_teed.
  intros. 
  econstructor; split. 
  econstructor; auto. simpl. inv H1. eapply atomic_statement_mem_event_lkinc. 
  eby eapply Val.has_type_lessdef. 
  eapply match_states_intro; eauto using incl_cons_inv.
  unfold nextinstr. rgso. rgss. rgso. rgss. simpl. reflexivity. 
  unfold nextinstr; rgso; rgss; rgso; rgss; simpl.
  eapply transl_code_at_pc_intro; eauto using code_tail_next_int, functions_transl_no_overflow.  
  simpl. 
  exploit code_tail_next; eauto; intro GOFS1.
  exploit code_tail_next; eauto; intro GOFS2.
  exploit code_tail_next; eauto; intro GOFS3.
  erewrite (unsigned_mod_mod _ sig tf _ _ f0 (Ptr 0 b)); eauto.
  assert (1 mod Int.modulus = 1) by done. 
  rewrite !H0; rewrite Zmod_small; rewrite Zmod_small. 
  by auto.
  by generalize (code_tail_bounds _ _ _ _ GOFS2);
     generalize (functions_transl_no_overflow _ _ _ _ FIND HTF);
     unfold Int.max_unsigned; omega.  
  by generalize (code_tail_bounds _ _ _ _ GOFS2);
     generalize (functions_transl_no_overflow _ _ _ _ FIND HTF);
     unfold Int.max_unsigned; omega.  
  by generalize (code_tail_bounds _ _ _ _ GOFS1);
     generalize (functions_transl_no_overflow _ _ _ _ FIND HTF);
     unfold Int.max_unsigned; omega.  
  unfold nextinstr; rgso; rgss; rgso; rgss. 
  eapply agree_set_undef_mreg; eauto.
  by rewrite (ireg_of_eq _ _ EQ0); rgss.  
  by intros; rewrite (ireg_of_eq _ _ EQ0) in H2;
    rgso; rgso; rgso; rgso; rgso; rgso.

Case "exec_Mfence".
  inv MS; find_current_instruction; monadInv HTF0.
  right; eexists; split; [by reduce_weakstep Heip; des_teed|].
  eapply match_states_intro; eauto using incl_cons_inv, agree_nextinstr.
  - by unfold nextinstr; rewrite Heip; rgss; simpl.
  - unfold nextinstr; rewrite Heip; rgss; simpl. 
    eauto using transl_code_at_pc_intro, code_tail_next_int, functions_transl_no_overflow.
 
Case "exec_function_internal".
  eby (right; right; eapply exec_function_internal_correct).

Case "exec_function_internal_oom".
  inv MS; right.
  assert (FF := proj2 TRANSF (Ptr 0 ofs)).
  specialize (find_function_block_0 b ofs); rewrite H in find_function_block_0;  rewrite find_function_block_0 in *.
  rewrite H in FF.
  destruct (Genv.find_funct_ptr tge (Ptr 0 ofs)) as [] _eqn : E; [|done].
  monadInv FF. destruct x as [sig tc]. monadInv EQ. destruct zlt; [|done]. inv EQ1.
  destruct sp.
  eexists; split.
  eapply steptau_weakstep; unfold_step. 
  rewrite AT; rewrite Int.repr_unsigned; rewrite E.
  simpl. destruct thread_event_eq_dec; [|done]. reflexivity.
  unfold write_int_result. unfold sub_with_borrow_out. rewrite (agree_sp _ _ _ AG).
  simpl. unfold_flags. simpl.
  eapply step_weakstep. unfold_step. destruct range_inside_dec.
  elim H1. simpl. unfold total_framesize. 
  replace (fn_framesize f + fn_paddedstacksize f) with
          (fn_paddedstacksize f + fn_framesize f) in r. done. omega.
  simpl; des_teed. 
  apply match_states_error.

Case "exec_function_external_call".
  right; inv MS.
  pose proof (find_function_block_0 b ofs) as E; rewrite H in E; subst b.
  destruct (function_ptr_translated H) as [tf [Htf1 Htf2]]. 
  eexists; split. 
  apply step_weakstep; simpl; unfold x86_step, xstep_fn, exec_pex_instr;
  rewrite AT; rewrite Int.repr_unsigned.
  rewrite Htf1. monadInv Htf2. 
  rewrite <- (sp_val _ _ _ AG).

  assert (forall x, map_eval_of_val_memarg (map val_of_eval_memarg x) = Some x).
    clear; induction x. 
    by simpl. 
    simpl. destruct a as [] _eqn:Ha. simpl. rewrite IHx. auto.
    simpl. destruct e; simpl; rewrite IHx; auto.
  assert (Hmal: memarglist_from_sig rs (sp + Int.repr Stacklayout.fe_retaddrsize) (ef_sig ef) 
          = memarglist_from_sig_asm rs0 (sp + Int.repr Stacklayout.fe_retaddrsize) (ef_sig ef)).
    unfold memarglist_from_sig, memarglist_from_sig_asm.
    destruct ef; simpl.
    unfold Conventions.loc_parameters. unfold Conventions.loc_arguments.
    destruct ef_sig. simpl. 
    assert (Hsi: forall i,
     map (memarg_of_location rs (sp + Int.repr Stacklayout.fe_retaddrsize))
      (map Conventions.parameter_of_argument
        (Conventions.loc_arguments_rec sig_args i)) =
     map
      (memarg_of_location_asm rs0 (sp + Int.repr Stacklayout.fe_retaddrsize))
      (map Conventions.parameter_of_argument
        (Conventions.loc_arguments_rec sig_args i))).
       clear; induction sig_args. 
       by simpl.
       intro. destruct a as [] _eqn:Ha; simpl; f_equal; apply IHsig_args.
     apply Hsi.

  rewrite Hmal in H1. rewrite <- H1. rewrite H0. des_teed. 

  eapply match_states_blocked; eauto.
  by rewrite Int.repr_unsigned; rewrite Htf1; monadInv Htf2. 

Case "exec_function_external_return".
  right; inv MS. 
  destruct (sig_res (ef_sig ef)) as [] _eqn:Hsr. destruct t as [] _eqn:Ht.
  (* Tint *)
  eexists; split.
  eapply step_weakstep; simpl; unfold x86_step, xstep_fn; simpl.
  rewrite Hsr; destruct typ_eq_dec; [|done]; rewrite H0; reflexivity. 
  eapply match_states_return_external; eauto. 
  unfold Conventions.loc_result; rewrite Hsr.
  eapply agree_set_mreg; eauto. rgss. done.
  intros; destruct r'; inv H; rgso; auto.
  unfold Conventions.loc_result; rewrite Hsr. rgso. apply AT2. 
  (* Tfloat *)
  eexists; split. 
  eapply step_weakstep; simpl; unfold x86_step, xstep_fn; simpl;
  rewrite Hsr; destruct typ_eq_dec; [|done]; rewrite H0; reflexivity. 
  eapply match_states_return_external; eauto. 
  unfold Conventions.loc_result; rewrite Hsr.
  eapply agree_set_mreg; eauto. rgss. done.
  intros; destruct r'; inv H; rgso; auto.
  unfold Conventions.loc_result; rewrite Hsr. rgso. apply AT2. 
  (* Tnone *)
  eexists; split. 
  eapply step_weakstep; simpl; unfold x86_step, xstep_fn; simpl;
  rewrite Hsr; destruct typ_eq_dec; [|done]; rewrite H0; reflexivity. 
  eapply match_states_return_external; eauto. 
  unfold Conventions.loc_result; rewrite Hsr.
  eapply agree_set_mreg; eauto. rgss. done.
  intros; destruct r'; inv H; rgso; auto.
  unfold Conventions.loc_result; rewrite Hsr. rgso. apply AT2. 

Case "exec_return".
  eby (right; eapply exec_return_correct).

Case "exec_return_exit_read_ra".
  right; inv MS. 
  (* internal *)
  exists (Freestackstate stkr); split.
  apply step_weakstep. unfold_step. rewrite AT2, AT3, AT4.
  simpl.
  rewrite (agree_sp _ _ _ AG). simpl. 
  by (destruct Ptr.eq_dec; [|done];
      (* destruct memory_chunk_eq_dec; [|done]; *)
      destruct Val.eq_dec; [|done]). 
  intros. inv H. 
  eexists; split; [vauto | apply match_freestackstate].
  eexists; split. vauto.
  apply match_states_error.
  (* external *)
  exists (Freestackstate stkr); split.
  apply step_weakstep. unfold_step. 
  rewrite (agree_sp _ _ _ AG). simpl. 
  by (destruct Ptr.eq_dec; [|done];
      (* destruct memory_chunk_eq_dec; [|done]; *)
      destruct Val.eq_dec; [|done]). 
  intros. inv H. 
  eexists; split; [vauto | apply match_freestackstate].
  eexists; split. vauto.
  apply match_states_error.
  
Case "exec_return_fail".
  inv MS; right.
  (* internal *)
  destruct (Val.eq_dec ra (Vptr nullptr));
  ( eexists; split;
  [ eapply step_weakstep; unfold_step; rewrite AT2, AT3, AT4; simpl;
    rewrite (agree_sp _ _ _ AG);
    unfold read_mem; destruct Ptr.eq_dec; [|done];
    destruct memory_chunk_eq_dec; [|done]; simpl; rewrite H1 |] ).
  (* ra = nullptr *)
  rewrite e; destruct Val.eq_dec as [|done]. 
  reflexivity. by elim done.  
  intros. exists Errorstate. split.   
  econstructor. rewrite e in H2; inv H2; vauto. auto.
  eby eapply Val.has_type_lessdef. 
  apply match_states_error.
  (* ra = some other pointer *)
  destruct Val.eq_dec. elim n; auto. reflexivity.
  intros.
  destruct v'; destruct ra; inv H2; try discriminate;
  econstructor; split; vauto.
  (* external *)
  destruct (Val.eq_dec ra (Vptr nullptr));
  ( eexists; split;
  [ eapply step_weakstep; unfold_step; 
    rewrite (agree_sp _ _ _ AG); simpl;
    unfold read_mem; destruct Ptr.eq_dec; [|done];
    (* destruct memory_chunk_eq_dec; [|done];*) simpl; rewrite H1 |] ).
  (* ra = nullptr *)
  rewrite e; destruct Val.eq_dec as [|done]. 
  reflexivity. by elim done.  
  intros. exists Errorstate. split.   
  econstructor. rewrite e in H2; inv H2; vauto. auto.
  eby eapply Val.has_type_lessdef. 
  apply match_states_error.
  (* ra = some other pointer *)
  destruct Val.eq_dec. elim n; auto. reflexivity.
  intros.
  destruct v'; destruct ra; inv H2; try discriminate;
  econstructor; split; vauto.
  
Case "exec_exit_free".
  right; inv MS. exists Exitstate. split.
  apply step_weakstep; simpl; unfold x86_step, xstep_fn; simpl; des_teed.
  apply match_exitstate.
  
Case "exec_exit".
  right; inv MS. exists Exitstate. split. 
  apply step_weakstep; simpl; unfold x86_step, xstep_fn; simpl; des_teed.
  apply match_exitstate.   
Qed. 


Lemma my_backward_sim_with_undefs:
  @backward_sim_with_undefs thread_labels lts tlts te_ldo te_ldi
     (@bsr thread_labels lts tlts match_states) (@bsc thread_labels tlts).
Proof.
  eapply (@forward_to_backward_sim_with_undefs thread_labels lts tlts 
            (mc_receptive ge) (x86_determinate tge) (mc_progress_dec ge)
            te_ldo te_ldi ldo_samekind_eq ldo_not_tau ldi_refl
            match_states (fun x y => False)). 
  apply (mk_forward_sim_with_undefs).   
    vauto.
  apply transf_step_correct.
Qed.

Lemma lessdef_list_length:
  forall {l l'} (LD : Val.lessdef_list l l'),
  length l = length l'.
Proof.
  induction l; intros. by inv LD.
  inv LD. simpl; f_equal. eauto.
Qed.

Lemma init_sim_succ:
  forall {p vals vals' tinit}
    (INIT: x86_init tge p vals = Some tinit)
    (LD:   Val.lessdef_list vals' vals),
    exists sinit, mc_init ge p vals' = Some sinit /\ match_states sinit tinit.
Proof.
  intros. unfold x86_init, mc_init in *.
  pose proof TRANSF as (MG & MF).
  specialize (MF p).
  pose proof (WTGENV (Vptr p)) as WTF. unfold Genv.find_funct in WTF.
  repeat (destruct Genv.find_funct_ptr); clarify; [].
  destruct f0; monadInv MF; clarify.
  destruct f0. monadInv EQ.
  destruct zlt; clarify. simpl in *.
  rewrite (lessdef_list_length LD).
  destruct beq_nat; [|done].
  eexists; split; try done. 
  inv INIT. econstructor.
  by apply Val.conv_list_lessdef.
Qed.

Lemma init_sim_fail:
  forall p vals vals'
    (INIT: x86_init tge p vals = None)
    (LD:  Val.lessdef_list vals' vals),
    mc_init ge p vals' = None.
Proof.
  intros. unfold mc_init, x86_init in *.
  pose proof TRANSF as (MG & MF).
  specialize (MF p).
  repeat (destruct Genv.find_funct_ptr); clarify; [].
  destruct f0; monadInv MF; clarify.
  destruct f0. monadInv EQ.
  destruct zlt; clarify. 
  simpl in *. 
  rewrite (lessdef_list_length LD).
  by destruct beq_nat.
Qed.

End PRESERVATION.


Definition full_genv_rel ge tge :=
  genv_rel ge tge /\ wt_genv ge /\ (forall (b : Z) (ofs : int),
       match Genv.find_funct_ptr ge (Ptr b ofs) with
       | Some _ => b = 0%Z
       | None => True
       end).

Require Machtyping.

Definition asmgen_match_prg (p : mc_sem.(SEM_PRG))
                              (p' : x86_sem.(SEM_PRG)) : Prop :=
   Machtyping.wt_program p /\ 
   transf_program p = OK p'.

Theorem asmgen_sim : Sim.sim tso_mm tso_mm mc_sem x86_sem asmgen_match_prg.
Proof.
  eapply (TSOsim_with_undefs.sim mc_sem x86_sem full_genv_rel bsim_rel 
                                 (fun _ => bsim_order)); 
    intros; simpl in *.
  - destruct GENVR as [[GR FR] _]; rewrite GR.
    by rewrite (transform_partial_program_main _ _ (proj2 MP)). 
  - destruct MP as [? MP]. 
    destruct (Genv.exists_matching_genv_and_mem_rev
                  (transform_partial_program_match _ _ MP) INIT) 
      as [sge [INIT' GEM]].
    exists sge; repeat (split; try done).
    intro; case_eq (Genv.find_funct sge f); intro; try done.
    eby eapply Genv.find_funct_prop.
    intros b ofs. 
    destruct (Genv.find_funct_ptr sge (Ptr b ofs)) as [] _eqn:FF; try done.
    pose proof (Genv.find_funct_mem_restr INIT' FF) as B.
    unfold low_mem_restr in B. by destruct zeq.
  - destruct GENVR as [GE [WT RESTR]].
    pose proof (init_sim_succ sge tge GE WT RESTR INIT LD) as [si [INIT' MS]].
    by exists si; split; [|apply fsr_in_bsr].
  - eby destruct GENVR as [? [? ?]]; eapply init_sim_fail.
  - by destruct GENR as [?[]]; eapply my_backward_sim_with_undefs.
Qed.
