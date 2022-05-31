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

(** The Mach intermediate language: abstract semantics. *)

Require Import Coqlib.
Require Import Maps.
Require Import Ast.
Require Import Mem.
Require Import Integers.
Require Import Values.
Require Import Pointers.
Require Import Events.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Conventions.
Require Import Mach.
Require Stacklayout.
Require Import Memcomp.
Require Import Libtactics.

(** This file defines the "abstract" semantics for the Mach
  intermediate language, as opposed to the more concrete
  semantics given in module [Machconcr].

  The only difference with the concrete semantics is the interpretation
  of the stack access instructions [Mgetstack], [Msetstack] and [Mgetparam].
  In the concrete semantics, these are interpreted as memory accesses
  relative to the stack pointer.  In the abstract semantics, these 
  instructions are interpreted as accesses in a frame environment,
  not resident in memory.  The frame environment is an additional
  component of the state.

  Not having the frame data in memory facilitates the proof of
  the [Stacking] pass, which shows that the generated code executes
  correctly with the abstract semantics.
*)

(** * Structure of abstract stack frames *)

(** An abstract stack frame is a mapping from (type, offset) pairs to
    values.  Like location sets (see module [Locations]), overlap
    can occur. *)

Definition frame : Type := typ -> Z -> val.

Definition typ_eq: forall (ty1 ty2: typ), {ty1=ty2} + {ty1<>ty2}.
Proof. decide equality. Defined.

Definition update (ty: typ) (ofs: Z) (v: val) (f: frame) : frame :=
  fun ty' ofs' => 
    if zeq ofs ofs' then
      if typ_eq ty ty' then v else Vundef
    else
      if zle (ofs' + Ast.typesize ty') ofs then f ty' ofs'
      else if zle (ofs + Ast.typesize ty) ofs' then f ty' ofs'
      else Vundef.

Lemma update_same:
  forall ty ofs v fr,
  update ty ofs v fr ty ofs = v.
Proof.
  unfold update; intros. 
  rewrite zeq_true. rewrite dec_eq_true. auto.
Qed. 

Lemma update_other:
  forall ty ofs v fr ty' ofs',
  ofs + Ast.typesize ty <= ofs' \/ ofs' + Ast.typesize ty' <= ofs ->
  update ty ofs v fr ty' ofs' = fr ty' ofs'.
Proof.
  unfold update; intros.
  generalize (Ast.typesize_pos ty). 
  generalize (Ast.typesize_pos ty'). intros.
  rewrite zeq_false.
  destruct H. rewrite zle_false. apply zle_true. auto. omega.
  apply zle_true. auto. 
  omega.
Qed.

Definition empty_frame : frame := fun ty ofs => Vundef.

Section FRAME_ACCESSES.

Variable fsize : Z.

(** A slot [(ty, ofs)] within a frame is valid in function [f] if it lies
  within the bounds of [f]'s frame, it does not overlap with
  the slots reserved for the return address and the back link,
  and it is aligned on a 4-byte boundary. *)

Inductive slot_valid (ty: typ) (ofs: Z): Prop :=
  slot_valid_intro: forall
    (LB: 0 <= ofs)
    (HB: ofs + Ast.typesize ty <= fsize)
(*    (ofs + Ast.typesize ty <= Int.signed f.(fn_link_ofs)
       \/ Int.signed f.(fn_link_ofs) + 4 <= ofs) ->
    (ofs + Ast.typesize ty <= Int.signed f.(fn_retaddr_ofs)
       \/ Int.signed f.(fn_retaddr_ofs) + 4 <= ofs) -> *)
    (ALG: (4 | ofs)),
    slot_valid ty ofs.

Ltac case_kill e :=
  let H := fresh "XXX" in
  case (e); 
    try done;
    try (by intros; right; intro H; inversion H; repeat match goal with  M: _ \/ _ |- _ => destruct M end);
    try (by left; apply slot_valid_intro; auto).

Lemma slot_valid_dec:
  forall ty ofs, {slot_valid ty ofs} + {~ slot_valid ty ofs}.
Proof.
  intros.
  case_kill (Z_gt_le_dec 0 ofs).
  case_kill (Z_gt_le_dec (ofs + Ast.typesize ty) fsize).
  case_kill (Zdivide_dec 4 ofs).
Qed.
(*
  case_kill (Z_gt_le_dec (ofs + Ast.typesize ty) (Int.signed f.(fn_link_ofs))).
   case_kill (Z_gt_le_dec (Int.signed f.(fn_link_ofs) + 4) ofs).
   case_kill (Z_gt_le_dec (ofs + Ast.typesize ty) (Int.signed f.(fn_retaddr_ofs))).
   case_kill (Z_gt_le_dec (Int.signed f.(fn_retaddr_ofs) + 4) ofs).
  case_kill (Z_gt_le_dec (ofs + Ast.typesize ty) (Int.signed f.(fn_retaddr_ofs))).
  case_kill (Z_gt_le_dec (Int.signed f.(fn_retaddr_ofs) + 4) ofs).
Qed. *)

(** [get_slot f fr ty ofs = Some v] if the frame [fr] contains value [v]
  with type [ty] at word offset [ofs]. *)

Definition get_slot: frame -> typ -> Z -> option val :=
  fun fr ty ofs,
    if slot_valid_dec ty ofs then Some (fr ty ofs) else None.


(** [set_slot f fr ty ofs v = Some fr'] if frame [fr'] is obtained from
  frame [fr] by storing value [v] with type [ty] at word offset [ofs]. *)

Definition set_slot: frame -> typ -> Z -> val -> option frame :=
  fun fr ty ofs v,
    if slot_valid_dec ty ofs then Some (update ty ofs v fr)
    else None.

(** Extract the values of the arguments of an external call. *)

Definition extcall_arg (rs: regset) (fr: frame) (l: loc) :=
  match l with
   | R r => Some (rs r)
   | S (Outgoing ofs ty) => get_slot fr ty (Int.signed (Int.repr (4 * ofs)))
   | _ => None
  end.

Definition extcall_args (rs: regset) (fr: frame) (l: list loc) :=
  map_olist (extcall_arg rs fr) l.

Definition extcall_arguments
   (rs: regset) (fr: frame) (sg: signature) (args: list val) : Prop :=
  extcall_args rs fr (Conventions.loc_arguments sg) = Some args.

    
End FRAME_ACCESSES.

(** Mach execution states. *)

Inductive stackframes: Type :=
  | Stackbase:
      forall (fr: frame)          (**r frame containing the initial args *)
             (size : Z),          (**r size of the initial frame *)
      stackframes
  | Stackframe:
      forall (f: function)        (**r calling function *)
             (sp: option pointer) (**r stack pointer in calling function *)
             (c: code)            (**r program point in calling function *)
             (fr: frame)          (**r frame state in calling function *)
             (rest: stackframes), (**r the remaining frames *)
      stackframes.

Inductive state: Type :=
  | State:
      forall (stack: stackframes)  (**r call stack *)
             (f: function)         (**r function currently executing *)
             (sp:  option pointer) (**r stack pointer *)
             (c: code)             (**r current program point *)
             (rs: regset)          (**r register state *)
             (fr: frame),          (**r frame state *)
      state
  | Callstate:
      forall (stack: stackframes)  (**r call stack *)
             (f: fundef)           (**r function to call *)
             (rs: regset),         (**r register state *)
      state
  | Returnstate:
      forall (stack: stackframes)  (**r call stack *)
             (rs: regset),         (**r register state *)
      state
  | Blockedstate:
      forall (stack: stackframes)  (**r call stack *)
             (rs: regset)          (**r register state *)
             (ef_sig: signature),  (**r signature of the extfunction to return *)
      state.

(** [parent_frame s] returns the frame of the calling function.
  It is used to access function parameters that are passed on the stack
  (the [Mgetparent] instruction).
  [parent_function s] returns the calling function itself.
  Suitable defaults are used if there are no calling function. *)

Definition parent_frame (s: stackframes) : frame :=
  match s with
  | Stackbase fr _  => fr
  | Stackframe f sp c fr s => fr
  end.

Definition empty_function := 
  mkfunction (mksignature nil None) nil 0 Int.zero 0.

Definition parent_size (s: stackframes) : Z :=
  match s with
  | Stackbase _ sz  => sz
  | Stackframe f sp c fr s => f.(fn_framesize)
  end.

Section RELSEM.

Variable ge: genv.

Definition find_function (ros: mreg + ident) (rs: regset) : option fundef :=
  match ros with
  | inl r => Genv.find_funct ge (rs r)
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

Inductive ma_step: state -> thread_event -> state -> Prop :=
  | exec_Mlabel:
      forall s f sp lbl c rs fr,
      ma_step (State s f sp (Mlabel lbl :: c) rs fr)
        TEtau (State s f sp c rs fr)
  | exec_Mgetstack:
      forall s f sp ofs ty dst c rs fr v
      (GS : get_slot f.(fn_framesize) fr ty (Int.signed ofs) = Some v),
      ma_step (State s f sp (Mgetstack ofs ty dst :: c) rs fr)
        TEtau (State s f sp c (rs#dst <- v) fr)
  | exec_Msetstack:
     forall s f sp src ofs ty c rs fr fr'
      (SS : set_slot f.(fn_framesize) fr ty (Int.signed ofs) (rs src) = Some fr'),
      ma_step (State s f sp (Msetstack src ofs ty :: c) rs fr)
        TEtau (State s f sp c rs fr')
  | exec_Mgetparam:
      forall s f sp ofs ty dst c rs fr v
      (GS : get_slot (parent_size s) (parent_frame s) ty (Int.signed ofs) = Some v),
      ma_step (State s f sp (Mgetparam ofs ty dst :: c) rs fr)
        TEtau (State s f sp c (rs#dst <- v) fr)
  | exec_Mop:
      forall s f sp op args res c rs fr v
      (EVAL : eval_operation ge sp op rs##args = Some v),
      ma_step (State s f sp (Mop op args res :: c) rs fr)
        TEtau (State s f sp c ((undef_op op rs)#res <- v) fr)
  | exec_Mload:
      forall s f sp chunk addr args dst c rs fr a v
      (EVALA: eval_addressing ge sp addr rs##args = Some (Vptr a))
      (HT : Val.has_type v (type_of_chunk chunk)),
      ma_step (State s f sp (Mload chunk addr args dst :: c) rs fr)
        (TEmem (MEread a chunk v))
        (State s f sp c ((undef_temps rs)#dst <- v) fr)
  | exec_Mstore:
      forall s f sp chunk addr args src c rs fr a v
      (EVALA : eval_addressing ge sp addr rs##args = Some (Vptr a))
      (VC : v = Val.conv (rs src) (type_of_chunk chunk)),
      ma_step (State s f sp (Mstore chunk addr args src :: c) rs fr)
        (TEmem (MEwrite a chunk (cast_value_to_chunk chunk v)))
        (State s f sp c (undef_temps rs) fr)
  | exec_Mcall:
      forall s f sp sig ros c rs fr f'
      (FF : find_function ros rs = Some f'),
      ma_step (State s f sp (Mcall sig ros :: c) rs fr)
        TEtau (Callstate (Stackframe f sp c fr s) f' rs)
  | exec_Mgoto:
      forall s f sp lbl c rs fr c'
      (FL : find_label lbl f.(fn_code) = Some c'),
      ma_step (State s f sp (Mgoto lbl :: c) rs fr)
        TEtau (State s f sp c' rs fr)
  | exec_Mcond_true:
      forall s f sp cond args lbl c rs fr c'
      (EVALC : eval_condition cond rs##args = Some true)
      (FL : find_label lbl f.(fn_code) = Some c'),
      ma_step (State s f sp (Mcond cond args lbl :: c) rs fr)
        TEtau (State s f sp c' (undef_temps rs) fr)
  | exec_Mcond_false:
      forall s f sp cond args lbl c rs fr
      (EVALC : eval_condition cond rs##args = Some false),
      ma_step (State s f sp (Mcond cond args lbl :: c) rs fr)
        TEtau (State s f sp c (undef_temps rs) fr)
  | exec_Mreturn:
      forall s f sp c rs fr lab
      (Elab : lab = match sp with None => TEtau | 
              Some stk => TEmem (MEfree (Ptr.add stk (Int.repr f.(fn_framesize))) MObjStack) end),
      ma_step (State s f sp (Mreturn :: c) rs fr)
        lab
        (Returnstate s rs)
  | exec_Mthreadcreate:
      forall s f sp pfn arg c rs fr
      (ARG : extcall_arguments f.(fn_framesize) rs fr thread_create_sig (Vptr pfn :: arg :: nil)),
      ma_step 
        (State s f sp (Mthreadcreate :: c) rs fr)
        (TEstart pfn (arg :: nil))
        (State s f sp c rs fr)
  | exec_Matomic:
      forall s f sp rs op args res v rs' lab c fr
      (ASME : atomic_statement_mem_event op (rs##args) v lab)
      (Ers' : rs' = ((undef_temps rs) # res <- v))
      (HTv : Val.has_type v Tint),
      ma_step 
        (State s f sp (Matomic op args res :: c) rs fr)
        (TEmem lab)
        (State s f sp c rs' fr)
  | exec_Mfence:
      forall s f sp rs c fr,
      ma_step 
        (State s f sp (Mfence :: c) rs fr)
        (TEmem MEfence)
        (State s f sp c rs fr)
  | exec_function_internal_empty:
      forall s f rs
      (EMPTY: f.(fn_stacksize) = Int.zero),
      ma_step (Callstate s (Internal f) rs)
        TEtau
        (State s f None f.(fn_code) rs empty_frame)
  | exec_function_internal_nonempty:
      forall s f rs stk stksize
      (NEMPTY : f.(fn_stacksize) <> Int.zero)
      (Estksize : stksize = f.(fn_stacksize)),
      ma_step (Callstate s (Internal f) rs)
        (TEmem (MEalloc stk stksize MObjStack)) 
        (State s f (Some (Ptr.sub_int stk (Int.repr (f.(fn_framesize)))))
               f.(fn_code) rs empty_frame)
  | exec_function_external_call:
      forall s ef args eargs rs1
      (EARG : 
        extcall_arguments (parent_size s) rs1 (parent_frame s) ef.(ef_sig) args)
      (Eargs : args = map val_of_eval eargs),
      ma_step (Callstate s (External ef) rs1)
         (TEext (Ecall ef.(ef_id) eargs))
         (Blockedstate s rs1 ef.(ef_sig))
  | exec_function_external_return:
      forall s efsig res eres rs1 rs2 typ
      (Etyp : typ = (match sig_res efsig with Some x => x | None => Tint end))
      (HT : Val.has_type res typ)
      (Eres : res = val_of_eval eres)
      (Ers2 : rs2 = (rs1#(Conventions.loc_result efsig) <- res)),
      ma_step (Blockedstate s rs1 efsig)
         (TEext (Ereturn typ eres))
         (Returnstate s rs2)
  | exec_return:
      forall f sp c fr s rs,
      ma_step (Returnstate (Stackframe f sp c fr s) rs)
        TEtau (State s f sp c rs fr)
  | exec_return_exit:
      forall rs fr sz,
      ma_step (Returnstate (Stackbase fr sz) rs)
        TEexit (Returnstate (Stackbase fr sz) rs).

Fixpoint build_frame_rec (locs : list loc) (vs : list val) (acc : frame) :=
  match locs, vs with
    | S (Outgoing ofs ty) :: locs, v :: vs =>
        build_frame_rec locs vs (update ty (4 * ofs) v acc)
    | R _ :: locs, v :: vs => 
        build_frame_rec locs vs acc
    | _, _ => acc
  end.

Definition build_frame (sig : signature) (vs : list val) :=
  build_frame_rec (Conventions.loc_arguments sig) vs empty_frame.

Definition ma_init  (p : pointer) (vs : list val) : option state :=
  match Genv.find_funct_ptr ge p with
   | Some (Internal f)  => 
       if beq_nat (length vs) (length f.(fn_sig).(sig_args))
         then Some (Callstate (Stackbase (build_frame f.(fn_sig) 
                                                      (Val.conv_list vs f.(fn_sig).(sig_args)))
                                         (4 * Conventions.size_arguments f.(fn_sig)))
                              (Internal f)
                              (Regmap.init Vundef))
         else None
   | _ => None
  end.

End RELSEM.

Tactic Notation "ma_step_cases" tactic(first) tactic(c) :=
    first; [
      c "exec_Mlabel" |
      c "exec_Mgetstack" |
      c "exec_Msetstack" |
      c "exec_Mgetparam" |
      c "exec_Mop" |
      c "exec_Mload" |
      c "exec_Mstore" |
      c "exec_Mcall" |
      c "exec_Mgoto" |
      c "exec_Mcond_true" |
      c "exec_Mcond_false" |
      c "exec_Mreturn" |
      c "exec_Mthreadcreate" |
      c "exec_Matomic" |
      c "exec_Mfence" |
      c "exec_function_internal_empty" |
      c "exec_function_internal_nonempty" |
      c "exec_function_external_call" |
      c "exec_function_external_return" |
      c "exec_return" |
      c "exec_return_exit"].

Definition ma_ge_init (p : program) (ge : genv) (m : Mem.mem) :=
  Genv.globalenv_initmem p ge low_mem_restr m.

(** * TSO machine set up *)

Section Macha_TSO.

Ltac atomic_dtac :=
  match goal with
    | H : atomic_statement_mem_event ?A ?B ?C ?D |- _ => inv H
  end.

Lemma ma_receptive :
  forall ge l l' s s',
    ma_step ge s l s' ->
    te_samekind l' l ->
    exists s'', ma_step ge s l' s''.
Proof.
  intros g l l' s s' Step Te_Samekind.
  inversion Step; 
     subst;
     destruct l' as [[] | [] | | | | | |];
     try destruct sp;
     simpl in *; subst; clarify;
     try rewrite Te_Samekind; 
     try (destruct Te_Samekind; subst);
     try (decompose [and] H0; subst);
     try (eexists;
       solve [ eassumption | econstructor; try eassumption; auto; done |
               econstructor; try apply H0; edone]);
     atomic_dtac; try done; destruct Te_Samekind as (-> & -> & -> & HTI);
     eexists; (eapply exec_Matomic; [| reflexivity | apply HTI, HTv]).
   (* The following are necessary to get around silly handling
      of existential variables in Coq. *)
   eby rewrite <- H1; econstructor.
   eby rewrite <- H1; econstructor.
   eby rewrite <- H1; econstructor.
   eby rewrite <- H1; econstructor.
Qed.

Ltac determinate_aux_tac :=
  repeat match goal with
    | H' : ?a = _, H'' : ?a = _ |- _ => rewrite H' in H''; clarify
    | H : map val_of_eval ?x = map val_of_eval ?y |- _ => 
        rewrite (map_val_of_eval_eq H); done
    | H :  atomic_statement_mem_event _ _ _ _,
      H' : atomic_statement_mem_event _ _ _ _ |- _ => 
      try (eby clarify'; eapply atomic_statement_determinate);
      rewrite (atomic_statement_determinate_eq H H') in *
  end.

Lemma ma_determinate:
  forall ge s s' s'' l l',
    ma_step ge s l s' ->
    ma_step ge s l' s'' ->
    (te_samekind l l' /\ (l = l' -> s' = s'')).
Proof.
  intros g s s' s'' l l' ST1 ST2; split.
  by destruct ST1; inv ST2; unfold extcall_arguments in *; clarify; simpl; determinate_aux_tac; destruct sp.

  by intro; subst; destruct ST1; inv ST2; clarify; determinate_aux_tac.
Qed.

Require Import Classical.

Lemma ma_progress_dec:
    forall ge s, (forall s' l', ~ ma_step ge s l' s') \/
      (exists l', exists s', ma_step ge s l' s').
Proof.
  intros g s.
  set (P := exists l' : thread_event, exists s' : state, ma_step g s l' s').
  destruct (classic P). auto.
  left. intros s' l'. revert s'. apply not_ex_all_not.
  revert l'. apply not_ex_all_not. auto.
Qed.

Definition ma_sem : SEM := 
  mkSEM state genv program ma_ge_init (@prog_main _ _) (@Genv.find_symbol _) 
  ma_step ma_init ma_progress_dec ma_receptive ma_determinate.

End Macha_TSO.


