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

(** The Mach intermediate language: concrete semantics. *)

Require Import Coqlib.
Require Import Maps.
Require Import Ast.
Require Import Integers.
Require Import Pointers.
Require Import Values.
Require Import Events.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Conventions.
Require Import Mach.
Require Stacklayout.
Require Asm.
Require Asmgenretaddr.
Require Import Simulations.
Require Import Mem.
Require Import Memcomp.
Require Import Libtactics.


(** In the concrete semantics for Mach, the three stack-related Mach
  instructions are interpreted as memory accesses relative to the
  stack pointer.  More precisely:
- [Mgetstack ofs ty r] is a memory load at offset [ofs * 4] relative
  to the stack pointer.
- [Msetstack r ofs ty] is a memory store at offset [ofs * 4] relative
  to the stack pointer.
- [Mgetparam ofs ty r] is a memory load at offset [ofs * 4]
  relative to the pointer found at offset 0 from the stack pointer.
  The semantics maintain a linked structure of activation records,
  with the current record containing a pointer to the record of the
  caller function at offset 0.

In addition to this linking of activation records, the concrete
semantics also make provisions for storing a back link at offset
[f.(fn_link_ofs)] from the stack pointer, and a return address at
offset [f.(fn_retaddr_ofs)].  The latter stack location will be used
by the Asm code generated by [Asmgen] to save the return address into
the caller at the beginning of a function, then restore it and jump to
it at the end of a function.  The Mach concrete semantics does not
attach any particular meaning to the pointer stored in this reserved
location, but makes sure that it is preserved during execution of a
function.  The [return_address_offset] predicate from module
[Asmgenretaddr] is used to guess the value of the return address that
the Asm code generated later will store in the reserved location.
*)

(*
Definition chunk_of_type (ty: typ) :=
  match ty with Tint => Mint32 | Tfloat => Mfloat64 end.

Definition load_stack (m: mem) (sp: pointer) (ty: typ) (ofs: int) :=
  load_ptr (chunk_of_type ty) m (MPtr.add sp ofs).

Definition store_stack (m: mem) (sp: pointer) (ty: typ) (ofs: int) (v: val) :=
  store_ptr (chunk_of_type ty) m (MPtr.add sp ofs) v.
*)

(** Extract the values of the arguments of an external call. *)

(*
Inductive extcall_arg: regset -> mem -> val -> loc -> val -> Prop :=
  | extcall_arg_reg: forall rs m sp r,
      extcall_arg rs m sp (R r) (rs r)
  | extcall_arg_stack: forall rs m sp ofs ty v,
      load_stack m sp ty (Int.repr (Stacklayout.fe_ofs_arg + 4 * ofs)) = Some v ->
      extcall_arg rs m sp (S (Outgoing ofs ty)) v.

Inductive extcall_args: regset -> mem -> val -> list loc -> list val -> Prop :=
  | extcall_args_nil: forall rs m sp,
      extcall_args rs m sp nil nil
  | extcall_args_cons: forall rs m sp l1 ll v1 vl,
      extcall_arg rs m sp l1 v1 -> extcall_args rs m sp ll vl ->
      extcall_args rs m sp (l1 :: ll) (v1 :: vl).

Definition extcall_arguments
   (rs: regset) (m: mem) (sp: val) (sg: signature) (args: list val) : Prop :=
  extcall_args rs m sp (Conventions.loc_arguments sg) args.
*)

(** Mach execution states. *)

Inductive stackframe: Type :=
  | Stackframe:
      forall (f: pointer)         (**r pointer to calling function *)
             (sp: pointer)        (**r stack pointer in calling function *)
             (retaddr: pointer)   (**r Asm return address in calling function *)
             (c: code),           (**r program point in calling function *)
      stackframe.

Inductive state: Type :=
  | Initstate:
      forall (f: pointer)              (**r pointer to the function to be called *)
             (args: list val),         (**r arguments to be passed to the function *)
      state
  | Initargsstate:
      forall (f: pointer)              (**r function to be called *)
             (args: list val)          (**r arguments to be passed to the function *)
             (locs: list loc)          (**r location for arguments *)
             (sp: pointer)             (**r stack pointer *)
             (stkr: arange)            (**r stack range *)
             (rs: regset),             (**r register state *)
      state
  | Freestackstate:
       forall (stkr : arange),         (**r stack range *)
      state
  | Exitstate:
      state
  | State:
      forall (stack: list stackframe)  (**r call stack *)
             (f: pointer)              (**r pointer to current function *)
             (sp: pointer)             (**r stack pointer *)
             (c: code)                 (**r current program point *)
             (stkr: arange)            (**r allocated stack range *)
             (rs: regset),             (**r register state *)
      state
  | Callstate:
      forall (stack: list stackframe)  (**r call stack *)
             (f: pointer)              (**r pointer to function to call *)
             (sp: pointer)             (**r stack pointer *)
             (stkr: arange)            (**r allocated stack range *)
             (rs: regset),             (**r register state *)
      state
  | Returnstate:
      forall (stack: list stackframe)  (**r call stack *)
             (sp: pointer)             (**r stack pointer *)
             (stkr: arange)            (**r allocated stack range *)
             (rs: regset),             (**r register state *)
      state
  | Blockedstate:
      forall (stack: list stackframe)  (**r call stack *)
             (sp: pointer)             (**r stack pointer *)
             (stkr: arange)            (**r allocated stack range *)
             (rs: regset)              (**r register state *)
             (efsig: signature),       (**r memory state *)
      state
  | Errorstate: state.

Definition parent_ra ts := match ts with
 | Stackframe fb sp ra c :: ts => ra
 | nil => Ptr 0 Int.zero
 end.

Definition parent_sp ts := match ts with
 | Stackframe fb sp ra c :: ts => sp
 | nil => Ptr 0 Int.mone
 end.

Fixpoint find_label2 (lbl: label) (c: code) (p: pointer) {struct c} : pointer :=
  match c with
  | nil => p
  | i1 :: il => if is_label lbl i1 then p else find_label2 lbl il (MPtr.add p Int.one)
  end.

Section RELSEM.

Variable ge: genv.

Definition parent_offset (f : function) : int :=
  Int.repr (fn_paddedstacksize f + fn_framesize f + Stacklayout.fe_retaddrsize).

Definition total_framesize (f : function) : int :=
  Int.repr (fn_paddedstacksize f + fn_framesize f).

Definition memarg_of_location (rs : regset) (sp : pointer) (l : loc) 
                           : pointer * memory_chunk + val :=
  match l with
    | R r => inr _ (Regmap.get r rs)
    | S (Incoming ofs ty) => 
        inl _ (MPtr.add sp (Int.repr (4 * ofs)), Asm.chunk_of_ty ty)
    | _ => inr _ Vundef
  end.

Definition memarglist_from_sig (rs : regset) (sp : pointer) (sig : signature)
                           : list (pointer * memory_chunk + val) :=
  map (memarg_of_location rs sp) (Conventions.loc_parameters sig).

Definition get_ra (s : list stackframe) :=
  match s with 
    | Stackframe _ _ ra _ :: _ => ra 
    | nil => nullptr
  end.

Inductive mc_step: state -> thread_event -> state -> Prop :=
  | exec_Initalloc: 
      forall pfn args fn stkp size sp
      (FF: Genv.find_funct_ptr ge pfn = Some fn)
      (Esz: size = 4 * Conventions.size_arguments (funsig fn))
      (SZ:  size + 15 + Stacklayout.fe_retaddrsize (* extra space for alignment and return address *) <= 
            Stacklayout.thread_stack_size)
      (Esp: sp = Asm.align_stack (MPtr.add stkp 
                                 (Int.repr (Stacklayout.thread_stack_size - size)))),
      mc_step
        (Initstate pfn args)
        (TEmem (MEalloc stkp (Int.repr Stacklayout.thread_stack_size) MObjStack))
        (Initargsstate
                  pfn args (Conventions.loc_parameters (funsig fn)) 
                  (MPtr.sub_int sp (Int.repr Stacklayout.fe_retaddrsize))
                  (stkp, Int.repr Stacklayout.thread_stack_size) (Regmap.init Vundef))
  | exec_Initalloc_oom:
      forall pfn args fn size
      (FF: Genv.find_funct_ptr ge pfn = Some fn)
      (Esz: size = 4 * Conventions.size_arguments (funsig fn))
      (SZ:  size + 15 + Stacklayout.fe_retaddrsize > Stacklayout.thread_stack_size),
      mc_step
        (Initstate pfn args)
        (TEoutofmem)
        (Initstate pfn args)
  | exec_Initargmem:
      forall pfn arg args ofs argp ty locs sp stkr rs
        (Eargp: argp = MPtr.add sp (Int.repr (4 * ofs + Stacklayout.fe_retaddrsize))),
      mc_step
        (Initargsstate pfn (arg :: args) (S (Incoming ofs ty) :: locs) sp stkr rs)
        (TEmem (MEwrite argp (Asm.chunk_of_ty ty) arg))
        (Initargsstate pfn args locs sp stkr rs)
  | exec_Initargreg:
      forall pfn arg args r locs sp stkr rs,
      mc_step
        (Initargsstate pfn (arg :: args) (R r :: locs) sp stkr rs)
        TEtau
        (Initargsstate pfn args locs sp stkr (rs#r <- arg))
  | exec_Initretaddr:
      forall pfn sp stkr rs,
      mc_step 
        (Initargsstate pfn nil nil sp stkr rs)
        (TEmem (MEwrite sp Mint32 (Vptr nullptr)))
        (Callstate nil pfn sp stkr rs)
  | exec_Mlabel:
      forall s f sp lbl c stkr rs,
      mc_step (State s f sp (Mlabel lbl :: c) stkr rs)
        TEtau (State s f sp c stkr rs)
  | exec_Mgetstack:
      forall s f sp ofs ty dst c rs v ptr chunk stkr rs'
      (Eptr   : ptr   = MPtr.add sp ofs)
      (Echunk : chunk = Asm.chunk_of_ty ty)
      (Ers'   : rs'   = (rs#dst <- v))
      (HT     : Val.has_type v (type_of_chunk chunk)),
      mc_step (State s f sp (Mgetstack ofs ty dst :: c) stkr rs)
        (TEmem (MEread ptr chunk v))
        (State s f sp c stkr rs')
  | exec_Msetstack:
      forall s f sp src ofs ty c stkr rs ptr chunk v
      (Eptr  : ptr   = MPtr.add sp ofs)
      (Echunk: chunk = Asm.chunk_of_ty ty)
      (Ev    : v     = Val.conv (rs src) (type_of_chunk chunk))
      (HT    : Val.has_type v (type_of_chunk chunk)),
      mc_step (State s f sp (Msetstack src ofs ty :: c) stkr rs)
        (TEmem (MEwrite ptr chunk (cast_value_to_chunk chunk v)))
        (State s f sp c stkr rs)
  | exec_Mgetparam:
      forall s fb f sp ofs ty dst c stkr rs v ptr chunk rs'
      (FF    : Genv.find_funct_ptr ge fb = Some (Internal f))
      (Eptr  : ptr   = MPtr.add (MPtr.add sp (parent_offset f)) ofs)
      (Echunk: chunk = Asm.chunk_of_ty ty)
      (Ers'  : rs'   = (rs#dst <- v))
      (HT    : Val.has_type v (type_of_chunk chunk)),
      mc_step (State s fb sp (Mgetparam ofs ty dst :: c) stkr rs)
        (TEmem (MEread ptr chunk v))
        (State s fb sp c stkr rs')
  | exec_Mop:
      forall s f sp op args res c stkr rs v
      (EVAL : eval_operation ge (Some sp) op rs##args = Some v),
      mc_step (State s f sp (Mop op args res :: c) stkr rs)
        TEtau (State s f sp c stkr ((undef_op op rs)#res <- v))
  | exec_Mload:
      forall s f sp chunk addr args dst c stkr rs rs' a v
      (EVAL : eval_addressing ge (Some sp) addr rs##args = Some (Vptr a))
      (HT   : Val.has_type v (type_of_chunk chunk))
      (Ers' : rs'   = ((undef_temps rs)#dst <- v)),
      mc_step (State s f sp (Mload chunk addr args dst :: c) stkr rs)
        (TEmem (MEread a chunk v))
        (State s f sp c stkr rs')
  | exec_Mstore:
      forall s f sp chunk addr args src c stkr rs a v
      (EVAL : eval_addressing ge (Some sp) addr rs##args = Some (Vptr a))
      (Ev   : v = Val.conv (rs src) (type_of_chunk chunk)),
      mc_step (State s f sp (Mstore chunk addr args src :: c) stkr rs)
        (TEmem (MEwrite a chunk (cast_value_to_chunk chunk v)))
        (State s f sp c stkr (undef_temps rs))
  | exec_Mcall:
      forall s fb sp sig ros c stkr rs f f' ra lab roffs sp'
      (FF : find_function_ptr ge ros rs = Some f')
      (GFF: Genv.find_funct_ptr ge fb = Some (Internal f))
      (RA : Asmgenretaddr.return_address_offset f c roffs)
      (Era: ra = Ptr (Int.unsigned (MPtr.offset fb)) roffs)
      (Esp: sp' = MPtr.sub_int sp (Int.repr Stacklayout.fe_retaddrsize))
      (RI : range_inside (sp', Int.zero) stkr)
      (El : lab = TEmem (MEwrite sp' Mint32 (Vptr ra))),
      mc_step (State s fb sp (Mcall sig ros :: c) stkr rs)
        lab (Callstate (Stackframe fb sp ra c :: s) f' sp' stkr rs)
  | exec_Mcall_oom:
      forall s fb sp sig ros c stkr rs sp' f'
      (FF : find_function_ptr ge ros rs = Some f')
      (Esp: sp' = MPtr.sub_int sp (Int.repr Stacklayout.fe_retaddrsize))
      (RI : ~ range_inside (sp', Int.zero) stkr),
      mc_step 
        (State s fb sp (Mcall sig ros :: c) stkr rs)
        (TEoutofmem)
        Errorstate
  | exec_Mgoto:
      forall s fb f sp lbl c stkr rs c'
      (GFF : Genv.find_funct_ptr ge fb = Some (Internal f))
      (FL  : find_label lbl f.(fn_code) = Some c'),
      mc_step (State s fb sp (Mgoto lbl :: c) stkr rs)
        TEtau (State s fb sp c' stkr rs)
  | exec_Mcond_true:
      forall s fb f sp cond args lbl c stkr rs c',
      eval_condition cond rs##args = Some true ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      mc_step (State s fb sp (Mcond cond args lbl :: c) stkr rs)
        TEtau (State s fb sp c' stkr (undef_temps rs))
  | exec_Mcond_false:
      forall s f sp cond args lbl c stkr rs,
      eval_condition cond rs##args = Some false ->
      mc_step (State s f sp (Mcond cond args lbl :: c) stkr rs)
        TEtau (State s f sp c stkr (undef_temps rs))
  | exec_Mreturn:
      forall s fb sp c stkr rs sp' f'
      (GFF   : Genv.find_funct_ptr ge fb = Some (Internal f'))
      (Esp'  : sp' = MPtr.add sp (total_framesize f'))
      (INSIDE: range_inside (sp', Int.zero) stkr),
      mc_step (State s fb sp (Mreturn :: c) stkr rs)
        TEtau
        (Returnstate s sp' stkr rs)
  | exec_Mthreadcreate:
      forall s f sp c stkr rs fn args,
      memarglist_from_sig rs sp thread_create_sig = fn :: args ->
      mc_step 
        (State s f sp (Mthreadcreate :: c) stkr rs)
        (TEstartmem fn args) 
        (State s f sp c stkr rs) 
 | exec_Matomic:
      forall s f sp rs op args res v rs' lab c stkr
      (ASME : atomic_statement_mem_event op (rs##args) v lab)
      (Ers' : rs' = ((undef_temps rs) # res <- v))
      (HTv : Val.has_type v Tint),
      mc_step 
        (State s f sp (Matomic op args res :: c) stkr rs)
        (TEmem lab)
        (State s f sp c stkr rs')
 | exec_Mfence:
      forall s f sp rs c stkr,
      mc_step 
        (State s f sp (Mfence :: c) stkr rs)
        (TEmem MEfence)
        (State s f sp c stkr rs)
  | exec_function_internal:
      forall s fb stkr rs f sp sp',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      sp' = MPtr.sub_int sp (total_framesize f) ->
      range_inside (sp', Int.zero) stkr ->
      (* lab = TEmem (MEwrite (MPtr.add sp (fn_link_ofs f)) Mint32 (Vptr sp')) -> *)
      mc_step (Callstate s fb sp stkr rs)
        TEtau (State s fb sp' f.(fn_code) stkr rs)
  | exec_function_internal_oom:
      forall s fb stkr rs f sp sp',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      sp' = MPtr.sub_int sp (total_framesize f) ->
      ~ range_inside (sp', Int.zero) stkr ->
      mc_step (Callstate s fb sp stkr rs)
        (TEoutofmem) Errorstate (* was (Callstate s fb sp stkr rs) *)
  | exec_function_external_call:
      forall s fb sp stkr rs ef memargs extmemargs,
      Genv.find_funct_ptr ge fb = Some (External ef) ->
      memarglist_from_sig rs (MPtr.add sp (Int.repr Stacklayout.fe_retaddrsize)) 
                          ef.(ef_sig) = memargs ->
      map val_of_eval_memarg extmemargs = memargs ->
      mc_step (Callstate s fb sp stkr rs)
         (TEexternalcallmem ef.(ef_id) extmemargs)
         (Blockedstate s sp stkr rs ef.(ef_sig))
  | exec_function_external_return:
      forall s stkr rs rs' ty efsig v ev sp,
      ty = (match sig_res efsig with Some x => x | None => Tint end) ->
      Val.has_type v ty ->
      rs' = (rs#(Conventions.loc_result efsig) <- v) ->
      v = val_of_eval ev ->
      mc_step (Blockedstate s sp stkr rs efsig)
         (TEext (Ereturn ty ev))
         (Returnstate s sp stkr rs')
  | exec_return:
      forall s f sp ra c stkr rs sp',
      sp' = MPtr.add sp (Int.repr Stacklayout.fe_retaddrsize) ->
      mc_step 
        (Returnstate (Stackframe f sp' ra c :: s) sp stkr rs)
        (TEmem (MEread sp Mint32 (Vptr ra)))
        (State s f sp' c stkr rs)
  | exec_return_exit_read_ra:
      forall sp stkr rs,
      mc_step (Returnstate nil sp stkr rs)
        (TEmem (MEread sp Mint32 (Vptr nullptr)))
        (Freestackstate stkr)
  | exec_return_fail:
      forall s sp stkr rs ra,
      ra <> (Vptr (get_ra s)) ->
      match s with 
        | Stackframe f' sp' ra' c' :: s' => 
            sp' = MPtr.add sp (Int.repr Stacklayout.fe_retaddrsize)
        | _ => True
      end ->
      Val.has_type ra Tint ->
      mc_step (Returnstate s sp stkr rs)
        (TEmem (MEread sp Mint32 ra)) 
        Errorstate
  | exec_exit_free:
      forall stkp n,
      mc_step (Freestackstate (stkp, n))
        (TEmem (MEfree stkp MObjStack))
        Exitstate
  | exec_exit:
      mc_step Exitstate TEexit Exitstate.

Definition mc_init  (p : pointer) (vs : list val) : option state :=
  match Genv.find_funct_ptr ge p with
   | Some (Internal f)  => 
       if beq_nat (length vs) (length f.(fn_sig).(sig_args))
         then Some (Initstate p (Val.conv_list vs f.(fn_sig).(sig_args)))
         else None
   | _ => None
  end.

End RELSEM.

Tactic Notation "mc_step_cases" tactic(first) tactic(c) :=
    first; [
      c "exec_Initalloc" |
      c "exec_Initalloc_oom" |
      c "exec_Initargmem" |
      c "exec_Initargreg" |
      c "exec_Initretaddr" |
      c "exec_Mlabel" |
      c "exec_Mgetstack" |
      c "exec_Msetstack" |
      c "exec_Mgetparam" |
      c "exec_Mop" |
      c "exec_Mload" |
      c "exec_Mstore" |
      c "exec_Mcall" |
      c "exec_Mcall_oom" |
      c "exec_Mgoto" |
      c "exec_Mcond_true" |
      c "exec_Mcond_false" |
      c "exec_Mreturn" |
      c "exec_Mthreadcreate" |
      c "exec_Matomic" |
      c "exec_Mfence" |
      c "exec_function_internal" |
      c "exec_function_internal_oom" |
      c "exec_function_external_call" |
      c "exec_function_external_return" |
      c "exec_return" |
      c "exec_return_exit_read_ra" |
      c "exec_return_fail" |
      c "exec_exit_free" |
      c "exec_exit"].

Hint Constructors mc_step : mc.

Definition mc_ge_init (p : program) (ge : genv) (m : Mem.mem) :=
  Genv.globalenv_initmem p ge low_mem_restr m.

(** * TSO machine setup *)

Section Machc_TSO.

Ltac atomic_dtac :=
  match goal with
    | H : atomic_statement_mem_event ?A ?B ?C ?D |- _ => inv H
  end.


Lemma mc_receptive :
  forall ge l l' s s',
    mc_step ge s l s' ->
    te_samekind l' l ->
    exists s'', mc_step ge s l' s''.
Proof.
  intros g l l' s s' Step Te_Samekind.
  
  destruct l' as [[] | [] | | | | | |]; destruct l as [[] | [] | | | | | |];
    simpl in Te_Samekind; try done;
    inversion Step;
    subst;
    try destruct sp; subst; clarify;
    try rewrite Te_Samekind; 
    repeat match goal with
             | H : _ /\ _ |- _ => destruct H; clarify
           end; eauto with mc;
    try (by destruct (Val.eq_dec v (Vptr ra)); subst; eauto with mc);
    try (by destruct (Val.eq_dec v (Vptr nullptr)); subst; eauto with mc);
    try (by destruct (Val.eq_dec v (Vptr (get_ra s0))); destruct s0; 
            subst; eauto with mc; destruct s; eauto with mc);
    eauto with mc;
    atomic_dtac; try done;
    eexists; (eapply exec_Matomic; [| reflexivity | apply H0, HTv]).
   eby rewrite <- H2; econstructor.
   eby rewrite <- H2; econstructor.
Qed.

Lemma val_of_eval_memarg_inj:
  forall l l',
    map val_of_eval_memarg l = map val_of_eval_memarg l' -> l' = l.
Proof.
  induction l as [|h l IH]; intro l'. by destruct l'.
  simpl. destruct l' as [|h' l']. done.
  intros E. injection E. intros El Eh.
  f_equal. 
    destruct h; destruct h'; try done; try (by inv Eh). 
    destruct e; destruct e0; try done; by inv Eh.
  eby eapply IH.
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
    | H : map val_of_eval_memarg ?a1 = ?mal,
      H' : map val_of_eval_memarg ?a2 = ?mal |- _ =>
        by (rewrite <- H  in H'; rewrite (val_of_eval_memarg_inj _ _ H'))
  end.


Lemma mc_determinate:
  forall ge s s' s'' l l',
    mc_step ge s l s' ->
    mc_step ge s l' s'' ->
    (te_samekind l l' /\ (l = l' -> s' = s'')).
Proof.
  intros g s s' s'' l l' ST1 ST2; split.
    destruct ST1; inversion ST2; subst; clarify; determinate_aux_tac; simpl.
    eby (repeat f_equal; eapply Asmgenretaddr.return_address_offset_determinate).
  intro; subst; destruct ST1; inv ST2; clarify; determinate_aux_tac.
Qed.

Require Import Classical.

Lemma mc_progress_dec:
  forall ge s, (forall s' l', ~ mc_step ge s l' s') \/
    (exists l', exists s', mc_step ge s l' s').
Proof.
  intros g s.
  set (P := exists l' : thread_event, exists s' : state, mc_step g s l' s').
  destruct (classic P). auto.
  left. intros s' l'. revert s'. apply not_ex_all_not.
  revert l'. apply not_ex_all_not. auto.
Qed.

Definition mc_sem : SEM := 
  mkSEM state genv program mc_ge_init (@prog_main _ _) (@Genv.find_symbol _) 
  mc_step mc_init mc_progress_dec mc_receptive mc_determinate.

End Machc_TSO.