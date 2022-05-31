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

(** The Linear intermediate language: abstract syntax and semantcs *)

(** The Linear language is a variant of LTLin where arithmetic
    instructions operate on machine registers (type [mreg]) instead
    of arbitrary locations.  Special instructions [Lgetstack] and
    [Lsetstack] are provided to access stack slots. *)

Require Import Coqlib.
Require Import Maps.
Require Import Ast.
Require Import Integers.
Require Import Pointers.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import LTL.
Require Import Conventions.
Require Import Memcomp.
Require Import Libtactics.

(** * Abstract syntax *)

Definition label := positive.

Inductive instruction: Type :=
  | Lgetstack: slot -> mreg -> instruction
  | Lsetstack: mreg -> slot -> instruction
  | Lop: operation -> list mreg -> mreg -> instruction
  | Lload: memory_chunk -> addressing -> list mreg -> mreg -> instruction
  | Lstore: memory_chunk -> addressing -> list mreg -> mreg -> instruction
  | Lcall: signature -> mreg + ident -> instruction
  | Llabel: label -> instruction
  | Lgoto: label -> instruction
  | Lcond: condition -> list mreg -> label -> instruction
  | Lreturn: instruction
  | Lthreadcreate: instruction
  | Latomic: atomic_statement -> list mreg -> mreg -> instruction
  | Lfence: instruction.

Definition code: Type := list instruction.

Record function: Type := mkfunction {
  fn_sig: signature;
  fn_stacksize: int (* was Z *);
  fn_code: code
}.

Definition fundef := Ast.fundef function.

Definition program := Ast.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => f.(fn_sig)
  | External ef => ef.(ef_sig)
  end.

Definition genv := Genv.t fundef.
Definition locset := Locmap.t.

(** * Operational semantics *)

(** Looking up labels in the instruction list.  *)

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Llabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Llabel lbl else instr <> Llabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl l); intro; congruence.
Qed.

(** [find_label lbl c] returns a list of instruction, suffix of the
  code [c], that immediately follows the [Llabel lbl] pseudo-instruction.
  If the label [lbl] is multiply-defined, the first occurrence is
  retained.  If the label [lbl] is not defined, [None] is returned. *)

Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
  match c with
  | nil => None
  | i1 :: il => if is_label lbl i1 then Some il else find_label lbl il
  end.

Section RELSEM.

Variable ge: genv.

Definition find_function (ros: mreg + ident) (rs: locset) : option fundef :=
  match ros with
  | inl r => Genv.find_funct ge (rs (R r))
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

Definition reglist (rs: locset) (rl: list mreg) : list val :=
  List.map (fun r => rs (R r)) rl.

(** Calling conventions are reflected at the level of location sets
  (environments mapping locations to values) by the following two 
  functions.  

  [call_regs caller] returns the location set at function entry,
  as a function of the location set [caller] of the calling function.
- Machine registers have the same values as in the caller.
- Incoming stack slots (used for parameter passing) have the same
  values as the corresponding outgoing stack slots (used for argument
  passing) in the caller.
- Local and outgoing stack slots are initialized to undefined values.
*) 

Definition call_regs (caller: locset) : locset :=
  fun (l: loc) =>
    match l with
    | R r => caller (R r)
    | S (Local ofs ty) => Vundef
    | S (Incoming ofs ty) => caller (S (Outgoing ofs ty))
    | S (Outgoing ofs ty) => Vundef
    end.

(** [return_regs caller callee] returns the location set after
  a call instruction, as a function of the location set [caller]
  of the caller before the call instruction and of the location
  set [callee] of the callee at the return instruction.
- Callee-save machine registers have the same values as in the caller
  before the call.
- Caller-save machine registers have the same values
  as in the callee at the return point.
- Stack slots have the same values as in the caller before the call.
*)

Definition return_regs (caller callee: locset) : locset :=
  fun (l: loc) =>
    match l with
    | R r =>
        if In_dec Loc.eq (R r) Conventions.temporaries then
          callee (R r)
        else if In_dec Loc.eq (R r) Conventions.destroyed_at_call then
          callee (R r)
        else
          caller (R r)
    | S s => caller (S s)
    end.

Definition undef_op (op: operation) (rs: locset) :=
  match op with
  | Omove => rs
  | _ => undef_temps rs
  end.

(** Linear execution states. *)

Inductive stackframe: Type :=
  | Stackframe:
      forall (f: function)         (**r calling function *)
             (sp: option pointer)  (**r stack pointer in calling function *)
             (rs: locset)          (**r location state in calling function *)
             (c: code),            (**r program point in calling function *)
      stackframe.

Inductive state: Type :=
  | State:
      forall (stack: list stackframe) (**r call stack *)
             (f: function)            (**r function currently executing *)
             (sp: option pointer)     (**r stack pointer *)
             (c: code)                (**r current program point *)
             (rs: locset),            (**r location state *)
      state
  | Callstate:
      forall (stack: list stackframe) (**r call stack *)
             (f: fundef)              (**r function to call *)
             (rs: locset),            (**r location state at point of call *)
      state
  | Returnstate:
      forall (stack: list stackframe) (**r call stack *)
             (rs: locset),            (**r location state at point of return *)
      state
  | Blockedstate:
      forall (stack: list stackframe) (**r call stack *)
             (rs: locset)             (**r location state at point of return *)
             (ef_sig: signature),     (**r signature of the function waiting to return *) 
      state.

(** [parent_locset cs] returns the mapping of values for locations
  of the caller function. *)

Definition parent_locset (stack: list stackframe) : locset :=
  match stack with
  | nil => Locmap.init Vundef
  | Stackframe f sp ls c :: stack' => ls
  end.

(** The main difference between the Linear transition relation
  and the LTL transition relation is the handling of function calls.
  In LTL, arguments and results to calls are transmitted via
  [vargs] and [vres] components of [Callstate] and [Returnstate],
  respectively.  The semantics takes care of transferring these values
  between the locations of the caller and of the callee.
  
  In Linear and lower-level languages (Mach, PPC), arguments and
  results are transmitted implicitly: the generated code for the
  caller arranges for arguments to be left in conventional registers
  and stack locations, as determined by the calling conventions, where
  the function being called will find them.  Similarly, conventional
  registers will be used to pass the result value back to the caller.
  This is reflected in the definition of [Callstate] and [Returnstate] 
  above, where a whole location state [rs] is passed instead of just
  the values of arguments or returns as in LTL.

  These location states passed across calls are treated in a way that
  reflects the callee-save/caller-save convention:
- The [exec_Lcall] transition from [State] to [Callstate]
  saves the current location state [ls] in the call stack,
  and passes it to the callee.
- The [exec_function_internal] transition from [Callstate] to [State]
  changes the view of stack slots ([Outgoing] slots slide to
  [Incoming] slots as per [call_regs]).
- The [exec_Lreturn] transition from [State] to [Returnstate]
  restores the values of callee-save locations from
  the location state of the caller, using [return_regs].

This protocol makes it much easier to later prove the correctness of
the [Stacking] pass, which inserts actual code that performs the
saving and restoring of callee-save registers described above.
*)

Inductive step: state -> thread_event -> state -> Prop :=
  | exec_Lgetstack:
      forall s f sp sl r b rs,
      step (State s f sp (Lgetstack sl r :: b) rs)
        TEtau (State s f sp b (Locmap.set (R r) (rs (S sl)) rs))
  | exec_Lsetstack:
      forall s f sp r sl b rs,
      step (State s f sp (Lsetstack r sl :: b) rs)
        TEtau (State s f sp b (Locmap.set (S sl) (rs (R r)) rs))
  | exec_Lop:
      forall s f sp op args res b rs v,
      eval_operation ge sp op (reglist rs args) = Some v ->
      step (State s f sp (Lop op args res :: b) rs)
        TEtau (State s f sp b (Locmap.set (R res) v (undef_op op rs)))
  | exec_Lload:
      forall s f sp chunk addr args dst b rs a v,
      eval_addressing ge sp addr (reglist rs args) = Some (Vptr a) ->
      Val.has_type v (type_of_chunk chunk) ->
      step (State s f sp (Lload chunk addr args dst :: b) rs)
        (TEmem (MEread a chunk v))
        (State s f sp b (Locmap.set (R dst) v (undef_temps rs)))
  | exec_Lstore:
      forall s f sp chunk addr args src b rs a v,
      eval_addressing ge sp addr (reglist rs args) = Some (Vptr a) ->
      v = Val.conv (rs (R src)) (type_of_chunk chunk) ->
      step (State s f sp (Lstore chunk addr args src :: b) rs)
        (TEmem (MEwrite a chunk (cast_value_to_chunk chunk v)))
        (State s f sp b (undef_temps rs))
  | exec_Lcall:
      forall s f sp sig ros b rs f',
      find_function ros rs = Some f' ->
      sig = funsig f' ->
      step (State s f sp (Lcall sig ros :: b) rs)
        TEtau (Callstate (Stackframe f sp rs b:: s) f' rs)
  | exec_Llabel:
      forall s f sp lbl b rs,
      step (State s f sp (Llabel lbl :: b) rs)
        TEtau (State s f sp b rs)
  | exec_Lgoto:
      forall s f sp lbl b rs b',
      find_label lbl f.(fn_code) = Some b' ->
      step (State s f sp (Lgoto lbl :: b) rs)
        TEtau (State s f sp b' rs)
  | exec_Lcond_true:
      forall s f sp cond args lbl b rs b',
      eval_condition cond (reglist rs args) = Some true ->
      find_label lbl f.(fn_code) = Some b' ->
      step (State s f sp (Lcond cond args lbl :: b) rs)
        TEtau (State s f sp b' (undef_temps rs))
  | exec_Lcond_false:
      forall s f sp cond args lbl b rs,
      eval_condition cond (reglist rs args) = Some false ->
      step (State s f sp (Lcond cond args lbl :: b) rs)
        TEtau (State s f sp b (undef_temps rs))
  | exec_Lreturn:
      forall s f sp b rs lab regs,
      lab = (match sp with 
               | None => TEtau 
               | Some stk => TEmem (MEfree stk MObjStack) end) ->
      regs = (return_regs (parent_locset s) rs) ->
      step (State s f sp (Lreturn :: b) rs)
        lab
        (Returnstate s regs)
  | exec_Lthreadcreate:
      forall s f sp pfn arg b rs,
      List.map rs (Conventions.loc_arguments thread_create_sig) =
        Vptr pfn :: arg :: nil ->
      step 
        (State s f sp (Lthreadcreate :: b) rs)
        (TEstart pfn (arg :: nil))
        (State s f sp b rs)
  | exec_Latomic:
      forall s f sp rs op args res v rs' lab b
      (ASME : atomic_statement_mem_event op (reglist rs args) v lab)
      (Ers' : rs' = Locmap.set (R res) v (undef_temps rs))
      (HTv : Val.has_type v Tint),
      step 
        (State s f sp (Latomic op args res :: b) rs)
        (TEmem lab)
        (State s f sp b rs')
  | exec_Lfence:
      forall s f sp rs b,
      step 
        (State s f sp (Lfence :: b) rs)
        (TEmem MEfence)
        (State s f sp b rs)
  | exec_function_internal_empty:
      forall s f rs code regs,
      f.(fn_stacksize) = Int.zero ->
      code = f.(fn_code) ->
      regs = call_regs rs ->
      step (Callstate s (Internal f) rs) TEtau
        (State s f None code regs)
  | exec_function_internal_nonempty:
      forall s f rs stk stksize code regs,
      stksize = f.(fn_stacksize) ->
      code = f.(fn_code) ->
      regs = call_regs rs ->
      stksize <> Int.zero ->
      step (Callstate s (Internal f) rs)
        (TEmem (MEalloc stk stksize MObjStack))
        (State s f (Some stk) code regs)
  | exec_function_external_call:
      forall s ef args eargs rs1,
      args = (*Val.conv_list*) (List.map rs1 (Conventions.loc_arguments ef.(ef_sig))) (*ef.(ef_sig).(sig_args)*) ->
      args = map val_of_eval eargs ->
      step (Callstate s (External ef) rs1)
         (TEext (Ecall ef.(ef_id) eargs))
         (Blockedstate s rs1 ef.(ef_sig))
  | exec_function_external_return:
      forall s efsig res eres rs1 rs2 typ,
      typ = (match sig_res efsig with Some x => x | None => Tint end) ->
      Val.has_type res typ ->
      rs2 = Locmap.set (R (Conventions.loc_result efsig)) res rs1 ->
      res = val_of_eval eres ->
      step (Blockedstate s rs1 efsig)
         (TEext (Ereturn typ eres))
         (Returnstate s rs2)
  | exec_return:
      forall s f sp rs0 c rs,
      step (Returnstate (Stackframe f sp rs0 c :: s) rs)
        TEtau (State s f sp c rs)
  | exec_return_exit:
      forall rs,
      step (Returnstate nil rs)
        TEexit (Returnstate nil rs).

Fixpoint build_locs (locs : list loc) (vs : list val) :=
  match locs, vs with
    | l :: locs, v :: vs => 
        (fun l' => if Loc.eq l' l then v else (build_locs locs vs) l')
    | _, _ => Locmap.init Vundef
  end.

Definition linear_init  (p : pointer) (vs : list val) : option state :=
  match Genv.find_funct_ptr ge p with
   | Some (Internal f)  =>
       if beq_nat (length vs) (length f.(fn_sig).(sig_args))
         then Some (Callstate nil (Internal f) 
                                  (build_locs (loc_arguments f.(fn_sig)) 
                                    (Val.conv_list vs f.(fn_sig).(sig_args))))
         else None
   | _ => None
  end.

End RELSEM.

Tactic Notation "instruction_cases" tactic(first) tactic(c) :=
    first; [
      c "Lgetstack" |
      c "Lsetstack" |
      c "Lop" |
      c "Lload" |
      c "Lstore" |
      c "Lcall" |
      c "Llabel" |
      c "Lgoto" |
      c "Lcond" |
      c "Lreturn" |
      c "Lthreadcreate" |
      c "Latomic" |
      c "Lfence"].

Tactic Notation "step_cases" tactic(first) tactic(c) :=
    first; [
      c "exec_Lgetstack" |
      c "exec_Lsetstack" |
      c "exec_Lop" |
      c "exec_Lload" |
      c "exec_Lstore" |
      c "exec_Lcall" |
      c "exec_Llabel" |
      c "exec_Lgoto" |
      c "exec_Lcond_true" |
      c "exec_Lcond_false" |
      c "exec_Lreturn" |
      c "exec_Lthreadcreate" |
      c "exec_Latomic" |
      c "exec_Lfence" |
      c "exec_function_internal_empty" |
      c "exec_function_internal_nonempty" |
      c "exec_function_external_call" |
      c "exec_function_external_return" |
      c "exec_return" |
      c "exec_return_exit"].


Definition linear_ge_init (p : program) (ge : genv) (m : Mem.mem) := 
  Genv.globalenv_initmem p ge low_mem_restr m.

Section Linear_TSO.

Ltac atomic_dtac :=
  match goal with
    | H : atomic_statement_mem_event ?A ?B ?C ?D |- _ => inv H
  end.

Lemma linear_receptive :
  forall ge l l' s s',
    step ge s l s' ->
    te_samekind l' l ->
    exists s'', step ge s l' s''.
Proof.
  intros g l l' s s' Step Te_Samekind.
  inversion Step; 
     subst;
     destruct l'; try destruct ev;
     try destruct sp;
     simpl in *; subst; clarify;
     try rewrite Te_Samekind; 
     try (destruct Te_Samekind; subst);
     try (decompose [and] H2; subst);
     try (eexists;
       solve [ eassumption | econstructor; try eassumption; auto; done |
               econstructor; try apply H1; edone]);
     atomic_dtac; try done; destruct Te_Samekind as (-> & -> & -> & HTI);
     eexists; (eapply exec_Latomic; [| reflexivity | apply HTI, HTv]).
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

Lemma linear_determinate:
  forall ge s s' s'' l l',
    step ge s l s' ->
    step ge s l' s'' ->
    (te_samekind l l' /\ (l = l' -> s' = s'')).
Proof.
  intros g s s' s'' l l' ST1 ST2; split.
    by destruct ST1; inv ST2; simpl; clarify; determinate_aux_tac; destruct sp.

  by intro; subst; destruct ST1; inv ST2; clarify; determinate_aux_tac.
Qed.

Require Import Classical.

Lemma linear_progress_dec:
  forall ge s, (forall s' l', ~ step ge s l' s') \/
    (exists l', exists s', step ge s l' s').
Proof.
  intros g s.
  set (P := exists l' : thread_event, exists s' : state, step g s l' s').
  destruct (classic P). auto.
  left. intros s' l'. revert s'. apply not_ex_all_not.
  revert l'. apply not_ex_all_not. auto.
Qed.

Definition linear_sem : SEM := 
  mkSEM state genv program linear_ge_init (@prog_main _ _) (@Genv.find_symbol _) 
  step linear_init linear_progress_dec linear_receptive linear_determinate.

End Linear_TSO.
