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
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Abstract syntax and semantics for the Cminor language. *)

Require Import Coqlib.
Require Import Maps.
Require Import Ast.
Require Import Integers.
Require Import Floats.
Require Import Pointers.
Require Import Events.
Require Import Values.
Require Import Globalenvs.
Require Import Switch.
Require Import Memcomp.
Require Cminorops.
Require Import Libtactics.

Definition unary_operation := Cminorops.unary_operation.
Definition binary_operation := Cminorops.binary_operation.
Definition atomic_statement := Cminorops.atomic_statement.
Definition eval_compare_mismatch := Cminorops.eval_compare_mismatch.
Definition eval_compare_null := Cminorops.eval_compare_null.
Definition eval_unop := Cminorops.eval_unop.
Definition eval_binop := Cminorops.eval_binop.

(** * Abstract syntax *)

(** Cminor is a low-level imperative language structured in expressions,
  statements, functions and programs.  We first define the constants
  and operators that occur within expressions. *)

Inductive constant : Type :=
  | Ointconst: int -> constant     (**r integer constant *)
  | Ofloatconst: float -> constant (**r floating-point constant *)
  | Oaddrsymbol: ident -> int -> constant (**r address of the symbol plus the offset *)
  | Oaddrstack: int -> constant.   (**r stack pointer plus the given offset *)

(** Expressions include reading local variables, constants and
  arithmetic operations, reading store locations, and conditional
  expressions (similar to [e1 ? e2 : e3] in C). *)

Inductive expr : Type :=
  | Evar : ident -> expr
  | Econst : constant -> expr
  | Eunop : unary_operation -> expr -> expr
  | Ebinop : binary_operation -> expr -> expr -> expr
  | Eload : memory_chunk -> expr -> expr
  | Econdition : expr -> expr -> expr -> expr.

(** Statements include expression evaluation, assignment to local variables,
  memory stores, function calls, an if/then/else conditional, infinite
  loops, blocks and early block exits, and early function returns.
  [Sexit n] terminates prematurely the execution of the [n+1]
  enclosing [Sblock] statements. *)

Definition label := ident.

Inductive stmt : Type :=
  | Sskip: stmt
  | Sassign : ident -> expr -> stmt
  | Sstore : memory_chunk -> expr -> expr -> stmt
  | Scall : option ident -> signature -> expr -> list expr -> stmt
  | Sseq: stmt -> stmt -> stmt
  | Sifthenelse: expr -> stmt -> stmt -> stmt
  | Sloop: stmt -> stmt
  | Sblock: stmt -> stmt
  | Sexit: nat -> stmt
  | Sswitch: expr -> list (int * nat) -> nat -> stmt
  | Sreturn: option expr -> stmt
  | Slabel: label -> stmt -> stmt
  | Sgoto: label -> stmt
  | Sthread_create: expr -> expr -> stmt
  | Satomic : option ident -> atomic_statement -> list expr -> stmt
  | Smfence : stmt.

(** Functions are composed of a signature, a list of parameter names,
  a list of local variables, and a  statement representing
  the function body.  Each function can allocate a memory block of
  size [fn_stackspace] on entrance.  This block will be deallocated
  automatically before the function returns.  Pointers into this block
  can be taken with the [Oaddrstack] operator. *)

Record function : Type := mkfunction {
  fn_sig: signature;
  fn_params: list ident;
  fn_vars: list ident;
  fn_stackspace: Z;
  fn_body: stmt
}.

Definition fundef := Ast.fundef function.
Definition program := Ast.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => f.(fn_sig)
  | External ef => ef.(ef_sig)
  end.

(** * Operational semantics (small-step) *)

(** Two kinds of evaluation environments are involved:
- [genv]: global environments, define symbols and functions;
- [env]: local environments, map local variables to values.
*)

Definition genv := Genv.t fundef.
Definition env := PTree.t val.

(** The following functions build the initial local environment at
  function entry, binding parameters to the provided arguments and
  initializing local variables to [Vundef]. *)

Fixpoint set_params (vl: list val) (il: list ident) {struct il} : env :=
  match il, vl with
  | i1 :: is, v1 :: vs => PTree.set i1 v1 (set_params vs is)
  | i1 :: is, nil => PTree.set i1 Vundef (set_params nil is)
  | _, _ => PTree.empty val
  end.

Fixpoint set_locals (il: list ident) (e: env) {struct il} : env :=
  match il with
  | nil => e
  | i1 :: is => PTree.set i1 Vundef (set_locals is e)
  end.

Definition set_optvar (optid: option ident) (v: val) (e: env) : env :=
  match optid with
  | None => e
  | Some id => PTree.set id v e
  end.

(** Continuations *)


Inductive cont: Type :=
  | Kstop: cont                         (**r stop program execution *)
  | Kseq: stmt -> cont -> cont          (**r execute stmt, then cont *)
  | Kblock: cont -> cont                (**r exit a block, then do cont *)
  | Kcall: option ident -> fundef -> option pointer -> env -> cont -> cont.
                                        (**r return to caller *)

Inductive expr_cont : Type :=
  | EKunop : unary_operation ->  expr_cont -> expr_cont
  | EKbinop1 : binary_operation -> expr -> expr_cont -> expr_cont
  | EKbinop2 : binary_operation -> val -> expr_cont -> expr_cont
  | EKload : memory_chunk -> expr_cont -> expr_cont
  | EKcall : option ident -> signature -> list expr -> cont -> expr_cont
  | EKargs : option ident -> val -> signature -> list expr -> list val -> cont -> expr_cont
  | EKatargs : option ident -> atomic_statement -> list expr -> list val -> cont -> expr_cont
  | EKcond : expr -> expr -> expr_cont -> expr_cont
  | EKassign : ident -> cont -> expr_cont
  | EKthread1 : expr -> cont -> expr_cont
  | EKthread2 : pointer -> cont -> expr_cont
  | EKcondstmt : stmt -> stmt -> cont -> expr_cont
  | EKswitch: list (int * nat) -> nat -> cont -> expr_cont
  | EKreturn: cont -> expr_cont
  | EKstoreaddr: memory_chunk -> expr -> cont -> expr_cont
  | EKstoreval: memory_chunk -> val -> cont -> expr_cont.

(** States *)

Inductive state: Type :=
  | SKexpr:                      (**r Execution within a function *)
      forall (e: expr)                  (**r statement under consideration *)
             (sp: option pointer)       (**r current stack pointer *)
             (env: env)                 (**r current local environment *)
             (k: expr_cont),            (**r its continuation -- what to do next *)
      state
  | SKval:                       (**r Execution within a function *)
      forall (v: val)                   (**r statement under consideration *)
             (sp: option pointer)       (**r current stack pointer *)
             (env: env)                 (**r current local environment *)
             (k: expr_cont),            (**r its continuation -- what to do next *)
      state
  | SKstmt:                      (**r Execution within a function *)
      forall (s: stmt)                  (**r statement under consideration *)
             (sp: option pointer)       (**r current stack pointer *)
             (env: env)                 (**r current local environment *)
             (k: cont),                 (**r its continuation -- what to do next *)
      state
  | SKcall:                      (**r Invocation of a function *)
      forall (args: list val)           (**r arguments provided by caller *)
             (k: cont),                 (**r what to do next  *)
      state
  | SKexternal:                    (**r Waiting for result of external function *)
      forall (efsig: signature)         (**r Return value *)
             (k: cont),                 (**r what to do next *)
      state
  | SKreturn:                    (**r Return from a function *)
      forall (v: val)                   (**r Return value *)
             (k: cont),                 (**r what to do next *)
      state.
             
Section RELSEM.

Variable ge: genv.

(** Evaluation of constants and operator applications.
    [None] is returned when the computation is undefined, e.g.
    if arguments are of the wrong types, or in case of an integer division
    by zero. *)

Definition eval_constant (sp: option pointer) (cst: constant) : option val :=
  match cst with
  | Ointconst n => Some (Vint n)
  | Ofloatconst n => Some (Vfloat n)
  | Oaddrsymbol s ofs =>
      match Genv.find_symbol ge s with
      | None => None
      | Some p => Some (Vptr (Ptr.add p ofs))
      end
  | Oaddrstack ofs =>
      match sp with
      | Some p => Some (Vptr (Ptr.add p ofs))
      | None => None
      end
  end.



Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kseq s k => call_cont k
  | Kblock k => call_cont k
(*  | Kfree ps v k =>  call_cont k *)
  | _ => k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ _ => True
  | _ => False
  end.

Definition get_fundef (k: cont) : option fundef :=
  match k with
   | Kcall _ fd _ _ _ => (Some fd)
   | _ => None
  end.

(** Find the statement and manufacture the continuation 
  corresponding to a label *)

Fixpoint find_label (lbl: label) (s: stmt) (k: cont) 
                    {struct s}: option (stmt * cont) :=
  match s with
  | Sseq s1 s2 =>
      match find_label lbl s1 (Kseq s2 k) with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sifthenelse a s1 s2 =>
      match find_label lbl s1 k with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sloop s1 =>
      find_label lbl s1 (Kseq (Sloop s1) k)
  | Sblock s1 =>
      find_label lbl s1 (Kblock k)
  | Slabel lbl' s' =>
      if ident_eq lbl lbl' then Some(s', k) else find_label lbl s' k
  | _ => None
  end.

(** * Operational semantics *)

Inductive cm_step : state -> thread_event -> state -> Prop :=
(* Var *)
| StepVar:
  forall sp id v env k
  (EVAL : PTree.get id env = Some v),
  cm_step (SKexpr (Evar id) sp env k)
          TEtau
          (SKval v sp env k)
(* Const *)
| StepConst:
  forall sp cst v env k
  (EC : eval_constant sp cst = Some v),
  cm_step (SKexpr (Econst cst) sp env k)
          TEtau
          (SKval v sp env k)
(* Unop *)
| StepUnop1:
  forall sp op e k env,
  cm_step (SKexpr (Eunop op e) sp env k)
          TEtau
          (SKexpr e sp env (EKunop op k))
| StepUnop:
  forall sp v v' op k env
  (EU : eval_unop op v = Some v'),
  cm_step (SKval v sp env (EKunop op k))
          TEtau
          (SKval v' sp env k)
(* Binop *)
| StepBinop1:
  forall sp op e1 e2 env k,
  cm_step (SKexpr (Ebinop op e1 e2) sp env k)
          TEtau
          (SKexpr e1 sp env (EKbinop1 op e2 k))
| StepBinop2:
  forall sp op v e2 env k,
  cm_step (SKval v sp env (EKbinop1 op e2 k))
          TEtau
          (SKexpr e2 sp env (EKbinop2 op v k))
| StepBinop:
  forall sp op v v1 v2 env k
  (EB : eval_binop op v1 v2 = Some v),
  cm_step (SKval v2 sp env (EKbinop2 op v1 k))
          TEtau
          (SKval v sp env k)
(* Load *)
| StepLoad1:
  forall sp c e env k,
  cm_step (SKexpr (Eload c e) sp env k)
          TEtau
          (SKexpr e sp env (EKload c k))
| StepLoad:
  forall sp p v c env k
  (HT : Val.has_type v (type_of_chunk c)),
  cm_step (SKval (Vptr p) sp env (EKload c k))
          (TEmem (MEread p c v))
          (SKval v sp env k)
(* Conditional *)
| StepIfThenElse:
  forall sp e1 e2 e3 k env,
  cm_step (SKexpr (Econdition e1 e2 e3) sp env k)
          TEtau
          (SKexpr e1 sp env (EKcond e2 e3 k)) 
| StepIfThenElseTrue:
  forall sp v e1 e2 k env
  (BOV : Val.bool_of_val v true),
  cm_step (SKval v sp env (EKcond e1 e2 k))
       TEtau
       (SKexpr e1 sp env k)
| StepIfThenElseFalse:
  forall sp v e1 e2 k env
  (BOV : Val.bool_of_val v false),
  cm_step (SKval v sp env (EKcond e1 e2 k))
          TEtau
          (SKexpr e2 sp env k)
(* Skip *)
| StepSkipBlock:
  forall sp k env,
  cm_step (SKstmt Sskip sp env (Kblock k))
          TEtau
          (SKstmt Sskip sp env k)
(* Assign *)
| StepAssign1:
  forall sp id e env k,
  cm_step (SKstmt (Sassign id e) sp env k)
          TEtau
          (SKexpr e sp env (EKassign id k))
| StepAssign:
  forall sp v id env env' k
  (VLS : PTree.set id v env = env'),
  cm_step (SKval v sp env (EKassign id k))
          TEtau
          (SKstmt Sskip sp env' k)
(* Store *)
| StepStore1:
  forall sp chunk e1 e2 env k,
  cm_step (SKstmt (Sstore chunk e1 e2) sp env k)
          TEtau
          (SKexpr e1 sp env (EKstoreaddr chunk e2 k))
| StepStore2:
  forall sp ptr chunk e2 env k,
  cm_step (SKval ptr sp env (EKstoreaddr chunk e2 k))
          TEtau
          (SKexpr e2 sp env (EKstoreval chunk ptr k))
| StepStore:
  forall sp v chunk ptr env k,
  cm_step (SKval v sp env (EKstoreval chunk (Vptr ptr) k))
          (TEmem (MEwrite ptr chunk (cast_value_to_chunk chunk v)))
          (SKstmt Sskip sp env k)
(* Call *)
| StepCall:
  forall sp optid sig e args env k,
  cm_step (SKstmt (Scall optid sig e args) sp env k)
          TEtau
          (SKexpr e sp env (EKcall optid sig args k))
| StepEmptyCall:
  forall sp vf fd sig optid env k
  (GFF : Genv.find_funct ge vf = Some fd)
  (FSIG : funsig fd = sig),
  cm_step (SKval vf sp env (EKcall optid sig nil k))
          TEtau
          (SKcall nil (Kcall optid fd sp env k))
| StepCallArgs1:
  forall sp vf (*fd*) optid sig arg1 args env k
  (*GFF : Genv.find_funct ge vf = Some fd*)
  (*FSIG : funsig fd = sig*),
  cm_step (SKval vf sp env (EKcall optid sig (arg1 :: args) k))
          TEtau
          (SKexpr arg1 sp env (EKargs optid vf sig args nil k))
| StepCallArgs2:
  forall sp v vs vf optid arg1 args env k sig,
  cm_step (SKval v sp env (EKargs optid vf sig (arg1 :: args) vs k))
          TEtau
          (SKexpr arg1 sp env (EKargs optid vf sig args (List.app vs (v::nil)) k))
| StepCallArgs:
  forall sp v vs vf fd optid env k sig
  (FSIG : funsig fd = sig),
  Genv.find_funct ge vf = Some fd ->  
  cm_step (SKval v sp env (EKargs optid vf sig nil vs k))
          TEtau
          (SKcall (List.app vs (v :: nil)) (Kcall optid fd sp env k))
(* Atomics *)
| StepAtomic : forall optid astmt e es k env sp,
  cm_step (SKstmt (Satomic optid astmt  (e :: es)) sp env k)  
          TEtau
          (SKexpr e sp env  (EKatargs optid astmt es nil k )  )
| StepAtomicArgs : forall v optid astmt vs e es k env sp,
  cm_step (SKval v sp env  (EKatargs optid astmt (e :: es) vs  k))  
           TEtau
           (SKexpr e sp env  (EKatargs optid astmt es (vs ++ v :: nil) k)) 
| StepAtomicFinishNone : forall v astmt vs k env p v' rmwi sp,
  Cminorops.sem_atomic_statement astmt ( vs ++ v :: nil ) = Some (p, rmwi)  ->
  Val.has_type v' (type_of_chunk Mint32)  ->
  cm_step (SKval v sp env  (EKatargs  None  astmt nil vs k))  
          (TEmem  (MErmw p Mint32 v' rmwi))  
          (SKstmt Sskip sp env k)
| StepAtomicFinishSome : forall v id astmt vs k env p v' rmwi sp,
  Cminorops.sem_atomic_statement astmt ( vs ++ v :: nil ) = Some (p, rmwi)  ->
  Val.has_type v' (type_of_chunk Mint32)  ->
  cm_step (SKval v sp env  (EKatargs  (Some id)  astmt nil vs k))  
           (TEmem  (MErmw p Mint32 v' rmwi))  
           (SKval v' sp env (EKassign id k) )
| StepFence : forall k env sp,
  cm_step (SKstmt Smfence sp env k)  
          (TEmem MEfence)
          (SKstmt Sskip sp env k)
(* Seq *)
| StepSeq:
  forall sp s1 s2 env k,
  cm_step (SKstmt (Sseq s1 s2) sp env k)
          TEtau
          (SKstmt s1 sp env (Kseq s2 k))
(* Conditional Statement *)
| StepCond:
  forall sp e s1 s2 env k,
  cm_step (SKstmt (Sifthenelse e s1 s2) sp env k)
          TEtau
          (SKexpr e sp env (EKcondstmt s1 s2 k))
| StepCondTrue:
  forall sp v s1 s2 env k
  (BOV : Val.bool_of_val v true),
  cm_step (SKval v sp env (EKcondstmt s1 s2 k))
          TEtau
          (SKstmt s1 sp env k) 
| StepCondFalse:
  forall sp v s1 s2 env k
  (BOV : Val.bool_of_val v  false),
  cm_step (SKval v sp env (EKcondstmt s1 s2 k))
          TEtau
          (SKstmt s2 sp env k) 
(* Loop *)
| StepLoop:
  forall sp s env k,
  cm_step (SKstmt (Sloop s) sp env k)
          TEtau
          (SKstmt s sp env (Kseq (Sloop s) k)) 
(* Block *)
| StepBlock:
  forall sp s env k,
  cm_step (SKstmt (Sblock s) sp env k)
          TEtau
          (SKstmt s sp env (Kblock k))
(* Exit *)
| StepExitSeq:
  forall sp n s k env,
  cm_step (SKstmt (Sexit n) sp env (Kseq s k))
          TEtau
          (SKstmt (Sexit n) sp env k)
| StepExitBlock:
  forall sp env k,
  cm_step (SKstmt (Sexit 0) sp env (Kblock k))
          TEtau
          (SKstmt Sskip sp env k)
| StepExitBlock1:
  forall sp n env k,
  cm_step (SKstmt (Sexit (S n)) sp env (Kblock k))
          TEtau
          (SKstmt (Sexit n) sp env k)
(* Switch *)
| StepSwitch:
  forall sp e cases default env k,
  cm_step (SKstmt (Sswitch e cases default) sp env k)
          TEtau
          (SKexpr e sp env (EKswitch cases default k))
(* Select *)
| StepSelect:
  forall sp n cases default env k,
  cm_step (SKval (Vint n) sp env (EKswitch cases default k))
          TEtau
          (SKstmt (Sexit (switch_target n default cases)) sp env k)
(* Label *)
| StepLabel:
  forall sp lbl s env k,
  cm_step (SKstmt (Slabel lbl s) sp env k)
          TEtau
          (SKstmt s sp env k)
(* Goto *)
| StepGoto:
  forall sp f lbl k s' k' k'' env
  (CC : call_cont k = k')
  (GFD : get_fundef k' = (Some (Internal f)))
  (FL : find_label lbl f.(fn_body) k' = Some (s', k'')),
  cm_step (SKstmt (Sgoto lbl) sp env k)
          TEtau
          (SKstmt s' sp env k'')
(* Return *)
| StepReturnNone:
  forall sp sp' f k k' env env' lab
  (CC : call_cont k = (Kcall None (Internal f) sp' env' k'))
  (FSIG : f.(fn_sig).(sig_res) = None),
  lab = (match sp with 
           None => TEtau | 
           Some stk => TEmem (MEfree stk MObjStack) end) ->
  cm_step (SKstmt (Sreturn None) sp env k)
          lab
          (SKreturn Vundef k)
| StepReturnSome:
  forall sp e f k env
  (CC : get_fundef (call_cont k) = Some (Internal f))
  (FSIG : f.(fn_sig).(sig_res) <> None),
  cm_step (SKstmt (Sreturn (Some e)) sp env k)
          TEtau
          (SKexpr e sp env (EKreturn k))
| StepReturnSome1:
  forall sp v k env lab,
  lab = (match sp with 
           None => TEtau | 
           Some stk => TEmem (MEfree stk MObjStack) end) ->
  cm_step (SKval v sp env (EKreturn k))
          lab
          (SKreturn v k)
| StepReturnFinish:
  forall sp v fd optid k k' env' env''
  (CC : call_cont k = (Kcall optid fd sp env' k'))
  (VLS : set_optvar optid v env' = env''),
  cm_step (SKreturn v k)
          TEtau
          (SKstmt Sskip sp env'' k')
(* Internal Call *)
| StepFunctionInternalNoStack:
  forall sp optid f vs k env env' ck
  (CC : ck  = (Kcall optid (Internal f) sp env' k))
  (FZ : f.(fn_stackspace) = 0)
  (INIT : set_locals f.(fn_vars) (set_params vs f.(fn_params)) = env),
  cm_step (SKcall vs ck)
          TEtau
          (SKstmt f.(fn_body) None env ck)
| StepFunctionInternalWithStack:
  forall sp optid p f vs k env env' ck fsize
  (CC : ck  = (Kcall optid (Internal f) sp env' k))
  (EQfsize : fsize = f.(fn_stackspace))
  (FNZ : fsize <> 0)
  (INIT : set_locals f.(fn_vars) (set_params vs f.(fn_params)) = env),
  cm_step (SKcall vs ck)
          (TEmem (MEalloc p (Int.repr fsize) MObjStack))
          (SKstmt f.(fn_body) (Some p) env ck)
(* External Call *)
| StepExternalCall:
  forall sp k ef vargs evargs tgt env id efsig ck
  (EARGS : vargs = map val_of_eval evargs),
  id = ef.(ef_id) ->
  efsig = ef.(ef_sig) ->
  ck = (Kcall tgt (External ef) sp env k) ->
  cm_step (SKcall vargs ck)
          (TEext (Ecall id evargs))
          (SKexternal efsig ck)
| StepExternalReturn:
  forall efsig vres evres k typ
  (TYP : typ = (match sig_res efsig with Some x => x | None => Tint end))
  (HT : Val.has_type vres typ)
  (ERES : vres = val_of_eval evres),
  cm_step (SKexternal efsig k)
          (TEext (Ereturn typ evres))
          (SKreturn vres k)
(* Continuation Management *)
| StepNext:
  forall sp s k env,
  cm_step (SKstmt Sskip sp env (Kseq s k))
          TEtau
          (SKstmt s sp env k)
| StepStop:
  forall sp env,
  cm_step (SKstmt Sskip sp env Kstop)
          TEexit
         (SKstmt Sskip sp env Kstop)
(* Thread *)
| StepThread : 
  forall sp efn earg k env,
  cm_step (SKstmt (Sthread_create efn earg) sp env k)
          TEtau
          (SKexpr efn sp env (EKthread1 earg k))
| StepThreadFn:
  forall sp earg p k env,
  cm_step (SKval (Vptr p) sp env (EKthread1 earg k))
          TEtau
          (SKexpr earg sp env (EKthread2 p k))
| StepThreadEvt : 
  forall sp p v k env,
  cm_step (SKval v sp env (EKthread2 p k))
          (TEstart p (v::nil))
          (SKstmt Sskip sp env k).

Definition cm_init  (p : pointer) (vs : list val) : option state :=
  match Genv.find_funct_ptr ge p with
   | Some (Internal f)  => 
       if beq_nat (length vs) (length f.(fn_sig).(sig_args))
         then Some (SKcall (Val.conv_list vs f.(fn_sig).(sig_args))
                           (Kcall None (Internal f) None (PTree.empty _) Kstop))
         else None
   | _ => None
  end.

End RELSEM.

Open Scope string_scope.
Open Scope list_scope.

Tactic Notation "cm_step_cases" tactic(first) tactic(c) :=
    first; [
      c "StepVar" |
      c "StepConst" |
      c "StepUnop1" |
      c "StepUnop" |
      c "StepBinop1" |
      c "StepBinop2" |
      c "StepBinop" |
      c "StepLoad1" |
      c "StepLoad" |
      c "StepIfThenElse" |
      c "StepIfThenElseTrue" |
      c "StepIfThenElseFalse" |
      c "StepSkipBlock" |
      c "StepAssign1" |
      c "StepAssign" |
      c "StepStore1" |
      c "StepStore2" |
      c "StepStore" |
      c "StepCall" |
      c "StepEmptyCall" |
      c "StepCallArgs1" |
      c "StepCallArgs2" |
      c "StepCallArgs" |
      c "StepAtomic" |
      c "StepAtomicArgs" |
      c "StepAtomicFinishNone" |
      c "StepAtomicFinishSome" |
      c "StepFence" |
      c "StepSeq" |
      c "StepCond" |
      c "StepCondTrue" |
      c "StepCondFalse" |
      c "StepLoop" |
      c "StepBlock" |
      c "StepExitSeq" |
      c "StepExitBlock" |
      c "StepExitBlock1" |
      c "StepSwitch" |
      c "StepSelect" |
      c "StepLabel" |
      c "StepGoto" |
      c "StepReturnNone" |
      c "StepReturnSome" |
      c "StepReturnSome1" |
      c "StepReturnFinish" |
      c "StepFunctionInternalNoStack" |
      c "StepFunctionInternalWithStack" |
      c "StepExternalCall" |
      c "StepExternalReturn" |
      c "StepNext" |
      c "StepStop" |
      c "StepThread" |
      c "StepThreadFn" |
      c "StepThreadEvt"].

Hint Constructors cm_step: cminor. 

Definition cm_ge_init (p : program) (ge : genv) (m : Mem.mem) := 
  Genv.globalenv_initmem p ge low_mem_restr m.

(** * TSO machine setup *)

Section Cminor_TSO.

Lemma cm_receptive :
  forall ge l l' s s', 
    cm_step ge s l s' -> 
    te_samekind l' l ->
    exists s'', cm_step ge s l' s''.
Proof. 
  intros g l l' s s' Step Te_Samekind. 
  (inversion Step);
     subst;
     destruct l' as [[] | [] | | | | | |];
     simpl in *;
     try done;
     try rewrite Te_Samekind; 
     try (decompose [and] Te_Samekind; subst);
     eauto with cminor;
     try (by destruct sp).
Qed.

(*
Ltac rewrite_right_aux_tac :=
  match goal with
    | H' : ?a = ?b, H'' : ?a = ?c |- ?P => 
      rewrite H' in H''; (discriminate || (inversion H''; subst; auto))
  end.
*)

Lemma bool_of_val_contr:
  forall v,
    Val.bool_of_val v true -> Val.bool_of_val v false -> False.
Proof.
  intros v BVT BVF.
  inversion BVT; inversion BVF as [ | EQ |]; subst; try done. inv EQ. done.
Qed.


Ltac determinate_aux_tac :=
  repeat match goal with
    | H' : Val.bool_of_val ?v true,
      H'' : Val.bool_of_val ?v false |- ?P =>
        pose proof (bool_of_val_contr _ H' H''); contradiction
    | H' : ?a = ?b, H'' : ?a = ?c |- ?P => 
      rewrite H' in H''; (discriminate || (inversion H''; subst; auto))
    | H' : Kcall _ _ _ _ _ = Kcall _ _ _ _ _ |- ?P => inv H'; clarify
    | H : map val_of_eval ?x = map val_of_eval ?y |- _ => 
        rewrite (map_val_of_eval_eq H); done
  end.

Lemma cm_determinate:
  forall ge s s' s'' l l',
    cm_step ge s l s' ->
    cm_step ge s l' s'' ->
    (te_samekind l l' /\ (l = l' -> s' = s'')).
Proof.
  intros g s s' s'' l l' ST1 ST2; split.
  by destruct ST1; inv ST2; clarify; determinate_aux_tac; try done;
     try destruct sp.
  by intro; subst; destruct ST1; inv ST2; clarify; determinate_aux_tac. 
Qed.  

Require Import Classical.

Lemma cm_progress_dec:
    forall ge s, (forall s' l', ~ cm_step ge s l' s') \/
      (exists l', exists s', cm_step ge s l' s').
Proof.
  intros g s.
  set (P := exists l' : thread_event, exists s' : state, cm_step g s l' s').
  destruct (classic P). auto. 
  left. intros s' l'. revert s'. apply not_ex_all_not. 
  revert l'. apply not_ex_all_not. auto.
Qed.

Definition cm_sem : SEM := 
  mkSEM state _ program 
  cm_ge_init (@prog_main _ _) (fun ge => Genv.find_symbol ge) 
  cm_step cm_init cm_progress_dec cm_receptive cm_determinate.

End Cminor_TSO.
