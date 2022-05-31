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
Require Import Floats.
Require Import Values.
Require Import Pointers.
Require Import Events.
Require Import Globalenvs.
Require Import Libtactics.
Require Import Memcomp.
Require Import Cminorgen.
Require Import Csharpminor.
Require Cminorops.

Definition unary_operation := Cminorops.unary_operation.
Definition binary_operation := Cminorops.binary_operation.
Definition atomic_statement := Cminorops.atomic_statement.
Definition eval_unop := Cminorops.eval_unop.
Definition eval_binop := Cminorops.eval_binop.

Section RELSEM.

Definition genv := Genv.t fundef.

Definition gvarenv := PTree.t var_kind.

Inductive env_item :=
| Env_local: val -> memory_chunk -> env_item
| Env_stack_scalar: memory_chunk -> Z -> env_item
| Env_stack_array: Z -> env_item.

Record env := mkcsenv {
  csenv_sp  : option pointer;
  csenv_env : PTree.t env_item 
}.

Fixpoint build_envmap (vars : list (ident * var_kind)) 
                      (cenv : compilenv) 
                      (acc  : PTree.t env_item) 
                   : option (PTree.t env_item) :=
  match vars with
    | nil => Some acc
    | (id, vi) :: t => 
        match PMap.get id cenv with
          | Var_local c' => 
            build_envmap t cenv (PTree.set id (Env_local Vundef c') acc)
          | Var_stack_scalar c' si => 
            build_envmap t cenv (PTree.set id (Env_stack_scalar c' si) acc)
          | Var_stack_array si => 
            build_envmap t cenv (PTree.set id (Env_stack_array si) acc)
          | _ => None
        end
  end.

Definition build_env (f : function) : option (PTree.t env_item * Z) :=
  let (cenv, fsz) := build_compilenv (PMap.init Var_global_array) f in
    match build_envmap (fn_variables f) cenv (PTree.empty env_item) with
      | Some e => Some (e, fsz)
      | None => None
    end.

(** Continuations *)

Inductive cont: Type :=
  | Kstop: cont                         (**r stop program execution *)
  | Kseq: stmt -> cont -> cont          (**r execute stmt, then cont *)
  | Kblock: cont -> cont                (**r exit a block, then do cont *)
  | Kcall: option ident -> fundef -> env -> cont -> cont. (**r return to caller *)

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
  | EKswitch: lbl_stmt -> cont -> expr_cont
  | EKreturn: cont -> expr_cont
  | EKstoreaddr: memory_chunk -> expr -> cont -> expr_cont
  | EKstoreval: memory_chunk -> val -> cont -> expr_cont.

Inductive state : Type :=
  | SKexpr : expr -> env -> expr_cont -> state
  | SKval : val -> env -> expr_cont -> state
  | SKstmt : stmt -> env -> cont -> state 
  | SKcall : list val -> cont -> state
  | SKfree : option pointer -> option val -> cont -> state
  | SKreturn : option val -> cont -> state  
  | SKbind : function -> list val -> list ident ->  env -> cont -> state
  | SKexternal: signature -> option ident -> env -> cont -> state
  | SKexternalReturn: option ident -> val -> env -> cont -> state.

(** Pop continuation until a call or stop *)

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kseq s k => call_cont k
  | Kblock k => call_cont k
  | _ => k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ => True
  | _ => False
  end.

Definition get_fundef (k: cont) : option fundef :=
  match k with
   | Kcall op fd e k => (Some fd)
   | _ => None
  end.

(** Resolve [switch] statements. *)

Fixpoint select_switch (n: int) (sl: lbl_stmt) {struct sl} : lbl_stmt :=
  match sl with
  | LSdefault _ => sl
  | LScase c s sl' => if Int.eq c n then sl else select_switch n sl'
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
  | Sswitch a sl =>
      find_label_ls lbl sl k
  | Slabel lbl' s' =>
      if ident_eq lbl lbl' then Some(s', k) else find_label lbl s' k
  | _ => None
  end

with find_label_ls (lbl: label) (sl: lbl_stmt) (k: cont) 
                   {struct sl}: option (stmt * cont) :=
  match sl with
  | LSdefault s => find_label lbl s k
  | LScase _ s sl' =>
      match find_label lbl s (Kseq (seq_of_lbl_stmt sl') k) with
      | Some sk => Some sk
      | None => find_label_ls lbl sl' k
      end
  end.

(** Evaluation of operator applications. *)

Definition eval_constant (cst: constant) : option val :=
  match cst with
  | Ointconst n => Some (Vint n)
  | Ofloatconst n => Some (Vfloat n)
  end.

(** Initialization of local variables that are parameters.  The value
  of the corresponding argument is stored into the memory block
  bound to the parameter. *)

Variable globenv : genv * gvarenv.
Definition ge : genv := fst globenv.
Definition gvare : gvarenv := snd globenv.

(* Evaluation of the address of a variable: 
   [eval_var_addr prg ge e id b] states that variable [id] 
   in environment [e] evaluates to block [b]. *)

Inductive eval_var_addr: env -> ident -> pointer -> Prop :=
  | eval_var_addr_local:
      forall e id sp c offs
      (EG : PTree.get id e.(csenv_env) = Some(Env_stack_scalar c offs))
      (EB : e.(csenv_sp) = Some sp),
      eval_var_addr e id (MPtr.add sp (Int.repr offs))
  | eval_var_addr_array:
      forall e id sp offs
      (EG : PTree.get id e.(csenv_env) = Some(Env_stack_array offs))
      (EB : e.(csenv_sp) = Some sp),
      eval_var_addr e id (MPtr.add sp (Int.repr offs))
  | eval_var_addr_global:
      forall e id p
      (EGN : PTree.get id e.(csenv_env) = None)
      (GFF : Genv.find_symbol ge id = Some p),
      eval_var_addr e id p.

(* Evaluation of a reference to a local scalar variable:
   [eval_var_ref prg ge e id b chunk] states
   that variable [id] in environment [e] evaluates to pointer [p]
   and is associated with the memory chunk [chunk]. *)

Inductive eval_var_local : env -> ident -> val -> Prop :=
  | eval_var_loc:
      forall e id v c
      (EG : PTree.get id e.(csenv_env) = Some (Env_local v c)),
      eval_var_local e id v.

Inductive var_local_store : env -> ident -> val -> env -> Prop :=
  | var_loc_store:
      forall e id vold v c
      (EG : PTree.get id e.(csenv_env) = Some (Env_local vold c)),
      var_local_store e id v (mkcsenv e.(csenv_sp) 
        (PTree.set id (Env_local (Val.load_result c v) c) e.(csenv_env))).

Inductive eval_var_ref: env -> ident -> pointer -> memory_chunk -> Prop :=
  | eval_var_ref_local:
      forall e id chunk offs sp
      (EG : PTree.get id e.(csenv_env) = Some(Env_stack_scalar chunk offs))
      (EB : e.(csenv_sp) = Some sp),
        eval_var_ref e id (MPtr.add sp (Int.repr offs)) chunk
  | eval_var_ref_global:
      forall e id p chunk
      (EG : PTree.get id e.(csenv_env) = None)
      (GFF : Genv.find_symbol ge id = Some p)
      (EGS : PTree.get id gvare = Some (Vscalar chunk)),
        eval_var_ref e id p chunk.

Inductive cst_step : state -> thread_event -> state -> Prop :=
(* Var *)
| StepVarLocal:
  forall id v env k
  (EVL : eval_var_local env id v),
  cst_step (SKexpr (Evar id) env k)
          TEtau
          (SKval v env k)
| StepVarStack:
  forall id p chunk v env k
  (EVR : eval_var_ref env id p chunk)
  (HT : Val.has_type v (type_of_chunk chunk)),
  cst_step (SKexpr (Evar id) env k)
          (TEmem (MEread p chunk v))
          (SKval v env k)
(* Addrof *)
| StepAddrOf:
  forall id p env k
  (EVA : eval_var_addr env id p),
  cst_step (SKexpr (Eaddrof id) env k)
          TEtau
          (SKval (Vptr p) env k)
(* Const *)
| StepConst:
  forall cst v env k
  (EC : eval_constant cst = Some v),
  cst_step (SKexpr (Econst cst) env k)
          TEtau
          (SKval v env k)
(* Unop *)
| StepUnop1:
  forall op e k env,
  cst_step (SKexpr (Eunop op e) env k)
          TEtau
          (SKexpr e env (EKunop op k))
| StepUnop:
  forall v v' op k env
  (EU : eval_unop op v = Some v'),
  cst_step (SKval v env (EKunop op k))
          TEtau
          (SKval v' env k)
(* Binop *)
| StepBinop1:
  forall op e1 e2 env k,
  cst_step (SKexpr (Ebinop op e1 e2) env k)
          TEtau
          (SKexpr e1 env (EKbinop1 op e2 k))
| StepBinop2:
  forall op v e2 env k,
  cst_step (SKval v env (EKbinop1 op e2 k))
          TEtau
          (SKexpr e2 env (EKbinop2 op v k))
| StepBinop:
  forall op v v1 v2 env k
  (EB : eval_binop op v1 v2 = Some v),
  cst_step (SKval v2 env (EKbinop2 op v1 k))
          TEtau
          (SKval v env k)
(* Load *)
| StepLoad1:
  forall c e env k,
  cst_step (SKexpr (Eload c e) env k)
          TEtau
          (SKexpr e env (EKload c k))
| StepLoad:
  forall p v c env k
  (HT : Val.has_type v (type_of_chunk c)),
  cst_step (SKval (Vptr p) env (EKload c k))
          (TEmem (MEread p c v))
          (SKval v env k)
(* Conditional *)
| StepIfThenElse:
  forall e1 e2 e3 k env,
  cst_step (SKexpr (Econdition e1 e2 e3) env k)
          TEtau
          (SKexpr e1 env (EKcond e2 e3 k)) 
| StepIfThenElseTrue:
  forall v e1 e2 k env
  (BOV : Val.bool_of_val v true),
  cst_step (SKval v env (EKcond e1 e2 k))
       TEtau
       (SKexpr e1 env k)
| StepIfThenElseFalse:
  forall v e1 e2 k env
  (BOV : Val.bool_of_val v false),
  cst_step (SKval v env (EKcond e1 e2 k))
          TEtau
          (SKexpr e2 env k)
(* Skip *)
| StepSkipBlock:
  forall k env,
  cst_step (SKstmt Sskip env (Kblock k))
          TEtau
          (SKstmt Sskip env k)
(* Assign *)
| StepAssign1:
  forall id e env k,
  cst_step (SKstmt (Sassign id e) env k)
          TEtau
          (SKexpr e env (EKassign id k))
| StepAssignEnv:
  forall v id p chunk env k
  (EVR: eval_var_ref env id p chunk),
  cst_step (SKval v env (EKassign id k))
          (TEmem (MEwrite p chunk (cast_value_to_chunk chunk v)))
          (SKstmt Sskip env k)
| StepAssignLocal:
  forall v id env env' k
  (VLS : var_local_store env id v env'),
  cst_step (SKval v env (EKassign id k))
          TEtau
          (SKstmt Sskip env' k)
(* Store *)
| StepStore1:
  forall chunk e1 e2 env k,
  cst_step (SKstmt (Sstore chunk e1 e2) env k)
          TEtau
          (SKexpr e1 env (EKstoreaddr chunk e2 k))
| StepStore2:
  forall ptr chunk e2 env k,
  cst_step (SKval ptr env (EKstoreaddr chunk e2 k))
          TEtau
          (SKexpr e2 env (EKstoreval chunk ptr k))
| StepStore:
  forall v chunk ptr env k,
  cst_step (SKval v env (EKstoreval chunk (Vptr ptr) k))
          (TEmem (MEwrite ptr chunk (cast_value_to_chunk chunk v)))
          (SKstmt Sskip env k)
(* Call *)
| StepCall:
  forall optid sig e args env k,
  cst_step (SKstmt (Scall optid sig e args) env k)
          TEtau
          (SKexpr e env (EKcall optid sig args k))
| StepEmptyCall:
  forall vf fd sig optid env k
  (GFF : Genv.find_funct ge vf = Some fd)
  (FSIG : funsig fd = sig),
  cst_step (SKval vf env (EKcall optid sig nil k))
          TEtau
          (SKcall nil (Kcall optid fd env k))
| StepCallArgs1:
  forall vf (*fd*) optid sig arg1 args env k,
  (*GFF : Genv.find_funct ge vf = Some fd*)
  cst_step (SKval vf env (EKcall optid sig (arg1 :: args) k))
          TEtau
          (SKexpr arg1 env (EKargs optid vf sig args nil k))
| StepCallArgs2:
  forall v vs vf optid arg1 args env sig k,
  cst_step (SKval v env (EKargs optid vf sig (arg1 :: args) vs k))
          TEtau
          (SKexpr arg1 env (EKargs optid vf sig args (List.app vs (v::nil)) k))
| StepCallArgs:
  forall v vs vf fd optid env sig k
  (FSIG : funsig fd = sig),
  Genv.find_funct ge vf = Some fd ->  
  cst_step (SKval v env (EKargs optid vf sig nil vs k))
          TEtau
          (SKcall (List.app vs (v :: nil)) (Kcall optid fd env k))
(* Atomics *)
| StepAtomic : forall optid astmt e es k env,
  cst_step (SKstmt (Satomic optid astmt  (e :: es)) env k)  
           TEtau
           (SKexpr e env  (EKatargs optid astmt es nil k )  )
| StepAtomicArgs : forall v optid astmt vs e es k env,
  cst_step (SKval v env  (EKatargs optid astmt (e :: es) vs  k))  
           TEtau
           (SKexpr e env  (EKatargs optid astmt es (vs ++ v :: nil) k)) 
| StepAtomicFinishNone : forall v astmt vs k env p v' rmwi,
  Cminorops.sem_atomic_statement astmt ( vs ++ v :: nil ) = Some (p, rmwi)  ->
  Val.has_type v' (type_of_chunk Mint32)  ->
  cst_step (SKval v env  (EKatargs  None  astmt nil vs k))  
           (TEmem  (MErmw p Mint32 v' rmwi))  
           (SKstmt Sskip env k)
| StepAtomicFinishSome : forall v id astmt vs k env p v' rmwi,
  Cminorops.sem_atomic_statement astmt ( vs ++ v :: nil ) = Some (p, rmwi)  ->
  Val.has_type v' (type_of_chunk Mint32)  ->
  cst_step (SKval v env  (EKatargs  (Some id)  astmt nil vs k))  
           (TEmem  (MErmw p Mint32 v' rmwi))  
           (SKval v' env (EKassign id k) )
| StepFence : forall k env,
  cst_step (SKstmt Smfence env k)  
           (TEmem MEfence)
           (SKstmt Sskip env k)
(* Seq *)
| StepSeq:
  forall s1 s2 env k,
  cst_step (SKstmt (Sseq s1 s2) env k)
          TEtau
          (SKstmt s1 env (Kseq s2 k))
(* Conditional Statement *)
| StepCond:
  forall e s1 s2 env k,
  cst_step (SKstmt (Sifthenelse e s1 s2) env k)
          TEtau
          (SKexpr e env (EKcondstmt s1 s2 k))
| StepCondTrue:
  forall v s1 s2 env k
  (BOV : Val.bool_of_val v true),
  cst_step (SKval v env (EKcondstmt s1 s2 k))
          TEtau
          (SKstmt s1 env k) 
| StepCondFalse:
  forall v s1 s2 env k
  (BOV : Val.bool_of_val v  false),
  cst_step (SKval v env (EKcondstmt s1 s2 k))
          TEtau
          (SKstmt s2 env k) 
(* Loop *)
| StepLoop:
  forall s env k,
  cst_step (SKstmt (Sloop s) env k)
          TEtau
          (SKstmt s env (Kseq (Sloop s) k)) 
(* Block *)
| StepBlock:
  forall s env k,
  cst_step (SKstmt (Sblock s) env k)
          TEtau
          (SKstmt s env (Kblock k))
(* Exit *)
| StepExitSeq:
  forall n s k env,
  cst_step (SKstmt (Sexit n) env (Kseq s k))
          TEtau
          (SKstmt (Sexit n) env k)
| StepExitBlock:
  forall env k,
  cst_step (SKstmt (Sexit 0) env (Kblock k))
          TEtau
          (SKstmt Sskip env k)
| StepExitBlock1:
  forall n env k,
  cst_step (SKstmt (Sexit (S n)) env (Kblock k))
          TEtau
          (SKstmt (Sexit n) env k)
(* Switch *)
| StepSwitch:
  forall e cases env k,
  cst_step (SKstmt (Sswitch e cases) env k)
          TEtau
          (SKexpr e env (EKswitch cases k))
(* Select *)
| StepSelect:
  forall n cases env k,
  cst_step (SKval (Vint n) env (EKswitch cases k))
          TEtau
          (SKstmt (seq_of_lbl_stmt (select_switch n cases)) env k)
(* Label *)
| StepLabel:
  forall lbl s env k,
  cst_step (SKstmt (Slabel lbl s) env k)
          TEtau
          (SKstmt s env k)
(* Goto *)
| StepGoto:
  forall f lbl k s' k' k'' env
  (CC : call_cont k = k')
  (GFD : get_fundef k' = (Some (Internal f)))
  (FL : find_label lbl f.(fn_body) k' = Some (s', k'')),
  cst_step (SKstmt (Sgoto lbl) env k)
          TEtau
          (SKstmt s' env k'')
(* Return *)
| StepReturnNone:
  forall f k k' env env'
  (CC : call_cont k = (Kcall None (Internal f) env' k'))
  (FSIG : f.(fn_sig).(sig_res) = None),
  cst_step (SKstmt (Sreturn None) env k)
          TEtau
          (SKfree env.(csenv_sp) None k)
| StepReturnFree:
  forall p k v,
  cst_step (SKfree (Some p) v k)
          (TEmem (MEfree p MObjStack))
          (SKreturn v k)
| StepReturnNoFree:
  forall k v,
  cst_step (SKfree None v k)
          TEtau
          (SKreturn v k)
| StepReturnNoneFinish:
  forall env' k k' fd optv
  (CC : call_cont k = (Kcall None fd env' k')),
  cst_step (SKreturn optv k)
          TEtau
          (SKstmt Sskip env' k')
| StepReturnSome:
  forall e f k env
  (CC : get_fundef (call_cont k) = Some (Internal f))
  (FSIG : f.(fn_sig).(sig_res) <> None),
  cst_step (SKstmt (Sreturn (Some e)) env k)
          TEtau
          (SKexpr e env (EKreturn k))
| StepReturnSome1:
  forall v k env,
  cst_step (SKval v env (EKreturn k))
          TEtau
          (SKfree env.(csenv_sp) (Some v) k)
| StepReturnFinishLocal:
  forall v fd id k k' env' env''
  (CC : call_cont k = (Kcall (Some id) fd env' k'))
  (VLS : var_local_store env' id v env''),
  cst_step (SKreturn (Some v) k)
          TEtau
          (SKstmt Sskip env'' k')
| StepReturnFinishStack:
  forall v c fd p id k k' env'
  (CC : call_cont k = (Kcall (Some id) fd env' k'))
  (EVR : eval_var_ref env' id p c),
  cst_step (SKreturn (Some v) k)
          (TEmem (MEwrite p c (cast_value_to_chunk c v)))
          (SKstmt Sskip env' k')
(* Internal Call *)
| StepFunctionInternalNoStack:
  forall optid f vs k env ck nenv
  (CC : ck  = (Kcall optid (Internal f) env k))
  (BE : build_env f = Some(nenv, 0))
  (ND : NoDup (List.map (@fst ident var_kind) (fn_variables f))),
  cst_step (SKcall vs ck)
          TEtau
          (SKbind f vs (map (@fst _ _) f.(fn_params))
                  (mkcsenv None nenv) ck)
| StepFunctionInternalWithStack:
  forall optid f vs k env ck nenv sp fsize
  (CC : ck  = (Kcall optid (Internal f) env k))
  (BE : build_env f = Some(nenv, fsize))
  (FNZ : fsize <> 0)
  (ND : NoDup (List.map (@fst ident var_kind) (fn_variables f))),
  cst_step (SKcall vs ck)
          (TEmem (MEalloc sp (Int.repr fsize) MObjStack))
          (SKbind f vs (map (@fst _ _ ) f.(fn_params)) 
                  (mkcsenv (Some sp) nenv) ck)
| StepBindArgsEnv:
  forall f id args env env' v vs k
  (VLS : var_local_store env id v env'),
  cst_step (SKbind f (v::vs) (id::args) env k)
          TEtau
          (SKbind f vs args env' k)
| StepBindArgsStack:
  forall f id args env v c vs k sp ofs
  (EG : env.(csenv_env) ! id = Some(Env_stack_scalar c ofs))
  (EB : env.(csenv_sp) = Some sp),
  cst_step (SKbind f (v::vs) (id::args) env k)
          (TEmem (MEwrite (MPtr.add sp (Int.repr ofs)) c (cast_value_to_chunk c v)))
          (SKbind f vs args env k)
| StepTransferFun:
  forall f k env,
  cst_step (SKbind f nil nil env k)
          TEtau
          (SKstmt f.(fn_body) env k)
(* External *)
| StepExternalCall:
  forall k ef vargs evargs tgt env
  (EARGS : vargs = map val_of_eval evargs),
  (* event_match ef vargs t vres -> *)
  cst_step (SKcall vargs (Kcall tgt (External ef) env k))
          (TEext (Ecall ef.(ef_id) evargs))
          (SKexternal ef.(ef_sig) tgt env k)
| StepExternalReturn:
  forall efsig tgt vres evres env k typ
  (TYP : typ = (match sig_res efsig with Some x => x | None => Tint end))
  (HT : Val.has_type vres typ)
  (ERES : vres = val_of_eval evres),
  cst_step (SKexternal efsig tgt env k)
          (TEext (Ereturn typ evres))
          (SKexternalReturn tgt vres env k)
| StepExternalStoreStack:
  forall vres env c p k tgt
  (EVR : eval_var_ref env tgt p c),
  cst_step (SKexternalReturn (Some tgt) vres env k)
          (TEmem (MEwrite p c (cast_value_to_chunk c vres)))
          (SKstmt Sskip env k)
| StepExternalStoreEnv:
  forall vres env env' k tgt
  (VLS : var_local_store env tgt vres env'),
  cst_step (SKexternalReturn (Some tgt) vres env k)
          TEtau
          (SKstmt Sskip env' k)
| StepExternalStoreNone:
  forall vres env k,
  cst_step (SKexternalReturn None vres env k)
          TEtau
          (SKstmt Sskip env k)
(* Continuation Management *)
| StepNext:
  forall s k env,
  cst_step (SKstmt Sskip env (Kseq s k))
          TEtau
          (SKstmt s env k)
| StepStop:
  forall env,
  cst_step (SKstmt Sskip env Kstop)
          TEexit
         (SKstmt Sskip env Kstop)
(* Thread *)
| StepThread : 
  forall efn earg k env,
  cst_step (SKstmt (Sthread_create efn earg) env k)
          TEtau
          (SKexpr efn env (EKthread1 earg k))
| StepThreadFn:
  forall earg p k env,
  cst_step (SKval (Vptr p) env (EKthread1 earg k))
          TEtau
          (SKexpr earg env (EKthread2 p k))
| StepThreadEvt : 
  forall p v k env,
  cst_step (SKval v env (EKthread2 p k))
          (TEstart p (v::nil))
          (SKstmt Sskip env k).

Definition cst_init  (p : pointer) (vs : list val) : option state :=
  match Genv.find_funct_ptr ge p with
   | Some (Internal f)  => 
       if beq_nat (length vs) (length f.(fn_sig).(sig_args))
         then Some (SKcall (Val.conv_list vs f.(fn_sig).(sig_args))
                   (Kcall None (Internal f) (mkcsenv None (PTree.empty env_item)) Kstop))
         else None
   | _ => None
  end.

End RELSEM.

Tactic Notation "cst_step_cases" tactic(first) tactic(c) :=
    first; [
      c "StepVarLocal" |
      c "StepVarStack" |
      c "StepAddrOf" |
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
      c "StepAssignEnv" |
      c "StepAssignLocal" |
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
      c "StepReturnFree" |
      c "StepReturnNoFree" |
      c "StepReturnNoneFinish" |
      c "StepReturnSome" |
      c "StepReturnSome1" |
      c "StepReturnFinishLocal" |
      c "StepReturnFinishStack" |
      c "StepFunctionInternalNoStack" |
      c "StepFunctionInternalWithStack" |
      c "StepBindArgsEnv" |
      c "StepBindArgsStack" |
      c "StepTransferFun" |
      c "StepExternalCall" |
      c "StepExternalReturn" |
      c "StepExternalStoreStack" |
      c "StepExternalStoreEnv" |
      c "StepExternalStoreNone" |
      c "StepNext" |
      c "StepStop" |
      c "StepThread" |
      c "StepThreadFn" |
      c "StepThreadEvt"].

Definition cst_ge_init (p : program) (ge : genv * gvarenv) (m : Mem.mem) := 
  Genv.globalenv_initmem p (fst ge) low_mem_restr m  /\ snd ge = global_var_env p.

(** * TSO machine setup *)

Section Cstk_TSO.

Lemma cst_receptive :
  forall ge l l' s s', 
    cst_step ge s l s' -> 
    te_samekind l' l ->
    exists s'', cst_step ge s l' s''.
Proof. 
  intros g l l' s s' Step Te_Samekind. 
  (cst_step_cases (inversion Step) Case);
     subst;
     destruct l' as [[] | [] | | | | | |];
     simpl in *;
     try done;
     try rewrite Te_Samekind; 
     try (decompose [and] Te_Samekind; subst);
     econstructor;
     try (by econstructor; try apply H0; eauto);
     try apply StepVar;
     edone.
Qed.

Ltac rewrite_right_aux_tac :=
  match goal with
    | H' : ?a = ?b, H'' : ?a = ?c |- ?P => 
      rewrite H' in H''; (discriminate || (inversion H''; subst; auto))
  end.

Lemma eval_var_ref_det:
  forall g e id c p c' p',
    eval_var_ref g e id c p ->
    eval_var_ref g e id c' p' ->
    c' = c /\ p' = p.
Proof.
  intros g e id c p c' p' EV1 EV2.
  destruct EV1; inv EV2; repeat rewrite_right_aux_tac.
Qed.

Lemma eval_var_addr_det:
  forall g e id p p',
    eval_var_addr g e id p ->
    eval_var_addr g e id p' ->
    p' = p.
Proof.
  intros g e id p p' EV1 EV2.
  destruct EV1; inv EV2; repeat rewrite_right_aux_tac.
Qed.

Lemma bool_of_val_contr:
  forall v,
    Val.bool_of_val v true -> Val.bool_of_val v false -> False.
Proof.
  intros v BVT BVF.
  inversion BVT; inversion BVF as [ | EQ |]; subst; try done. inv EQ. done.
Qed.

Lemma eval_store_ref_local_contr:
  forall ge env env' id v p c,
    var_local_store env id v env' -> 
    eval_var_ref ge env id p c ->
    False.
Proof.
  intros gen en en' id v p c LS MS.
  inv LS; inv MS; rewrite EG in *; discriminate.
Qed.

Lemma eval_var_ref_local_contr:
  forall ge env id v p c,
    eval_var_local env id v -> 
    eval_var_ref ge env id p c ->
    False.
Proof.
  intros gen en id v p c LS MS.
  inv LS; inv MS; rewrite EG in *; discriminate.
Qed.

Lemma eval_var_local_det:
  forall env id v v',
    eval_var_local env id v -> 
    eval_var_local env id v' ->
    v = v'.
Proof.
  intros en id v v' EL1 EL2.
  destruct EL1. inv EL2. rewrite_right_aux_tac.
Qed.

Lemma var_local_store_det:
  forall en id v en1 en2,
    var_local_store en id v en1 -> 
    var_local_store en id v en2 ->
    en1 = en2.
Proof.
  intros en id v en1 en2 EL1 EL2.
  destruct EL1. inv EL2. rewrite_right_aux_tac.
Qed.

Ltac determinate_aux_tac :=
  repeat match goal with
    | H' : eval_var_ref ?g ?e ?id _ _,
      H'': eval_var_ref ?g ?e ?id _ _ |- ?P =>
        destruct (eval_var_ref_det _ _ _ _ _ _ _ H' H''); subst; done
    | H' : eval_var_addr ?g ?e ?id _,
      H'': eval_var_addr ?g ?e ?id _ |- ?P =>
        rewrite (eval_var_addr_det _ _ _ _ _ H' H'') in *; done
    | H' : eval_var_local ?e ?i _,
      H'': eval_var_local ?e ?i _ |- ?P =>
        rewrite (eval_var_local_det _ _ _ _ H' H''); done
    | H' : var_local_store ?e ?i ?v _,
      H'': var_local_store ?e ?i ?v _ |- ?P =>
        rewrite (var_local_store_det _ _ _ _ _ H' H''); done
    | H' : Val.bool_of_val ?v true,
      H'' : Val.bool_of_val ?v false |- ?P =>
        pose proof (bool_of_val_contr _ H' H''); contradiction
    | H' : eval_var_local ?e ?i _,
      H'' : eval_var_ref _ ?e ?i _ _ |- ?P =>
        pose proof (eval_var_ref_local_contr _ _ _ _ _ _ H' H''); 
          contradiction
    | H' : var_local_store ?e ?i _ _,
      H'' : eval_var_ref _ ?e ?i _ _ |- ?P =>
        pose proof (eval_store_ref_local_contr _ _ _ _ _ _ _ H' H''); 
          contradiction
    | H' : ?a = ?b, H'' : ?a = ?c |- ?P => 
      rewrite H' in H''; (discriminate || (inversion H''; subst; auto))
    | H' : Kcall _ _ _ _ = Kcall _ _ _ _ |- ?P => inv H'; 
        try rewrite_right_aux_tac;
        clarify
    | H : map val_of_eval ?x = map val_of_eval ?y |- _ => 
        rewrite (map_val_of_eval_eq H); done
  end.

Lemma cst_determinate:
  forall ge s s' s'' l l',
    cst_step ge s l s' ->
    cst_step ge s l' s'' ->
    (te_samekind l l' /\ (l = l' -> s' = s'')).
Proof.
  intros g s s' s'' l l' ST1 ST2; split.
  by destruct ST1; inv ST2; clarify; determinate_aux_tac; try done;
    inv VLS; determinate_aux_tac.

  by intro; subst; destruct ST1; inv ST2; clarify; determinate_aux_tac. 
Qed.  

Require Import Classical.

Lemma cst_progress_dec:
    forall ge s, (forall s' l', ~ cst_step ge s l' s') \/
      (exists l', exists s', cst_step ge s l' s').
Proof.
  intros g s.
  set (P := exists l' : thread_event, exists s' : state, cst_step g s l' s').
  destruct (classic P). auto. 
  left. intros s' l'. revert s'. apply not_ex_all_not. 
  revert l'. apply not_ex_all_not. auto.
Qed.

Definition cst_sem : SEM := 
  mkSEM state _ program 
  cst_ge_init (@prog_main _ _) (fun ge => Genv.find_symbol (fst ge)) 
  cst_step cst_init cst_progress_dec cst_receptive cst_determinate.

End Cstk_TSO.
