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

(* This is the third third of Csem.v, from Csem3.v *)

(* preamble required for processing Csem3 interactively in isolation
Require Import Coqlib.
Require Import Values.
Require Import Pointers.
Require Import Integers.
Require Import Floats.
Require Import Events.
Require Import Ast.
Require Import Csyntax.
Require Import Globalenvs.
Require Import Errors.
Require Import Maps.
Require Import Libtactics.
Require Import Memcomp.
Require Import Mergesort.
Require Import Csemp.


Section STEP.

Variable ge: genv.
*)


Definition neutral_for_cast_dec (ty : type) : {neutral_for_cast ty} +
                                              {~ neutral_for_cast ty}.
Proof.
  intros. 
  destruct ty;
    try (destruct i); 
    try (left; constructor);
    try (right; intro H; inv H).
Defined.

Definition cast_ex (v : val) (ty ty' : type) : option val :=
  match v, ty, ty' with
    | Vint i, Tint sz1 si1, Tint sz2 si2 =>
        Some (Vint (cast_int_int sz2 si2 i))
    | Vfloat f, Tfloat sz1, Tint sz2 si2 =>
        Some (Vint (cast_int_int sz2 si2 (cast_float_int si2 f)))
    | Vint i, Tint sz1 si1, Tfloat sz2 =>
        Some (Vfloat (cast_float_float sz2 (cast_int_float si1 i)))
    | Vfloat f, Tfloat sz1, Tfloat sz2 =>
        Some (Vfloat (cast_float_float sz2 f))
    | Vptr p, _, _ =>
        if neutral_for_cast_dec ty 
          then if neutral_for_cast_dec ty'
            then Some (Vptr p)
            else None
          else None
    | Vint i, _, _ =>
        if neutral_for_cast_dec ty 
          then if neutral_for_cast_dec ty'
            then Some (Vint i)
            else None
          else None
    | _, _, _ => None
  end.

Inductive cl_step_res : Type :=
  | Rnostep : cl_step_res
  | Rsimple : thread_event -> state -> cl_step_res
  | Rread   : pointer -> memory_chunk -> (val -> state) -> cl_step_res
  | Rreturn : typ -> (val -> state) -> cl_step_res
  | Ralloc  : int -> mobject_kind -> (pointer -> state) -> cl_step_res
  | Rrmw    : pointer -> memory_chunk -> rmw_instr -> (val -> state) -> cl_step_res.


Definition eval_of_val (v : val) : option eventval :=
  match v with
    | Vint i => Some (EVint i)
    | Vfloat f => Some (EVfloat f)
    | _ => None
  end.

Fixpoint map_eval_of_val (vs : list val) : option (list eventval) :=
  match vs with
    | nil => Some nil
    | v :: r =>
        optbind 
          (fun er => option_map (fun ev => ev :: er) (eval_of_val v))
            (map_eval_of_val r)
  end.  

Definition cl_step_fn1 (s : state) : cl_step_res :=
  match s with
  | (SKexpr (Expr (Econst_int i) ty) env k) =>
      Rsimple TEtau (SKval (Vint i) env k)
  | (SKexpr (Expr (Econst_float f) ty) env k) =>
      Rsimple TEtau (SKval (Vfloat f) env k)
  | (SKexpr (Expr (Evar id) ty) env k) =>
      Rsimple TEtau (SKlval (Expr (Evar id) ty) env (EKlval ty k))
  | (SKlval (Expr (Evar id) ty) env k) =>
      match env!id with
      | Some p =>
          Rsimple TEtau (SKval (Vptr p) env k)
      | None =>
          match Genv.find_symbol ge id with
          | Some p => 
              Rsimple TEtau (SKval (Vptr p) env k)
          | None => Rnostep
          end
      end
  | (SKval (Vptr p) env (EKlval ty k)) =>
      match access_mode ty with
      | By_value c => Rread p c (fun v => SKval v env k)
      | _ => Rsimple TEtau (SKval (Vptr p) env k)
      end
  | (SKexpr (Expr (Eaddrof e) ty) env k) => Rsimple TEtau (SKlval e env k)
  | (SKexpr (Expr (Ederef e) ty) env k) => 
      Rsimple TEtau (SKexpr e env (EKlval ty k))
  | (SKlval (Expr (Ederef e) ty) env k) => 
      Rsimple TEtau (SKexpr e env k)
  | (SKexpr (Expr (Efield e i) ty) env k) =>
      Rsimple TEtau (SKlval (Expr (Efield e i) ty) env (EKlval ty k))
  | (SKlval (Expr (Efield e i) ty) env k) =>
      match typeof e with
      | Tstruct id fList => 
          match field_offset i fList with
          | OK delta =>
              Rsimple TEtau (SKlval e env (EKfield delta k))
          | _ => Rnostep
          end
      | Tunion id fList => Rsimple TEtau (SKlval e env k)
      | _ => Rnostep
      end
  | (SKval (Vptr p) env (EKfield delta k)) =>
      Rsimple TEtau (SKval (Vptr (Ptr.add p (Int.repr delta))) env k)
  | (SKexpr (Expr (Esizeof ty') ty) env k) =>
      Rsimple TEtau (SKval (Vint (Int.repr (sizeof ty'))) env k)
  | (SKexpr (Expr (Eunop op e) ty) env k) =>
      Rsimple TEtau (SKexpr e env (EKunop op (typeof e) k))
  | (SKval v env (EKunop op ty k))  =>
      match sem_unary_operation op v ty with
      | Some v' => Rsimple TEtau (SKval v' env k)
      | None => Rnostep
      end
  | (SKexpr (Expr (Ebinop op e1 e2) ty) env k) =>
      Rsimple TEtau (SKexpr e1 env (EKbinop1 op (typeof e1) (typeof e2) ty e2 k))
  | (SKval v env (EKbinop1 op ty1 ty2 ty e2 k)) =>
      if (valid_arg op ty1 ty2 v) 
         then Rsimple TEtau (SKexpr e2 env (EKbinop2 op ty1 ty2 ty v k))
         else Rnostep
  | (SKval v2 env (EKbinop2 op ty1 ty2 ty v1 k)) =>
      match sem_binary_operation op v1 ty1 v2 ty2 with 
      | Some v' => Rsimple TEtau (SKval v' env k)
      | None => Rnostep
      end
  | (SKexpr (Expr (Econdition e1 e2 e3) ty) env k) =>
      Rsimple TEtau (SKexpr e1 env (EKcondition e2 e3 (typeof e1) k))
  | (SKval v env (EKcondition e2 e3 ty k)) =>
      if eval_true v ty
         then Rsimple TEtau (SKexpr e2 env k)
         else if eval_false v ty
              then Rsimple TEtau (SKexpr e3 env k)
              else Rnostep
  | (SKexpr (Expr (Ecast ty a) ty') env k) => 
      Rsimple TEtau (SKexpr a env (EKcast (typeof a) ty k))
  | (SKexpr (Expr (Eandbool e1 e2) ty) env k) =>
      Rsimple TEtau (SKexpr (Expr (Econdition e1
                                    (Expr (Econdition e2
                                            (Expr (Econst_int (Int.repr 1)) ty)
                                            (Expr (Econst_int (Int.repr 0)) ty))
                                           ty)
                                    (Expr (Econst_int (Int.repr 0)) ty)) ty)
                        env k)
  | (SKexpr (Expr (Eorbool e1 e2) ty) env k) =>
      Rsimple TEtau (SKexpr (Expr (Econdition e1
                                    (Expr (Econst_int (Int.repr 1)) ty)
                                    (Expr
                                      (Econdition e2
                                        (Expr (Econst_int (Int.repr 1)) ty)
                                        (Expr (Econst_int (Int.repr 0)) ty))
                                      ty)) ty) env k)
  | (SKval v env (EKcast ty ty' k)) =>
      match cast_ex v ty ty' with
      | Some v' => Rsimple TEtau (SKval v' env k)
      | None => Rnostep
      end
  | (SKstmt (Sthread_create efn eargs) env k) =>
      Rsimple TEtau (SKexpr efn env (EKthread1 eargs k))
  | (SKval v env (EKthread1 eargs k)) =>
      match v with
      | Vptr p => Rsimple TEtau (SKexpr eargs env (EKthread2 p k))
      | _ => Rnostep
      end
  | (SKval v env (EKthread2 p k)) =>
      Rsimple (TEstart p (v::nil)) (SKstmt Sskip env k)
  | (SKstmt (Sassign e1 e2) env k) =>
      Rsimple TEtau (SKlval e1 env (EKassign1 e2 (typeof e1) k))
  | (SKval v env (EKassign1 e c k)) =>
      Rsimple TEtau (SKexpr e env (EKassign2 v c k))
  | (SKval v1 env (EKassign2 (Vptr p2) ty1 k)) =>
    match type_to_chunk ty1 with
      | Some c1 => Rsimple (TEmem (MEwrite p2 c1 (cast_value_to_chunk c1 v1))) (SKstmt Sskip env k)
      | None => Rnostep
    end
  | (SKstmt (Ssequence s1 s2) env k) =>
      Rsimple TEtau (SKstmt s1 env (Kseq s2 k))
  | (SKstmt (Scall None e args) env k) =>
      Rsimple TEtau (SKexpr e env (EKcall None (typeof e) args k))
  | (SKstmt (Scall (Some lhs) e args) env k) =>
      Rsimple TEtau (SKexpr e env (EKcall (Some lhs) (typeof e) args k))
  | (SKval v env (EKcall opt ty nil k)) =>
      match Genv.find_funct ge v with
      | Some fd => 
          if type_eq (type_of_fundef fd) ty
            then Rsimple TEtau (SKcall nil (Kcall opt fd env k))
            else Rnostep
      | None => Rnostep
      end
  | (SKval v env (EKcall opt ty (arg1 :: args) k)) =>
      Rsimple TEtau (SKexpr arg1 env (EKargs opt v ty nil args k))
  | (SKval v1 env (EKargs opt v ty vs (arg1 :: args) k)) =>
      Rsimple TEtau (SKexpr arg1 env (EKargs opt v ty (List.app vs (v1::nil)) args k))
  | (SKval v' env (EKargs opt v ty vs nil k)) =>
      match Genv.find_funct ge v with
      | Some fd => 
          if type_eq (type_of_fundef fd) ty
            then Rsimple TEtau (SKcall (List.app vs (v'::nil)) (Kcall opt fd env k))
            else Rnostep
      | None => Rnostep
      end
  | (SKstmt Scontinue env (Kseq s k)) =>
      Rsimple TEtau (SKstmt Scontinue env k)
  | (SKstmt Sbreak env (Kseq s k)) =>
      Rsimple TEtau (SKstmt Sbreak env k)
  | (SKstmt (Sifthenelse e1 s1 s2) env k) =>
      Rsimple TEtau (SKexpr e1 env (EKcond (typeof e1) s1 s2 k))
  | (SKval v env (EKcond ty s1 s2 k)) =>
      if eval_true v ty 
        then Rsimple TEtau (SKstmt s1 env k)
        else if eval_false  v ty
          then Rsimple TEtau (SKstmt s2 env k)
          else Rnostep
(* atomics *)
  | SKstmt (Satomic lhs astmt (e :: es)) env k =>
    Rsimple TEtau (SKexpr e env (EKatargs lhs astmt nil es k))

  | SKval v env  (EKatargs lhs astmt vs  (e::es) k) =>
    Rsimple TEtau (SKexpr e env  (EKatargs lhs astmt  (vs ++ v :: nil) es k))

  | SKval v env (EKatargs None astmt vs nil k) =>
    match sem_atomic_statement astmt (vs ++ v :: nil) with
      | None => Rnostep
      | Some (p, rmwi) =>
        Rrmw p Mint32 rmwi (fun v' => SKstmt Sskip env k)
    end

  | SKval v env (EKatargs (Some (id, ty)) astmt vs nil k) =>
    match sem_atomic_statement astmt (vs ++ v :: nil) with
      | None => Rnostep
      | Some (p, rmwi) =>
        Rrmw p Mint32 rmwi (fun v' => SKoptstorevar (Some (id, ty)) v' env k)
    end

  | SKstmt Smfence env k => 
      Rsimple (TEmem MEfence) (SKstmt Sskip env k)

(* while *)
  | (SKstmt (Swhile e s) env k) =>
      Rsimple TEtau (SKexpr e env (EKwhile e s k))

  | (SKval v env (EKwhile e s k)) =>
      if eval_true v (typeof e) 
        then Rsimple TEtau (SKstmt s env (Kwhile e s k))
        else if eval_false  v (typeof e)
          then Rsimple TEtau (SKstmt Sskip env k)
          else Rnostep

  | (SKstmt Scontinue env (Kwhile e s k)) =>
      Rsimple TEtau (SKstmt (Swhile e s) env k)

  | (SKstmt Sbreak env (Kwhile e s k)) =>
      Rsimple TEtau (SKstmt Sskip env k)

(* dowhile *)

  | (SKstmt (Sdowhile e s) env k) =>
      Rsimple TEtau (SKstmt s env (Kdowhile s e k))

  | (SKval v env (EKdowhile s e k)) =>
      if eval_true v (typeof e) 
        then Rsimple TEtau (SKstmt (Sdowhile e s) env k)
        else if eval_false  v (typeof e)
          then Rsimple TEtau (SKstmt Sskip env k)
          else Rnostep

  | (SKstmt Scontinue env (Kdowhile s e k)) =>
      Rsimple TEtau (SKexpr e env (EKdowhile s e k))

  | (SKstmt Sbreak env (Kdowhile s e k)) =>
      Rsimple TEtau (SKstmt Sskip env k)

(* for *)
  | (SKstmt (Sfor s1 e2 s3 s) env k) =>
      Rsimple TEtau (SKstmt s1 env (KforCond e2 s3 s k) )

  | (SKstmt Sbreak env (KforIncr e2 s3 s k)) =>
      Rsimple TEtau (SKstmt Sskip env k)

  | (SKstmt Scontinue env (KforIncr e2 s3 s k)) =>
      Rsimple TEtau (SKstmt s3 env (KforCond e2 s3 s k))

  | (SKstmt Sskip env (KforIncr e2 s3 s k)) =>
      Rsimple TEtau (SKstmt s3 env (KforCond e2 s3 s k))

  | (SKval v env (EKforTest e2 s3 s k)) =>
      if eval_true v (typeof e2) 
        then Rsimple TEtau (SKstmt s env (KforIncr e2 s3 s k) )
        else if eval_false  v (typeof e2)
          then Rsimple TEtau (SKstmt Sskip env k)
          else Rnostep
  | (SKstmt (Sreturn None) env k) =>
     match (call_cont k) with
      | (Kcall None (Internal f) envpp k') =>
          match f.(fn_return) with
          | Tvoid => Rsimple TEtau (SKstmt Sskip env (Kfree (sorted_pointers_of_env env) None k))
          | _ => Rnostep
          end
      | _ => Rnostep
      end
  | (SKstmt (Sreturn (Some e)) envp k) =>
     match (get_fundef (call_cont k)) with
     | Some (Internal fn) =>
        match fn.(fn_return) with
          | Tvoid => Rnostep
          | _ => Rsimple TEtau (SKexpr e envp (EKreturn k))
          end
      | _ => Rnostep
      end
  | (SKstmt Sskip env (Kfree (p1 :: ps) v k)) =>
      Rsimple (TEmem (MEfree p1 MObjStack)) (SKstmt Sskip env (Kfree ps v k))
  | (SKval v env (EKreturn k)) =>
      Rsimple TEtau (SKstmt Sskip env (Kfree (sorted_pointers_of_env env) (Some v) k))
  | (SKstmt (Sswitch e sl) env k) =>
      Rsimple TEtau (SKexpr e env (EKswitch sl k))
  | (SKval (Vint n) env (EKswitch sl k)) =>
      Rsimple TEtau (SKstmt (seq_of_labeled_statement (select_switch n sl)) 
                       env (Kswitch k))
  | (SKstmt Sbreak env (Kswitch k)) => Rsimple TEtau (SKstmt Sskip env k)
  | (SKstmt Scontinue env (Kswitch k)) => Rsimple TEtau (SKstmt Scontinue env k)
  | (SKstmt (Slabel lbl s) env k) =>
      Rsimple TEtau (SKstmt s env k)
  | (SKstmt (Sgoto lbl) env k)  =>
      let k1 := (call_cont k) in
      match (get_fundef k1) with
      | Some (Internal f) =>
          match find_label lbl f.(fn_body) k1 with
          | Some (s', k') => Rsimple TEtau (SKstmt s' env k')
          | None => Rnostep
          end
      | _ => Rnostep
      end
  | (SKcall vs (Kcall opt (Internal f) env k)) =>
     Rsimple TEtau
        (SKalloc vs (f.(fn_params) ++ f.(fn_vars)) empty_env 
                             (Kcall opt (Internal f) env k))
  | (SKalloc vs ((id,ty) :: args) env k) =>
      Ralloc (Int.repr(sizeof ty)) MObjStack 
           (fun p => SKalloc vs args (PTree.set id p env) k)
  | (SKalloc vs nil env (Kcall opt (Internal f) env' k)) =>
      Rsimple TEtau (SKbind f vs (f.(fn_params)) env (Kcall opt (Internal f) env' k))
  | (SKbind f (v::vs) ((id,ty)::args) env k) =>
      match PTree.get id env, type_to_chunk ty with
      | Some p, Some c => 
          Rsimple (TEmem (MEwrite p c (cast_value_to_chunk c v))) (SKbind f vs args env k)
      | _, _ => Rnostep
      end
  | (SKbind f nil nil env k) =>
      Rsimple TEtau (SKstmt f.(fn_body) env k)
  | (SKcall vs (Kcall tgt (External id targs tres) env k)) =>
      match map_eval_of_val vs with
        | Some vs => Rsimple (TEext (Ecall id vs)) (SKExternal (External id targs tres) tgt env k)
        | None => Rnostep
      end
  | (SKExternal (External id tys ty) tgt env k) =>
      match (opttyp_of_type ty) with
      | Some x =>  Rreturn x (fun vres => SKoptstorevar tgt vres env k)
      | None => Rreturn Ast.Tint (fun vres => SKoptstorevar tgt vres env k)
      end
  | (SKoptstorevar (Some(id,ty)) vres env k) =>
      match type_to_chunk ty with
      | (Some c) => match env!id with
                    | None => match Genv.find_symbol ge id with
                             | Some p => Rsimple (TEmem (MEwrite p c (cast_value_to_chunk c vres))) (SKstmt Sskip env k)
                             | None => Rnostep
                             end
                    | Some p => Rsimple (TEmem (MEwrite p c (cast_value_to_chunk c vres))) (SKstmt Sskip env k)
                    end
      | None => Rnostep
      end
  | (SKoptstorevar None vres env k) =>
      Rsimple TEtau (SKstmt Sskip env k)
  | (SKstmt Sskip env (Kseq s k)) =>
      Rsimple TEtau (SKstmt s env k)
  | (SKstmt Sskip env (Kwhile e s k)) =>
      Rsimple TEtau (SKstmt (Swhile e s) env k)
  | (SKstmt Sskip env (Kdowhile s e k)) =>
      Rsimple TEtau (SKexpr e env (EKdowhile s e k))
  | (SKstmt Sskip env (Kswitch k)) => Rsimple TEtau (SKstmt Sskip env k)
  | (SKstmt Sskip env (KforCond e2 s3 s k)) =>
      Rsimple TEtau (SKexpr e2 env (EKforTest e2 s3 s k))

(*  | (SKstmt Sskip env (KforCond e2 s3 s k)) =>
      Rsimple TEtau (SKstmt (Sifthenelse e2  (  (Ssequence  (Sdowhile (Expr (Econst_int (Int.repr 0)) (Tint I32 Signed)) s )  s3)  )  Sbreak) env (KforLoop e2 s3 s k) )
*)
  | (SKstmt Sskip env (Kfree nil None k)) =>
      match call_cont k with 
      | (Kcall None f env k') => Rsimple TEtau (SKstmt Sskip env k')
      | _ => Rnostep
      end
  | (SKstmt Sskip env' (Kfree nil (Some v) k)) =>
      match call_cont k with
      | (Kcall (Some(id,ty)) f env k') =>
          match type_to_chunk ty with
          | (Some c) => match env!id with
                        | None => match Genv.find_symbol ge id with
                                  | Some p => Rsimple (TEmem (MEwrite p c (cast_value_to_chunk c v))) 
                                                      (SKstmt Sskip env k')
                                  | _ => Rnostep
                                  end
                        | Some p => Rsimple (TEmem (MEwrite p c (cast_value_to_chunk c v))) 
                                            (SKstmt Sskip env k')
                        end
          | _ => Rnostep
          end
      | (Kcall None f env k') => Rsimple TEtau (SKstmt Sskip env k')
      | _ => Rnostep
      end
  | (SKstmt Sskip env Kstop) => Rsimple (TEexit) (SKstmt Sskip env Kstop)
  | _ => Rnostep
  end.

Definition cl_step_fn (s : state) (te : thread_event) : option state :=
  match cl_step_fn1 s with
  | Rnostep => None
  | Rsimple te' s => if thread_event_eq_dec te te' then Some s else None
  | Rread   p c f =>
      match te with
      | TEmem (MEread p' c' v) => 
           if Ptr.eq_dec p p' then 
             if memory_chunk_eq_dec c c' then 
               if Val.has_type v (type_of_chunk c) then Some (f v)
               else None
             else None
           else None
      | _ => None
      end
  | Rreturn typ f =>
      match te with
      | TEext (Ereturn typ' v) => 
          if typ_eq_dec typ typ' then
            if Val.has_type (val_of_eval v) typ 
              then Some (f (val_of_eval v))
            else None
          else None
      | _ => None
      end
  | Ralloc size k f =>
      match te with 
      | TEmem (MEalloc p size' k') =>
          if Int.eq_dec size size' 
            then if mobject_kind_eq_dec k k'
              then Some (f p) 
              else None
            else None
      | _ => None
      end
  | Rrmw p c i f => 
      match te with
      | TEmem (MErmw p' c' v i') => 
           if Ptr.eq_dec p p' then 
             if memory_chunk_eq_dec c c' then
               if rmw_instr_dec i i' then
                 if Val.has_type v (type_of_chunk c) then Some (f v)
                 else None
               else None
             else None
           else None
      | _ => None
      end    
  end.

End STEP.

(* Instantiation of the variables in the module signature SEM *)
Definition ST := state.
Definition PRG := program.
Definition GE := genv.

Definition step := cl_step.
Definition cl_ge_init (p : program) (ge : genv) (m : Mem.mem) := 
  Genv.globalenv_initmem p ge no_mem_restr m.

(* Proof of correspondence between the executable and the relational semantics *)

Ltac ite_some_asm_destruction := 
  match goal with
    | H : context[if ?E then _ else _] |- _ => destruct E; try discriminate
    | H : Some _ = Some _ |- _ => inversion H; clear H
  end.

Lemma cast_ex_some:
  forall v ty ty' v',
  cast_ex v ty ty' = Some v' ->
  cast v ty ty' v'.
Proof.
  intros v ty ty' v' CEX.
  destruct v; destruct ty; destruct ty'; try discriminate; try constructor;
    unfold cast_ex in CEX; try repeat ite_some_asm_destruction; subst; 
      try constructor; try done.
Qed.

Lemma map_eval_of_val_succ:
  forall {vs evs},
    map_eval_of_val vs = Some evs ->
    vs = map val_of_eval evs.
Proof.
  induction vs as [|v vs IH]. destruct evs; try done.
  intros evs. simpl. destruct map_eval_of_val; simpl; [|done].
  specialize (IH _ (refl_equal _)); subst.
  destruct (eval_of_val v) as [ev|] _eqn : Ev; simpl; [|done].
  intro E; inv E. simpl. 
  by destruct v; destruct ev; try done; simpl in *; inv Ev.
Qed.

Ltac asm_match_destruction := match goal with
    | H' : is_true ?a ?b, H'' : is_false ?a ?b |- ?P => 
        byContradiction; apply (is_true_is_false_contr _ _ H' H'')
    | H' : ?n <> ?n |- _ => elim H'; reflexivity
    | H : Some _ = Some _ |- _ => inversion H; clear H
    | H : neutral_for_cast (Tfloat _) |- _ => inv H
    | H': ?a = ?b |- ?P => rewrite H'
    | H': ?a = ?b \/ ?c |- ?P => destruct H'
    | H : context[match ?v with (_,_) => _ end] |- _ => destruct v as [] _eqn: ?
    | H : context[if eval_true ?E ?F then _ else _] |- _ => destruct (eval_true E F)
    | H : context[if eval_false ?E ?F then _ else _] |- _ => destruct (eval_false E F)
    | H : context[if Val.has_type ?E ?F then _ else _] |- _ => destruct (Val.has_type E F) as [] _eqn: ?
    | H : context[if valid_arg ?a ?b ?c ?d then _ else _] |- _ => destruct (valid_arg a b c d) as [] _eqn: ?; try discriminate
    | H : context[if ?v then _ else _] |- _ => destruct v; try discriminate
    | H : context[(match ?v with
          | Vundef => _ | Vint _ => _ | Vfloat _ => _ | Vptr _ => _ end)] |- _ => destruct v as [] _eqn: ?
    | H : context[(match ?v with
          | Some _ => _ | None => _ end)] |- _ => destruct v as [] _eqn: ?
    | H : context[(match ?v with
          | OK _ => _ | Error _ => _ end)] |- _ => destruct v as [] _eqn: ?
    | H : context[(match ?v with
          | Internal _ => _ | External _ _ _ => _ end)] |- _ => destruct v as [] _eqn: ?
    | H : context[(match ?v with
          | nil => _ | _::_ => _ end)] |- _ => destruct v as [] _eqn: ?
    | H : context[(match ?v with
          | Tvoid => _ | Tint _ _ => _ | Tfloat _ => _ | Tpointer _ => _
          | Tarray _ _ => _ | Tfunction _ _ => _ | Tstruct _ _ => _
          | Tunion _ _ => _ | Tcomp_ptr _ => _ end)] |- _ => destruct v as [] _eqn: ? 
    | H : context[(match ?v with
        | TEext _ => _ | TEmem _ => _ | TEtau   => _ | TEexit => _ 
        | TEstart _ _ => _ | TEstartmem _ _ => _
        | TEexternalcallmem _ _ => _
        | TEoutofmem => _ end)] |- _ => 
             destruct v as [[] |[] | | | | | |] _eqn: ?
    | H : context[(match ?v with
          | MObjStack => _ | MObjGlobal => _ | MObjHeap => _ end)] |- _ => 
             destruct v as [] _eqn: ?
    | H : context[(match ?v with 
           | By_value _ => _ | By_reference => _ 
           | By_nothing => _ end)] |- _ => destruct v as [] _eqn: ?
    | H : context[(match ?c with
            | Kstop => _
            | Kseq _ _ => _
            | Kwhile _ _ _ => _
            | Kdowhile _ _ _ => _
            | KforIncr _ _ _ _ => _
            | KforCond _ _ _ _ => _
            | Kcall _ _ _ _  =>  _
            | Kswitch _ => _
            | Kfree _ _ _ => _
            end)] |- _ => destruct c as [] _eqn: ?
    | H : map_eval_of_val _ = Some _ |- _ => rewrite (map_eval_of_val_succ H) in *
    end.

Ltac byRewriteAsm := 
  repeat match goal with
    | |- ?n <> ?m => let X := fresh in intro X; inversion X; fail
    | H: ?a = ?b |- _ => rewrite H
    | H : ?n <> ?n |- _ => elim H; reflexivity
  end.

Lemma cl_step_match_fn1:
    forall ge s l s',
      cl_step_fn ge s l = Some s' -> cl_step ge s l s'.
Proof. 

  unfold cl_step_fn.
  intros ge s l s' H.
  destruct s as [[[]] | [[]]|vv ? []|[]| | | | |]; simpl in H;
   clarify;
   try (destruct (cast_ex vv t t0) as [] _eqn : EQ; try apply cast_ex_some in EQ; clarify);
   try (destruct vv; simpl in H; clarify);
   repeat (vauto; asm_match_destruction); vauto;
  try (eapply StepReturnSome; try edone; congruence).
  (* destruct p; vauto.
  econstructor; try edone; by rewrite Heqc0. *)
  eapply StepExternalReturn; try edone. rewrite Heqo0; done.
  eapply StepExternalReturn; try edone. rewrite Heqo0; done.
Qed.

Lemma neutral_for_cast_int_cast:
  forall it s i,
    neutral_for_cast (Tint it s) ->
    cast_int_int it s i = i.
Proof.

  by inversion 1. 
Qed.

Lemma map_eval_of_val_eq:
  forall evs,
    map_eval_of_val (map val_of_eval evs) = Some evs.
Proof.
  induction evs as [|[] evs IH]; try done; simpl; rewrite IH; done.
Qed.

Ltac goal_match_destruction := match goal with
    | H': ?a = ?b \/ ?c |- ?P => destruct H'
    | H': ?a = ?b |- ?P => rewrite H'
    | |- context[if eval_true ?E ?F then _ else _]  => destruct (eval_true E F)
    | |- context[if eval_false ?E ?F then _ else _] => destruct (eval_false E F)
    | |- context[if ?E then _ else _] => destruct E; try discriminate
    | |- context[(match ?v with
          | Vundef => _ | Vint _ => _ | Vfloat _ => _ | Vptr _ => _ end)] => destruct v as [] _eqn: ?
    | |- context[(match ?v with
          | Some _ => _ | None => _ end)] => destruct v as [] _eqn: ?
    | |- context[(match ?v with
          | MObjStack => _ | MObjHeap => _ | MObjGlobal => _ end)] => 
            destruct v as [] _eqn: ?
    | |- context[(match ?v with
          | Internal _ => _ | External _ _ _ => _ end)] => destruct v as [] _eqn: ?
    | |- context[(match ?v with
          | nil => _ | _::_ => _ end)] => destruct v as [] _eqn: ?
    | |- context[(match ?v with
          | Tvoid => _ | Tint _ _ => _ | Tfloat _ => _ | Tpointer _ => _
          | Tarray _ _ => _ | Tfunction _ _ => _ | Tstruct _ _ => _
          | Tunion _ _ => _ | Tcomp_ptr _ => _ end)] => destruct v as [] _eqn: ? 
    | |- context[(match ?v with
        | TEext _ => _ | TEmem _ => _ | TEtau => _ | TEexit => _ 
        | TEstart _ _ => _ | TEstartmem _ _ => _ | TEexternalcallmem _ _
        | TEoutofmem => _ end)]
          => destruct v as [[] |[] | | | | | |] _eqn: ?
    | H' : is_true ?a ?b, H'' : is_false ?a ?b |- ?P => 
      byContradiction; apply (is_true_is_false_contr _ _ H' H'')
    | H' : ?n <> ?n |- _ => elim H'; reflexivity
    | H : Some _ = Some _ |- _ => inversion H; clear H
    | H : cast _ _ _ _ |- _ => inv H; simpl in *
    | H : context[map_eval_of_val (map val_of_eval _)] |- _ =>
      rewrite map_eval_of_val_eq in H
    | p : (ident * type)%type |- _ => destruct p 
    end.

Lemma cl_step_match_fn:
    forall ge s l s',
      cl_step ge s l s' -> cl_step_fn ge s l = Some s'.
Proof.

  unfold cl_step_fn.
  intros ge s l s' H; inversion H; subst; simpl;
    repeat goal_match_destruction; clarify; repeat asm_match_destruction; clarify.
  by rewrite neutral_for_cast_int_cast.


Qed.


Lemma cl_receptive :
  forall ge l l' s s', 
    cl_step ge s l s' -> 
    te_samekind l' l ->
    exists s'', cl_step ge s l' s''.
Proof. 

  intros ge l l' s s' Step Te_Samekind. 
  inversion Step;
     subst;
     destruct l'; try destruct ev;
     simpl in *;
     try done;
     try rewrite Te_Samekind; 
     try (decompose [and] Te_Samekind; subst);
     econstructor;
     try (by econstructor; try (eby apply H1); eauto);
     try (by eassumption).

Qed.

Lemma cl_determinate:
  forall ge s s' s'' l l',
    cl_step ge s l s' ->
    cl_step ge s l' s'' ->
    (te_samekind l l' /\
      (l = l' -> s' = s'')).
Proof.

  intros ge s s' s'' l l' ST1 ST2. 
  apply cl_step_match_fn in ST2.
  split. 
    by revert ST2; unfold cl_step_fn; destruct ST1; subst; simpl;
       try done; repeat goal_match_destruction; try done; subst; auto.

  by apply cl_step_match_fn in ST1; intro; subst; rewrite ST2 in ST1; inv ST1.

Qed.  

Require Import Classical.

Lemma cl_progress_dec:
  forall ge s, (forall s' l', ~ cl_step ge s l' s') \/
    (exists l', exists s', cl_step ge s l' s').
Proof.

  intros ge s.
  set (P := exists l' : thread_event, exists s' : state, cl_step ge s l' s').
  destruct (classic P). auto. 
  left. intros s' l'. revert s'. apply not_ex_all_not. 
  revert l'. apply not_ex_all_not. auto.
Qed.

Definition cl_sem : SEM := 
  mkSEM state genv program cl_ge_init (@prog_main _ _) (@Genv.find_symbol _) 
  cl_step cl_init cl_progress_dec cl_receptive cl_determinate.

End Clight. 




