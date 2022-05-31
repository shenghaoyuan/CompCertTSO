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

(** * Typing constraints on C programs *)

Require Import Coqlib.
Require Import Maps.
Require Import Ast.
Require Import Csyntax.

(** ** Typing rules *)

(** We now define a simple, incomplete type system for the Clight language.
  This ``type system'' is very coarse: we check only the typing properties
  that matter for the translation to be correct.  Essentially,
  we need to check that the types attached to variable references
  match the declaration types for those variables. *)

(** A typing environment maps variable names to their types. *)

Definition typenv := PTree.t type.

Section TYPING.

Variable env: typenv.

Inductive wt_expr: expr -> Prop :=
  | wt_Econst_int: forall i ty,
     wt_expr (Expr (Econst_int i) ty)
  | wt_Econst_float: forall f ty,
     wt_expr (Expr (Econst_float f) ty)
  | wt_Evar: forall id ty,
     env!id = Some ty ->
     wt_expr (Expr (Evar id) ty)
  | wt_Ederef: forall e ty,
     wt_expr e ->
     wt_expr (Expr (Ederef e) ty)
  | wt_Eaddrof: forall e ty,
     wt_expr e ->
     wt_expr (Expr (Eaddrof e) ty)
  | wt_Eunop: forall op e ty,
     wt_expr e ->
     wt_expr (Expr (Eunop op e) ty)
  | wt_Ebinop: forall op e1 e2 ty,
     wt_expr e1 -> wt_expr e2 ->
     wt_expr (Expr (Ebinop op e1 e2) ty)
  | wt_Ecast: forall e ty ty',
     wt_expr e ->
     wt_expr (Expr (Ecast ty' e) ty)
  | wt_Econdition: forall e1 e2 e3 ty,
     wt_expr e1 -> wt_expr e2 -> wt_expr e3 ->
     wt_expr (Expr (Econdition e1 e2 e3) ty)
  | wt_Eandbool: forall e1 e2 ty,
     wt_expr e1 -> wt_expr e2 ->
     wt_expr (Expr (Eandbool e1 e2) ty)
  | wt_Eorbool: forall e1 e2 ty,
     wt_expr e1 -> wt_expr e2 ->
     wt_expr (Expr (Eorbool e1 e2) ty)
  | wt_Esizeof: forall ty' ty,
     wt_expr (Expr (Esizeof ty') ty)
  | wt_Efield: forall e id ty,
     wt_expr e ->
     wt_expr (Expr (Efield e id) ty).

Inductive wt_optexpr: option expr -> Prop :=
  | wt_Enone:
      wt_optexpr None
  | wt_Esome: forall e,
      wt_expr e ->
      wt_optexpr (Some e).

Inductive wt_optexpr_lhs: option (ident * type) -> Prop :=
  | wt_Enone_lhs:
      wt_optexpr_lhs None
  | wt_Esome_lhs: forall id ty,
      env!id = Some ty ->
      wt_optexpr_lhs (Some (id,ty)).

Inductive wt_exprlist: list expr -> Prop :=
  | wt_Enil:
     wt_exprlist nil
  | wt_Econs: forall e el,
     wt_expr e -> wt_exprlist el -> wt_exprlist (e :: el).
   
Inductive wt_stmt: statement -> Prop :=
  | wt_Sskip:
     wt_stmt Sskip
  | wt_Sassign: forall e1 e2,
     wt_expr e1 -> wt_expr e2 ->
     wt_stmt (Sassign e1 e2)
  | wt_Scall: forall lhs e1 el,
     wt_optexpr_lhs lhs ->
     wt_expr e1 ->
     wt_exprlist el ->
     wt_stmt (Scall lhs e1 el)
  | wt_Ssequence: forall s1 s2,
     wt_stmt s1 -> wt_stmt s2 ->
     wt_stmt (Ssequence s1 s2)
  | wt_Siftheelse: forall e s1 s2,
     wt_expr e -> wt_stmt s1 -> wt_stmt s2 ->
     wt_stmt (Sifthenelse e s1 s2)
  | wt_Swhile: forall e s,
     wt_expr e -> wt_stmt s ->
     wt_stmt (Swhile e s)
  | wt_Sdowhile: forall e s,
     wt_expr e -> wt_stmt s ->
     wt_stmt (Sdowhile e s)
  | wt_Sfor: forall e s1 s2 s3,
     wt_expr e -> wt_stmt s1 -> wt_stmt s2 -> wt_stmt s3 ->
     wt_stmt (Sfor s1 e s2 s3)
  | wt_Sbreak:
     wt_stmt Sbreak
  | wt_Scontinue:
     wt_stmt Scontinue
  | wt_Sreturn: forall opte,
     wt_optexpr opte ->
     wt_stmt (Sreturn opte)
  | wt_Sswitch: forall e sl,
     wt_expr e -> wt_lblstmts sl ->
     wt_stmt (Sswitch e sl)
  | wt_Slabel: forall lbl s,
     wt_stmt s ->
     wt_stmt (Slabel lbl s)
  | wt_Sgoto: forall lbl,
     wt_stmt (Sgoto lbl)
  | wt_Sthread_create: forall efn earg,
     wt_expr efn -> wt_expr earg -> 
     wt_stmt (Sthread_create efn earg)
  | wt_Atomic: forall lhs a es,
     wt_optexpr_lhs lhs ->
     wt_exprlist es ->
     wt_stmt (Satomic lhs a es)
  | wt_Mfence:
     wt_stmt (Smfence)

with wt_lblstmts: labeled_statements -> Prop :=
  | wt_LSdefault: forall s,
     wt_stmt s ->
     wt_lblstmts (LSdefault s)
  | wt_LScase: forall n s sl,
     wt_stmt s -> wt_lblstmts sl ->
     wt_lblstmts (LScase n s sl).

End TYPING.

Definition add_var (env: typenv) (id_ty: ident * type) : typenv :=
  PTree.set (fst id_ty) (snd id_ty) env.

Definition add_vars (env: typenv) (vars: list(ident * type)) : typenv :=
  List.fold_left add_var vars env.

Definition var_names (vars: list(ident * type)) : list ident :=
  List.map (@fst ident type) vars.

Inductive wt_function: typenv -> function -> Prop :=
  | wt_function_intro: forall env f,
      NoDup (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
      wt_stmt (add_vars env (f.(fn_params) ++ f.(fn_vars))) f.(fn_body) ->
      wt_function env f.

Inductive wt_fundef: typenv -> fundef -> Prop :=
  | wt_fundef_Internal: forall env f,
      wt_function env f ->
      wt_fundef env (Internal f)
  | wt_fundef_External: forall env id args res,
      wt_fundef env (External id args res).

Definition add_global_var
     (env: typenv) (id_ty_init: ident * list init_data * type) : typenv :=
  match id_ty_init with (id, init, ty) => PTree.set id ty env end.

Definition add_global_vars
     (env: typenv) (vars: list(ident * list init_data * type)) : typenv :=
  List.fold_left add_global_var vars env.

Definition add_global_fun
     (env: typenv) (id_fd: ident * fundef) : typenv :=
  PTree.set (fst id_fd) (type_of_fundef (snd id_fd)) env.

Definition add_global_funs
     (env: typenv) (funs: list(ident * fundef)) : typenv :=
  List.fold_left add_global_fun funs env.

Definition global_typenv (p: program) :=
  add_global_vars (add_global_funs (PTree.empty type) p.(prog_funct)) p.(prog_vars).

Record wt_program (p: program) : Prop :=  mk_wt_program {
  wt_program_funct:
    forall id fd,
    In (id, fd) p.(prog_funct) ->
    wt_fundef (global_typenv p) fd;
  wt_program_main:
    forall fd,
    In (p.(prog_main), fd) p.(prog_funct) ->
    exists targs, type_of_fundef fd = Tfunction targs (Tint I32 Signed)
}.

(* ** Type-checking algorithm *)

(** We now define and prove correct a type-checking algorithm
  for the type system defined above. *)

Lemma eq_signedness: forall (s1 s2: signedness), {s1=s2} + {s1<>s2}.
Proof. decide equality. Qed.

Lemma eq_intsize: forall (s1 s2: intsize), {s1=s2} + {s1<>s2}.
Proof. decide equality. Qed.

Lemma eq_floatsize: forall (s1 s2: floatsize), {s1=s2} + {s1<>s2}.
Proof. decide equality. Qed.

Fixpoint eq_type (t1 t2: type) {struct t1}: bool :=
  match t1, t2 with
  | Tvoid, Tvoid => true
  | Tint sz1 sg1, Tint sz2 sg2 =>
      if eq_intsize sz1 sz2
      then if eq_signedness sg1 sg2 then true else false
      else false
  | Tfloat sz1, Tfloat sz2 =>
      if eq_floatsize sz1 sz2 then true else false
  | Tpointer u1, Tpointer u2 => eq_type u1 u2
  | Tarray u1 sz1, Tarray u2 sz2 =>
      eq_type u1 u2 && if zeq sz1 sz2 then true else false
  | Tfunction args1 res1, Tfunction args2 res2 =>
      eq_typelist args1 args2 && eq_type res1 res2
  | Tstruct id1 f1, Tstruct id2 f2 =>
      if ident_eq id1 id2 then eq_fieldlist f1 f2 else false
  | Tunion id1 f1, Tunion id2 f2 =>
      if ident_eq id1 id2 then eq_fieldlist f1 f2 else false
  | Tcomp_ptr id1, Tcomp_ptr id2 =>
      if ident_eq id1 id2 then true else false
  | _, _ => false
  end

with eq_typelist (t1 t2: typelist) {struct t1} : bool :=
  match t1, t2 with
  | Tnil, Tnil => true
  | Tcons u1 r1, Tcons u2 r2 => eq_type u1 u2 && eq_typelist r1 r2
  | _, _ => false
  end

with eq_fieldlist (f1 f2: fieldlist) {struct f1} : bool :=
  match f1, f2 with
  | Fnil, Fnil => true
  | Fcons id1 t1 r1, Fcons id2 t2 r2 =>
      if ident_eq id1 id2
      then eq_type t1 t2 && eq_fieldlist r1 r2
      else false
  | _, _ => false
  end.

Ltac TrueInv :=
  match goal with
  | [ H: ((if ?x then ?y else false) = true) |- _ ] =>
        destruct x; [TrueInv | discriminate]
  | [ H: (?x && ?y = true) |- _ ] =>
        elim (andb_prop _ _ H); clear H; intros; TrueInv
  | _ =>
        idtac
  end.

Scheme type_ind_3 := Induction for type Sort Prop
  with typelist_ind_3 := Induction for typelist Sort Prop
  with fieldlist_ind_3 := Induction for fieldlist Sort Prop.

Lemma eq_type_correct:
  forall t1 t2, eq_type t1 t2 = true -> t1 = t2.
Proof.
  apply (type_ind_3 (fun t1 => forall t2, eq_type t1 t2 = true -> t1 = t2)
                    (fun t1 => forall t2, eq_typelist t1 t2 = true -> t1 = t2)
                    (fun t1 => forall t2, eq_fieldlist t1 t2 = true -> t1 = t2));
  intros; destruct t2; simpl in *; try discriminate.
  auto.
  TrueInv. congruence.
  TrueInv. congruence.
  decEq; auto.
  TrueInv. decEq; auto.
  TrueInv. decEq; auto.
  TrueInv. subst i0. decEq; auto.
  TrueInv. subst i0. decEq; auto.
  TrueInv. congruence.
  auto.
  TrueInv. decEq; auto.
  auto.
  TrueInv. decEq; auto.
Qed.

Section TYPECHECKING.

Variable env: typenv.

Fixpoint typecheck_expr (a: Csyntax.expr) {struct a} : bool :=
  match a with
  | Expr ad aty => typecheck_exprdescr ad aty
  end

with typecheck_exprdescr (a: Csyntax.expr_descr) (ty: type) {struct a} : bool :=
  match a with
  | Csyntax.Econst_int n => true
  | Csyntax.Econst_float n => true
  | Csyntax.Evar id =>
      match env!id with
      | None => false
      | Some ty' => eq_type ty ty'
      end
  | Csyntax.Ederef b => typecheck_expr b
  | Csyntax.Eaddrof b => typecheck_expr b
  | Csyntax.Eunop op b => typecheck_expr b
  | Csyntax.Ebinop op b c => typecheck_expr b && typecheck_expr c
  | Csyntax.Ecast ty b => typecheck_expr b
  | Csyntax.Econdition b c d => typecheck_expr b && typecheck_expr c && typecheck_expr d
  | Csyntax.Eandbool b c => typecheck_expr b && typecheck_expr c
  | Csyntax.Eorbool b c => typecheck_expr b && typecheck_expr c
  | Csyntax.Esizeof ty => true
  | Csyntax.Efield b i => typecheck_expr b
  end.

Fixpoint typecheck_exprlist (al: list Csyntax.expr): bool :=
  match al with
  | nil => true
  | a1 :: a2 => typecheck_expr a1 && typecheck_exprlist a2
  end.

Definition typecheck_optexpr (opta: option Csyntax.expr): bool :=
  match opta with
  | None => true
  | Some a => typecheck_expr a
  end.

Definition typecheck_optexpr_lhs (opta: option (ident * type)): bool :=
  match opta with
  | None => true
  | Some (id,ty) => typecheck_exprdescr (Csyntax.Evar id) ty
  end.

Scheme expr_ind_2 := Induction for expr Sort Prop
  with expr_descr_ind_2 := Induction for expr_descr Sort Prop.

Lemma typecheck_expr_correct:
  forall a, typecheck_expr a = true -> wt_expr env a.
Proof.
  apply (expr_ind_2 (fun a => typecheck_expr a = true -> wt_expr env a)
                    (fun a => forall ty, typecheck_exprdescr a ty = true -> wt_expr env (Expr a ty)));
  simpl; intros; TrueInv; try constructor; auto.
  destruct (env!i). decEq; symmetry; apply eq_type_correct; auto.
  discriminate.
Qed.

Lemma typecheck_exprlist_correct:
  forall a, typecheck_exprlist a = true -> wt_exprlist env a.
Proof.
  induction a; simpl; intros.
  constructor.
  TrueInv. constructor; auto. apply typecheck_expr_correct; auto.
Qed.

Lemma typecheck_optexpr_correct:
  forall a, typecheck_optexpr a = true -> wt_optexpr env a.
Proof.
  destruct a; simpl; intros.
  constructor. apply typecheck_expr_correct; auto.
  constructor.
Qed.

Lemma typecheck_optexpr_lhs_correct:
  forall p, typecheck_optexpr_lhs p = true -> wt_optexpr_lhs env p.
Proof.
  destruct p.  destruct p; simpl; intros.
  constructor. destruct (env!i). 
  pose proof (eq_type_correct t t0). rewrite H in H0. decEq.
  intuition. inv H.
  constructor.
Qed.


Fixpoint typecheck_stmt (s: Csyntax.statement) {struct s} : bool :=
  match s with
  | Csyntax.Sskip => true
  | Csyntax.Sassign b c => typecheck_expr b && typecheck_expr c
  | Csyntax.Scall opt_lhs b cl => typecheck_optexpr_lhs opt_lhs &&
         typecheck_expr b && typecheck_exprlist cl
  | Csyntax.Ssequence s1 s2 => typecheck_stmt s1 && typecheck_stmt s2
  | Csyntax.Sifthenelse e s1 s2 =>
      typecheck_expr e && typecheck_stmt s1 && typecheck_stmt s2
  | Csyntax.Swhile e s1 => typecheck_expr e && typecheck_stmt s1
  | Csyntax.Sdowhile e s1 => typecheck_expr e && typecheck_stmt s1
  | Csyntax.Sfor e1 e2 e3 s1 =>
      typecheck_stmt e1 && typecheck_expr e2 &&
      typecheck_stmt e3 && typecheck_stmt s1
  | Csyntax.Sbreak => true
  | Csyntax.Scontinue => true
  | Csyntax.Sreturn (Some e) => typecheck_expr e
  | Csyntax.Sreturn None => true
  | Csyntax.Sswitch e sl => typecheck_expr e && typecheck_lblstmts sl
  | Csyntax.Slabel lbl s => typecheck_stmt s
  | Csyntax.Sgoto lbl => true
  | Csyntax.Sthread_create efn earg => typecheck_expr efn && typecheck_expr earg
  | Csyntax.Satomic a aop cl => typecheck_optexpr_lhs a && typecheck_exprlist cl
  | Csyntax.Smfence => true
  end    

with typecheck_lblstmts (sl: labeled_statements) {struct sl}: bool :=
  match sl with
  | LSdefault s => typecheck_stmt s
  | LScase _ s rem => typecheck_stmt s && typecheck_lblstmts rem
  end.

Scheme stmt_ind_2 := Induction for statement Sort Prop
  with lblstmts_ind_2 := Induction for labeled_statements Sort Prop.

Lemma typecheck_stmt_correct:
  forall s, typecheck_stmt s = true -> wt_stmt env s.
Proof.
  generalize typecheck_expr_correct; intro.
  generalize typecheck_exprlist_correct; intro.
  generalize typecheck_optexpr_correct; intro.
  generalize typecheck_optexpr_lhs_correct; intro.
  apply (stmt_ind_2 (fun s => typecheck_stmt s = true -> wt_stmt env s)
                    (fun s => typecheck_lblstmts s = true -> wt_lblstmts env s));
  simpl; intros;  TrueInv; try constructor; auto.
Qed.

End TYPECHECKING.

Definition typecheck_function (env: typenv) (f: function) : bool :=
  if nodup_dec ident_eq
                      (var_names f.(fn_params) ++ var_names f.(fn_vars))
  then typecheck_stmt (add_vars env (f.(fn_params) ++ f.(fn_vars)))
                      f.(fn_body)
  else false.

Lemma typecheck_function_correct:
  forall env f, typecheck_function env f = true -> wt_function env f.
Proof.
  unfold typecheck_function; intros; TrueInv.
  constructor. auto. apply typecheck_stmt_correct; auto.
Qed.

Definition typecheck_fundef (main: ident) (env: typenv) (id_fd: ident * fundef) : bool :=
  let (id, fd) := id_fd in
  match fd with
  | Internal f => typecheck_function env f
  | External _ _ _ => true
  end &&
  if ident_eq id main
  then match type_of_fundef fd with
       | Tfunction targs tres => eq_type tres (Tint I32 Signed)
       | _ => false
       end
  else true.

Lemma typecheck_fundef_correct:
  forall main env id fd,
  typecheck_fundef main env (id, fd) = true ->
  wt_fundef env fd /\
  (id = main ->
   exists targs, type_of_fundef fd = Tfunction targs (Tint I32 Signed)).
Proof.
  intros. unfold typecheck_fundef in H; TrueInv.
  split. 
    destruct fd.
    constructor. apply typecheck_function_correct; auto. 
    constructor.
  intro. destruct (ident_eq id main). 
  destruct (type_of_fundef fd); try discriminate. 
  exists t; decEq; auto. apply eq_type_correct; auto.
  congruence.
Qed.

Definition typecheck_program (p: program) : bool :=
  List.forallb (typecheck_fundef p.(prog_main) (global_typenv p))
               p.(prog_funct).

Lemma typecheck_program_correct:
  forall p, typecheck_program p = true -> wt_program p.
Proof.
  unfold typecheck_program; intros. 
  rewrite List.forallb_forall in H. 
  constructor; intros.
  exploit typecheck_fundef_correct; eauto. tauto. 
  exploit typecheck_fundef_correct; eauto. tauto. 
Qed.
