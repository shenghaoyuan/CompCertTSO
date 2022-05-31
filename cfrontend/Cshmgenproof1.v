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
(*                                                                    *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** * Correctness of the C front end, part 1: simulation relation definition *)

Require Import Coqlib.
Require Import Libtactics.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Ast.
Require Import Values.
Require Import Events.


Require Import Mem.
Require Import Memcomp.
Require Import Globalenvs.
Require Import Pointers.
Require Import Csyntax.
Require Import Csem.
Require Import Ctyping.
Require Import Cminorops.
Require Import Csharpminor.
Require Import Cshmgen.
Require Import Simulations.
Require Import Mergesort.
Require Import Permutation.

Section CLIGHT_DEFS.

Variable prog: Csyntax.program.
Variable tprog: Csharpminor.program.
Hypothesis WTPROG: wt_program prog.
Hypothesis TRANSL: transl_program prog = OK tprog.


(** Mergesort uniqueness *)

Lemma in_app_decomp:
  forall A (a : A) l,
  In a l -> exists l1, exists l2, l = l1 ++ a :: l2.
Proof.
  induction l as [|h t IH].
  done.

  simpl. intros [-> | INt].
  exists nil; exists t. done.

  destruct (IH INt) as [l1 [l2 E]].
  by exists (h :: l1); exists l2; rewrite E; rewrite app_comm_cons.
Qed.

Lemma sorted_unique:
  forall A (le : A -> A -> Prop) l l',
    (forall x y, le x y -> le y x -> x = y) ->
    Permutation l l' ->
    Sorted _ le l ->
    Sorted _ le l' ->
    l = l'.
Proof.
  intros A le l l' SYM; revert l'.
  induction l as [|h l IH].
  intros l' P S1 S2. by apply sym_eq, Permutation_nil.
  
  intros l' P S1 S2.
  destruct (in_app_decomp _ _ _ (Permutation_in _ P (in_eq h _)))
    as [l1 [l2 ->]].
  destruct l1 as [|h1 t1]. 
    simpl in *; f_equal.
    apply IH; [eby eapply Permutation_cons_inv |
               by inv S1 | by inv S2].
  rewrite <- app_comm_cons.
  assert (Eh : h = h1).
    apply SYM.
      inversion S1 as [| ? ? LST SREST]; subst.
      apply LST. eapply Permutation_in. 
      apply Permutation_sym. eapply Permutation_cons_app_inv. 
      eapply P. rewrite <- app_comm_cons. apply in_eq.
    rewrite <- app_comm_cons in S2.
    inversion S2 as [| ? ? LST' SREST']; subst.
    apply LST'. apply in_or_app. right. apply in_eq.
  rewrite <- Eh in *. f_equal.
  apply IH.
      rewrite <- app_comm_cons in P.
      eby eapply Permutation_cons_inv.
    by inv S1.
  rewrite <- app_comm_cons in S2. by inv S2.
Qed.

(** Lookup of the caller's continuation in an expression 
    continuation chain. *)
Fixpoint call_cont_expr_cont (k: Clight.expr_cont) : Clight.cont :=
  match k with
  | Clight.EKunop _ _ k => call_cont_expr_cont k
  | Clight.EKbinop1 _ _ _ _ _ k => call_cont_expr_cont k
  | Clight.EKbinop2 _ _ _ _ _ k => call_cont_expr_cont k
  | Clight.EKcast _ _ k => call_cont_expr_cont k
  | Clight.EKcondition _ _ _ k => call_cont_expr_cont k
  | Clight.EKfield _ k => call_cont_expr_cont k
  | Clight.EKlval _ k => call_cont_expr_cont k
  | Clight.EKassign1 _ _ k => Clight.call_cont k
  | Clight.EKassign2 _ _ k => Clight.call_cont k
  | Clight.EKcall _ _ _ k => Clight.call_cont k
  | Clight.EKargs _ _ _ _ _ k => Clight.call_cont k
  | Clight.EKatargs _ _ _ _ k => Clight.call_cont k  
  | Clight.EKcond _ _ _ k => Clight.call_cont k
  | Clight.EKwhile _ _ k => Clight.call_cont k
  | Clight.EKdowhile _ _ k => Clight.call_cont k
  | Clight.EKforTest _ _ _ k => Clight.call_cont k
  | Clight.EKreturn k => Clight.call_cont k
  | Clight.EKswitch _ k => Clight.call_cont k
  | Clight.EKthread1 _ k  => Clight.call_cont k
  | Clight.EKthread2 _ k => Clight.call_cont k
end.


(** * Matching relation definition *)

(**  Assume fixed global environments that are related *)

Variables (ge : Clight.cl_sem.(SEM_GE)) (tge : cs_sem.(SEM_GE)).

Let lts := (mklts thread_labels (Clight.step ge)).
Let tlts := (mklts thread_labels (cs_step tge)).

Definition genv_rel : Clight.GE -> genv -> Prop :=
 (fun x y => Genv.genv_match (fun a b => transl_fundef a = OK b) y x).

Hypothesis globenv_fn_in:
  forall p f, Genv.find_funct_ptr ge p = Some f -> 
              exists id, In (id, f) prog.(prog_funct).

(** Conversions and auxiliary functions for constants, unops, and binops *)

Definition make_float_cvt (sg : signedness) :=
  match sg with
    | Signed => Ofloatofint
    | Unsigned => Ofloatofintu
  end.

Definition make_int_cvt (sg : signedness) :=
  match sg with
    | Signed => Ointoffloat
    | Unsigned => Ointuoffloat
  end.



Definition match_unop (op: Csyntax.unary_operation) (ty: type) : res unary_operation :=
  match op with
  | Csyntax.Onotbool => match ty with
                        | Tfloat _ => Error(msg "Cshmgenproof.match_unop")
                        | _ => OK (Onotbool)
                        end
  | Csyntax.Onotint => OK (Onotint)
  | Csyntax.Oneg => match ty with
                     | Tint _ _ => OK (Onegint)
                     | Tfloat _ => OK (Onegf)
                     | _ => Error (msg "Cshmgenproof.match_unop")
                    end
  end.

Definition cmp (c : comparison) (ty1 : type) (ty2 : type) : res binary_operation :=
  match classify_cmp ty1 ty2 with
   | cmp_case_I32unsi => OK (Ocmpu c)
   | cmp_case_ipip => OK (Ocmp c)
   | cmp_case_ff => OK (Ocmpf c)
   | cmp_default => Error (msg "Cshmgenproof3.cmp")
 end.

Definition match_binop (op: Csyntax.binary_operation) (ty1 : type) (ty2: type) : 
res binary_operation :=
  match op with
   | Csyntax.Oadd  => match classify_add ty1 ty2 with
                       | add_case_ff => OK (Oaddf)
                       | _ => OK (Oadd)
                      end
   | Csyntax.Osub => match classify_sub ty1 ty2 with
                       | sub_case_ff => OK (Osubf)
                       | sub_case_pp _ => OK (Odivu)
                       | _ => OK (Osub)
                     end
   | Csyntax.Omul => match classify_mul ty1 ty2 with
                       | mul_case_ff => OK (Omulf)
                       | mul_case_ii => OK (Omul)
                       | mul_default => Error (msg "Cshmgenproof.match_binop")
                     end
   | Csyntax.Odiv => match classify_div ty1 ty2 with
                       | div_case_I32unsi => OK (Odivu)
                       | div_case_ii => OK (Odiv)
                       | div_case_ff => OK (Odivf)
                       | div_default => Error (msg "Cshmgenproof.match_binop")
                     end
   | Csyntax.Omod => match classify_mod ty1 ty2 with
                       | mod_case_I32unsi => OK (Omodu)
                       | mod_case_ii => OK (Omod)
                       | mod_default => Error (msg "Cshmgenproof.match_binop")
                     end
   | Csyntax.Oand => OK (Oand)
   | Csyntax.Oor => OK (Oor)
   | Csyntax.Oxor => OK (Oxor)
   | Csyntax.Oshl => OK (Oshl)
   | Csyntax.Oshr => match classify_shr ty1 ty2 with
                       | shr_case_I32unsi => OK (Oshru)
                       | shr_case_ii => OK (Oshr)
                       | shr_default => Error (msg "Cshmgenproof.match_binop")
                     end
   | Csyntax.Oeq => cmp Ceq ty1 ty2
   | Csyntax.One => cmp Cne ty1 ty2
   | Csyntax.Olt => cmp Clt ty1 ty2
   | Csyntax.Ogt => cmp Cgt ty1 ty2
   | Csyntax.Ole => cmp Cle ty1 ty2
   | Csyntax.Oge => cmp Cge ty1 ty2 
 end.

Definition gen_binop_exp (op: Csyntax.binary_operation) (ty : type) 
                         (ty': type) (te : expr) : expr :=
  match op with
  | Csyntax.Oadd => match classify_add ty ty' with 
                    | add_case_pi ty' =>
                        (Ebinop Omul (make_intconst (Int.repr (Csyntax.sizeof ty'))) te)
                    | add_case_ip ty' =>
                        (Ebinop Omul (make_intconst (Int.repr (Csyntax.sizeof ty'))) te)
                    | _ => te
                    end
  | Csyntax.Osub => match classify_sub ty ty' with 
                    | sub_case_pi ty' =>
                        (Ebinop Omul (make_intconst (Int.repr (Csyntax.sizeof ty'))) te)
                    | sub_case_pp ty' =>
                        (make_intconst (Int.repr (Csyntax.sizeof ty')))
                    | _ => te
                    end
  | _ => te
  end.

Definition gen_binop2_exp (op: Csyntax.binary_operation) (ty : type) 
                         (ty': type) (te : expr) : expr :=
  match op with
  | Csyntax.Oadd => match classify_add ty ty' with 
                    | add_case_pi ty' =>
                        (Ebinop Omul (make_intconst (Int.repr (Csyntax.sizeof ty'))) te)
                    | add_case_ip ty' =>
                        (Ebinop Omul (make_intconst (Int.repr (Csyntax.sizeof ty'))) te)
                    | _ => te
                    end
  | Csyntax.Osub => match classify_sub ty ty' with 
                    | sub_case_pi ty' =>
                        (Ebinop Omul (make_intconst (Int.repr (Csyntax.sizeof ty'))) te)
                    | sub_case_pp ty' =>
                        (make_intconst (Int.repr (Csyntax.sizeof ty')))
                    | _ => te
                    end
  | _ => te
  end.

Definition classify (op : Csyntax.binary_operation) (ty1 : type) (ty2 : type) : bool :=
  match op with
  | Csyntax.Oadd => match (classify_add ty1 ty2) with
                    | add_case_ip _ => true
                    | add_case_pi _ => true
                    | _ => false
                    end
  | Csyntax.Osub => match (classify_sub ty1 ty2) with
                    | sub_case_pp _ => true
                    | sub_case_pi _ => true
                    | _ => false
                    end
  | _ => false
  end.

Hypothesis TRANSF: genv_rel ge (fst tge).

(** * Matching between environments *)

(** In this section, we define a matching relation between
  a Clight local environment and a Csharpminor local environment,
  parameterized by an assignment of types to the Clight variables. *)

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol (fst tge) id = Genv.find_symbol ge id.
Proof. intros id. by destruct TRANSF. Qed.

Lemma var_kind_by_value:
  forall ty chunk,
  access_mode ty = By_value chunk ->
  var_kind_of_type ty = OK(Vscalar chunk).
Proof.
  intros ty chunk; destruct ty; simpl; try congruence.
  destruct i; try congruence; destruct s; congruence.
  destruct f; congruence.
Qed.

Lemma sizeof_var_kind_of_type: 
  forall ty vk, 
  var_kind_of_type ty = OK vk ->
  Csharpminor.sizeof vk = Csyntax.sizeof ty. 
Proof. 
  intros ty vk.
  assert (sizeof (Varray (Csyntax.sizeof ty)) = Csyntax.sizeof ty).  
  simpl. rewrite Zmax_spec. apply zlt_false.    
  generalize (Csyntax.sizeof_pos ty). omega.   
  destruct ty; try (destruct i; try destruct s); try (destruct f);   
  simpl; intro EQ; inversion EQ; subst vk; auto.         
Qed.            

Definition match_var_kind (ty: type) (vk: var_kind) : Prop :=
  match access_mode ty with
  | By_value chunk => vk = Vscalar chunk
  | _ => True
  end.

Record match_env (tyenv: typenv) (e: Clight.env) (te: env) : Prop :=
  mk_match_env {
    me_local:
      forall id b,
      e!id = Some b ->
      exists vk, exists ty,
        tyenv!id = Some ty
        /\ match_var_kind ty vk
        /\ te!id = Some (b, vk);
    me_local_inv:
      forall id b vk,
      te!id = Some (b, vk) -> e!id = Some b;
    me_global:
      forall id ty,
      e!id = None -> tyenv!id = Some ty ->
      te!id = None /\ 
      (forall chunk, 
         access_mode ty = By_value chunk -> 
         (PTree.get id (snd tge)) = Some (Vscalar chunk))
  }.

Definition globvarenv 
    (gv: gvarenv)
    (vars: list (ident * list init_data * var_kind)) :=
  List.fold_left
    (fun gve x => match x with (id, init, k) => PTree.set id k gve end)
    vars gv.

Definition type_not_by_value (ty: type) : Prop :=
  match access_mode ty with
  | By_value _ => False
  | _ => True
  end.

Lemma add_global_funs_charact:
  forall fns tyenv,
  (forall id ty, tyenv!id = Some ty -> type_not_by_value ty) ->
  (forall id ty, (add_global_funs tyenv fns)!id = Some ty -> 
                   type_not_by_value ty).
Proof.
  induction fns; simpl; intros.
  eauto.
  apply IHfns with (add_global_fun tyenv a) id.
  intros until ty0. destruct a as [id1 fn1]. 
  unfold add_global_fun; simpl. rewrite PTree.gsspec.
  destruct (peq id0 id1). 
  intros. inversion H1. 
  unfold type_of_fundef. destruct fn1; exact I.
  eauto.
  auto.
Qed.

Definition global_fun_typenv :=
  add_global_funs (PTree.empty type) prog.(prog_funct).

Definition match_globalenv (tyenv: typenv) (gv: gvarenv): Prop := 
   forall id ty chunk, 
   tyenv!id = Some ty -> access_mode ty = By_value chunk ->
     gv!id = Some (Vscalar chunk).    

Lemma add_global_funs_match_global_env:
  match_globalenv global_fun_typenv (PTree.empty var_kind).
Proof.
  intros; red; intros.
  assert (type_not_by_value ty).
    apply add_global_funs_charact with (prog_funct prog) (PTree.empty type) id.
    intros until ty0. rewrite PTree.gempty. congruence.
    assumption.
  red in H1. rewrite H0 in H1. contradiction.
Qed.

Lemma add_global_var_match_globalenv:
  forall vars tenv gv tvars,
  match_globalenv tenv gv ->
  map_partial Ast.prefix_var_name transl_globvar vars = OK tvars ->
  match_globalenv (add_global_vars tenv vars) (globvarenv gv tvars).
Proof.
  induction vars; simpl.
  intros. inversion H0. assumption.
  destruct a as [[id init] ty]. intros until tvars; intro.
  caseEq (transl_globvar ty); simpl; try congruence. intros vk VK. 
  caseEq (map_partial Ast.prefix_var_name transl_globvar vars); simpl; try congruence. intros tvars' EQ1 EQ2.
  inversion EQ2; clear EQ2. simpl. 
  apply IHvars; auto.
  red. intros until chunk. repeat rewrite PTree.gsspec. 
  destruct (peq id0 id); intros.
  inversion H0; clear H0; subst id0 ty0. 
  generalize (var_kind_by_value _ _ H2). 
  unfold transl_globvar in VK. congruence.
  red in H. eauto. 
Qed.


Lemma match_globalenv_match_env_empty:     
forall tyenv,
  match_globalenv tyenv (snd tge) ->
  match_env tyenv Clight.empty_env empty_env. 
Proof.
  intros. unfold Clight.empty_env, empty_env.
  constructor.
  intros until b. repeat rewrite PTree.gempty. congruence.
  intros until vk. rewrite PTree.gempty. congruence.
  intros. split.
  apply PTree.gempty.
  intros. red in H. eauto. 
Qed. 

Lemma gso_list: forall id l t
  (NIN: ~ In id (map (@fst _ _) l)),
 PTree.get id (Ctyping.add_vars t l) = PTree.get id t.
Proof.
  induction l; intros; clarify. simpl. 
  destruct a.
  unfold add_var. simpl. rewrite IHl. rewrite PTree.gso. done.
  intro. elim NIN. by left.
  intro. elim NIN. by right.
Qed.

Lemma nodup_map_rev:
  forall A B (f : A -> B) l,
    NoDup (map f l) -> NoDup l.
Proof.
  intros A B f l.
  induction l as [|h l IH].
  intro. constructor.
  
  simpl. intro ND. inv ND.
  constructor. 2 : by apply IH.
  intro IN. elim H1. by apply in_map.
Qed.


Lemma add_vars_ok: forall tyenv args,
  NoDup (map (@fst _ _) args) ->
  forall id ty,
   In (id,ty) args -> (Ctyping.add_vars tyenv args)!id = Some ty.
Proof.
  intros tyenv args; revert tyenv.
  induction args; intros N ND id ty TY. 
  inv ND. simpl in TY.  done.
   simpl in *. unfold add_var.
  inversion ND as [|id' r' NIN ND']. subst.
  destruct TY as [ E | IN ].
   subst. simpl. 
   by rewrite gso_list, PTree.gss.
  by rewrite (IHargs _ ND' _ _ IN).
Qed.


Lemma match_env_set:
  forall tyenv env tenv i p v ty,
  match_var_kind ty v ->
  match_env tyenv env tenv ->
  match_env (add_var tyenv (i,ty)) (env ! i <- p) (tenv ! i <- (p,v)).
Proof.
   intros.
   destruct H0. constructor.
   
   intros id b E.
   destruct (peq id i) as [N1 | N2].
   rewrite N1 in *. rewrite PTree.gss in *.
   exists v. exists ty. inv E. 
   split. unfold add_var. simpl. by rewrite PTree.gss.  done.
   unfold add_var. simpl. rewrite !PTree.gso; try done; [].
   eapply me_local0. by rewrite PTree.gso in E; [|done].

   intros id b vk TE.
   destruct (peq id i) as [N1 | N2].
   rewrite N1 in *. rewrite PTree.gss in *.  
   by inv TE.  
   rewrite !PTree.gso in *; try done. eby eapply me_local_inv0.

   intros id b E T.
   destruct (peq id i) as [N1 | N2].
   split. rewrite N1 in *. rewrite PTree.gss in *. done.

   intros.
   rewrite N1 in *. rewrite PTree.gss in *. done.
   unfold add_var in T; simpl in *. rewrite !PTree.gso in *; try done.
   split; try (eby eapply me_global); edone.
Qed.


Definition match_lhs (o : option (ident * type)) (o' : option ident) :=
  match (o,o') with
  | (None, None) => True
  | ((Some (id,ty)), (Some id')) => id = id' 
  | _ => False
  end.

Fixpoint match_args (args : list (ident * type)) (targs : list ident) 
   {struct args} :=
  match (args,targs) with
  | (nil,nil) => True
  | ((id,ty)::args', id'::targs') => (id = id') /\ (match_args args' targs')
  | _ => False
  end.

Definition typenv_fun (f: Csyntax.function) :=                                    
  add_vars (global_typenv prog) (f.(Csyntax.fn_params) ++ f.(Csyntax.fn_vars)).
  
(** Matching translations for blocks *)

Inductive match_transl: stmt -> cont -> stmt -> cont -> Prop :=
  | match_transl_0: forall ts tk,
      match_transl ts tk ts tk
  | match_transl_1: forall ts tk,
      match_transl (Sblock ts) tk ts (Kblock tk).

(** Measure function *)

Fixpoint countEKlval (k : Clight.expr_cont) { struct k} : nat :=
  match k with
    | (Clight.EKlval ty k') => (1 + (countEKlval k')%nat)%nat
    | (Clight.EKcast ty1 ty2 k') => (1 + (countEKlval k'))%nat 
    | k => 0%nat
  end.

Fixpoint countDeref (e : Csyntax.expr)  { struct e} : nat :=
  match e with
    |  (Csyntax.Expr (Csyntax.Ederef e') ty) => (S (S (S (S (S (countDeref e'))))))
    |  (Csyntax.Expr (Csyntax.Efield e' i) ty) => S (countDeref e')
    |  (Csyntax.Expr (Csyntax.Ecast ty1 e) ty) => (S (S (S (S (countDeref e)))))
    |  (Csyntax.Expr (Csyntax.Eaddrof e') ty) => 
            (S (S (S (S (S (S (countDeref e')))))))
    |  e  => 0%nat
  end.

Definition measure (st: Clight.state) : nat := 
 match st with
  | (Clight.SKexpr (Expr (Ecast ty e) ty') env k) =>  
       (7 + (countEKlval k) + (countDeref e))%nat 

  | (Clight.SKexpr (Expr (Ederef e) ty) env k) => 
       (5 + (countEKlval k) + (countDeref e))%nat

  | (Clight.SKexpr (Expr (Csyntax.Evar id) ty) env k) =>
      (3 + (countEKlval k))%nat

  | (Clight.SKlval (Expr (Csyntax.Evar id) ty) env (Clight.EKlval ty' k)) =>
      (2 + (countEKlval k))%nat

  | (Clight.SKlval (Expr (Ederef e) ty) env k) =>
      (6 + (countEKlval k) + (countDeref e))%nat 
 
  | (Clight.SKlval (Expr (Efield e id) ty) env k) =>
      (2 + (countEKlval k) + (countDeref e))%nat

  | (Clight.SKexpr (Expr (Efield e id) ty) env k) =>
      (4 + (countEKlval k) + (countDeref e))%nat

  | (Clight.SKexpr (Expr (Csyntax.Eandbool e1 e2) ty) env k) =>
      (2 + (countEKlval k))%nat

  | (Clight.SKexpr (Expr (Csyntax.Eorbool e1 e2) ty) env k) =>
      (2 + (countEKlval k))%nat
  
  | (Clight.SKexpr e env (Clight.EKlval ty k)) =>
      (1 + (countEKlval k) + (countDeref e))%nat

  | (Clight.SKexpr (Expr (Csyntax.Eaddrof e) ty) env k) => 
     ((countEKlval k) + (countDeref (Expr (Csyntax.Eaddrof e) ty))%nat)%nat 

  | (Clight.SKstmt (Csyntax.Sassign (Expr (Csyntax.Evar id) ty) e) env k) => 4%nat
  
  | (Clight.SKlval e env k) => (1 + (countEKlval k) + (countDeref e))%nat

  | (Clight.SKstmt (Csyntax.Scall (Some (id,ty)) e args) env k) => 
       (7 + (countDeref e))%nat
  
  | (Clight.SKval (Vptr p) env (Clight.EKcast ty1 ty2 k)) => (1 + (countEKlval k))%nat

  | (Clight.SKval (Vptr p) env (Clight.EKlval ty k) ) =>  (1 + (countEKlval k))%nat

  | (Clight.SKval (Vint i) env (Clight.EKcast (Tint sz1 si1) (Tint I32 si2) k)) =>
       (1 + (countEKlval k))%nat

  | (Clight.SKval (Vint i) env (Clight.EKcast (Tint sz1 si1) (Tint I8 si2) k)) =>
       (1 + (countEKlval k))%nat

  | (Clight.SKval (Vint i) env (Clight.EKcast (Tint sz1 si1) (Tpointer ty) k)) =>
       (1 + (countEKlval k))%nat

  | (Clight.SKval (Vint i) env (Clight.EKcast (Tint sz1 si1) (Tarray ty z) k)) =>
       (1 + (countEKlval k))%nat

  | (Clight.SKval (Vint i) env (Clight.EKcast (Tint sz1 si1) (Tfunction t0 ty) k)) =>
       (1 + (countEKlval k))%nat

  | (Clight.SKval (Vint i) env (Clight.EKcast (Tpointer ty) ty' k)) =>
       (1 + (countEKlval k))%nat 

  | (Clight.SKval (Vint i) env (Clight.EKcast (Tarray ty z) ty' k)) =>
       (1 + (countEKlval k))%nat 

  | (Clight.SKval (Vint i) env (Clight.EKcast (Tfunction t0 ty) ty' k)) =>
       (1 + (countEKlval k))%nat 

  | (Clight.SKval (Vfloat f) env (Clight.EKcast (Tfloat sz1) (Tfloat F64) k)) =>
       (1 + (countEKlval k))%nat

  | s => 0%nat
  end.

Definition typeEnvOfCont k := 
  match k with
    | (Clight.Kcall opt_lhs (Internal f) env' k') => (typenv_fun f)
    | _ => (global_typenv prog)
  end.


Definition bodyOfCont k := 
  match k with
    | (Clight.Kcall opt_lhs (Internal f) env' k') => f.(Csyntax.fn_body)
    | _ => Csyntax.Sskip
  end.

(** Matching expression continuations in given environments *)

Inductive match_expr_cont: Clight.env -> Csharpminor.env -> typenv -> nat -> nat -> 
                             Clight.expr_cont ->  Csharpminor.expr_cont -> Prop :=
   | match_EKlval_load: forall env tenv tyenv nbrk ncnt ty k tk c,
      access_mode ty = By_value c ->
      match_expr_cont env tenv tyenv nbrk ncnt k tk -> 
      match_expr_cont env tenv tyenv nbrk ncnt (Clight.EKlval ty k) (EKload c tk)
   | match_EKlval_ref: forall env tenv tyenv nbrk ncnt ty k tk,
      access_mode ty = By_reference \/ access_mode ty = By_nothing ->
      match_expr_cont env tenv  tyenv nbrk ncnt k tk -> 
      match_expr_cont env tenv  tyenv nbrk ncnt (Clight.EKlval ty k) tk  
   | match_EKunop: forall env tenv tyenv nbrk ncnt op top ty k tk,
      match_unop op ty = OK top ->
      match_expr_cont env tenv tyenv nbrk ncnt k tk ->
      match_expr_cont env tenv tyenv nbrk ncnt (Clight.EKunop op ty k) (EKunop top tk)
   | match_EKunop_float: forall env tenv tyenv nbrk ncnt k tk f,
      match_expr_cont env tenv tyenv nbrk ncnt k tk ->
      match_expr_cont env tenv tyenv nbrk ncnt 
        (Clight.EKunop Csyntax.Onotbool (Tfloat f) k) 
        (EKbinop1 (Ocmpf Ceq) (Econst (Ofloatconst Float.zero)) tk)
   | match_EKbinop1_add_case_pi: forall env tenv tyenv nbrk ncnt top ty1 ty2 ty ty' k tk e2 te2 n ,
     match_expr_cont env tenv tyenv nbrk ncnt k tk ->
     match_binop Csyntax.Oadd ty1 ty2 = OK top ->
     classify_add ty1 ty2 = add_case_pi ty' ->
     match_expr_cont env tenv tyenv nbrk ncnt k tk ->
     transl_expr e2 = OK te2 ->
     eval_constant n = Some (Vint (Int.repr (Csyntax.sizeof ty'))) ->
     wt_expr tyenv e2 ->
     match_expr_cont env tenv tyenv nbrk ncnt 
        (Clight.EKbinop1 Csyntax.Oadd ty1 ty2 ty e2 k)
        (EKbinop1 top (Ebinop Omul (Econst n) te2) tk)
   | match_EKbinop1_add_case_ip: forall env tenv tyenv nbrk ncnt top ty1 ty2 ty ty' k tk e2 te2,
     match_expr_cont env tenv tyenv nbrk ncnt k tk ->
     match_binop Csyntax.Oadd ty1 ty2 = OK top ->
     classify_add ty1 ty2 = add_case_ip ty' ->
     match_expr_cont env tenv tyenv nbrk ncnt k tk ->
     transl_expr e2 = OK te2 ->
     wt_expr tyenv e2 ->
     match_expr_cont env tenv tyenv nbrk ncnt 
        (Clight.EKbinop1 Csyntax.Oadd ty1 ty2 ty e2 k)
        (EKbinop2 Omul (Vint (Int.repr (Csyntax.sizeof ty'))) (EKbinop1 top te2 tk))
   | match_EKbinop1_sub_case_pi: forall env tenv tyenv nbrk ncnt top ty1 ty2 ty ty' k tk e2 te2 n,
     match_expr_cont env tenv tyenv nbrk ncnt k tk ->
     match_binop Csyntax.Osub ty1 ty2 = OK top ->
     classify_sub ty1 ty2 = sub_case_pi ty' ->
     match_expr_cont env tenv tyenv nbrk ncnt k tk ->
     eval_constant n = Some (Vint (Int.repr (Csyntax.sizeof ty'))) ->
     transl_expr e2 = OK te2 ->
     wt_expr tyenv e2 ->
     match_expr_cont env tenv tyenv nbrk ncnt 
        (Clight.EKbinop1 Csyntax.Osub ty1 ty2 ty e2 k)
        (EKbinop1 top (Ebinop Omul (Econst n) te2) tk)
   | match_EKbinop1_sub_case_pp: forall env tenv tyenv nbrk ncnt top ty1 ty2 ty ty' k tk e2 te2 n,
     match_expr_cont env tenv tyenv nbrk ncnt k tk ->
     match_binop Csyntax.Osub ty1 ty2 = OK top ->
     classify_sub ty1 ty2 = sub_case_pp ty' ->
     match_expr_cont env tenv tyenv nbrk ncnt k tk ->
     eval_constant n = (Some (Vint (Int.repr (Csyntax.sizeof ty')))) ->
     wt_expr tyenv e2 ->
     transl_expr e2 = OK te2 ->
     match_expr_cont env tenv tyenv nbrk ncnt 
        (Clight.EKbinop1 Csyntax.Osub ty1 ty2 ty e2 k)
        (EKbinop1 Osub te2 (EKbinop1 top (Econst n) tk))
   | match_EKbinop2_add_case_pi: forall env tenv tyenv nbrk ncnt top ty1 ty2 ty ty' k tk v,
     match_expr_cont env tenv tyenv nbrk ncnt k tk ->
     match_binop Csyntax.Oadd ty1 ty2 = OK top ->
     classify_add ty1 ty2 = add_case_pi ty' ->
     match_expr_cont env tenv tyenv nbrk ncnt k tk ->
     match_expr_cont env tenv tyenv nbrk ncnt 
        (Clight.EKbinop2 Csyntax.Oadd ty1 ty2 ty v k)
        (EKbinop2 Omul (Vint (Int.repr (Csyntax.sizeof ty'))) (EKbinop2 top v tk))
   | match_EKbinop2_add_case_ip: forall env tenv tyenv nbrk ncnt top ty1 ty2 ty ty' k tk v v',
     match_expr_cont env tenv tyenv nbrk ncnt k tk ->
     match_binop Csyntax.Oadd ty1 ty2 = OK top ->
     classify_add ty1 ty2 = add_case_ip ty' ->
     v' = (Int.mul (Int.repr (Csyntax.sizeof ty')) v) ->
     match_expr_cont env tenv tyenv nbrk ncnt k tk ->
     match_expr_cont env tenv tyenv nbrk ncnt 
        (Clight.EKbinop2 Csyntax.Oadd ty1 ty2 ty (Vint v) k)
        (EKbinop2 top (Vint v') tk)
   | match_EKbinop2_sub_case_pi: forall env tenv tyenv nbrk ncnt top ty1 ty2 ty ty' k tk v,
     match_expr_cont env tenv tyenv nbrk ncnt k tk ->
     match_binop Csyntax.Osub ty1 ty2 = OK top ->
     classify_sub ty1 ty2 = sub_case_pi ty' ->
     match_expr_cont env tenv tyenv nbrk ncnt k tk ->
     match_expr_cont env tenv tyenv nbrk ncnt 
        (Clight.EKbinop2 Csyntax.Osub ty1 ty2 ty v k)
        (EKbinop2 Omul (Vint (Int.repr (Csyntax.sizeof ty'))) (EKbinop2 top v tk))
   | match_EKbinop2_sub_case_pp: forall env tenv tyenv nbrk ncnt top ty1 ty2 ty ty' k tk n v,
     match_expr_cont env tenv tyenv nbrk ncnt k tk ->
     match_binop Csyntax.Osub ty1 ty2 = OK top ->
     classify_sub ty1 ty2 = sub_case_pp ty' ->
     match_expr_cont env tenv tyenv nbrk ncnt k tk ->
     eval_constant n = Some (Vint (Int.repr (Csyntax.sizeof ty'))) ->
     match_expr_cont env tenv tyenv nbrk ncnt 
        (Clight.EKbinop2 Csyntax.Osub ty1 ty2 ty v k)
        (EKbinop2 Osub v (EKbinop1 top (Econst n) tk))
   | match_EKbinop1: forall env tenv tyenv nbrk ncnt op ty k tk e te top ty1 ty2,
      match_binop op ty1 ty2 = OK top ->
      transl_expr e = OK te ->
      wt_expr tyenv e ->
      classify op ty1 ty2 = false ->
      match_expr_cont env tenv tyenv nbrk ncnt k tk ->
      match_expr_cont env tenv tyenv nbrk ncnt 
                      (Clight.EKbinop1 op ty1 ty2 ty e k) (EKbinop1 top te tk)
   | match_EKbinop2: forall env tenv tyenv nbrk ncnt op ty ty1 ty2 k tk top v,
      match_binop op ty1 ty2 = OK top ->
      classify op ty1 ty2 = false ->
      match_expr_cont env tenv tyenv nbrk ncnt k tk ->
      match_expr_cont env tenv tyenv nbrk ncnt (Clight.EKbinop2 op ty1 ty2 ty v k) 
                                      (EKbinop2 top v tk)
   | match_EKfield_exp: forall env tenv tyenv nbrk ncnt k tk n,
      match_expr_cont env tenv tyenv nbrk ncnt k tk  ->
      match_expr_cont env tenv tyenv nbrk ncnt 
          (Clight.EKfield n k)  (EKbinop1 Oadd (make_intconst (Int.repr n)) tk)
   | match_EKassign1: forall env tenv tyenv nbrk ncnt k tk e te c ty,
     transl_expr e = OK te ->
     wt_expr tyenv e ->
     access_mode ty = By_value c -> 
     Clight.type_to_chunk ty = Some c -> 
     match_cont env tenv tyenv nbrk ncnt k tk ->
     match_expr_cont env tenv tyenv nbrk ncnt (Clight.EKassign1 e ty k)  
                                     (EKstoreaddr c te tk) 
   | match_EKassign2_exp: forall env tenv tyenv nbrk ncnt k tk v c ty,
     match_cont env tenv tyenv nbrk ncnt k tk ->
     access_mode ty = By_value c -> 
     match_expr_cont env tenv tyenv nbrk ncnt (Clight.EKassign2 v ty k) 
                                      (EKstoreval c v tk)
   | match_EKassign2_var: forall env tenv tyenv nbrk ncnt k tk p ty id c,
     match_cont env tenv tyenv nbrk ncnt k tk ->
     Clight.type_to_chunk ty = Some c ->  
     eval_var_ref tge tenv id p c -> 
     match_expr_cont env tenv tyenv nbrk ncnt (Clight.EKassign2 (Vptr p) ty k)
                                     (EKassign id tk)
   | match_EKcall: forall env tenv tyenv nbrk ncnt k tk es es' ret ret' sig targs tres ty
      (WTLHS: wt_optexpr_lhs tyenv ret),
      transl_exprlist es = OK es' ->
      match_lhs ret ret' ->
      wt_exprlist tyenv es ->
      match_env tyenv env tenv ->
      match_cont env tenv tyenv nbrk ncnt k tk ->
      classify_fun ty = fun_case_f targs tres ->
      sig = signature_of_type targs tres ->
      match_expr_cont env tenv tyenv nbrk ncnt (Clight.EKcall ret ty es k) 
                                      (EKcall ret' sig es' tk)
   | match_EKargs: forall env tenv tyenv nbrk ncnt v vs es es' k tk ret ret' targs tres ty sig
       (WTLHS: wt_optexpr_lhs tyenv ret),
       transl_exprlist es = OK es' ->
       wt_exprlist tyenv es ->
       match_lhs ret ret' ->
       match_cont env tenv tyenv nbrk ncnt k tk ->
       classify_fun ty = fun_case_f targs tres ->
       sig = signature_of_type targs tres ->
       match_expr_cont env tenv tyenv nbrk ncnt 
                       (Clight.EKargs ret v ty vs es k) 
                       (EKargs ret' v sig es' vs tk)
   | match_EKatargs: forall env tenv tyenv nbrk ncnt vs es es' k tk ret ret' aop astmt
       (WTLHS: wt_optexpr_lhs tyenv ret),
       transl_exprlist es = OK es' ->
       transl_atomic_statement aop = OK astmt ->
       wt_exprlist tyenv es ->
       match_lhs ret ret' ->
       match_cont env tenv tyenv nbrk ncnt k tk ->
       match_expr_cont env tenv tyenv nbrk ncnt 
                       (Clight.EKatargs ret aop vs es k) 
                       (EKatargs ret' astmt es' vs tk)
   | match_EKthread1: forall env tenv tyenv nbrk ncnt k tk e e',
       transl_expr e = OK e' ->
       wt_expr tyenv e ->
       match_cont env tenv tyenv nbrk ncnt k tk ->
       match_expr_cont env tenv tyenv nbrk ncnt (Clight.EKthread1 e k) (EKthread1 e' tk) 
    | match_EKthread2: forall env tenv tyenv nbrk ncnt k tk p,
       match_cont env tenv tyenv nbrk ncnt k tk ->
       match_expr_cont env tenv tyenv nbrk ncnt (Clight.EKthread2 p k) (EKthread2 p tk)
    | match_EKswitch: forall env tenv tyenv nbrk ncnt ls tls k tk,
       wt_lblstmts tyenv ls ->
       transl_lbl_stmt 0%nat (S ncnt) ls = OK tls ->
       match_cont env tenv tyenv nbrk ncnt k tk ->
       match_expr_cont env tenv tyenv nbrk ncnt  
           (Clight.EKswitch ls k) (EKswitch tls (Kblock tk))
    | match_EKreturn: forall env tenv tyenv nbrk ncnt k tk,
       match_cont env tenv tyenv nbrk ncnt k tk ->
       match_expr_cont env tenv tyenv nbrk ncnt (Clight.EKreturn k)
                                       (EKreturn tk)
    | match_EKcast: forall env tenv tyenv nbrk ncnt k tk ty1 ty2 tk1 tk2,
        match_expr_cont env tenv tyenv nbrk ncnt k tk ->
        tk2 = match ty2 with
               | Tint I8 Signed => EKunop Ocast8signed tk
               | Tint I8 Unsigned => EKunop Ocast8unsigned tk
               | Tint I16 Signed => EKunop Ocast16signed tk
               | Tint I16 Unsigned => EKunop Ocast16unsigned tk
               | Tfloat F32 => EKunop Osingleoffloat tk
               | _ => tk
             end -> 
        tk1 = match ty1,ty2 with
               | Tint _ uns, Tfloat _ => (EKunop (make_float_cvt (uns)) tk2)
               | Tfloat _ , Tint _ uns => (EKunop (make_int_cvt (uns)) tk2)
               | _, _ => tk2
              end ->
        match_expr_cont env tenv tyenv nbrk ncnt (Clight.EKcast ty1 ty2 k) tk1
    | match_EKcond: forall env tenv tyenv nbrk ncnt ty s1 s2 k ts1 ts2 tk,
        transl_statement nbrk ncnt s1 = OK ts1 ->
        transl_statement nbrk ncnt s2 = OK ts2 ->
        wt_stmt tyenv s1 ->
        wt_stmt tyenv s2 ->
        match_cont env tenv tyenv nbrk ncnt k tk ->
        (forall f, ty <> Tfloat f) ->
         match_expr_cont env tenv tyenv nbrk ncnt
           (Clight.EKcond ty s1 s2 k) (EKcondstmt ts1 ts2 tk)
    | match_EKcond_float: forall env tenv tyenv nbrk ncnt s1 s2 k ts1 ts2 tk f,
        transl_statement nbrk ncnt s1 = OK ts1 ->
        transl_statement nbrk ncnt s2 = OK ts2 ->
        wt_stmt tyenv s1 ->
        wt_stmt tyenv s2 ->
        match_cont env tenv tyenv nbrk ncnt k tk ->
        match_expr_cont env tenv tyenv nbrk ncnt
          (Clight.EKcond (Tfloat f) s1 s2 k) 
          (EKbinop1 (Ocmpf Cne) (Econst (Ofloatconst Float.zero))
             (EKcondstmt ts1 ts2 tk))
    | match_EKcondition: forall env tenv tyenv nbrk ncnt ty k tk e2 e3 te2 te3,
        transl_expr e2 = OK te2 ->
        transl_expr e3 = OK te3 ->
        wt_expr tyenv e2 ->
        wt_expr tyenv e3 ->
        match_expr_cont env tenv tyenv nbrk ncnt k tk ->
        (forall f, ty <> Tfloat f) ->
           match_expr_cont env tenv tyenv nbrk ncnt 
              (Clight.EKcondition e2 e3 ty k)  (EKcond te2 te3 tk)
    | match_EKcondition_float: forall env tenv tyenv nbrk ncnt k tk e2 e3 te2 te3 f,
        transl_expr e2 = OK te2 ->
        transl_expr e3 = OK te3 ->
        wt_expr tyenv e2 ->
        wt_expr tyenv e3 -> 
        match_expr_cont env tenv tyenv nbrk ncnt k tk ->
        match_expr_cont env tenv tyenv nbrk ncnt 
            (Clight.EKcondition e2 e3 (Tfloat f) k)
            (EKbinop1 (Ocmpf Cne) (Econst (Ofloatconst Float.zero))
                      (EKcond te2 te3 tk))
     | match_EKwhile: forall env tenv tyenv nbrk ncnt e s k te ts tk,
         exit_if_false e = OK te ->
         transl_statement 1%nat 0%nat s = OK ts ->
         match_cont env tenv tyenv nbrk ncnt k tk ->
         wt_expr tyenv e ->
         wt_stmt tyenv s ->
         (forall f, (typeof e) <> Tfloat f) ->
         match_expr_cont env tenv tyenv 1%nat 0%nat
           (Clight.EKwhile e s k)
           (EKcondstmt Sskip (Sexit 0)
              (Kseq (Sblock ts) 
                    (Kseq (Sloop (Sseq te (Sblock ts))) (Kblock tk))))
     | match_EKwhile_float: forall env tenv tyenv nbrk ncnt e s k te ts tk f,
         exit_if_false e = OK te ->
         transl_statement 1%nat 0%nat s = OK ts ->
         wt_expr tyenv e ->
         wt_stmt tyenv s ->
         typeof e = Tfloat f ->
         match_cont env tenv tyenv nbrk ncnt k tk ->
         match_expr_cont env tenv tyenv 1%nat 0%nat
           (Clight.EKwhile e s k)
           (EKbinop1 (Ocmpf Cne) 
               (Econst (Ofloatconst Float.zero))
               (EKcondstmt Sskip (Sexit 0)
                 (Kseq (Sblock ts) 
                    (Kseq (Sloop (Sseq te (Sblock ts))) (Kblock tk)))))     
    | match_EKdowhile: forall env tenv tyenv nbrk ncnt e s k te ts tk,
         exit_if_false e = OK te ->
         transl_statement 1%nat 0%nat s = OK ts ->
         match_cont env tenv tyenv nbrk ncnt k tk ->
         wt_expr tyenv e ->
         wt_stmt tyenv s ->
         (forall f, (typeof e) <> Tfloat f) ->
         match_expr_cont env tenv tyenv 1%nat 0%nat
           (Clight.EKdowhile s e k)
           (EKcondstmt Sskip (Sexit 0)
              (Kseq (Sloop (Sseq (Sblock ts) te)) (Kblock tk)))
     | match_EKdowhile_float: forall env tenv tyenv nbrk ncnt e s k te ts tk f,
         exit_if_false e = OK te ->
         transl_statement 1%nat 0%nat s = OK ts ->
         wt_expr tyenv e ->
         wt_stmt tyenv s ->
         typeof e = Tfloat f ->
         match_cont env tenv tyenv nbrk ncnt k tk ->
         match_expr_cont env tenv tyenv 1%nat 0%nat
           (Clight.EKdowhile s e k)
           (EKbinop1 (Ocmpf Cne) 
               (Econst (Ofloatconst Float.zero))
               (EKcondstmt Sskip (Sexit 0)
                 (Kseq (Sloop (Sseq (Sblock ts) te)) (Kblock tk))))
     | match_EKforTest: forall env tenv tyenv nbrk ncnt e2 te2 s3 ts3 s ts k tk,
         exit_if_false e2 = OK te2 ->
         wt_expr tyenv e2 ->
         wt_stmt tyenv s3 ->
         wt_stmt tyenv s ->
         transl_statement 1%nat 0%nat s = OK ts ->
         transl_statement nbrk ncnt s3 = OK ts3 ->
         match_cont env tenv tyenv nbrk ncnt k tk ->
         (forall f, (typeof e2) <> Tfloat f) ->
         match_expr_cont env tenv tyenv 1%nat 0%nat
           (Clight.EKforTest e2 s3 s k)
           (EKcondstmt Sskip (Sexit 0)
               (Kseq (Sseq (Sblock ts) ts3)  
                     (Kseq (Sloop (Sseq te2 (Sseq (Sblock ts) ts3)))
                           (Kblock tk))))
     | match_EKforTest_float: forall env tenv tyenv nbrk ncnt e2 te2 s3 ts3 s ts k tk f,
         exit_if_false e2 = OK te2 ->
         wt_expr tyenv e2 ->
         wt_stmt tyenv s3 ->
         wt_stmt tyenv s ->
         typeof e2 = Tfloat f ->
         transl_statement 1%nat 0%nat s = OK ts ->
         transl_statement nbrk ncnt s3 = OK ts3 ->
         match_cont env tenv tyenv nbrk ncnt k tk ->
         match_expr_cont env tenv tyenv 1%nat 0%nat
           (Clight.EKforTest e2 s3 s k)
           (EKbinop1 (Ocmpf Cne)  
             (Econst (Ofloatconst Float.zero))
             (EKcondstmt Sskip (Sexit 0)
                (Kseq (Sseq (Sblock ts) ts3)
                      (Kseq (Sloop (Sseq te2 (Sseq (Sblock ts) ts3)))
                            (Kblock tk)))))

with match_cont: Clight.env -> Csharpminor.env -> typenv -> nat -> nat -> Clight.cont -> Csharpminor.cont -> Prop :=
  | match_Kstop: forall env tenv tyenv nbrk ncnt,
      match_cont env tenv tyenv nbrk ncnt Clight.Kstop Kstop
  | match_Kswitch: forall env tenv tyenv nbrk ncnt k tk,
      match_cont env tenv tyenv nbrk ncnt k tk ->
      match_cont env tenv tyenv 0%nat (S ncnt) (Clight.Kswitch k) (Kblock tk) 
  | match_Kseq: forall env tenv tyenv nbrk ncnt s k ts tk,
      transl_statement nbrk ncnt s = OK ts ->
      wt_stmt tyenv s ->
      match_cont env tenv tyenv nbrk ncnt k tk ->
      match_cont env tenv tyenv nbrk ncnt
                 (Clight.Kseq s k) (Kseq ts tk)
  | match_Kwhile: forall env tenv tyenv a s k ta ts tk nbrk ncnt,
      transl_statement 1%nat 0%nat s = OK ts -> 
      exit_if_false a = OK ta -> 
      wt_expr tyenv a ->
      wt_stmt tyenv s ->
      match_cont env tenv tyenv nbrk ncnt k tk ->
      match_cont env tenv tyenv 1%nat 0%nat
                 (Clight.Kwhile a s k) 
                 (Kblock (Kseq (Sloop (Sseq ta (Sblock ts))) (Kblock tk)))
  | match_Kdowhile: forall env tenv tyenv a s k ta ts tk nbrk ncnt,
      transl_statement 1%nat 0%nat s = OK ts -> 
      exit_if_false a = OK ta -> 
      wt_expr tyenv a ->
      wt_stmt tyenv s ->
      match_cont env tenv tyenv nbrk ncnt k tk ->
      match_cont env tenv tyenv 1%nat 0%nat
                 (Clight.Kdowhile s a k) 
                 (Kblock (Kseq ta (Kseq (Sloop (Sseq (Sblock ts) ta)) (Kblock tk))))
 | match_Kcall: forall env 
                  tenv env' tenv' tyenv tyenv' fd tfd k tk o o' nbrk ncnt nbrk' ncnt'
      (WTS: wt_optexpr_lhs tyenv' o),
      transl_fundef fd = OK tfd ->
      match_lhs o o' ->
      match fd with
      | Internal f => (wt_fundef (global_typenv prog) fd)
      | _ => False
      end ->
      wt_stmt tyenv' (bodyOfCont (Clight.call_cont k))  ->
      match_env tyenv' env tenv ->
      match_cont env tenv tyenv' nbrk' ncnt' k tk ->
      match_cont env' tenv' tyenv nbrk ncnt (Clight.Kcall o fd env k) 
                                            (Kcall o' tfd tenv tk) 
   | match_KforCond: forall env tenv tyenv e2 te2 s3 ts3 s ts k tk nbrk ncnt,
       exit_if_false e2 = OK te2 ->
       wt_expr tyenv e2 ->
       wt_stmt tyenv s3 ->
       wt_stmt tyenv s ->
       transl_statement nbrk ncnt s3 = OK ts3 ->
       transl_statement 1 0 s = OK ts ->
       match_cont env tenv tyenv nbrk ncnt k tk ->
       match_cont env tenv tyenv nbrk ncnt 
        (Clight.KforCond e2 s3 s k)
        (Kseq (Sblock (Sloop (Sseq te2 (Sseq (Sblock ts) ts3)))) tk)
   | match_KforCondIncr: forall env tenv tyenv e2 te2 s3 ts3 s ts k tk nbrk ncnt,
       exit_if_false e2 = OK te2 ->
       wt_expr tyenv e2 ->
       wt_stmt tyenv s3 ->
       wt_stmt tyenv s ->
       transl_statement nbrk ncnt s3 = OK ts3 ->
       transl_statement 1 0 s = OK ts ->
       match_cont env tenv tyenv nbrk ncnt k tk ->
       match_cont env tenv tyenv nbrk ncnt 
        (Clight.KforCond e2 s3 s k)
        (Kseq (Sloop (Sseq te2 (Sseq (Sblock ts) ts3))) (Kblock tk))
   | match_KforIncr: forall env tenv tyenv e2 te2 s3 ts3 s ts k tk nbrk ncnt,
       exit_if_false e2 = OK te2 ->
       wt_expr tyenv e2 ->
       wt_stmt tyenv s3 ->
       wt_stmt tyenv s ->
       transl_statement nbrk ncnt s3 = OK ts3 ->
       transl_statement 1 0 s = OK ts ->
       match_cont env tenv tyenv nbrk ncnt k tk ->
       match_cont env tenv tyenv 1 0
        (Clight.KforIncr e2 s3 s k)
        (Kblock (Kseq ts3 
                   (Kseq (Sloop (Sseq te2 (Sseq (Sblock ts) ts3))) 
                         (Kblock tk))))
   | match_Kfree: forall env tenv tyenv  ps v k tk nbrk ncnt 
       (MENV: match_env tyenv env tenv)
       (MK: match_cont env tenv tyenv nbrk ncnt k tk),
      match_cont env tenv tyenv nbrk ncnt (Clight.Kfree ps v k) (Kfree ps v tk).

Lemma match_cont_call_cont:   
  forall  env tenv tyenv tyenv' nbrk ncnt k tk nbrk' ncnt',
  match_cont env tenv tyenv' nbrk ncnt k tk -> 
  match_cont env tenv tyenv nbrk' ncnt' (Clight.call_cont k) (call_cont tk).
Proof.
 induction 1;  simpl; auto; vauto.
Qed.

Lemma match_cont_is_call_cont:                                                        
  forall env tenv typenv nbrk ncnt k tk  nbrk' ncnt',
  match_cont env tenv typenv nbrk ncnt k tk ->
  Clight.is_call_cont k -> 
  match_cont env tenv typenv nbrk' ncnt' k tk /\ is_call_cont tk.   
Proof.
  intros. inv H; simpl in H0; try contradiction; simpl; intuition; try discriminate.
  eapply match_Kstop.
  eapply match_Kcall; try edone.
Qed.            


Inductive match_states: Clight.state -> state -> Prop :=
  | match_val: forall k tk nbrk ncnt v typEnv env tenv 
      (MENV: match_env typEnv env tenv)
      (WTB: wt_stmt typEnv (bodyOfCont (call_cont_expr_cont k)))
      (MK: match_expr_cont env tenv typEnv nbrk ncnt k tk),
    match_states (Clight.SKval v env k) (SKval v tenv tk)
  | match_expr:
    forall e te typEnv nbrk ncnt k tk env tenv
      (MENV: match_env typEnv env tenv)
      (WTB: wt_stmt typEnv (bodyOfCont (call_cont_expr_cont k)))
      (MK: match_expr_cont env tenv typEnv nbrk ncnt k tk)
      (WT: wt_expr typEnv e)
      (TE: transl_expr e = OK te),
    match_states (Clight.SKexpr e env k) (SKexpr te tenv tk)
  | match_stmt:
    forall s ts nbrk ncnt k tk typEnv env tenv
      (MENV: match_env typEnv env tenv)
      (WTB: wt_stmt typEnv (bodyOfCont (Clight.call_cont k)))
      (MK: match_cont env tenv typEnv nbrk ncnt k tk)
      (WT: wt_stmt typEnv s)
      (TS: transl_statement nbrk ncnt s = OK ts),       
    match_states (Clight.SKstmt s env k) (SKstmt ts tenv tk)
  | match_lval:
    forall k tk nbrk ncnt typEnv te e env tenv
       (MENV: match_env typEnv env tenv)
       (WTB: wt_stmt typEnv (bodyOfCont (call_cont_expr_cont k)))
       (MK: match_expr_cont env tenv typEnv nbrk ncnt k tk)
       (WT: wt_expr typEnv e)
       (TE: transl_lvalue e = OK te),
    match_states (Clight.SKlval e env k) (SKexpr te tenv tk)
  | match_var_val:
    forall k tk ty id nbrk ncnt typEnv c env tenv
       (MENV: match_env typEnv env tenv)
       (WTB: wt_stmt typEnv (bodyOfCont (call_cont_expr_cont k)))
       (WT: wt_expr typEnv (Expr (Csyntax.Evar id) ty))
       (AM: access_mode ty = By_value c) 
       (MK: match_expr_cont env tenv typEnv nbrk ncnt k tk),
    match_states (Clight.SKlval (Expr (Csyntax.Evar id) ty) env (Clight.EKlval ty k))
                 (SKexpr (Evar id) tenv tk)
  | match_var_ref:
    forall k tk ty id nbrk ncnt typEnv env tenv
       (MENV: match_env typEnv env tenv)
       (WTB: wt_stmt typEnv (bodyOfCont (call_cont_expr_cont k)))
       (WT: wt_expr typEnv (Expr (Csyntax.Evar id) ty))
       (AM: access_mode ty = By_reference \/ access_mode ty = By_nothing)
       (MK: match_expr_cont env tenv typEnv nbrk ncnt k tk),
    match_states (Clight.SKlval (Expr (Csyntax.Evar id) ty) env (Clight.EKlval ty k))
                 (SKexpr (Eaddrof id) tenv tk)
  | match_var_value_local_and_global:
    forall k tk ty id p nbrk ncnt typEnv c env tenv
       (MENV: match_env typEnv env tenv)
       (WTB: wt_stmt typEnv (bodyOfCont (call_cont_expr_cont k)))
       (AM: access_mode ty = By_value c)
       (WT: wt_expr typEnv (Expr (Csyntax.Evar id) ty))
       (MK: match_expr_cont env tenv typEnv nbrk ncnt k tk),
     transl_expr (Expr (Csyntax.Evar id) ty) = OK (Evar id) ->
     eval_var_ref tge tenv id p c ->
     match_states (Clight.SKval (Vptr p) env (Clight.EKlval ty k))
                  (SKexpr (Evar id) tenv tk)
  | match_assign_lval_id:
    forall e2 te2 typEnv k tk id ty ty' c nbrk ncnt env tenv
        (MENV: match_env typEnv env tenv)
        (WTB: wt_stmt typEnv (bodyOfCont (Clight.call_cont k)))  
        (MK: match_cont env tenv typEnv nbrk ncnt k tk)
        (AM: access_mode ty = By_value c) 
        (WT: wt_expr typEnv (Expr (Csyntax.Evar id) ty))
        (WT1: wt_expr typEnv e2)
        (C: Clight.type_to_chunk ty' = Some c) 
        (TE2: transl_expr e2 = OK te2),
    match_states (Clight.SKlval (Expr (Csyntax.Evar id) ty) env 
                      (Clight.EKassign1 e2 ty' k))
                 (SKstmt (Sassign id te2) tenv tk)
  | match_assign_lval_step:
    forall e1 e2 te1 te2 typEnv k tk ty c nbrk ncnt env tenv 
        (MENV: match_env typEnv env tenv)
        (WTB: wt_stmt typEnv (bodyOfCont (Clight.call_cont k)))   
        (MK: match_cont env tenv typEnv nbrk ncnt k tk)
        (WT1: wt_stmt typEnv (Csyntax.Sassign e1 e2))
        (WT2: wt_expr typEnv e1)
        (WT3: wt_expr typEnv e2)
        (AM: access_mode ty = By_value c)   
        (TE1: transl_lvalue e1 = OK te1)
        (TE2: transl_expr e2 = OK te2),
    match_states (Clight.SKlval e1 env (Clight.EKassign1 e2 ty k))
                 (SKexpr te1 tenv (EKstoreaddr c te2 tk))
  | match_assign_lval_ptr:
    forall e2 te2 typEnv k tk  p c id ty ty' nbrk ncnt env tenv
        (MENV: match_env typEnv env tenv)
        (WTB: wt_stmt typEnv (bodyOfCont (Clight.call_cont k)))
        (MK: match_cont env tenv typEnv nbrk ncnt k tk)
        (EV: eval_var_addr tge tenv id p)
        (WT1: wt_expr typEnv (Expr (Csyntax.Evar id) ty))
        (WT2: wt_expr typEnv e2)
        (AM: access_mode ty' = By_value c)  
        (TE2: transl_expr e2 = OK te2),
    match_states (Clight.SKval (Vptr p) env (Clight.EKassign1 e2 ty' k))
                 (SKexpr (Eaddrof id) tenv (EKstoreaddr c te2 tk))
  | match_assign_lval_stutter:
    forall e2 te2 typEnv k tk  p id ty ty' c nbrk ncnt env tenv
        (MENV: match_env typEnv env tenv)
        (WTB: wt_stmt typEnv (bodyOfCont (Clight.call_cont k)))
        (MK: match_cont env tenv typEnv nbrk ncnt k tk)
        (C : Clight.type_to_chunk ty' = (Some c))
        (EV: eval_var_ref tge tenv id p c)  
        (AM: access_mode ty = By_value c)  
        (WT1: wt_expr typEnv (Expr (Csyntax.Evar id) ty))
        (WT2: wt_expr typEnv e2)
        (TE2: transl_expr e2 = OK te2),
    match_states (Clight.SKval (Vptr p) env (Clight.EKassign1 e2 ty' k))
                 (SKstmt (Sassign id te2) tenv tk)
  | match_call:
    forall typEnv k tk fd opt_lhs topt_lhs vs nbrk ncnt tfd env tenv 
        (MENV: match_env typEnv env tenv)
        (WTB: wt_stmt typEnv (bodyOfCont (Clight.call_cont k)))
        (WT: wt_fundef (global_typenv prog) fd) 
        (MK: match_cont env tenv typEnv nbrk ncnt k tk),
    wt_optexpr_lhs typEnv opt_lhs ->
    match_lhs opt_lhs topt_lhs ->
    transl_fundef fd = OK tfd ->
    match_states (Clight.SKcall vs (Clight.Kcall opt_lhs fd env k))
                 (SKcall vs (Kcall topt_lhs tfd tenv tk))
  | match_while:
    forall typEnv k tk e te s ts nbrk ncnt env tenv 
      (MENV: match_env typEnv env tenv)
      (WTB: wt_stmt typEnv (bodyOfCont (Clight.call_cont k)))
      (WT: wt_stmt typEnv (Swhile e s))
      (MK: match_cont env tenv typEnv nbrk ncnt k tk),
    exit_if_false e = OK te ->
    transl_statement 1 0 s = OK ts ->
    match_states (Clight.SKstmt (Swhile e s) env k)
                 (SKstmt te tenv
                    (Kseq (Sblock ts)
                          (Kseq (Sloop (Sseq te (Sblock ts)))
                                (Kblock tk))))
  | match_dowhile:
    forall typEnv k tk e te s ts nbrk ncnt env tenv
      (MENV: match_env typEnv env tenv)
      (WTB: wt_stmt typEnv (bodyOfCont (Clight.call_cont k)))
      (WT: wt_stmt typEnv (Sdowhile e s))
      (MK: match_cont env tenv typEnv nbrk ncnt k tk),
    exit_if_false e = OK te ->
    transl_statement 1 0 s = OK ts ->
    match_states (Clight.SKstmt (Sdowhile e s) env k)
                 (SKstmt (Sblock ts) tenv
                    (Kseq te
                          (Kseq (Sloop (Sseq (Sblock ts) te))
                                (Kblock tk))))
  | match_forCond:
    forall typEnv k tk e2 te2 s ts s3 ts3 nbrk ncnt env tenv
      (MENV: match_env typEnv env tenv)
      (WTB: wt_stmt typEnv (bodyOfCont (Clight.call_cont k)))
      (WT: wt_stmt typEnv (Sfor Csyntax.Sskip e2 s3 s))
      (MK: match_cont env tenv typEnv nbrk ncnt k tk),
    exit_if_false e2 = OK te2 ->
    transl_statement nbrk ncnt s3 = OK ts3 ->
    transl_statement 1 0 s = OK ts ->
    match_states (Clight.SKstmt Csyntax.Sskip env (Clight.KforCond e2 s3 s k))
                 (SKstmt (Sseq te2
                            (Sseq (Sblock ts) ts3))
                         tenv
                        (Kseq (Sloop (Sseq te2 (Sseq (Sblock ts) ts3)))
                              (Kblock tk)))
  | match_Switch:
    forall typEnv e te ls tls k tk nbrk ncnt env tenv
      (MENV: match_env typEnv env tenv)
      (WTB: wt_stmt typEnv (bodyOfCont (Clight.call_cont k)))
      (WT: wt_stmt typEnv (Csyntax.Sswitch e ls))
      (MK: match_cont env tenv typEnv nbrk ncnt k tk),
    transl_expr e = OK te ->
    transl_lbl_stmt 0%nat (S ncnt) ls = OK tls ->
    match_states (Clight.SKstmt (Csyntax.Sswitch e ls) env k)
                 (SKstmt (Sswitch te tls) tenv (Kblock tk))
  | match_Alloc:
    forall typEnv tenv env nbrk ncnt vs tfn fn optid toptid k'  
           tk' env' tenv' args targs
       (MENV: match_env typEnv env tenv)
       (TV: transl_vars args = OK targs)
       (PARS: forall id ty, 
               In (id, ty) fn.(Csyntax.fn_params) ->
              (typEnv!id = Some ty /\ ~ In id (map (@fst _ _) args))
              \/ (In (id,ty) args))
       (ND: NoDup (map (@fst _ _) args))
       (WT: wt_stmt (add_vars typEnv args) fn.(Csyntax.fn_body))
       (TF: transl_function fn = OK tfn)
       (MK: match_cont env tenv typEnv nbrk ncnt 
             (Clight.Kcall optid (Internal fn) env' k')
             (Kcall toptid (Ast.Internal tfn) tenv' tk')),
    match_states (Clight.SKalloc vs args env 
                     (Clight.Kcall optid (Internal fn) env' k'))
                 (SKalloc vs targs tenv 
                     (Kcall toptid (Ast.Internal tfn) tenv' tk'))
  | match_Bind:
    forall typEnv tenv env nbrk ncnt tfn fn k' tk' env' tenv' args targs
           optid toptid vs
       (MENV: match_env typEnv env tenv)
       (ARGS: transl_params args = OK targs)
       (WT: wt_stmt typEnv fn.(Csyntax.fn_body))
       (PARS: forall id ty, In (id, ty) args -> typEnv ! id = Some ty) 
       (MK: match_cont env tenv typEnv nbrk ncnt 
             (Clight.Kcall optid (Internal fn) env' k')
             (Kcall toptid (Ast.Internal tfn) tenv' tk')),
    match_states (Clight.SKbind fn vs args env 
                     (Clight.Kcall optid (Internal fn) env' k'))
                 (SKbind tfn vs (map (@fst _ _) targs) tenv
                     (Kcall toptid (Ast.Internal tfn) tenv' tk'))
  | match_ext_call:
    forall typEnv k tk opt_lhs topt_lhs nbrk ncnt env tenv sig tys ty id tfd
        (MENV: match_env typEnv env tenv)
        (WTB: wt_stmt typEnv (bodyOfCont (Clight.call_cont k)))
        (WT: wt_fundef (global_typenv prog) (External id tys ty)) 
        (WTS: wt_optexpr_lhs typEnv opt_lhs)
        (MK: match_cont env tenv typEnv nbrk ncnt k tk),
    match_lhs opt_lhs topt_lhs -> 
    Csyntax.opttyp_of_type ty = sig.(sig_res) ->
    transl_fundef (External id tys ty) = OK tfd ->
    match_states (Clight.SKExternal (External id tys ty) opt_lhs env k)
                 (SKexternal sig topt_lhs tenv tk)
  | match_ext_ret:
    forall typEnv k tk opt_lhs topt_lhs nbrk ncnt env tenv tys ty id evl
        (MENV: match_env typEnv env tenv)
        (WTB: wt_stmt typEnv (bodyOfCont (Clight.call_cont k)))
        (WT: wt_fundef (global_typenv prog) (External id tys ty)) 
        (WTS: wt_optexpr_lhs typEnv opt_lhs)
        (MK: match_cont env tenv typEnv nbrk ncnt k tk),
    match_lhs opt_lhs topt_lhs -> 
    match_states (Clight.SKoptstorevar opt_lhs (val_of_eval evl) env k)
                 (SKexternalReturn topt_lhs (val_of_eval evl) tenv tk)
  | match_ext_ret_assign:
    forall typEnv k tk v nbrk ncnt env tenv (* tys *) ty id
        (MENV: match_env typEnv env tenv)
        (WTB: wt_stmt typEnv (bodyOfCont (Clight.call_cont k)))
        (* WT: wt_fundef (global_typenv prog) (External id tys ty) *) 
        (WTS: typEnv ! id = Some ty)
        (MK: match_cont env tenv typEnv nbrk ncnt k tk),
    match_states (Clight.SKoptstorevar (Some (id, ty)) v env k)
                 (SKval v tenv (EKassign id tk)).

Ltac dest := repeat match goal with
   | H : match ?a with
        | Some x => _
        | None => _
        end = _ |- _ => destruct a as [] _eqn: ?; clarify
   | H : _, H': _ |- _ => specialize (H _ _ _ H'); clarify
   end.

Scheme stmt_ind :=     Induction for statement Sort Prop 
  with lbl_stmt_ind := Induction for labeled_statements Sort Prop. 

Lemma match_call_cont_label:
  forall l s s' k k'
  (LAB: Clight.find_label l s k = Some (s', k')),
  Clight.call_cont k = Clight.call_cont k'.
Proof.
  intro.
  set (PLS ls := forall ls' k k',
       Clight.find_label_ls l ls k = Some (ls', k') ->
       Clight.call_cont k = Clight.call_cont k'). 

  induction s using stmt_ind with (P0 := PLS);
     subst PLS; simpl; intros; try done; dest. 
  destruct ident_eq; clarify. dest.
Qed.

Lemma sorted_unique2:
  forall A (le : A -> A -> Prop) l l',
    (forall x y, In x l -> In y l -> le x y -> le y x -> x = y) ->
    Permutation l l' ->
    Sorted _ le l ->
    Sorted _ le l' ->
    l = l'.
Proof.
  intros A le l l'; revert l'.
  induction l as [|h l IH].
  intros l' SYM P S1 S2. by apply sym_eq, Permutation_nil.
  
  intros l' SYM P S1 S2.
  destruct (in_app_decomp _ _ _ (Permutation_in _ P (in_eq h _)))
    as [l1 [l2 ->]].
  destruct l1 as [|h1 t1]. 
    simpl in *; f_equal.
    apply IH; [ | eby eapply Permutation_cons_inv |
               by inv S1 | by inv S2].
    by intros ? ? ? ?; apply SYM; vauto.
  rewrite <- app_comm_cons.
  assert (Eh : h = h1).
    apply SYM; vauto.
         eapply Permutation_in. eby apply Permutation_sym.
         by left.
      inversion S1 as [| ? ? LST SREST]; subst.
      apply LST. eapply Permutation_in. 
      apply Permutation_sym. eapply Permutation_cons_app_inv. 
      eapply P. rewrite <- app_comm_cons. apply in_eq.
    rewrite <- app_comm_cons in S2.
    inversion S2 as [| ? ? LST' SREST']; subst.
    apply LST'. apply in_or_app. right. apply in_eq.
  rewrite <- Eh in *. f_equal.
  apply IH. intros ? ? ? ?; apply SYM; vauto.
      rewrite <- app_comm_cons in P.
      eby eapply Permutation_cons_inv.
    by inv S1.
  rewrite <- app_comm_cons in S2. by inv S2.
Qed.

Lemma match_sorted_pointers:
  forall typenv env tenv,
  match_env typenv env tenv ->
  Clight.sorted_pointers_of_env env = sorted_pointers_of_env tenv.
Proof.
  intros.
  unfold Clight.sorted_pointers_of_env, sorted_pointers_of_env.
  destruct mergesort as [l (SORT & PERM & _)].
  destruct mergesort as [l' (SORT' & PERM' & _)].
  replace (fun idpk : positive * (pointer * var_kind) => fst (snd (idpk))) with
    (fun idpk : positive * (pointer * var_kind) => snd (fst idpk, fst (snd idpk))).
  rewrite <- (map_map (fun idpk : positive * (pointer * var_kind) => 
                          (fst idpk, fst (snd idpk)))
                      (fun pk : (positive * pointer) => (snd pk))).
  f_equal.
  2: apply extensionality; intro; done. 
  eapply sorted_unique2.  3: edone.
  intros [x1 x2] [y1 y2] INx INy LEx LEy. 
  simpl in *; unfold Ple in *.
  assert (Zpos x1 = Zpos y1) by omega. clarify.
  eapply Permutation_in in INy; try eassumption.
  eapply Permutation_in in INx; try eassumption.
  eapply PTree.elements_complete in INy. eapply PTree.elements_complete in INx.
  rewrite INx in INy. clarify.
  apply (Permutation_trans PERM).
  eapply Permutation_sym, Permutation_trans.
  eapply Permutation_map. edone.
  eapply NoDup_Permutation.
  apply list_map_norepet. eapply nodup_map_rev. apply PTree.elements_keys_norepet.
  intros x y INx INy N. destruct x; destruct y. simpl.
  intro E. clarify. 
  eapply PTree.elements_complete in INy. eapply PTree.elements_complete in INx.
  rewrite INx in INy; clarify.
  eapply nodup_map_rev. apply PTree.elements_keys_norepet.
  intro x.  
  eapply iff_trans. 
    eapply in_map_iff.
  split.
     intros [[? [? ?]] [? ?]]; clarify. simpl.
     apply PTree.elements_complete in H1.
     destruct H as [? X ?].
      eapply PTree.elements_correct. eby eapply X.
  intro INx. destruct x as [? ?]; eapply PTree.elements_complete in INx.
  destruct H as [X ? ?].
  pose proof (X _ _ INx) as (k & typ & ? & ? & ?).
  by eexists (_, (_, k)); split; [simpl| apply PTree.elements_correct].
  clear PERM' PERM.
  induction SORT' as [| x l' H' IH]; simpl.
   vauto.
   econstructor; try eassumption. 
   intros [? ?] INx. apply in_map_iff in INx. destruct INx as [[? [? ?]] [? INx]].
   by clarify; eapply H' in INx.
Qed. 


Lemma transl_lbl_stmt_1:
  forall nbrk ncnt n sl tsl,
  transl_lbl_stmt nbrk ncnt sl = OK tsl ->
  transl_lbl_stmt nbrk ncnt
     (Clight.select_switch n sl) = OK (select_switch n tsl).
Proof.
  induction sl; intros.
  monadInv H. simpl. rewrite EQ. auto.
  generalize H; intro TR. monadInv TR. simpl. 
  destruct (Int.eq i n). auto. auto. 
Qed.

Lemma transl_lbl_stmt_2:
  forall nbrk ncnt sl tsl,
  transl_lbl_stmt nbrk ncnt sl = OK tsl ->
  transl_statement nbrk ncnt (Clight.seq_of_labeled_statement sl) = OK (seq_of_lbl_stmt tsl).
Proof.
  induction sl; intros.
  monadInv H. simpl. auto.
  monadInv H. simpl. rewrite EQ; simpl. rewrite (IHsl _ EQ1). simpl. auto.
Qed.

Lemma wt_select_switch:
  forall n tyenv sl,
  wt_lblstmts tyenv sl ->
  wt_lblstmts tyenv (Clight.select_switch n sl).
Proof.
  induction 1. simpl.
  apply wt_LSdefault; done. 
  unfold Clight.select_switch.
  destruct (Int.eq n0 n).
  apply wt_LScase; done.
  done.
Qed.

Lemma wt_seq_of_labeled_statement:
  forall tyenv sl,
  wt_lblstmts tyenv sl ->
  wt_stmt tyenv (Clight.seq_of_labeled_statement sl).
Proof.
  induction 1; simpl. done.
  apply wt_Ssequence; done. 
Qed.

Lemma functions_well_typed:
  forall v f,
  Genv.find_funct ge v = Some f ->
  wt_fundef (global_typenv prog) f.
Proof.
  intros. destruct WTPROG.
  unfold Genv.find_funct in H; destruct v; try done.
  destruct (globenv_fn_in p f). done.
  apply (wt_program_funct x f H0).
Qed.

(** * Properties of the translation functions *)

Lemma map_partial_names:
  forall (A B: Type) (f: A -> res B)
         (l: list (ident * A)) (tl: list (ident * B)),
  map_partial prefix_var_name f l = OK tl ->
  List.map (@fst ident B) tl = List.map (@fst ident A) l.
Proof.
  induction l; simpl.
  intros. inversion H. reflexivity.
  intro tl. destruct a as [id x]. destruct (f x); try congruence.
  caseEq (map_partial prefix_var_name f l); simpl; intros; try congruence.
  inv H0. simpl. decEq. auto.
Qed.
   
Lemma map_partial_append:
  forall (A B: Type) (f: A -> res B)
         (l1 l2: list (ident * A)) (tl1 tl2: list (ident * B)),
  map_partial prefix_var_name f l1 = OK tl1 ->
  map_partial prefix_var_name f l2 = OK tl2 ->
  map_partial prefix_var_name f (l1 ++ l2) = OK (tl1 ++ tl2).
Proof.
  induction l1; intros until tl2; simpl.
  intros. inversion H. simpl; auto.
  destruct a as [id x]. destruct (f x); try congruence.
  caseEq (map_partial prefix_var_name f l1); simpl; intros; try congruence.
  inv H0. rewrite (IHl1 _ _ _ H H1). auto.
Qed.
 
Lemma transl_params_names:
  forall vars tvars,
  transl_params vars = OK tvars ->
  List.map (@fst ident memory_chunk) tvars = Ctyping.var_names vars.
Proof.
  exact (map_partial_names _ _ chunk_of_type).
Qed.

Lemma transl_vars_names:
  forall vars tvars,
  transl_vars vars = OK tvars ->
  List.map (@fst ident var_kind) tvars = Ctyping.var_names vars.
Proof.
  exact (map_partial_names _ _ var_kind_of_type).
Qed.

Lemma transl_names_norepet:
  forall params vars sg tparams tvars body,
  NoDup (var_names params ++ var_names vars) ->
  transl_params params = OK tparams ->
  transl_vars vars = OK tvars ->
  let f := Csharpminor.mkfunction sg tparams tvars body in
  NoDup (fn_params_names f ++ fn_vars_names f).
Proof.
  intros. unfold fn_params_names, fn_vars_names, f. simpl.
  rewrite (transl_params_names _ _ H0).
  rewrite (transl_vars_names _ _ H1).
  auto.
Qed.

Lemma transl_vars_append:
  forall l1 l2 tl1 tl2,
  transl_vars l1 = OK tl1 -> transl_vars l2 = OK tl2 ->
  transl_vars (l1 ++ l2) = OK (tl1 ++ tl2).
Proof.
  exact (map_partial_append _ _ var_kind_of_type).
Qed.

Lemma transl_params_vars:
  forall params tparams,
  transl_params params = OK tparams ->
  transl_vars params =
  OK (List.map (fun id_chunk => (fst id_chunk, Vscalar (snd id_chunk))) tparams).
Proof.
  induction params; intro tparams; simpl.
  intros. inversion H. reflexivity.
  destruct a as [id x]. 
  unfold chunk_of_type. caseEq (access_mode x); try congruence.
  intros chunk AM. 
  caseEq (transl_params params); simpl; intros; try congruence.
  inv H0. 
  rewrite (var_kind_by_value _ _ AM). 
  rewrite (IHparams _ H). reflexivity.
Qed.

Lemma transl_fn_variables:
  forall params vars sg tparams tvars body,
  transl_params params = OK tparams ->
  transl_vars vars = OK tvars ->
  let f := Csharpminor.mkfunction sg tparams tvars body in
  transl_vars (params ++ vars) = OK (fn_variables f).
Proof.
  intros. 
  generalize (transl_params_vars _ _ H); intro.
  rewrite (transl_vars_append _ _ _ _ H1 H0).
  reflexivity.
Qed.

Section FIND_LABEL.						
Variable lbl: label.								

Remark exit_if_false_no_label:
 forall a s, exit_if_false a = OK s -> forall k, find_label lbl s k = None.
Proof.	
  intros. unfold exit_if_false in H. monadInv H. simpl. auto.
Qed.													       

(*
  set (PLS ls := forall ls' k k',
       Clight.find_label_ls l ls k = Some (ls', k') ->
       Clight.call_cont k = Clight.call_cont k'). 

  induction s using stmt_ind with (P0 := PLS);
     subst PLS; simpl; intros; try done; dest. 
  destruct ident_eq; clarify. dest.
*)

Lemma transl_find_label:							
  forall env tenv tyenv s nbrk ncnt k ts tk
  (WT: wt_stmt tyenv s)
  (TR: transl_statement nbrk ncnt s = OK ts)			       
  (MC: match_cont env tenv tyenv nbrk ncnt k tk),
  match Clight.find_label lbl s k with					       
  | None => find_label lbl ts tk = None					       
  | Some (s', k') =>							       
      exists ts', exists tk', exists nbrk', exists ncnt',		       
      find_label lbl ts tk = Some (ts', tk')				       
      /\ transl_statement nbrk' ncnt' s' = OK ts'			       
      /\ match_cont env tenv tyenv nbrk' ncnt' k' tk'	
      /\ wt_stmt tyenv s'						       
  end. 
Proof.
  intros until s.

  induction s using stmt_ind with (P0 := fun ls =>
    forall nbrk ncnt k tls tk
    (WT: wt_lblstmts tyenv ls)						       
    (TR: transl_lbl_stmt nbrk ncnt ls = OK tls)				       
    (MC: match_cont env tenv tyenv nbrk ncnt k tk),
    match Clight.find_label_ls lbl ls k with				       
    | None => find_label_ls lbl tls tk = None				       
    | Some (s', k') =>							       
        exists ts', exists tk', exists nbrk', exists ncnt',		       
        find_label_ls lbl tls tk = Some (ts', tk')			       
        /\ transl_statement nbrk' ncnt' s' = OK ts'			       
        /\ match_cont env tenv tyenv nbrk' ncnt' k' tk'
        /\ wt_stmt tyenv s'						       
    end) ;
 intros; inv WT; try done; try (monadInv TR); simpl; try done.
(* assign *)
  simpl in TR. destruct (is_variable e); monadInv TR.
  unfold var_set in EQ0. destruct (access_mode (typeof e)); inv EQ0. auto.
  unfold make_store in EQ2. destruct (access_mode (typeof e)); inv EQ2. auto.
(* call *)
  simpl in TR. destruct (classify_fun (typeof e)); monadInv TR. auto.
(* seq *)
  exploit (IHs1 nbrk ncnt (Clight.Kseq s2 k)); 
      eauto. constructor; eauto.			       
  destruct (Clight.find_label lbl s1 (Clight.Kseq s2 k)) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B [C D]]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H. eapply IHs2; eauto.
(* ifthenelse *)
  exploit IHs1; eauto.
  destruct (Clight.find_label lbl s1 k) as [[s' k'] | ].	
  intros [ts' [tk' [nbrk' [ncnt' [A [B [C D]]]]]]].	
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.		
  intro. rewrite H. eapply IHs2; eauto.	
(* while *)		
  rewrite (exit_if_false_no_label _ _ EQ).
  eapply IHs; eauto. econstructor; eauto.		
(* dowhile *)	
  exploit (IHs 1%nat 0%nat (Clight.Kdowhile s e k)); eauto. 
       econstructor; eauto.
  destruct (Clight.find_label lbl s (Clight.Kdowhile s e k)) as [[s' k'] | ].	
  intros [ts' [tk' [nbrk' [ncnt' [A [B [C D]]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.	
  intro. rewrite H. by eapply exit_if_false_no_label; eauto.
(* for *)	
  simpl in TR. destruct (is_Sskip s1); monadInv TR.	
  simpl. rewrite (exit_if_false_no_label _ _ EQ).
  exploit (IHs3 1%nat 0%nat (Clight.KforIncr e s2 s3 k)); eauto. 
    econstructor; eauto.
  destruct (Clight.find_label lbl s3 (Clight.KforIncr e s2 s3 k)) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B [C D]]]]]]]. 	
  rewrite A.
     exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.	
  intro. rewrite H.	
  eapply IHs2; eauto.
   econstructor; edone.
  exploit (IHs1 nbrk ncnt (Clight.KforCond e s2 s3 k)); eauto.
    econstructor; eauto.
  simpl. rewrite (exit_if_false_no_label _ _ EQ1).
  destruct (Clight.find_label lbl s1 (Clight.KforCond e s2 s3 k)) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B [C D]]]]]]]. 	
  rewrite A.
     exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H.
  exploit (IHs3 1%nat 0%nat (Clight.KforIncr e s2 s3 k)); eauto.
    econstructor; eauto.
  destruct (Clight.find_label lbl s3 (Clight.KforIncr e s2 s3 k)) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B [C D]]]]]]]. 	
  rewrite A.
     exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H0.
  eapply IHs2; eauto.
   econstructor; edone.
(* return *)	
  simpl in TR. destruct o; monadInv TR. auto. by auto.	
(* switch *)	
  eapply IHs with (k := Clight.Kswitch k); eauto. 
    by econstructor; eauto. 
(* label *)	
  destruct (ident_eq lbl l).
  exists x; exists tk; exists nbrk; exists ncnt; auto.	
  by eapply IHs; eauto.
(* default *)		
  eapply IHs; eauto.
(* case *)	
  exploit (IHs nbrk ncnt (Clight.Kseq (Clight.seq_of_labeled_statement l) k)); eauto.
  econstructor; eauto. apply transl_lbl_stmt_2; eauto.
  apply wt_seq_of_labeled_statement; auto.
  destruct (Clight.find_label lbl s (Clight.Kseq (Clight.seq_of_labeled_statement l) k)) as [[s' k'] | ].		 
  intros [ts' [tk' [nbrk' [ncnt' [A [B [C D]]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H.
  eapply IHs0; eauto.	
Qed.							

End FIND_LABEL.

Definition order (s s': Clight.state) : Prop := (measure s < measure s')%nat.

End CLIGHT_DEFS.

Open Scope string_scope.
Open Scope list_scope.

(*
Tactic Notation "cl_step_cases" tactic(first) tactic(c) :=
    first; [
      c "StepConstInt" |
      c "StepConstFloat" |
      c "StepVarExprByValue" |
      c "StepVarLocal" |
      c "StepVarGlobal" |
      c "StepLoadByValue" |
      c "StepLoadNotByValue" |
      c "StepAddr" |
      c "StepEcondition" |  
      c "StepEconditiontrue" |
      c "StepEconditionfalse" |
      c "StepDeref" |
      c "StepDerefLval" |
      c "StepField" |
      c "StepFstruct1" |
      c "StepFstruct2" |
      c "StepFunion" |
      c "StepSizeOf" |
      c "StepUnop1" |
      c "StepUnop" |
      c "StepBinop1" |
      c "StepBinop2" |
      c "StepBinop" |
      c "StepCast1" |
      c "StepCast2" |
      c "StepAndbool" |
      c "StepOrbool" |
      c "StepThread" |
      c "StepThreadFn" |
      c "StepThreadEvt" |
      c "StepAssign1" |
      c "StepAssign2" |
      c "StepAssign" |
      c "StepSeq" |
      c "StepCallNone" |
      c "StepCallSome" |
      c "StepCallArgsNone" |
      c "StepCallArgs1" |
      c "StepCallArgs2" |
      c "StepCallFinish" |
      c "StepContinue" |
      c "StepBreak" |
      c "StepIfThenElse" |
      c "StepIfThenElseTrue" |
      c "StepIfThenElseFalse" |
      c "StepWhile" |
      c "StepWhileTrue" |
      c "StepWhileFalse" |
      c "StepContinueWhile" |
      c "StepBreakWhile" |
      c "StepDoWhile" |
      c "StepDoWhileTrue" |
      c "StepDoWhileFalse" |
      c "StepDoContinueWhile" |
      c "StepDoBreakWhile" |
      c "StepForInit" |
      c "StepForCond" |
      c "StepForTrue" | 
      c "StepForFalse" |
      c "StepForIncr" |
      c "StepForBreak" |
      c "StepForContinue" |
      c "StepReturnNone" |
      c "StepReturn1" |
      c "StepReturnSome" |
      c "StepReturnSome1" |
      c "StepSwitch" |
      c "StepSelectSwitch" |
      c "StepBreakSwitch" |
      c "StepContinueSwitch" |
      c "StepLabel" |
      c "StepGoto" |
      c "StepFunctionInternal" |
      c "StepAllocLocal" |
      c "StepBindArgsStart" |
      c "StepBindArgs" |
      c "StepTransferFun" |
      c "StepExternalCall" |
      c "StepExternalReturn" |
      c "StepExternalStoreSomeLocal" |
      c "StepExternalStoreSomeGlobal" |
      c "StepExternalStoreNone" |
      c "StepSkip" |
      c "StepWhileLoop" |
      c "StepDoWhileLoop" |
      c "StepSkipSwitch" |
      c "StepReturnNoneFinish" |
      c "StepReturnSomeFinishLocal" |
      c "StepReturnSomeFinishGlobal" |
      c "StepStop"]. 
*)


Tactic Notation "cl_step_cases" tactic(first) tactic(c) :=
    first; [
      c "StepConstInt" |
      c "StepConstFloat" |
      c "StepVarExprByValue" |
      c "StepVarLocal" |
      c "StepVarGlobal" |
      c "StepLoadByValue" |
      c "StepLoadNotByValue" |
      c "StepAddr" |
      c "StepEcondition" |
      c "StepEconditiontrue" |
      c "StepEconditionfalse" |
      c "StepDeref" |
      c "StepDerefLval" |
      c "StepField" |
      c "StepFstruct1" |
      c "StepFstruct2" |
      c "StepFunion" |
      c "StepSizeOf" |
      c "StepUnop1" |
      c "StepUnop" |
      c "StepBinop1" |
      c "StepBinop2" |
      c "StepBinop" |
      c "StepCast1" |
      c "StepCast2" |
      c "StepAndbool" |
      c "StepOrbool" |
      c "StepThread" |
      c "StepThreadFn" |
      c "StepThreadEvt" |
      c "StepAssign1" |
      c "StepAssign2" |
      c "StepAssign" |
      c "StepSeq" |
      c "StepCall" |
      c "StepCallargsnone" |
      c "StepCallArgs1" |
      c "StepCallArgs2" |
      c "StepCallFinish" |
      c "StepAtomic" |
      c "StepAtomicArgs" |
      c "StepAtomicFinishNone" |
      c "StepAtomicFinishSome" |
      c "StepFence" |
      c "StepContinue" |
      c "StepBreak" |
      c "StepIfThenElse" |
      c "StepIfThenElseTrue" |
      c "StepIfThenElseFalse" |
      c "StepWhile" |
      c "StepWhileTrue" |
      c "StepWhileFalse" |
      c "StepContinueWhile" |
      c "StepBreakWhile" |
      c "StepDoWhile" |
      c "StepDoWhileTrue" |
      c "StepDoWhileFalse" |
      c "StepDoContinueWhile" |
      c "StepDoBreakWhile" |
      c "StepForInit" |
      c "StepForCond" |
      c "StepForTrue" |
      c "StepForFalse" |
      c "StepForIncr" |
      c "StepForBreak" |
      c "StepForContinue" |
      c "StepReturnNone" |
      c "StepReturn1" |
      c "StepReturnSome" |
      c "StepReturnSome1" |
      c "StepSwitch" |
      c "StepSelectSwitch" |
      c "StepBreakSwitch" |
      c "StepContinueSwitch" |
      c "StepLabel" |
      c "StepGoto" |
      c "StepFunctionInternal" |
      c "StepAllocLocal" |
      c "StepBindArgsStart" |
      c "StepBindArgs" |
      c "StepTransferFun" |
      c "StepExternalCall" |
      c "StepExternalReturn" |
      c "StepExternalStoreSomeLocal" |
      c "StepExternalStoreSomeGlobal" |
      c "StepExternalStoreNone" |
      c "StepSkip" |
      c "StepWhileLoop" |
      c "StepDoWhileLoop" |
      c "StepSkipSwitch" |
      c "StepReturnNoneFinish" |
      c "StepReturnSomeFinishLocal" |
      c "StepReturnSomeFinishGlobal" |
      c "StepStop"].
