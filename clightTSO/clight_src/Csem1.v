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

(* This is first third of Csem.v, from Csem1.v  *)

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
Require Import Ctyping.

Module Clight.

(** The semantics uses two environments.  The global environment
  maps names of functions and global variables to pointers,
  and function pointers to their definitions.  (See module [Globalenvs].) *)

Definition genv := Genv.t fundef.

(** The local environment maps local variables to pointers. **)
Definition env := PTree.t pointer. (* map variable -> location *)
Definition empty_env: env := (PTree.empty pointer).

(** Interpretation of values as truth values.
  Non-zero integers, non-zero floats and non-null pointers are
  considered as true.  The integer zero (which also represents
  the null pointer) and the float 0.0 are false. *)

Inductive is_false: val -> type -> Prop :=
  | is_false_int: forall sz sg,
      is_false (Vint Int.zero) (Tint sz sg)
  | is_false_pointer: forall t,
      is_false (Vint Int.zero) (Tpointer t)
 | is_false_float: forall f sz,
      Float.cmp Ceq f Float.zero ->
      is_false (Vfloat f) (Tfloat sz).

Inductive is_true: val -> type -> Prop :=
  | is_true_int_int: forall n sz sg,
      n <> Int.zero ->
      is_true (Vint n) (Tint sz sg)
  | is_true_pointer_int: forall p sz sg,
      is_true (Vptr p) (Tint sz sg)
  | is_true_int_pointer: forall n t,
      n <> Int.zero ->
      is_true (Vint n) (Tpointer t)
  | is_true_pointer_pointer: forall p t,
      is_true (Vptr p) (Tpointer t)
 | is_true_float: forall f sz,
      Float.cmp Cne f Float.zero ->
      is_true (Vfloat f) (Tfloat sz).


(** Executable versions of the above *)

Definition eval_true (v: val) (ty: type) : {is_true v ty} + {~ is_true v ty}.
Proof.
  intros. destruct v; destruct ty;
  try (destruct (Int.eq_dec i Int.zero); subst);
  try (destruct (Float.cmp Cne f Float.zero) as [] _eqn: X);
  try (by right; intro H; inv H; try rewrite X in *; auto);
  try (by left; constructor; auto).
Defined.

Definition eval_false (v: val) (ty: type) : {is_false v ty} + {~ is_false v ty}.
Proof.
  intros. destruct v; destruct ty;
  try (destruct (Int.eq_dec i Int.zero); subst);
  try (destruct (Float.cmp Ceq f Float.zero) as [] _eqn: X);
  try (by right; intro H; inv H; try rewrite X in *; auto);
  try (by left; constructor; auto).
Defined.

(** Basic soundness property for booleans. *)

Lemma is_true_is_false_contr:
  forall v t,
    is_true v t -> is_false v t -> False.
Proof.
  intros v t IST ISF.
  inv IST; inv ISF; auto.
  by rewrite Float.cmp_ne_eq in H; case (negP H).
Qed.

Inductive bool_of_val : val -> type -> val -> Prop :=
  | bool_of_val_true:   forall v ty, 
         is_true v ty -> 
         bool_of_val v ty Vtrue
  | bool_of_val_false:   forall v ty,
        is_false v ty ->
        bool_of_val v ty Vfalse.

Definition blocks_of_env (e:env) : list pointer :=
   (List.map (@snd ident pointer) (PTree.elements e)).

Definition sorted_pointers_of_env (e:env) : list pointer :=
 let (l,_) := mergesort _ 
                (fun x y => Ple (fst x) (fst y)) 
                (fun x y z => Ple_trans (fst x) (fst y) (fst z)) 
                (fun x y => Ple_total (fst x) (fst y))
                (fun x y => ple (fst x) (fst y))
                (PTree.elements e)
 in List.map (fun idpk => (snd idpk)) l.


(** The following [sem_] functions compute the result of an operator
  application.  Since operators are overloaded, the result depends
  both on the static types of the arguments and on their run-time values.
  Unlike in C, automatic conversions between integers and floats
  are not performed.  For instance, [e1 + e2] is undefined if [e1]
  is a float and [e2] an integer.  The Clight producer must have explicitly
  promoted [e2] to a float. *)

Function sem_neg (v: val) (ty: type) : option val :=
  match ty with
  | Tint _ _ =>
      match v with
      | Vint n => Some (Vint (Int.neg n))
      | _ => None
      end
  | Tfloat _ =>
      match v with
      | Vfloat f => Some (Vfloat (Float.neg f))
      | _ => None
      end
  | _ => None
  end.

Function sem_notint (v: val) : option val :=
  match v with
  | Vint n => Some (Vint (Int.xor n Int.mone))
  | _ => None
  end.

Function sem_notbool (v: val) (ty: type) : option val :=
  match ty with
  | Tint _ _ =>
      match v with
      | Vint n => Some (Val.of_bool (Int.eq n Int.zero))
      | Vptr _  => Some Vfalse
      | _ => None
      end
  | Tpointer _ =>
      match v with
      | Vint n => Some (Val.of_bool (Int.eq n Int.zero))
      | Vptr _  => Some Vfalse
      | _ => None
      end
  | Tfloat _ =>
      match v with
      | Vfloat f => Some (Val.of_bool (Float.cmp Ceq f Float.zero))
      | _ => None
      end
  | _ => None
  end.

Function sem_add (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_add t1 t2 with 
  | add_case_ii =>                      (**r integer addition *)
      match v1, v2 with
      | Vint n1, Vint n2 => Some (Vint (Int.add n1 n2))
      | _,  _ => None
      end
  | add_case_ff =>                      (**r float addition *)
      match v1, v2 with
      | Vfloat n1, Vfloat n2 => Some (Vfloat (Float.add n1 n2))
      | _,  _ => None
      end
  | add_case_pi ty =>                   (**r pointer plus integer *)
      match v1,v2 with
      | Vptr p, Vint n2 => Some (Vptr (Ptr.add p (Int.mul (Int.repr (sizeof ty)) n2)))
      | _,  _ => None
      end   
  | add_case_ip ty =>                   (**r integer plus pointer *)
      match v1,v2 with
      | Vint n1, Vptr p => Some (Vptr (Ptr.add p (Int.mul (Int.repr (sizeof ty)) n1)))
      | _,  _ => None
      end   
  | add_default => None
end.

Function sem_sub (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_sub t1 t2 with
  | sub_case_ii =>               (**r integer subtraction *)
      match v1,v2 with
      | Vint n1, Vint n2 => Some (Vint (Int.sub n1 n2))
      | _,  _ => None
      end 
  | sub_case_ff =>               (**r float subtraction *)
      match v1,v2 with
      | Vfloat f1, Vfloat f2 => Some (Vfloat(Float.sub f1 f2))
      | _,  _ => None
      end
  | sub_case_pi ty =>            (**r pointer minus  *)
      match v1,v2 with
      | Vptr p, Vint n2 => Some (Vptr (Ptr.sub_int p (Int.mul (Int.repr (sizeof ty)) n2)))
      | _,  _ => None
      end
  | sub_case_pp ty =>          (**r pointer minus pointer *)
      match v1,v2 with
      | Vptr p1, Vptr p2 => 
          if zeq (Ptr.block p1) (Ptr.block p2) then
            if Int.eq (Int.repr (sizeof ty)) Int.zero then None
            else Some (Vint (Int.divu (Int.sub (Ptr.offset p1) (Ptr.offset p2))
                            (Int.repr (sizeof ty))))
          else None
      | _, _ => None
      end
  | sub_default => None
  end.
 
Function sem_mul (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
 match classify_mul t1 t2 with
  | mul_case_ii =>
      match v1,v2 with
      | Vint n1, Vint n2 => Some (Vint (Int.mul n1 n2))
      | _,  _ => None
      end
  | mul_case_ff =>
      match v1,v2 with
      | Vfloat f1, Vfloat f2 => Some (Vfloat (Float.mul f1 f2))
      | _,  _ => None
      end
  | mul_default =>
      None
end.

Function sem_div (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
   match classify_div t1 t2 with
  | div_case_I32unsi =>
      match v1,v2 with
      | Vint n1, Vint n2 =>
          if Int.eq n2 Int.zero then None else Some (Vint (Int.divu n1 n2))
      | _,_ => None
      end
  | div_case_ii =>
      match v1,v2 with
       | Vint n1, Vint n2 =>
          if Int.eq n2 Int.zero then None else Some (Vint(Int.divs n1 n2))
      | _,_ => None
      end
  | div_case_ff =>
      match v1,v2 with
      | Vfloat f1, Vfloat f2 => Some (Vfloat(Float.div f1 f2))
      | _,  _ => None
      end 
  | div_default =>
      None
end.

Function sem_mod (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_mod t1 t2 with
  | mod_case_I32unsi =>
      match v1, v2 with
      | Vint n1, Vint n2 =>
          if Int.eq n2 Int.zero then None else Some (Vint (Int.modu n1 n2))
      | _, _ => None
      end
  | mod_case_ii =>
      match v1,v2 with
      | Vint n1, Vint n2 =>
          if Int.eq n2 Int.zero then None else Some (Vint (Int.mods n1 n2))
      | _, _ => None
      end
  | mod_default =>
      None
  end.

Function sem_and (v1 v2: val) : option val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Some (Vint(Int.and n1 n2))
  | _, _ => None
  end .

Function sem_or (v1 v2: val) : option val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Some (Vint(Int.or n1 n2))
  | _, _ => None
  end. 

Function sem_xor (v1 v2: val): option val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Some (Vint(Int.xor n1 n2))
  | _, _ => None
  end.

Function sem_shl (v1 v2: val): option val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 (Int.repr 32) then Some (Vint(Int.shl n1 n2)) else None
  | _, _ => None
  end.

Function sem_shr (v1: val) (t1: type) (v2: val) (t2: type): option val :=
  match classify_shr t1 t2 with 
  | shr_case_I32unsi => 
      match v1,v2 with 
      | Vint n1, Vint n2 =>
          if Int.ltu n2 (Int.repr 32) then Some (Vint (Int.shru n1 n2)) else None
      | _,_ => None
      end
   | shr_case_ii => 
      match v1,v2 with
      | Vint n1,  Vint n2 =>
          if Int.ltu n2 (Int.repr 32) then Some (Vint (Int.shr n1 n2)) else None
      | _,  _ => None
      end
   | shr_default=>
      None
   end.

Function sem_cmp_mismatch (c: comparison): option val :=
  match c with
  | Ceq =>  Some Vfalse
  | Cne =>  Some Vtrue
  | _   => None
  end.

Function sem_cmp (c:comparison)
                  (v1: val) (t1: type) (v2: val) (t2: type) : option val :=
  match classify_cmp t1 t2 with
  | cmp_case_I32unsi =>
      match v1,v2 with
      | Vint n1, Vint n2 => Some (Val.of_bool (Int.cmpu c n1 n2))
      | _,  _ => None
      end
  | cmp_case_ipip =>
      match v1,v2 with
      | Vint n1, Vint n2 => Some (Val.of_bool (Int.cmp c n1 n2))
      | Vptr p1,  Vptr p2  => Val.option_val_of_bool3 (Ptr.cmp c p1 p2)
(*        if zeq (Ptr.block p1) (Ptr.block p2)
           then Some (Val.of_bool (Int.cmp c (Ptr.offset p1) (Ptr.offset p2)))
           else sem_cmp_mismatch c *)
      | Vptr p, Vint n =>
          if Int.eq n Int.zero then sem_cmp_mismatch c else None
      | Vint n, Vptr p =>
          if Int.eq n Int.zero then sem_cmp_mismatch c else None
      | _,  _ => None
      end
  | cmp_case_ff =>
      match v1,v2 with
      | Vfloat f1, Vfloat f2 => Some (Val.of_bool (Float.cmp c f1 f2))  
      | _,  _ => None
      end
  | cmp_default => None
  end.

Definition sem_unary_operation
            (op: unary_operation) (v: val) (ty: type): option val :=
  match op with
  | Onotbool => sem_notbool v ty
  | Onotint => sem_notint v
  | Oneg => sem_neg v ty
  end.

Definition sem_binary_operation
    (op: binary_operation)
    (v1: val) (t1: type) (v2: val) (t2:type) : option val :=
  match op with
  | Oadd => sem_add v1 t1 v2 t2
  | Osub => sem_sub v1 t1 v2 t2 
  | Omul => sem_mul v1 t1 v2 t2
  | Omod => sem_mod v1 t1 v2 t2
  | Odiv => sem_div v1 t1 v2 t2 
  | Oand => sem_and v1 v2  
  | Oor  => sem_or v1 v2 
  | Oxor  => sem_xor v1 v2 
  | Oshl => sem_shl v1 v2 
  | Oshr  => sem_shr v1 t1 v2 t2   
  | Oeq => sem_cmp Ceq v1 t1 v2 t2 
  | One => sem_cmp Cne v1 t1 v2 t2 
  | Olt => sem_cmp Clt v1 t1 v2 t2 
  | Ogt => sem_cmp Cgt v1 t1 v2 t2 
  | Ole => sem_cmp Cle v1 t1 v2 t2 
  | Oge => sem_cmp Cge v1 t1 v2 t2 
  end.

Definition valid_arg (op : binary_operation) (ty1 : type) (ty2 : type) (v : val) : bool :=
 match op with
 | Oadd => match ty1 with
           | (Tint _ _) => match ty2 with
                           | (Tpointer _) => 
                              match v with
                              | (Vint _) => true
                              | _ => false
                              end
                           | (Tarray t0 z) =>
                             match v with
                             | (Vint _) => true
                             | _ => false
                             end
                           | _ => true
                           end
            | (Tpointer _) => match v with
                              | (Vptr _) => true
                              | _ => false
                              end
            | _  => true
            end
 | Osub => match ty1 with
            | (Tpointer _) => match ty2 with
                              | (Tpointer _ ) =>
                                match v with
                                | (Vptr _ ) => true
                                | _ => false
                                end
                              | (Tarray t0 z) => 
                                match v with
                                | (Vptr _ ) => true
                                |  _ => false
                                end
                              | _ => true
                              end
            | (Tarray t0 z) => match ty2 with
                               | (Tarray t1 z1) =>
                                 match v with
                                 | (Vptr _) => true
                                 | _ => false
                                 end
                               | _ => true
                              end
              | _ => true
             end
  | _ => true
 end.
                           
(** Semantic of casts.  [cast v1 t1 t2 v2] holds if value [v1],
  viewed with static type [t1], can be cast to type [t2],
  resulting in value [v2].  *)

Definition cast_int_int (sz: intsize) (sg: signedness) (i: int) : int :=
  match sz, sg with
  | I8, Signed => Int.sign_ext 8 i
  | I8, Unsigned => Int.zero_ext 8 i
  | I16, Signed => Int.sign_ext 16 i
  | I16, Unsigned => Int.zero_ext 16 i 
  | I32, _ => i
  end.

Definition cast_int_float (si : signedness) (i: int) : float :=
  match si with
  | Signed => Float.floatofint i
  | Unsigned => Float.floatofintu i
  end.

Definition cast_float_int (si : signedness) (f: float) : int :=
  match si with
  | Signed => Float.intoffloat f
  | Unsigned => Float.intuoffloat f
  end.

Definition cast_float_float (sz: floatsize) (f: float) : float :=
  match sz with
  | F32 => Float.singleoffloat f
  | F64 => f
  end.

Inductive neutral_for_cast: type -> Prop :=
  | nfc_int: forall sg,
      neutral_for_cast (Tint I32 sg)
  | nfc_ptr: forall ty,
      neutral_for_cast (Tpointer ty)
  | nfc_array: forall ty sz,
      neutral_for_cast (Tarray ty sz)
  | nfc_fun: forall targs tres,
      neutral_for_cast (Tfunction targs tres).

Inductive cast : val -> type -> type -> val -> Prop :=
  | cast_ii:   forall i sz2 sz1 si1 si2,            (**r int to int  *)
      cast (Vint i) (Tint sz1 si1) (Tint sz2 si2)
           (Vint (cast_int_int sz2 si2 i))
  | cast_fi:   forall f sz1 sz2 si2,                (**r float to int *)
      cast (Vfloat f) (Tfloat sz1) (Tint sz2 si2)
           (Vint (cast_int_int sz2 si2 (cast_float_int si2 f)))
  | cast_if:   forall i sz1 sz2 si1,                (**r int to float  *)
      cast (Vint i) (Tint sz1 si1) (Tfloat sz2)
          (Vfloat (cast_float_float sz2 (cast_int_float si1 i)))
  | cast_ff:   forall f sz1 sz2,                    (**r float to float *)
      cast (Vfloat f) (Tfloat sz1) (Tfloat sz2)
           (Vfloat (cast_float_float sz2 f))
  | cast_nn_p: forall p t1 t2, (**r no change in data representation *)
      neutral_for_cast t1 -> neutral_for_cast t2 ->
      cast (Vptr p) t1 t2 (Vptr p)
  | cast_nn_i: forall n t1 t2,     (**r no change in data representation *)
      neutral_for_cast t1 -> neutral_for_cast t2 ->
      cast (Vint n) t1 t2 (Vint n).


(** [load_value_of_type ty v p] computes the value [v] of a datum
  of type [ty] addressed by pointer [p].  If the type [ty] indicates 
  an access by value, the value is returned.  If the type [ty] indicates 
  an access by reference, the pointer value [Vptr p] is returned. *)

Definition load_value_of_type (ty_dest : type) (v: val) (p: pointer): option val :=
  match (access_mode ty_dest) with
  | By_value chunk =>  Some v 
  | By_reference => Some (Vptr p)
  | By_nothing => None
  end.

(** Selection of the appropriate case of a [switch], given the value [n]
  of the selector expression. *)

Fixpoint select_switch (n: int) (sl: labeled_statements)
                       {struct sl}: labeled_statements :=
  match sl with
  | LSdefault _ => sl
  | LScase c s sl' => if Int.eq c n then sl else select_switch n sl'
  end.


(** Turn a labeled statement into a sequence *)

Fixpoint seq_of_labeled_statement (sl: labeled_statements) : statement :=
  match sl with
  | LSdefault s => s
  | LScase c s sl' => Ssequence s (seq_of_labeled_statement sl')
  end.

Definition sem_atomic_statement 
  (astmt : atomic_statement) (args : list val) : option (pointer * rmw_instr) := 
  match astmt, args with
    | AScas, Vptr p :: n :: o :: nil =>
        if (Val.eq_dec o Vundef)
          then None
            else if (Val.has_type o Ast.Tint)
              then if (Val.eq_dec n Vundef)
                then None
                else if (Val.has_type n Ast.Tint)
                  then Some (p, rmw_CAS o n)
                  else None
              else None
    | ASlkinc, Vptr p :: nil => Some (p, rmw_ADD (Vint Int.one))
    | _, _ => None
  end.
