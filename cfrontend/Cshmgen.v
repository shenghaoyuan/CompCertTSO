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

(** Translation from Clight to Csharpminor. *)

(** The main transformations performed by this first part are:
- Resolution of all type-dependent behaviours: overloaded operators
   are resolved, address computations for array and struct accesses
   are made explicit, etc.
- Translation of Clight's loops and [switch] statements into
   Csharpminor's simpler control structures.
*)

Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import Ast.
Require Import Csyntax.
Require Import Cminor.
Require Import Cminorops.
Require Import Csharpminor.

Open Local Scope string_scope.
Open Local Scope error_monad_scope.

(** * Operations on C types *)

Definition signature_of_function (f: Csyntax.function) : signature :=
  mksignature 
   (typlist_of_typelist (type_of_params (Csyntax.fn_params f)))
   (opttyp_of_type (Csyntax.fn_return f)).

Definition chunk_of_type (ty: type): res memory_chunk :=
  match access_mode ty with
  | By_value chunk => OK chunk
  | _ => Error (msg "Cshmgen.chunk_of_type")
  end.

(** [var_kind_of_type ty] returns the Csharpminor ``variable kind''
  (scalar or array) that corresponds to the given Clight type [ty]. *)

Definition var_kind_of_type (ty: type): res var_kind :=
  match ty with
  | Tint I8 Signed => OK(Vscalar Mint8signed)
  | Tint I8 Unsigned => OK(Vscalar Mint8unsigned)
  | Tint I16 Signed => OK(Vscalar Mint16signed)
  | Tint I16 Unsigned => OK(Vscalar Mint16unsigned)
  | Tint I32 _ => OK(Vscalar Mint32)
  | Tfloat F32 => OK(Vscalar Mfloat32)
  | Tfloat F64 => OK(Vscalar Mfloat64)
  | Tvoid => Error (msg "Cshmgen.var_kind_of_type(void)")
  | Tpointer _ => OK(Vscalar Mint32)
  | Tarray _ _ => OK(Varray (Csyntax.sizeof ty))
  | Tfunction _ _ => Error (msg "Cshmgen.var_kind_of_type(function)")
  | Tstruct _ fList => OK(Varray (Csyntax.sizeof ty))
  | Tunion _ fList => OK(Varray (Csyntax.sizeof ty))
  | Tcomp_ptr _ => OK(Vscalar Mint32)
end.
  
(** * Csharpminor constructors *)

(** The following functions build Csharpminor expressions that compute
   the value of a C operation.  Most construction functions take
   as arguments
-  Csharpminor subexpressions that compute the values of the
     arguments of the operation;
-  The C types of the arguments of the operation.  These types
     are used to insert the necessary numeric conversions and to
     resolve operation overloading.
   Most of these functions return an [option expr], with [None] 
   denoting a case where the operation is not defined at the given types.
*)

Definition make_intconst (n: int) :=  Econst (Ointconst n).

Definition make_floatconst (f: float) :=  Econst (Ofloatconst f).

Definition make_floatofint (e: expr) (sg: signedness) :=
  match sg with
  | Signed => Eunop Ofloatofint e
  | Unsigned => Eunop Ofloatofintu e
  end.

Definition make_intoffloat (e: expr) (sg: signedness) :=
  match sg with
  | Signed => Eunop Ointoffloat e
  | Unsigned => Eunop Ointuoffloat e
  end.

(** [make_boolean e ty] returns a Csharpminor expression that evaluates
   to the boolean value of [e].  Recall that:
-  in Csharpminor, [false] is the integer 0,
       [true] any non-zero integer or any pointer
-  in C, [false] is the integer 0, the null pointer, the float 0.0
       [true] is any non-zero integer, non-null pointer, non-null float.
*)
Definition make_boolean (e: expr) (ty: type) :=
  match ty with
  | Tfloat _ => Ebinop (Ocmpf Cne) e (make_floatconst Float.zero) 
  | _ => e
  end.

Definition make_neg (e: expr) (ty: type) :=
  match ty with
  | Tint _ _ => OK (Eunop Onegint e)
  | Tfloat _ => OK (Eunop Onegf e)
  | _ => Error (msg "Cshmgen.make_neg")
  end.

Definition make_notbool (e: expr) (ty: type) :=
  match ty with
  | Tfloat _ => Ebinop (Ocmpf Ceq) e (make_floatconst Float.zero)
  | _ => Eunop Onotbool e
  end.

Definition make_notint (e: expr) (ty: type) :=
  Eunop Onotint e.

Definition make_add (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  match classify_add ty1 ty2 with
  | add_case_ii => OK (Ebinop Oadd e1 e2)
  | add_case_ff => OK (Ebinop Oaddf e1 e2)
  | add_case_pi ty =>
      let n := make_intconst (Int.repr (Csyntax.sizeof ty)) in
      OK (Ebinop Oadd e1 (Ebinop Omul n e2))
  | add_case_ip ty =>
      let n := make_intconst (Int.repr (Csyntax.sizeof ty)) in
      OK (Ebinop Oadd (Ebinop Omul n e1) e2)
  | add_default => Error (msg "Cshmgen.make_add")
  end.

Definition make_sub (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  match classify_sub ty1 ty2 with
  | sub_case_ii => OK (Ebinop Osub e1 e2)
  | sub_case_ff => OK (Ebinop Osubf e1 e2)
  | sub_case_pi ty =>
      let n := make_intconst (Int.repr (Csyntax.sizeof ty)) in
      OK (Ebinop Osub e1 (Ebinop Omul n e2))
  | sub_case_pp ty =>
      let n := make_intconst (Int.repr (Csyntax.sizeof ty)) in
      OK (Ebinop Odivu (Ebinop Osub e1 e2) n)
  | sub_default => Error (msg "Cshmgen.make_sub")
  end.

Definition make_mul (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  match classify_mul ty1 ty2 with
  | mul_case_ii => OK (Ebinop Omul e1 e2)
  | mul_case_ff => OK (Ebinop Omulf e1 e2)
  | mul_default => Error (msg "Cshmgen.make_mul")
  end.

Definition make_div (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  match classify_div ty1 ty2 with
  | div_case_I32unsi => OK (Ebinop Odivu e1 e2)
  | div_case_ii => OK (Ebinop Odiv e1 e2)
  | div_case_ff => OK (Ebinop Odivf e1 e2)
  | div_default => Error (msg "Cshmgen.make_div")
  end.

Definition make_mod (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  match classify_mod ty1 ty2 with
  | mod_case_I32unsi => OK (Ebinop Omodu e1 e2)
  | mod_case_ii=> OK (Ebinop Omod e1 e2)
  | mod_default => Error (msg "Cshmgen.make_mod")
  end.

Definition make_and (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  OK(Ebinop Oand e1 e2).

Definition make_or (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  OK(Ebinop Oor e1 e2).

Definition make_xor (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  OK(Ebinop Oxor e1 e2).

Definition make_shl (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  OK(Ebinop Oshl e1 e2).

Definition make_shr (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  match classify_shr ty1 ty2 with
  | shr_case_I32unsi => OK (Ebinop Oshru e1 e2)
  | shr_case_ii=> OK (Ebinop Oshr e1 e2)
  | shr_default => Error (msg "Cshmgen.make_shr")
  end.

Definition make_cmp (c: comparison) (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  match classify_cmp ty1 ty2 with
  | cmp_case_I32unsi => OK (Ebinop (Ocmpu c) e1 e2)
  | cmp_case_ipip => OK (Ebinop (Ocmp c) e1 e2)
  | cmp_case_ff => OK (Ebinop (Ocmpf c) e1 e2)
  | cmp_default => Error (msg "Cshmgen.make_shr")
  end.

Definition make_andbool (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  Econdition
    (make_boolean e1 ty1)
    (Econdition
       (make_boolean e2 ty2)
       (make_intconst Int.one)
       (make_intconst Int.zero))
    (make_intconst Int.zero).

Definition make_orbool (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  Econdition
    (make_boolean e1 ty1)
    (make_intconst Int.one)
    (Econdition
       (make_boolean e2 ty2)
       (make_intconst Int.one)
       (make_intconst Int.zero)).

(** [make_cast from to e] applies to [e] the numeric conversions needed
   to transform a result of type [from] to a result of type [to].
   It is decomposed in two functions:
-  [make_cast1]  converts from integers to floats or from floats to integers;
-  [make_cast2]  converts to a "small" int or float type if necessary.
*)

Definition make_cast1 (from to: type) (e: expr) :=
  match from, to with
  | Tint _ uns, Tfloat _ => make_floatofint e uns
  | Tfloat _, Tint _ uns => make_intoffloat e uns
  | _, _ => e
  end.

Definition make_cast2 (from to: type) (e: expr) :=
  match to with
  | Tint I8 Signed => Eunop Ocast8signed e  
  | Tint I8 Unsigned => Eunop Ocast8unsigned e  
  | Tint I16 Signed => Eunop Ocast16signed e  
  | Tint I16 Unsigned => Eunop Ocast16unsigned e  
  | Tfloat F32 => Eunop Osingleoffloat e
  | _ => e
  end.

Definition make_cast (from to: type) (e: expr) :=
  make_cast2 from to (make_cast1 from to e).

(** [make_load addr ty_res] loads a value of type [ty_res] from
   the memory location denoted by the Csharpminor expression [addr].
   If [ty_res] is an array or function type, returns [addr] instead,
   as consistent with C semantics.
*)

Definition make_load (addr: expr) (ty_res: type) :=
  match (access_mode ty_res) with
  | By_value chunk => OK (Eload chunk addr)
  | By_reference => OK addr
  | By_nothing => Error (msg "Cshmgen.make_load")
  end.

(** [make_store addr ty_res rhs ty_rhs] stores the value of the
   Csharpminor expression [rhs] into the memory location denoted by the
   Csharpminor expression [addr].  
   [ty] is the type of the memory location. *)

Definition make_store (addr: expr) (ty: type) (rhs: expr) :=
  match access_mode ty with
  | By_value chunk => OK (Sstore chunk addr rhs)
  | _ => Error (msg "Cshmgen.make_store")
  end.

(** * Reading and writing variables *)

(** Determine if a C expression is a variable *)

Definition is_variable (e: Csyntax.expr) : option ident :=
  match e with
  | Expr (Csyntax.Evar id) _ => Some id
  | _ => None
  end.

(** [var_get id ty] returns Csharpminor code that evaluates to the
   value of C variable [id] with type [ty].  Note that 
   C variables of array or function type evaluate to the address
   of the corresponding Clight memory block, while variables of other types
   evaluate to the contents of the corresponding C memory block.
*)

Definition var_get (id: ident) (ty: type) :=
  match access_mode ty with
  | By_value chunk => OK (Evar id)
  | By_reference => OK (Eaddrof id)
  | _ => Error (MSG "Cshmgen.var_get " :: CTX id :: nil)
  end.

(** Likewise, [var_set id ty rhs] stores the value of the Csharpminor
   expression [rhs] into the Clight variable [id] of type [ty].
*)

Definition var_set (id: ident) (ty: type) (rhs: expr) :=
  match access_mode ty with
  | By_value chunk => OK (Sassign id rhs)
  | _ => Error (MSG "Cshmgen.var_set " :: CTX id :: nil)
  end.

(** Auxiliary for translating call statements *)

Definition transl_lhs_call (opta: option (ident * type)): res (option ident) :=
  match opta with
  | None => OK None
  | Some (id,ty) => OK (Some id)
  end.

(** ** Translation of operators *)

Definition transl_unop (op: Csyntax.unary_operation) (a: expr) (ta: type) : res expr :=
  match op with
  | Csyntax.Onotbool => OK(make_notbool a ta)
  | Csyntax.Onotint => OK(make_notint a ta)
  | Csyntax.Oneg => make_neg a ta
  end.

Definition transl_binop (op: Csyntax.binary_operation)
                        (a: expr) (ta: type)
                        (b: expr) (tb: type) : res expr :=
  match op with
  | Csyntax.Oadd => make_add a ta b tb
  | Csyntax.Osub => make_sub a ta b tb
  | Csyntax.Omul => make_mul a ta b tb
  | Csyntax.Odiv => make_div a ta b tb
  | Csyntax.Omod => make_mod a ta b tb
  | Csyntax.Oand => make_and a ta b tb
  | Csyntax.Oor  => make_or a ta b tb
  | Csyntax.Oxor => make_xor a ta b tb
  | Csyntax.Oshl => make_shl a ta b tb
  | Csyntax.Oshr => make_shr a ta b tb
  | Csyntax.Oeq => make_cmp Ceq a ta b tb
  | Csyntax.One => make_cmp Cne a ta b tb
  | Csyntax.Olt => make_cmp Clt a ta b tb
  | Csyntax.Ogt => make_cmp Cgt a ta b tb
  | Csyntax.Ole => make_cmp Cle a ta b tb
  | Csyntax.Oge => make_cmp Cge a ta b tb
  end.

(** * Translation of expressions *)

(** [transl_expr a] returns the Csharpminor code that computes the value
   of expression [a]. The computation is performed in the error monad
   (see module [Errors]) to enable error reporting.

   Most cases are self-explanatory.  We outline the non-obvious cases:
<<
   a && b    --->    a ? (b ? 1 : 0) : 0

   a || b    --->    a ? 1 : (b ? 1 : 0)
>>
*)

Fixpoint transl_expr (a: Csyntax.expr) {struct a} : res expr :=
  match a with
  | Expr (Csyntax.Econst_int n) _ =>
      OK(make_intconst n)
  | Expr (Csyntax.Econst_float n) _ =>
      OK(make_floatconst n)
  | Expr (Csyntax.Evar id) ty =>
      var_get id ty
  | Expr (Csyntax.Ederef b) _ =>
      do tb <- transl_expr b;
      make_load tb (typeof a)
  | Expr (Csyntax.Eaddrof b) _ =>
      transl_lvalue b
  | Expr (Csyntax.Eunop op b) _ =>
      do tb <- transl_expr b;
      transl_unop op tb (typeof b)
  | Expr (Csyntax.Ebinop op b c) _ =>
      do tb <- transl_expr b;
      do tc <- transl_expr c;
      transl_binop op tb (typeof b) tc (typeof c)
  | Expr (Csyntax.Ecast ty b) _ =>
      do tb <- transl_expr b;
      OK (make_cast (typeof b) ty tb)
  | Expr (Csyntax.Econdition b c d) _ =>
      do tb <- transl_expr b;
      do tc <- transl_expr c;
      do td <- transl_expr d;
      OK(Econdition (make_boolean tb (typeof b)) tc td)
  | Expr (Csyntax.Eandbool b c) _ =>
      do tb <- transl_expr b;
      do tc <- transl_expr c;
      OK(make_andbool tb (typeof b) tc (typeof c))
  | Expr (Csyntax.Eorbool b c) _ =>
      do tb <- transl_expr b;
      do tc <- transl_expr c;
      OK(make_orbool tb (typeof b) tc (typeof c))
  | Expr (Csyntax.Esizeof ty) _ =>
      OK(make_intconst (Int.repr (Csyntax.sizeof ty)))
  | Expr (Csyntax.Efield b i) ty => 
      match typeof b with
      | Tstruct _ fld =>
          do tb <- transl_lvalue b;
          do ofs <- field_offset i fld;
          make_load
            (Ebinop Oadd tb (make_intconst (Int.repr ofs)))
            ty
      | Tunion _ fld =>
          do tb <- transl_lvalue b;
          make_load tb ty
      | _ =>
          Error(msg "Cshmgen.transl_expr(field)")
      end
  end

(** [transl_lvalue a] returns the Csharpminor code that evaluates
   [a] as a lvalue, that is, code that returns the memory address
   where the value of [a] is stored.
*)

with transl_lvalue (a: Csyntax.expr) {struct a} : res expr :=
  match a with
  | Expr (Csyntax.Evar id) _ =>
      OK (Eaddrof id)
  | Expr (Csyntax.Ederef b) _ =>
      transl_expr b
  | Expr (Csyntax.Efield b i) ty => 
      match typeof b with
      | Tstruct _ fld =>
          do tb <- transl_lvalue b;
          do ofs <- field_offset i fld;
          OK (Ebinop Oadd tb (make_intconst (Int.repr ofs)))
      | Tunion _ fld =>
          transl_lvalue b
      | _ =>
          Error(msg "Cshmgen.transl_lvalue(field)")
      end
  | _ => 
      Error(msg "Cshmgen.transl_lvalue")
  end.

(** [transl_exprlist al] returns a list of Csharpminor expressions
   that compute the values of the list [al] of Csyntax expressions.
   Used for function applications. *)

Fixpoint transl_exprlist (al: list Csyntax.expr): res (list expr) :=
  match al with
  | nil => OK nil
  | a1 :: a2 =>
      do ta1 <- transl_expr a1;
      do ta2 <- transl_exprlist a2;
      OK (ta1 :: ta2)
  end.

(** * Translation of statements *)

(** [exit_if_false e] return the statement that tests the boolean
   value of the Clight expression [e].  If [e] evaluates to false,
   an [exit 0] is performed.  If [e] evaluates to true, the generated
   statement continues in sequence. *)

Definition exit_if_false (e: Csyntax.expr) : res stmt :=
  do te <- transl_expr e;
  OK(Sifthenelse
        (make_boolean te (typeof e))
        Sskip
        (Sexit 0%nat)).

(** [transl_statement nbrk ncnt s] returns a Csharpminor statement
   that performs the same computations as the CabsCoq statement [s].

   If the statement [s] terminates prematurely on a [break] construct,
   the generated Csharpminor statement terminates prematurely on an
   [exit nbrk] construct.

   If the statement [s] terminates prematurely on a [continue]
   construct, the generated Csharpminor statement terminates
   prematurely on an [exit ncnt] construct.

   The general translation for loops is as follows:
<<
while (e1) s;       --->     block {
                               loop {
                                 if (!e1) exit 0;
                                 block { s }
                                 // continue in s branches here
                               }
                             }
                             // break in s branches here

do s; while (e1);   --->     block {
                               loop {
                                 block { s }
                                 // continue in s branches here
                                 if (!e1) exit 0;
                               }
                             }
                             // break in s branches here

for (e1;e2;e3) s;   --->     e1;
                             block {
                               loop {
                                 if (!e2) exit 0;
                                 block { s }
                                 // continue in s branches here
                                 e3;
                               }
                             }
                             // break in s branches here
>>
*)


Definition is_Sskip:
  forall (s: Csyntax.statement), {s = Csyntax.Sskip} + {s <> Csyntax.Sskip}.
Proof.
  destruct s; ((left; reflexivity) || (right; congruence)).
Qed.

Definition transl_atomic_statement (aop: Csyntax.atomic_statement) : res atomic_statement :=
  match aop with
  | Csyntax.AScas => OK AScas
  | Csyntax.ASlkinc => OK ASlkinc
  end.

Fixpoint transl_statement (nbrk ncnt: nat) (s: Csyntax.statement) {struct s} : res stmt :=
  match s with
  | Csyntax.Sskip =>
      OK Sskip
  | Csyntax.Sassign b c =>
      match is_variable b with
      | Some id =>
          do tc <- transl_expr c;
          var_set id (typeof b) tc
      | None =>
          do tb <- transl_lvalue b;
          do tc <- transl_expr c;
          make_store tb (typeof b) tc
      end 
  | Csyntax.Scall opta b cl =>
      match classify_fun (typeof b) with
      | fun_case_f args res =>
          do optid <- transl_lhs_call opta;
          do tb <- transl_expr b;
          do tcl <- transl_exprlist cl;
          OK(Scall optid (signature_of_type args res) tb tcl)
      | _ => Error(msg "Cshmgen.transl_stmt(call)")
      end
  | Csyntax.Ssequence s1 s2 =>
      do ts1 <- transl_statement nbrk ncnt s1;
      do ts2 <- transl_statement nbrk ncnt s2;
      OK (Sseq ts1 ts2)
  | Csyntax.Sifthenelse e s1 s2 =>
      do te <- transl_expr e;
      do ts1 <- transl_statement nbrk ncnt s1;
      do ts2 <- transl_statement nbrk ncnt s2;
      OK (Sifthenelse (make_boolean te (typeof e)) ts1 ts2)
  | Csyntax.Swhile e s1 =>
      do te <- exit_if_false e;
      do ts1 <- transl_statement 1%nat 0%nat s1;
      OK (Sblock (Sloop (Sseq te (Sblock ts1))))
  | Csyntax.Sdowhile e s1 =>
      do te <- exit_if_false e;
      do ts1 <- transl_statement 1%nat 0%nat s1;
      OK (Sblock (Sloop (Sseq (Sblock ts1) te)))
  | Csyntax.Sfor e1 e2 e3 s1 =>
      if is_Sskip e1 then
       (do te2 <- exit_if_false e2;
        do te3 <- transl_statement nbrk ncnt e3;
        do ts1 <- transl_statement 1%nat 0%nat s1;
        OK (Sblock (Sloop (Sseq te2 (Sseq (Sblock ts1) te3)))))
      else
       (do te1 <- transl_statement nbrk ncnt e1;
        do te2 <- exit_if_false e2;
        do te3 <- transl_statement nbrk ncnt e3;
        do ts1 <- transl_statement 1%nat 0%nat s1;
        OK (Sseq te1 (Sblock (Sloop (Sseq te2 (Sseq (Sblock ts1) te3))))))
  | Csyntax.Sbreak =>
      OK (Sexit nbrk)
  | Csyntax.Scontinue =>
      OK (Sexit ncnt)
  | Csyntax.Sreturn (Some e) =>
      do te <- transl_expr e;
      OK (Sreturn (Some te))
  | Csyntax.Sreturn None =>
      OK (Sreturn None)
  | Csyntax.Sswitch a sl =>
      do ta <- transl_expr a;
      do tsl <- transl_lbl_stmt 0%nat (S ncnt) sl;
      OK (Sblock (Sswitch ta tsl))
  | Csyntax.Slabel lbl s =>
      do ts <- transl_statement nbrk ncnt s;
      OK (Slabel lbl ts)
  | Csyntax.Sgoto lbl =>
      OK (Sgoto lbl)
  | Csyntax.Sthread_create efn earg =>
      do tefn <- transl_expr efn;
      do targ <- transl_expr earg;
      OK (Sthread_create tefn targ)
  | Csyntax.Satomic opta aop el =>
      do optid <- transl_lhs_call opta;
      do taop <- transl_atomic_statement aop;
      do tel <- transl_exprlist el;
      OK (Satomic optid taop tel)
  | Csyntax.Smfence => 
      OK Smfence
  end

with transl_lbl_stmt (nbrk ncnt: nat) (sl: Csyntax.labeled_statements)
                     {struct sl}: res lbl_stmt :=
  match sl with
  | Csyntax.LSdefault s =>
      do ts <- transl_statement nbrk ncnt s;
      OK (LSdefault ts)
  | Csyntax.LScase n s sl' =>
      do ts <- transl_statement nbrk ncnt s;
      do tsl' <- transl_lbl_stmt nbrk ncnt sl';
      OK (LScase n ts tsl')
  end.

(*** Translation of functions *)

Definition prefix_var_name (id: ident) : errmsg :=
  MSG "In local variable " :: CTX id :: MSG ": " :: nil.

Definition transl_params (l: list (ident * type)) :=
   Ast.map_partial prefix_var_name chunk_of_type l.
Definition transl_vars (l: list (ident * type)) :=
   Ast.map_partial prefix_var_name var_kind_of_type l.

Definition transl_function (f: Csyntax.function) : res function :=
  do tparams <- transl_params (Csyntax.fn_params f);
  do tvars <- transl_vars (Csyntax.fn_vars f);
  do tbody <- transl_statement 1%nat 0%nat (Csyntax.fn_body f);
  OK (mkfunction (signature_of_function f) tparams tvars tbody).

Definition transl_fundef (f: Csyntax.fundef) : res fundef :=
  match f with
  | Csyntax.Internal g => 
      do tg <- transl_function g; OK(Ast.Internal tg)
  | Csyntax.External id args res =>
      OK(Ast.External (external_function id args res))
  end.

(** ** Translation of programs *)

Definition transl_globvar (ty: type) := var_kind_of_type ty.

Definition transl_program (p: Csyntax.program) : res program :=
  transform_partial_program2 transl_fundef transl_globvar p.
