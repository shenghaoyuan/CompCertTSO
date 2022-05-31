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

(** Translation from Mach to x86. *)

Require Import Coqlib.
Require Import Maps.
Require Import Errors.
Require Import Ast.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Mem.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import Mach.
Require Import Asm.

(** Assertions : this morally belongs to Errors *)

Definition assertion (b: bool) : res unit :=
  if b then OK tt else Error(msg "Assertion failed").

Remark assertion_inversion:
  forall b x, assertion b = OK x -> b = true.
Proof.
  unfold assertion; intros. destruct b; inv H; auto.
Qed.

Remark assertion_inversion_1:
  forall (P Q: Prop) (a: {P}+{Q}) x,
  assertion (proj_sumbool a) = OK x -> P.
Proof.
  intros. exploit assertion_inversion; eauto. 
  unfold proj_sumbool. destruct a. auto. congruence.
Qed.

Remark assertion_inversion_2:
  forall (P Q: Prop) (a: {P}+{Q}) x,
  assertion (negb(proj_sumbool a)) = OK x -> Q.
Proof.
  intros. exploit assertion_inversion; eauto. 
  unfold proj_sumbool. destruct a; simpl. congruence. auto.
Qed.

(* end of assertions *)

Open Local Scope string_scope.
Open Local Scope error_monad_scope.

(** Extracting integer or float registers. *)

Definition ireg_of (r: mreg) : res ireg :=
  match preg_of r with IR mr => OK mr | _ => Error(msg "Asmgen.ireg_of") end.

Definition freg_of (r: mreg) : res freg :=
  match preg_of r with FR mr => OK mr | _ => Error(msg "Asmgen.freg_of") end.

(** Auxiliaries to manipulate the fp stack. *)

(* Definition save_fp_stack (fr: freg) (k: list instruction) := *)
(*   Xmovsd (Xfmr (Xm None (Some ESP) (Cint (Int.repr (-8)))) fr) :: *)
(*   Xfldl (Xm None (Some ESP) (Cint (Int.repr (-8)))) :: k. *)

(* Definition load_fp_stack (fr: freg) (k: list instruction) := *)
(*   Xfstpl (Xm None (Some ESP) (Cint (Int.repr (-8)))) :: *)
(*   Xmovsd (Xfrm fr (Xm None (Some ESP) (Cint (Int.repr (-8))))) :: k. *)

(** Smart constructors for various operations *)

Definition mk_mov (rd rs: preg) (k: code) : res code :=
  match rd, rs with
  | IR rd, IR rs => 
      OK (Xmov (Xrr rd rs) :: k)
  | FR rd, FR rs => 
      OK (Xmovsd (Xfrr rd rs) :: k)
  | ST0, FR rs => 
      OK (Xmovrst rs :: k) (* was: save_fp_stack rs k *)
  | FR rd, ST0 => 
      OK (Xmovstr rd :: k) (* was: load_fp_stack rd k *)
  | _, _ => 
      Error(msg "Asmgen.mk_mov")
  end.

Definition mk_shift (shift_instr: shiftop_name)
                    (r1 r2: ireg) (k: code) : res code :=
  if ireg_eq r2 ECX then
    OK (Xshift shift_instr (Xr r1) Xc_CL :: k)
  else
    do x <- assertion (negb (ireg_eq r1 ECX));
    OK (Xmov (Xrr ECX r2) :: Xshift shift_instr (Xr r1) Xc_CL :: k).

Definition mk_shrximm (r: ireg) (n: int) (k: code) : res code :=
  do x <- assertion (negb (ireg_eq r ECX));
  let p := Int.sub (Int.shl Int.one n) Int.one in
  OK (Xbinop Xtest (Xrr r r) :: 
      Xlea ECX (Xm None (Some r) (Cint p)) ::
      Xcmov X_L r (Xr ECX) ::
      Xshift Xsar (Xr r) (Xc_imm (Cint n)) :: k).

Definition get_low_ireg (r: ireg) : option low_ireg :=
  match r with
  | EAX => Some AX
  | EBX => Some BX 
  | ECX => Some CX
  | EDX => Some DX
  | ESI | EDI | EBP | ESP => None
  end.

Definition mk_intconv (ex: extend) (rd rs: ireg) (k: code) :=
  match get_low_ireg rs with
    | Some rs' => OK (Xmovx ex rd (Xlr rs') :: k)
    | None => OK (Xmov (Xrr EDX rs) :: Xmovx ex rd (Xlr DX) :: k)
  end.

Definition mk_smallstore (ex: extend) (addr: xmem) (rs: ireg) (k: code) :=
  match get_low_ireg rs with
    | Some rs' => OK (Xmovt ex addr rs' :: k)
    | None => 
      OK (Xlea ECX addr :: Xmov (Xrr EDX rs) ::
          Xmovt ex (Xm None (Some ECX) (Cint Int.zero)) DX :: k)
  end.

Definition mk_div (setedx_instr: instruction) (div_instr: monop_name)
                  (r1 r2: ireg) (k: code) : res code :=
  if ireg_eq r1 EAX then
    if ireg_eq r2 EDX then
      OK (Xmov (Xrr ECX EDX) :: 
          setedx_instr :: Xmonop div_instr (Xr ECX) :: k)
    else
      OK (setedx_instr :: Xmonop div_instr (Xr r2) :: k)
  else
    do x <- assertion (negb (ireg_eq r1 ECX));
    if ireg_eq r2 EAX then
      OK (Xmov (Xrr ECX EAX) :: Xmov (Xrr EAX r1) ::
          setedx_instr :: Xmonop div_instr (Xr ECX) ::
          Xmov (Xrr r1 EAX) :: Xmov (Xrr EAX ECX) :: k)
    else
      OK (Xmovif XMM7 EAX :: Xmov (Xrr ECX r2) :: Xmov (Xrr EAX r1) ::
          setedx_instr :: Xmonop div_instr (Xr ECX) ::
          Xmov (Xrr r2 ECX) :: Xmov (Xrr r1 EAX) :: Xmovfi EAX XMM7 :: k).

Definition mk_mod (setedx_instr: instruction) (div_instr: monop_name)
                  (r1 r2: ireg) (k: code) : res code :=
  if ireg_eq r1 EAX then
    if ireg_eq r2 EDX then
      OK (Xmov (Xrr ECX EDX) :: 
          setedx_instr :: Xmonop div_instr (Xr ECX) :: 
          Xmov (Xrr EAX EDX) :: k)
    else
      OK (setedx_instr :: Xmonop div_instr (Xr r2) :: 
          Xmov (Xrr EAX EDX) :: k)
  else
    do x <- assertion (negb (ireg_eq r1 ECX));
    if ireg_eq r2 EDX then
      OK (Xmovif XMM7 EAX :: Xmov (Xrr ECX EDX) ::
          Xmov (Xrr EAX r1) ::
          setedx_instr :: Xmonop div_instr (Xr ECX) ::
          Xmov (Xrr r1 EDX) :: Xmovfi EAX XMM7 :: k)
    else
      OK (Xmovif XMM7 EAX :: Xmov (Xrr ECX r2) :: Xmov (Xrr EAX r1) ::
          setedx_instr :: Xmonop div_instr (Xr ECX) ::
          Xmov (Xrr r2 ECX) :: Xmov (Xrr r1 EDX) :: Xmovfi EAX XMM7 :: k).

(** Floating-point comparison.  We swap the operands in some cases
   to simplify the handling of the unordered case. *)

Definition floatcomp (cmp: comparison) (r1 r2: freg) : instruction :=
  match cmp with
  | Clt | Cle => Xbinopf Xcomisd (Xfrr r2 r1)
  | Ceq | Cne | Cgt | Cge => Xbinopf Xcomisd (Xfrr r1 r2)
  end.

(** Translation of a condition.  Prepends to [k] the instructions
  that evaluate the condition and leave its boolean result in one of
  the bits of the condition register.  The bit in question is
  determined by the [crbit_for_cond] function. *)

Definition transl_cond (cond: condition) (args: list mreg) (k: code) :=
  match cond, args with 
  | Ccomp c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2; 
      OK (Xbinop Xcmp (Xrr r1 r2) :: k)
  | Ccompu c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;   
      OK (Xbinop Xcmp (Xrr r1 r2) :: k)
  | Ccompimm c n, a1 :: nil =>
      do r1 <- ireg_of a1; 
      OK (Xbinop Xcmp (Xri r1 (Cint n)) :: k)
  | Ccompuimm c n, a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (if Int.eq_dec n Int.zero 
          then Xbinop Xtest (Xrr r1 r1) :: k 
          else Xbinop Xcmp (Xri r1 (Cint n)) :: k)
  | Ccompf cmp, a1 :: a2 :: nil =>
      do r1 <- freg_of a1; do r2 <- freg_of a2; 
      OK (floatcomp cmp r1 r2 :: k)
  | Cnotcompf cmp, a1 :: a2 :: nil =>
      do r1 <- freg_of a1; do r2 <- freg_of a2; 
      OK (floatcomp cmp r1 r2 :: k)
  | Cmaskzero n, a1 :: nil =>
      do r1 <- ireg_of a1; 
      OK (Xbinop Xtest (Xri r1 (Cint n)) :: k)
  | Cmasknotzero n, a1 :: nil =>
      do r1 <- ireg_of a1; 
      OK (Xbinop Xtest (Xri r1 (Cint n)) :: k)
  | _, _ =>
      Error (msg "Asmgen.transl_cond")
  end.

Definition cond_for_cmp (cmp: comparison) (sign: bool) :=
  match cmp, sign with
  | Ceq, _     => X_E 
  | Cne, _     => X_NE
  | Clt, true  => X_L 
  | Clt, false => X_B
  | Cle, true  => X_LE
  | Cle, false => X_BE 
  | Cgt, true  => X_G 
  | Cgt, false => X_A 
  | Cge, true  => X_GE  
  | Cge, false => X_AE 
  end.

Definition testcond_for_cond (cond: condition) :=
  match cond with
  | Ccomp cmp       => cond_for_cmp cmp true
  | Ccompu cmp      => cond_for_cmp cmp false
  | Ccompimm cmp n  => cond_for_cmp cmp true
  | Ccompuimm cmp n => cond_for_cmp cmp false
  | Ccompf cmp =>
      match cmp with
      | Ceq => X_ENP
      | Cne => X_NEP
      | Clt => X_A
      | Cle => X_AE
      | Cgt => X_A
      | Cge => X_AE
      end
  | Cnotcompf c =>
      match c with
      | Ceq => X_NEP
      | Cne => X_ENP
      | Clt => X_BE
      | Cle => X_B
      | Cgt => X_BE
      | Cge => X_B
      end
  | Cmaskzero n     => X_E
  | Cmasknotzero n  => X_NE
  end.

(** Smart constructors for transforming 3-address into 2-address code, 
    and for saving and restoring registers. *)

(** Accessing slots in the stack frame.  *)

Definition loadind (base: ireg) (ofs: int) (ty: typ) (dst: mreg) (k: code) :=
  match ty with
  | Tint =>
      do r <- ireg_of dst;
      OK (Xmov (Xrm r (Xm None (Some base) (Cint ofs))) :: k)
  | Tfloat =>
      match preg_of dst with
      | FR r => OK (Xmovsd (Xfrm r (Xm None (Some base) (Cint ofs))) :: k)
      | ST0  => OK (Xfldl (Xm None (Some base) (Cint ofs)) :: k)
      | _ => Error (msg "Asmgen.loadind") 
      end
  end.

Definition storeind (src: mreg) (base: ireg) (ofs: int) (ty: typ) (k: code) :=
  match ty with
  | Tint =>
      do r <- ireg_of src;
      OK (Xmov (Xmr (Xm None (Some base) (Cint ofs)) r) :: k)
  | Tfloat =>
      match preg_of src with
      | FR r => OK (Xmovsd (Xfmr (Xm None (Some base) (Cint ofs)) r) :: k)
      | ST0  => OK (Xfstpl (Xm None (Some base) (Cint ofs)) :: k)
      | _ => Error (msg "Asmgen.storeind")
      end
  end.

(** Translation of addressing modes *)

Definition transl_scale sc :=
  match (Int.unsigned sc) with
  | 1 => OK (mkword2 false false)
  | 2 => OK (mkword2 false true) 
  | 4 => OK (mkword2 true false) 
  | 8 => OK (mkword2 true true)
  | _ => Error (msg "Asmgen.transl_scale") 
  end.

Definition transl_addressing (a: addressing) (args: list mreg): res xmem :=
  match a, args with
  | Aindexed n, a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (Xm None (Some r1) (Cint n))
  | Aindexed2 n, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Xm (Some ((mkword2 false false), r2)) (Some r1) (Cint n))
  | Ascaled sc n, a1 :: nil =>
      do r1 <- ireg_of a1; do tsc <- transl_scale sc;
      OK (Xm (Some (tsc,r1)) None (Cint n))
  | Aindexed2scaled sc n, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2; do tsc <- transl_scale sc;
      OK (Xm (Some (tsc,r2)) (Some r1) (Cint n))
  | Aindexed2scaledrev sc n, a2 :: a1 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2; do tsc <- transl_scale sc;
      OK (Xm (Some (tsc,r2)) (Some r1) (Cint n))
  | Aglobal id ofs, nil =>
      OK (Xm None None (Csymbol id ofs))
  | Abased id ofs, a1 :: nil =>
      do r1 <- ireg_of a1; 
      OK (Xm None (Some r1) (Csymbol id ofs))
  | Abasedscaled sc id ofs, a1 :: nil =>
      do r1 <- ireg_of a1; do tsc <- transl_scale sc;
      OK (Xm (Some (tsc,r1)) None (Csymbol id ofs))
  | Ainstack n, nil =>
      OK (Xm None (Some ESP) (Cint n))
  | _, _ => 
      Error(msg "Asmgen.transl_addressing")
  end.

(** Translation of the arithmetic operation [r <- op(args)].
  The corresponding instructions are prepended to [k]. *)

Notation " [ x ] " := (cons x nil).

Definition transl_op
              (op: operation) (args: list mreg) (res: mreg) (k: code) :=
  match op, args with
  | Omove, a1 :: nil =>
      mk_mov (preg_of res) (preg_of a1) k
  | Ointconst n, nil =>
      do r <- ireg_of res;
      OK (Xmov (Xri r (Cint n)) :: k)
  | Ofloatconst f, nil =>
      do r <- freg_of res;
      OK (Xfloatconst r f :: k)
  | Ocast8signed, a1 :: nil =>
      do r1 <- ireg_of a1; do r <- ireg_of res; mk_intconv SX_I8 r r1 k
  | Ocast8unsigned, a1 :: nil =>
      do r1 <- ireg_of a1; do r <- ireg_of res; mk_intconv ZX_I8 r r1 k
  | Ocast16signed, a1 :: nil =>
      do r1 <- ireg_of a1; do r <- ireg_of res; mk_intconv SX_I16 r r1 k
(*      Xcwtl :: k *)
  | Ocast16unsigned, a1 :: nil =>              
      do r1 <- ireg_of a1; do r <- ireg_of res; mk_intconv ZX_I16 r r1 k
  | Oneg, a1 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; 
      OK (Xmonop Xneg (Xr r) :: k)
  | Osub, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; 
      OK (Xbinop Xsub (Xrr r r2) :: k)
  | Omul, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; 
      OK (Xbinop Ximul (Xrr r r2) :: k)
  | Omulimm n, a1 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; 
      OK (Xbinop Ximul (Xri r (Cint n)) :: k)
  | Odiv, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; 
      mk_div Xcltd Xidiv r r2 k
  | Odivu, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; 
      mk_div (Xxor_self EDX) Xdiv r r2 k
  | Omod, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; 
      mk_mod Xcltd Xidiv r r2 k
  | Omodu, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; 
      mk_mod (Xxor_self EDX) Xdiv r r2 k
  | Oand, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; 
      OK (Xbinop Xand (Xrr r r2) :: k)
  | Oandimm n, a1 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res;
      OK (Xbinop Xand (Xri r (Cint n)) :: k)
  | Oor, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; 
      OK (Xbinop Xor (Xrr r r2) :: k)
  | Oorimm n, a1 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res;
      OK (Xbinop Xor (Xri r (Cint n)) :: k)
  | Oxor, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; 
      OK (Xbinop Xxor (Xrr r r2) :: k)
  | Oxorimm n, a1 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res;
      OK (Xbinop Xxor (Xri r (Cint n)) :: k)
  | Oshl, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; 
      mk_shift Xsal r r2 k
  | Oshlimm n, a1 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res;
      OK (Xshift Xsal (Xr r) (Xc_imm (Cint n)) :: k)
  | Oshr, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; 
      mk_shift Xsar r r2 k
  | Oshrimm n, a1 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res;
      OK (Xshift Xsar (Xr r) (Xc_imm (Cint n)) :: k)
  | Oshru, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; 
      mk_shift Xshr r r2 k
  | Oshruimm n, a1 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res;
      OK (Xshift Xshr (Xr r) (Xc_imm (Cint n)) :: k)
  | Oshrximm n, a1 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; mk_shrximm r n k
  | Ororimm n, a1 :: nil =>
      do x <- assertion (mreg_eq a1 res); do r <- ireg_of res; 
      OK (Xshift Xror (Xr r) (Xc_imm (Cint n)) :: k)
  | Olea addr, _ =>
      do am <- transl_addressing addr args; do r <- ireg_of res;
      OK (Xlea r am :: k)
  | Onegf, a1 :: nil => 
      do x <- assertion (mreg_eq a1 res);
      do r <- freg_of res; 
      OK (Xnegf r :: k)
  | Oaddf, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- freg_of res; do r2 <- freg_of a2; 
      OK (Xbinopf Xaddf (Xfrr r r2) :: k)
  | Osubf, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- freg_of res; do r2 <- freg_of a2; 
      OK (Xbinopf Xsubf (Xfrr r r2) :: k)
  | Omulf, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- freg_of res; do r2 <- freg_of a2; 
      OK (Xbinopf Xmulf (Xfrr r r2) :: k)
  | Odivf, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- freg_of res; do r2 <- freg_of a2; 
      OK (Xbinopf Xdivf (Xfrr r r2) :: k)
  | Osingleoffloat, a1 :: nil =>
      do r <- freg_of res; do r1 <- freg_of a1; 
      OK (Xmovftr r r1 :: k) 
  | Ointoffloat, a1 :: nil =>
      do r <- ireg_of res; do r1 <- freg_of a1; 
      OK (Xcvttsd2si r r1 :: k)
  | Ofloatofint, a1 :: nil =>
      do r <- freg_of res; do r1 <- ireg_of a1; 
      OK (Xcvtsi2sd r r1 :: k)
  | Ointuoffloat, a1 :: nil =>
      do r <- ireg_of res; do r1 <- freg_of a1; 
      OK (Xfctiu r r1 :: k)  
      (* pseudo-instruction, Xavier compiles it away in SelectOp *)
  | Ofloatofintu, a1 :: nil =>
      do r <- freg_of res; do r1 <- ireg_of a1; 
      OK (Xiuctf r r1 :: k) 
      (* pseudo-instruction, Xavier compiles it away in SelectOp *)
  | Ocmp cond, args =>
      do r <- ireg_of res;
      transl_cond cond args (Xset (testcond_for_cond cond) r :: k)
      (* ECX is really CL here *)
      (* Xavier pp mov when pp set *)
  | _, _ => 
      Error (msg "Asmgen.translop")
  end.

Definition transl_aop
              (aop: atomic_statement) (args: list mreg) (r: mreg) (k: code) : res code :=
  match aop, args with
  | AScas, a1 :: a3 :: a2 :: nil =>
      (* corresponds to res = atomic_cas (a1, a2, a3) *)
      (* a1 = loc, a2 = old value, a3 = new value     *)
      (* res = [a1] after cmpxchg *)

      let move_to_eax r k := 
        if ireg_eq EAX r then k else (Xmov (Xrr EAX r) :: k) in

      do rr <- ireg_of r;
      do r1 <- ireg_of a1;
      do r2 <- ireg_of a2;
      do r3 <- ireg_of a3;

      do x1 <- assertion (negb (ireg_eq EAX r1));
      do x3 <- assertion (negb (ireg_eq EAX r3));

      if ireg_eq rr EAX
      then 
        OK (move_to_eax r2 (Xcmpxchg (Xm None (Some r1) (Cint Int.zero)) r3 :: k))
      else 
        OK (Xmovif XMM7 EAX :: 
            move_to_eax r2 
             ( Xcmpxchg (Xm None (Some r1) (Cint Int.zero)) r3 ::
               Xmov (Xrr rr EAX) ::
               Xmovfi EAX XMM7 :: k ))

  | ASlkinc, a1 :: nil =>
      do r1 <- ireg_of a1;
      do rr <- ireg_of r;
      do x1 <- assertion (negb (ireg_eq r1 ECX));
      OK (Xmov (Xri ECX (Cint Int.one)) ::
          Xxadd (Xm None (Some r1) (Cint Int.zero)) ECX ::
          Xmov (Xrr rr ECX) :: k)

  | _, _ => Error (msg "Asmgen.transl_aop")
  end.

(** Code to translate [Mload] and [Mstore] instructions. *)

Definition transl_load (chunk: memory_chunk)
                       (addr: addressing) (args: list mreg) (dest: mreg)
                       (k: code) : res code :=
  do am <- transl_addressing addr args;
  match chunk with
  | Mint8unsigned =>
      do r <- ireg_of dest; OK (Xmovx ZX_I8 r (Xlmm am) :: k)
  | Mint8signed =>
      do r <- ireg_of dest; OK (Xmovx SX_I8 r (Xlmm am) :: k)
  | Mint16unsigned =>
      do r <- ireg_of dest; OK (Xmovx ZX_I16 r (Xlmm am) :: k)
  | Mint16signed =>
      do r <- ireg_of dest; OK (Xmovx SX_I16 r (Xlmm am) :: k)
  | Mint32 =>
      do r <- ireg_of dest; OK (Xmov (Xrm r am) :: k)
  | Mfloat32 =>
      do r <- freg_of dest; OK (Xcvtss2sd r am :: k)
  | Mfloat64 =>
      do r <- freg_of dest; OK (Xmovsd (Xfrm r am) :: k)
  end.

Definition transl_store (chunk: memory_chunk)
                        (addr: addressing) (args: list mreg) (src: mreg)
                        (k: code) : res code :=
  do am <- transl_addressing addr args;
  match chunk with
  | Mint8unsigned =>
      do r <- ireg_of src; mk_smallstore ZX_I8 am r k
  | Mint8signed =>
      do r <- ireg_of src; mk_smallstore SX_I8 am r k
  | Mint16unsigned =>
      do r <- ireg_of src; mk_smallstore ZX_I16 am r k
  | Mint16signed =>
      do r <- ireg_of src; mk_smallstore SX_I16 am r k
  | Mint32 =>
      do r <- ireg_of src; OK (Xmov (Xmr am r) :: k)
  | Mfloat32 =>
      do r <- freg_of src; OK (Xmovftm am r :: k)
  | Mfloat64 =>
      do r <- freg_of src; OK (Xmovsd (Xfmr am r) :: k)
  end.


(** Translation of a Mach instruction. *)

Definition transl_instr (f: Mach.function) (i: Mach.instruction) (k: code) :=
  match i with
  | Mgetstack ofs ty dst =>
      loadind ESP ofs ty dst k
  | Msetstack src ofs ty =>
      storeind src ESP ofs ty k
  | Mgetparam ofs ty dst =>
      let sf_size := Int.repr (
        Mach.fn_paddedstacksize f + Mach.fn_framesize f + Stacklayout.fe_retaddrsize) in 
      loadind ESP (Int.add ofs sf_size) ty dst k
  | Mop op args res =>
      transl_op op args res k
  | Mload chunk addr args dst =>
      transl_load chunk addr args dst k
  | Mstore chunk addr args src =>
      transl_store chunk addr args src k
  | Mcall sig (inl reg) =>
      do r <- ireg_of reg; 
      OK (Xcallreg r :: k) (* :: (load_fp_stack sig k) *)
  | Mcall sig (inr symb) =>
      OK (Xcall symb :: k)  (* :: (load_fp_stack sig k) *) 
  | Mlabel lbl =>
      OK (Xlabel lbl :: k)
  | Mgoto lbl =>
      OK (Xjump X_ALWAYS lbl :: k)
  | Mcond cond args lbl =>
      transl_cond cond args (Xjump (testcond_for_cond cond) lbl :: k)
  (* | Mjumptable arg tbl =>  jumptables exists only in compcert 1.7 *)
  (*     Xbtbl (ireg_of arg) tbl :: k *)
  | Mreturn =>
      let ss := Int.repr (f.(fn_framesize) + (Mach.fn_paddedstacksize f)) in
      OK (Xbinop Xadd (Xri ESP (Cint ss)) :: (Xret (Cint Int.zero)) :: k)
  | Matomic aop args res =>
      transl_aop aop args res k
  | Mfence =>
      OK (Xmfence :: k)
  | Mthreadcreate =>
      OK (Xthreadcreate :: k)
  end.

Fixpoint transl_code (f: Mach.function) (il: list Mach.instruction) :=
  match il with
  | nil => OK nil
  | i1 :: il' => do k <- transl_code f il'; transl_instr f i1 k
  end.

(** Translation of a whole function.  Note that we must check
  that the generated code contains less than [2^32] instructions,
  otherwise the offset part of the [PC] code pointer could wrap
  around, leading to incorrect executions. *)

Fixpoint code_size (c: code) : Z :=
  match c with
  | nil => 0
  | instr :: c' => code_size c' + 1
  end.

Definition transf_function (f: Mach.function) :=
  do c <- transl_code f f.(fn_code);
  if zlt (code_size c) Int.max_unsigned 
  then 
    let code :=
      (* allocate stack space - Xalloc should not modify ESP *)
      let ss := Int.repr (f.(fn_framesize) + (Mach.fn_paddedstacksize f)) in
      Xbinop Xsub (Xri ESP (Cint ss)) ::
      (* code *)
      c in
    OK(f.(fn_sig), code)
  else Error (msg "code size exceeded").

Definition transf_fundef (f: Mach.fundef) : res Asm.fundef :=
  transf_partial_fundef transf_function f.

Definition transf_program (p: Mach.program) : res Asm.program :=
  transform_partial_program transf_fundef p.

