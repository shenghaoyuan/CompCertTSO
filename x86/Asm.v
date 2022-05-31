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

(** Abstract syntax for x86 assembly language *)
Require Import String.
Require Import Coqlib.
Require Import Maps.
Require Import Ast.
Require Import Integers.
Require Import Floats.
Require Import Pointers.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Locations.
Require Import Memcomp.
Require Stacklayout.
Require Conventions.
Require Import Libtactics.

(** X86 assembler syntax and semantics are taken from Myreen [cite].
    The HOL code has been hand-translated into Coq.  Some
    instructions, and support for SSE2 registers and instructions have
    been added to the original development.

  We kept the the previous HOL general addressing mode structure.
  This introduces a little bit of complexity over hard-coding
  particular instruction/addressing-mode combinations, but it's almost
  inevitable for x86, and there's a lot of uniformity, eg among
  binops, to compensate.


  We made an extractable emulator - though for the assembly Ast rather
  than machine-code.  Porting and inverting Magnus's decoder is left
  for future work. *)

(** A 2-bit value, used by the AST below. *)
 
Record word2 :=  mkword2 { hi:bool; lo:bool}.

(** Label names *)

Definition label := positive.

(** * Instruction Syntax *)

(** ** Registers *)

Inductive ireg := EAX | EBX | ECX | EDX | ESP | EBP | ESI | EDI.
Inductive low_ireg := AX | BX | CX | DX.
Inductive freg := XMM0 | XMM1 | XMM2 | XMM3 |XMM4 | XMM5 | XMM6 | XMM7.
Inductive eflags := CF | PF | AF | ZF | SF | OF .

Definition ireg_of_low r := 
  match r with
    | AX => EAX
    | BX => EBX
    | CX => ECX
    | DX => EDX
  end.

Lemma low_ireg_eq (x y: ireg): {x=y} + {x<>y}.
Proof. decide equality. Qed.

Lemma ireg_eq (x y: ireg): {x=y} + {x<>y}.
Proof. decide equality. Qed.

Lemma freg_eq (x y: freg): {x=y} + {x<>y}.
Proof. decide equality. Qed.

Lemma eflags_eq (x y: eflags): {x=y} + {x<>y}.
Proof. decide equality. Qed.

(** ** Instruction operands *)

(** x86 immediate arguments (a.k.a., CompCert symbolic constants).

  Immediate operands to an arithmetic instruction or an indexed memory
  access can be either integer literals, or a symbolic reference (the
  address of a symbol). These symbolic references are resolved later
  by the linker. *)

Inductive imm :=
  | Cint    (i: int)
  | Csymbol (s: ident) (offset: int).

(** Generalised indexed-memory addressing mode:
      [mem[2^{scale} * index + base + displacement]] *)

Inductive xmem := 
  | Xm (idx: option (word2 * ireg)) (base: option ireg) (displ: imm).

(** Three possible kinds of register-or-memory addressing modes: *)

Inductive ireg_or_mem := 
  | Xr  (r: ireg)
  | Xmm (xm: xmem).

Inductive low_ireg_or_mem := 
  | Xlr  (lr: low_ireg)
  | Xlmm (xm: xmem).

Inductive float_reg_or_mem := 
  | Xfr  (fr: freg)
  | Xfmm (xm: xmem).

(** Pairs of destination and source operand *)

Inductive int_dest_src := 
  | Xri (dst: ireg) (src: imm)     (**r r32, imm32/imm8(sign-extended) *)
  | Xrr (dst: ireg) (src: ireg)    (**r r32, r32 *)
  | Xrm (dst: ireg) (src: xmem)    (**r r32, m32 *)
  | Xmr (dst: xmem) (src: ireg).   (**r m32, r32 *)

Inductive float_dest_src := 
  | Xfrr (dst: freg) (src: freg)  (**r  xmm, xmm *)
  | Xfrm (dst: freg) (src: xmem)  (**r  xmm, m64 *)
  | Xfmr (dst: xmem) (src: freg). (**r  m64, xmm *)

(** Count operand for shift and rotate instructions*)

Inductive count :=
  | Xc_imm (i: imm)    (**r imm8 *)
  | Xc_CL              (**r CL register *).

(** ** Binary and unary operations *)

Inductive int_binop_name := 
  | Xadd | Xsub | Ximul | Xand | Xor  | Xxor | Xcmp | Xtest.

Inductive float_binop_name := 
  Xaddf | Xsubf | Xmulf | Xdivf | Xcomisd.

Inductive shiftop_name := 
  Xsar | Xsal | Xshr | Xrol | Xror.

Inductive monop_name := 
  Xnot | Xneg | Xdiv | Xidiv.

(** ** Conditionals for branches and movs *)

Inductive cond := 
  | X_ALWAYS
  | X_E | X_NE | X_L | X_B | X_LE | X_BE | X_G | X_A | X_GE | X_AE | X_ENP | X_NEP
  | X_NS.

(** NB: [X_ENP] and [X_NEP] are composite conditions. *)


(** ** Sign-extesions *)

(** These are used in the [Xmovx] instruction to represent the
  following four x86 instructions:

<<
    MOVZX r32, r/m8
    MOVZX r32, r/m16
    MOVSX r32, r/m8
    MOVSX r32, r/m16
>>
  *)

(* OLD COMMENT:
Currently: RTL-down generation of write labels not trimmed; RTL-up
trimmed (with cast_value_to_chunk chunk v).  We should do that in all
phases, including here in Asm.
*)

Inductive extend := ZX_I8 | ZX_I16 | SX_I8 | SX_I16.

(** ** Instructions *)

(** These include a number of standard x86 instructions generated by our
compiler and a number of pseudo-instructions standing for short instruction
sequences, whose meaning is described below.  Ideally, these should have been
represented as single instructions in the AST, but unfortunately their
semantics cannot be specified using Compcert's current set up.  These are:

- [Xxor_self r] standing for [XOR r, r].  It is a pseudo-instruction 
  to work around the fact that [Val.xor x x]  is not always [Vzero] (in
  particular, when [x = Vundef]).
- [Xmovftr] and [Xmovftm] for truncating floating point moves 
  (dropping precision). These are pseudo-instructions because 
  our semantic values do not include single-point floating point values.
- [Xmovstr] and [Xmovrst] for moving values between the FP stack and the XMM registers.
- [Xset cc r] for setting [r <- cc].  This corresponds to
<<
    SETcc   CL
    MOVZBL  r, CL 
>>
  because the semantics of [SETcc] cannot be represented faithfully otherwise.
  [SETcc] writes only the least significant byte of [ECX] leaving the rest
  unchanged. If, however, [ECX] held [Vundef], then the resulting value of
  [ECX] cannot be represented.

- [Xnegf] for negating floating point numbers; 
  [Xfctiu] for converting a floating point number to an unsigned integer;
  [Xiuctf] for converting an unsigned integer to a floating point number
  These are pseudo-instructions because the floating point semantics is 
  axiomatized.
*)

(** 
  Note that we perform arithmetics only on [Mfloat64] values and we use
  the [xmm] registers to do so. This raises the following issues:

- To load a [Mfloat32] value, we do: 
<<
    CVTSS2SD  xmm_res, mem/32
>>

- To store a [Mfloat32] value, we do the pseudo-op [Xmovftm] ("move float
  truncate (memory)") which corresponds to the instruction sequence:
<<
    CVTSD2SS  xmm7,    xmm_arg
    MOVSS     mem/32,  xmm7
>>

- To drop precision (when there is cast to [Mfloat32]), we insert the
  pseudo-op [Xmovftr] ("move float truncate (register)"), which corresponds
  to the instruction sequence:
<<
    CVTSD2SS  xmm_res, xmm_arg
    CVTSS2SD  xmm_res, xmm_res
>>

- The x86 calling conventions require that floating point return values
  are stored in [ST.(0)]. We introduce the [Xmovrst] and [Xmovstr] 
  pseudo-instructions to save and load the head of the floating point stack
  into a register.  These are implemented using [ESP - 8] as a temporary 
  stack slot:
<<
    % movrst                    |   % movstr
    MOVSD  [ESP - 8], xmm_arg   |   FSTPL  [ESP - 8]
    FLDL   [ESP - 8]            |   MOVSD  xmm_res, [ESP - 8]
>>

*)

Inductive instruction := 
  | Xbinop     : int_binop_name -> int_dest_src -> instruction
  | Xbinopf    : float_binop_name -> float_dest_src -> instruction
  | Xmonop     : monop_name -> ireg_or_mem -> instruction
  | Xshift     : shiftop_name -> ireg_or_mem -> count -> instruction 
  | Xcltd      : instruction
  | Xxor_self  : ireg -> instruction                               (**r xor r, r (see above) *)
  | Xlea       : ireg -> xmem -> instruction 
  | Xcallreg   : ireg -> instruction
  | Xcall      : ident -> instruction
  | Xret       : imm -> instruction  (**r the optional [imm16] is how much extra to pop *)
  | Xmov       : int_dest_src -> instruction                      (**r move 32-bit int *)
  | Xmovt      : extend -> xmem -> low_ireg -> instruction        (**r move truncate *)
  | Xmovx      : extend -> ireg -> low_ireg_or_mem -> instruction (**r move extend *)
  | Xmovsd     : float_dest_src -> instruction                    (**r move 64-bit float *)
  | Xmovftr    : freg -> freg -> instruction                      (**r pseudo-op (see above) *)
  | Xmovftm    : xmem -> freg -> instruction                      (**r pseudo-op (see above) *)
  | Xmovif     : freg -> ireg -> instruction
  | Xmovfi     : ireg -> freg -> instruction
  | Xmovstr    : freg -> instruction                              (**r pseudo-op (see above) *)
  | Xmovrst    : freg -> instruction                              (**r pseudo-op (see above) *)
  | Xset       : cond -> ireg -> instruction                      (**r pseudo-op (SET;MOVZBL)*)
  | Xcmov      : cond -> ireg -> ireg_or_mem -> instruction
  | Xjump      : cond -> label -> instruction
  | Xlabel     : label -> instruction
  (* floating point *)
  | Xfloatconst : freg -> float -> instruction 
  | Xcvttsd2si  : ireg -> freg -> instruction
  | Xcvtsi2sd   : freg -> ireg -> instruction
  | Xcvtss2sd   : freg -> xmem -> instruction
  | Xnegf       : freg -> instruction            (**r pseudo-instruction *)
  | Xfctiu      : ireg -> freg -> instruction    (**r pseudo-instruction *)
  | Xiuctf      : freg -> ireg -> instruction    (**r pseudo-instruction *)
  | Xfstpl      : xmem -> instruction
  | Xfldl       : xmem -> instruction
  (* locked instructions *)
  | Xmfence    : instruction
  | Xcmpxchg   : xmem -> ireg  -> instruction
  | Xxadd      : xmem -> ireg -> instruction
  | Xthreadcreate : instruction.
  (* | Xbtbl      : ireg -> list label -> instruction *)
  (* | Xxchg      : reg_or_mem -> ireg -> instruction  *)
  (* | Xpop       : reg_or_mem -> instruction *)
  (* | Xpush      : imm_rm -> instruction  *)
  (* | Xleave     : instruction *)

(** * Semantics *)

(** ** Auxiliary data structures *)

(** Partially executed instructions.  These are needed to expose
  the memory labels and sequencing thereof, via some intermediate
  states (either in the processor state, eg a "pending write option"
  pseudoregister, or in the instructions). *)

Inductive pex_instruction := 
  | XPEdone  : pex_instruction
  | XPEstorei : ireg_or_mem -> val -> pex_instruction         (**r write 32bit int *)
  | XPEstoref : float_reg_or_mem -> val -> pex_instruction    (**r write 64bit float *)
  | XPEstorem : val -> memory_chunk -> val -> pex_instruction (**r write to memory *). 

Definition code := list instruction.
Definition fundef := Ast.fundef (signature * code).
Definition program := Ast.program fundef unit.

Inductive preg: Type :=
  | IR: ireg -> preg                    (**r integer registers *)
  | FR: freg -> preg                    (**r float registers *) 
  | ST0: preg                           (**r top of FP stack *)
  | EIP: preg                           (**r program counter *)
  | EFLAG: eflags -> preg.              (**r bits of the status register *)

Coercion IR: ireg >-> preg.
Coercion EFLAG: eflags >-> preg.
Coercion FR: freg >-> preg.

Lemma preg_eq: forall (x y: preg), {x=y} + {x<>y}.
Proof. decide equality; auto using ireg_eq, freg_eq, eflags_eq. Qed.

Module PregEq.
  Definition t := preg.
  Definition eq := preg_eq.
End PregEq.

Module Pregmap := EMap(PregEq).

Definition regset := Pregmap.t val.
Definition genv := Genv.t fundef.

Notation "a # b" := (a b) (at level 1, only parsing).
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level).

(** Undefining some registers *)

Fixpoint undef_regs (l: list preg) (rs: regset) : regset :=
  match l with
  | nil => rs
  | r :: l' => undef_regs l' (rs#r <- Vundef)
  end.

Inductive state: Type :=
  | Initstate:
      forall (f: pointer)              (**r pointer to the function to be called *)
             (args: list val),         (**r arguments to be passed to the function *)
      state
  | Initargsstate:
      forall (f: pointer)              (**r function to be called *)
             (args: list val)          (**r arguments to be passed to the function *)
             (locs: list loc)          (**r location for arguments *)
             (stkr: arange)            (**r stack range *)
             (rs: regset),             (**r register state *)
      state
  | Freestackstate:
      forall (stkr: arange),           (**r stack range *)
      state
  | Exitstate:
      state
  | Blockedstate:
       forall (s_regs: regset)           (**r registers *)
              (stkr: arange)             (**r allocated stack size *)
              (sig: signature),          (**r signature of the external function *)
       state
  | ReturnExternal:
       forall (s_regs: regset)           (**r registers *)
              (stkr: arange),            (**r allocated stack size *)
       state       
  | State:
       forall (s_regs: regset)           (**r registers *)
              (s_instr: pex_instruction) (**r fancy partially executed instructions,
                                              not really useful for us *)
              (stkr: arange),            (**r allocated stack size *)
       state.

Inductive cl_step_res : Type :=
  | Rnostep : cl_step_res
  | Rtau : state -> cl_step_res
  | Rwrite : pointer -> memory_chunk -> val -> state -> cl_step_res
  | Routofmemory : state -> cl_step_res
  | Rexternalcallmem : ident -> list (pointer * memory_chunk + eventval) -> state -> cl_step_res
  | Rfree : pointer -> mobject_kind -> state -> cl_step_res
  | Rexit : state -> cl_step_res  
  | Rread   : pointer -> memory_chunk -> (val -> state) -> cl_step_res
  | Rreturn : typ -> (val -> state) -> cl_step_res
  | Ralloc  : int -> mobject_kind -> (pointer -> state) -> cl_step_res
  | Rstart  : pointer * memory_chunk + val -> list (pointer * memory_chunk + val) -> state -> cl_step_res
  | Rmfence : state -> cl_step_res
  | Rmxadd  : pointer -> memory_chunk -> val -> (val -> state) -> cl_step_res
  | Rmcmpxchg : pointer -> memory_chunk -> val -> val -> (val -> state) -> cl_step_res.

Definition preg_of (r: mreg) : preg :=
  match r with
  | rEAX => IR EAX 
  | rEBX => IR EBX 
  | rEBP => IR EBP
  | rESI => IR ESI 
  | rEDI => IR EDI
  | IT1 => IR EDX 
  | IT2 => IR ECX  
  | rXMM0 => FR XMM0 
  | rXMM1 => FR XMM1 
  | rXMM2 => FR XMM2 
  | rXMM3 => FR XMM3 
  | rXMM4 => FR XMM4 
  | rXMM5 => FR XMM5
  | FT1 => FR XMM6 
  | FT2 => FR XMM7 
  | FP0 => ST0
  end.

Section x86semantics.

Variable ge: genv.

(** ** Finding instruction to execute *)

(** Looking up instructions in a code sequence by position. *)

Fixpoint find_instr (pos: Z) (c: code) {struct c} : option instruction :=
  match c with
  | nil => None
  | i :: il => if zeq pos 0 then Some i else find_instr (pos - 1) il
  end.

(** Position corresponding to a label *)

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Xlabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Xlabel lbl else instr <> Xlabel lbl.
Proof.
  destruct instr; simpl; try done. 
  destruct (peq lbl l); congruence. 
Qed.

Fixpoint label_pos (lbl: label) (pos: Z) (c: code) {struct c} : option Z :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some (pos + 1) else label_pos lbl (pos + 1) c'
  end.

(** Manipulations over the [EIP] register: continuing with the next
   instruction ([nextinstr]) or branching to a label ([goto_label]). *)

Definition nextinstr (rs : regset) :=
  rs#EIP <- (Val.add rs#EIP Vone).

Definition goto_label (lbl: label) (rs: regset) (stkr: arange) :=
  match rs EIP with
    | Vptr (Ptr b ofs) => 
      match Genv.find_funct_ptr ge (Ptr 0 (Int.repr b)) with
        | Some (Internal (_, c)) =>
          match label_pos lbl 0 c with
            | None => Rnostep
            | Some pos => 
                Rtau (State (rs # EIP <- (Vptr (Ptr b (Int.repr pos)))) XPEdone stkr)
          end
        | _ => Rnostep
      end
    | _ => Rnostep
  end.

(** Calculate operand values *)

Definition get_symbol (id: ident) : val :=
  match Genv.find_symbol ge id with
  | Some p => Vptr p
  | None => Vundef
  end.

Definition value_of_imm imm :=
  match imm with
  | Cint n => Vint n
  | Csymbol id ofs => Val.add (get_symbol id) (Vint ofs)
  end.

(** Calculate the effective address of an [m??] operand (possibly with a scaled
    index and displacement - overapproximating what is allowed in x86) *)

Definition ea_rm_base (rs:regset) (opt_r:option ireg) := match opt_r with
  | None => Vzero
  | Some r => rs#r
end.

Definition index_of_s s : Z := match (s.(hi),s.(lo)) with
 | (true,true) => 8
 | (true,false) => 4
 | (false,true) => 2
 | (false,false) => 1
end.

Definition ea_rm_index (rs:regset) (opt_sr:option (word2 * ireg)) :=
  match opt_sr with
  | None => Vzero
  | Some (s,r) => 
      match (s.(hi),s.(lo)) with
      | (false,false) => rs#r
      | _ => Val.mul rs#r (Vint (Int.repr (index_of_s s))) (*   r*(2**s) *)
      end
  end.

Definition ea (rs:regset) xm :=
  match xm with
    | (Xm i b d) =>
      Val.add (ea_rm_index rs i) (Val.add (ea_rm_base rs b) (value_of_imm d))
  end.

(** 8-bit and 16-bit conversions *)

Definition chunk_of_extend ex :=
  match ex with
    | ZX_I8 => Mint8unsigned
    | ZX_I16 => Mint16unsigned
    | SX_I8 => Mint8signed
    | SX_I16 => Mint16signed
  end.

Definition do_extend ex : val -> val :=
  match ex with
    | ZX_I8  => Val.zero_ext 8
    | ZX_I16 => Val.zero_ext 16
    | SX_I8  => Val.sign_ext 8
    | SX_I16 => Val.sign_ext 16
  end.

(** Calculate the value a count operand  *)

Definition value_of_count (rs:regset) count := match count with
  | Xc_imm imm => value_of_imm imm
  | Xc_CL => Val.zero_ext 8 (rs#ECX)  (**r masking to CL, otherwise unsound *)
end.

(** Read from & write to memory *)

Definition read_mem p chunk (f : val -> state) := 
  match p with
    | Vptr p => Rread p chunk f
    | _ => Rnostep
  end.

Definition write_mem rs p chunk (v: val) (stkr: arange) :=
  match p with
    | Vptr p => Rwrite p chunk (cast_value_to_chunk chunk v)(*Val.conv v (type_of_chunk chunk)*) 
                 (State rs XPEdone stkr)
    | _ => Rnostep
  end.

(** Read from & write to effective address *)

Definition read_ea  (rs:regset) xm chunk (f : val -> state) := 
  match ea rs xm with
    | Vptr p => Rread p chunk f
    | _ => Rnostep
  end.

Definition write_ea (rs:regset) xm chunk (v : val) (stkr: arange) := 
  match ea rs xm with
    | Vptr p => Rwrite p chunk (cast_value_to_chunk chunk v) (*Val.conv v (type_of_chunk chunk)*) 
                  (State rs XPEdone stkr)
    | _ => Rnostep
  end.

(** Read from & write to register-or-memory *)

Definition read_int_rm (rs:regset) x (f : val -> state) := 
  match x with
    | Xr  r => Rtau (f (rs r))
    | Xmm m => read_ea rs m Mint32 f
  end.

Definition read_low_int_rm (rs:regset) x ex (f : val -> state) := 
  match x with
    | Xlr  r => Rtau (f (do_extend ex (rs (ireg_of_low r))))
    | Xlmm m => read_ea rs m (chunk_of_extend ex) f
  end.

Definition read_float_rm (rs:regset) x (f : val -> state) := 
  match x with
    | Xfr  r => Rtau (f (rs r))
    | Xfmm m => read_ea rs m Mfloat64 f
  end.

Definition write_int_rm (rs:regset) x (v : val) (stkr : arange) :=
  match x with
    | Xr r =>  Rtau (State (rs # r <- v) XPEdone stkr)
    | Xmm m => write_ea rs m Mint32 v stkr
  end.

Definition write_float_rm (rs:regset) x (v : val) (stkr : arange) :=
  match x with
    | Xfr r =>  Rtau (State (rs # r <- v) XPEdone stkr)
    | Xfmm m => write_ea rs m Mfloat64 v stkr
  end.

(** Read from [dest_src] *)

Definition read_int_dest_src (rs:regset) ds (f : val -> val -> state) := 
  match ds with
    | Xri r i  => Rtau (f (rs r) (value_of_imm i))
    | Xrr r r2 => Rtau (f (rs r) (rs r2))
    | Xrm r m  => read_ea rs m Mint32 (f (rs r))
    | Xmr m r  => read_ea rs m Mint32 (fun v => f v (rs r))
  end.

Definition read_float_dest_src (rs:regset) ds (f : val -> val -> state) := 
  match ds with
    | Xfrr r r2 => Rtau (f (rs r) (rs r2))
    | Xfrm r m  => read_ea rs m Mfloat64 (f (rs r))
    | Xfmr m r  => read_ea rs m Mfloat64 (fun v => f v (rs r))
  end.

Definition move_int_dest_src (rs:regset) ds stkr := 
  match ds with
    | Xri r i  => Rtau (State(rs # r <- (value_of_imm i)) XPEdone stkr)
    | Xrr r r2 => Rtau (State(rs # r <- (rs r2)) XPEdone stkr)
    | Xrm r m  => read_ea rs m Mint32 (fun v => State (rs # r <- v) XPEdone stkr)
    | Xmr m r  => write_ea rs m Mint32 (rs r) stkr
  end.

Definition move_float_dest_src (rs:regset) ds stkr := 
  match ds with
    | Xfrr r r2 => Rtau (State(rs # r <- (rs r2)) XPEdone stkr)
    | Xfrm r m  => read_ea rs m  Mfloat64 (fun v => State (rs # r <- v) XPEdone stkr)
    | Xfmr m r  => write_ea rs m Mfloat64 (rs r) stkr
  end.

(** Return the destination of a [dest_src]. *)

Definition int_rm_dest ds := 
  match ds with
    | Xri r i  => Xr r
    | Xrr r r2 => Xr r 
    | Xrm r m  => Xr r 
    | Xmr m r  => Xmm m
  end.

Definition float_rm_dest ds := 
  match ds with
    | Xfrr r r2 => Xfr r 
    | Xfrm r m  => Xfr r 
    | Xfmr m r  => Xfmm m
  end.

Definition chunk_of_ty (ty: typ) : memory_chunk := 
   match ty with
     | Tint   => Mint32
     | Tfloat => Mfloat64
   end.

(** ** Updating the flags *)

Definition byte_parity (v:val) : val :=
  match v with
  | Vint n => Vundef
    (* TODO (if we ever need this): EVEN o LENGTH o FILTER I o n2bits 8 o w2n *)
  | _ => Vundef
  end.

Definition int_msb (n: int) : bool :=
  negb (Int.eq (Int.and n (Int.repr Int.half_modulus)) Int.zero).

Definition word_msb (v:val) : val :=
  match v with
  | Vint n => Val.of_bool (int_msb n)
  | _ => Vundef
  end.

Definition word_signed_overflow_sub (a b: int) : val :=
  Val.of_bool
    (andb (xorb (int_msb a) (int_msb b))
          (xorb (int_msb (Int.sub a b)) (int_msb a))).

Definition word_is_zero (v:val) :=
  match v with
    | Vint n => (if Int.eq n Int.zero then Vtrue else Vfalse)
    | _ => Vundef 
  end.

Definition write_eflag (f:eflags) (v:val) (rs:regset) :regset :=
  rs#(EFLAG f) <- v.

Definition write_logical_eflags (v:val) (rs:regset) :regset :=
    write_eflag PF (byte_parity v) (
    write_eflag ZF (word_is_zero v) (
    write_eflag SF (word_msb v) (
    write_eflag OF Vfalse (
    write_eflag CF Vfalse (
    write_eflag AF Vundef rs))))).  (* the AF value is not modelled *)

Definition write_arith_eflags (vc:val*val*val*val) (rs:regset) :regset :=
    let '(v,vcf,vof,_) := vc in
    write_eflag PF (byte_parity v) (
    write_eflag ZF (word_is_zero v) (
    write_eflag SF (word_msb v) (
    write_eflag OF vof (
    write_eflag CF vcf (
    write_eflag AF Vundef rs))))).

Definition write_arith_eflags_ZF (vc:val*val*val*val) (rs:regset) :regset :=
    let '(v,vcf,vof,vzf) := vc in
    write_eflag PF (byte_parity v) (
    write_eflag ZF vzf (
    write_eflag SF (word_msb v) (
    write_eflag OF vof (
    write_eflag CF vcf (
    write_eflag AF Vundef rs))))).

Definition erase_eflags (rs:regset) :regset :=
    write_eflag PF Vundef (
    write_eflag ZF Vundef (
    write_eflag SF Vundef (
    write_eflag OF Vundef (
    write_eflag CF Vundef (
    write_eflag AF Vundef rs))))).

(** ** Binary ALU operations *)

Definition write_int_result rs rm vc stkr :=
  State (write_arith_eflags vc rs) (XPEstorei rm (let '(v,_,_,_) := vc in v)) stkr.

Definition write_result_flags_only rs vc stkr :=
  State (write_arith_eflags_ZF vc rs) XPEdone stkr.

Definition write_logical_result rs rm v stkr :=
  State (write_logical_eflags v rs) (XPEstorei rm v) stkr. 

Definition write_logical_result_flags_only rs v stkr :=
  State (write_logical_eflags v rs) XPEdone stkr.

Definition write_result_erase_flags rs rm v stkr :=
  State (erase_eflags rs) (XPEstorei rm v) stkr. 

(** These two properly belong in Int.v *)
Definition add_carry (x y: int) : int :=
  if zle (Zplus (Int.unsigned x) (Int.unsigned y)) Int.modulus
  then Int.zero
  else Int.one.

Definition sub_borrow (x y: int) : int :=
  if zlt (Int.unsigned x) (Int.unsigned y)
  then Int.one
  else Int.zero.

(** These two properly belong in Values.v.  Note that for pointers the
    carry and borrow are calculated just from the offset arithmetic;
    the soundness of this w.r.t. real x86 execution would depend on
    the block base address being zero, or on some more subtle property
    ensuring that arithmetic on pointers never over/underflows *)

Definition add_with_carry_out (v1 v2: val) : (val*val*val*val) :=
  match v1, v2 with
  | Vint n1, Vint n2 => (Vint(Int.add n1 n2), Vint (add_carry n1 n2), Vundef, Vundef)
  | Vptr (Ptr b1 ofs1), Vint n2 =>
    (Vptr (Ptr b1 (Int.add ofs1 n2)), Vint (add_carry ofs1 n2), Vundef, Vundef)
  | Vint n1, Vptr (Ptr b2 ofs2) =>
    (Vptr (Ptr b2 (Int.add ofs2 n1)), Vint (add_carry n1 ofs2), Vundef, Vundef)
  | _, _ => (Vundef, Vundef, Vundef, Vundef)
  end.

(** VV: The following definition is really hacky.
    Normally, for the subtraction of pointers, we should require b1 = b2 = 0.
    Here we assume 
      (1) all pointers to be compared are non-zero (the null pointer is 
          represented as Vint 0), and 
      (2) pointers to different blocks are unequal.
    The fourth component of the result encodes this hack.
 *) 
Definition sub_with_borrow_out (v1 v2: val) : (val*val*val*val) :=
  match v1, v2 with
    | Vint n1, Vint n2 => 
        (Vint(Int.sub n1 n2), Vint (sub_borrow n1 n2),
         word_signed_overflow_sub n1 n2, word_is_zero (Vint (Int.sub n1 n2)))
    | Vptr (Ptr b1 ofs1), Vint n2 => 
        (Vptr (Ptr b1 (Int.sub ofs1 n2)), Vint (sub_borrow ofs1 n2), 
         word_signed_overflow_sub ofs1 n2, Vzero)
    | Vint n1, Vptr (Ptr b2 ofs2) => 
        (Vundef, Vundef, Vundef, Vzero)
    | Vptr (Ptr b1 ofs1), Vptr (Ptr b2 ofs2) => 
        if zeq b1 b2 then 
          (Vint (Int.sub ofs1 ofs2), Vint (sub_borrow ofs1 ofs2),
           word_signed_overflow_sub ofs1 ofs2, word_is_zero (Vint (Int.sub ofs1 ofs2)))
        else (Vundef, Vundef, Vundef, Vzero)
    | _, _ => (Vundef, Vundef, Vundef, Vundef)
  end.

Definition write_int_binop rs binop rm stkr (v1 v2 : val) : state :=
  match binop with
    | Xadd  => write_int_result rs rm (add_with_carry_out v1 v2) stkr
    | Xsub  => write_int_result rs rm (sub_with_borrow_out v1 v2) stkr
    | Ximul => write_result_erase_flags rs rm (Val.mul v1 v2) stkr
    | Xcmp  => write_result_flags_only rs (sub_with_borrow_out v1 v2) stkr
    | Xand  => write_logical_result rs rm (Val.and v1 v2) stkr
    | Xxor  => write_logical_result rs rm (Val.xor v1 v2) stkr
    | Xor   => write_logical_result rs rm (Val.or v1 v2) stkr
    | Xtest => write_logical_result_flags_only rs (Val.and v1 v2) stkr
  end.

(** ** Binary floating point operations *)

Definition floatop (v1 v2: val) (op: float -> float -> float): val :=
  match v1, v2 with
    | Vfloat f1, Vfloat f2 => Vfloat (op f1 f2)
    | _, _ => Vundef
  end.

Definition unorderedf (v1 v2 : val) :=
  match v1, v2 with
    | Vfloat f1, Vfloat f2 => Val.of_bool (Float.unordered f1 f2)
    | _, _ => Vundef
  end.

Definition write_comisd rs (v1 v2 : val) stkr : state :=
    State (
      write_eflag OF Vzero (
      write_eflag AF Vzero (
      write_eflag SF Vzero (
      write_eflag PF (unorderedf v1 v2) (
      write_eflag ZF (Val.or (unorderedf v1 v2) (Val.cmpf Ceq v1 v2)) (
      write_eflag CF (Val.or (unorderedf v1 v2) (Val.cmpf Clt v1 v2)) rs))))))
    XPEdone
    stkr.

Definition write_float_binop rs binop rm stkr (v1 v2 : val)  :=
  match binop with
    | Xaddf  => State rs (XPEstoref rm (floatop v1 v2 Float.add)) stkr
    | Xsubf  => State rs (XPEstoref rm (floatop v1 v2 Float.sub)) stkr
    | Xmulf  => State rs (XPEstoref rm (floatop v1 v2 Float.mul)) stkr
    | Xdivf  => State rs (XPEstoref rm (floatop v1 v2 Float.div)) stkr
    | Xcomisd => write_comisd rs v1 v2 stkr
  end.

(** ** Shift operations *)

(**
  NB 1: the above semantics over-approximates the resulting flags, e.g.
  setting all to Vundef for the shift operations.

  NB 2: the Values.v shift operations are Vundef if the shift index is
  bigger than wordsize whereas the x86 masks to 5 (or 6) bits.
*)

Definition write_shift rs shiftop_name rm (v1 v2:val) :=
  match shiftop_name with
    | Xrol  => write_result_erase_flags rs rm (Val.rol v1 v2)
    | Xshr  => write_result_erase_flags rs rm (Val.shru v1 v2)
    | Xsar  => write_result_erase_flags rs rm (Val.shr v1 v2)
    | Xsal  => write_result_erase_flags rs rm (Val.shl v1 v2)
    | Xror  => write_result_erase_flags rs rm (Val.ror v1 v2)
  end.

(** ** Unary operations *)

Definition write_monop rs monop rm stkr v :=
  match monop with
    | Xnot => State rs (XPEstorei rm (Val.notint v)) stkr
    | Xneg => write_int_result rs rm (Val.sub Vzero v, Vundef, Vundef, Vundef) stkr
    | Xdiv => 
        if Val.eq_dec (rs#EDX) Vzero then 
          State (rs#EAX <- (Val.divu rs#EAX v)
                   #EDX <- (Val.modu rs#EAX v))
                XPEdone stkr
        else 
          State (rs#EAX <- Vundef
                   #EDX <- Vundef)
                XPEdone stkr
    | Xidiv =>
        if Val.eq_dec (rs#EDX) (Val.sign (rs#EAX)) then 
          State (rs#EAX <- (Val.divs rs#EAX v)
                   #EDX <- (Val.mods rs#EAX v))
                XPEdone stkr
        else 
          State (rs#EAX <- Vundef
                   #EDX <- Vundef)
                XPEdone stkr
  end.

(** ** Evaluating conditions of eflags *)

Definition vi_eq (v1 v2: val): bool3 :=
  match v1, v2 with
  | Vint n1, Vint n2 => if (Int.eq n1 n2) then b3_true else b3_false
  | _, _ => b3_unknown
  end.

Definition read_cond (rs:regset) cond : bool3 :=
  match cond with
  | X_A      => andb3 (vi_eq (rs#CF) Vzero) (vi_eq (rs#ZF) Vzero)       (**r CF=0 /\ ZF=0    *)
  | X_AE     => vi_eq (rs#CF) Vzero                                     (**r CF=0            *)
  | X_ALWAYS => b3_true                                                 (**r t               *)
  | X_B      => vi_eq (rs#CF) Vone                                      (**r CF=1            *)
  | X_BE     => orb3 (vi_eq (rs#CF) Vone)  (vi_eq (rs#ZF) Vone)         (**r CF=1 \/ ZF=1    *)
  | X_E      => vi_eq (rs#ZF) Vone                                      (**r ZF=1            *)
  | X_G      => andb3(vi_eq (rs#ZF) Vzero) (vi_eq (rs#SF) (rs#OF))      (**r ZF=0 /\ SF=OF   *)
  | X_GE     => vi_eq (rs#SF) (rs#OF)                                   (**r SF=OF           *)
  | X_L      => negb3 (vi_eq (rs#SF) (rs#OF))                           (**r SF=/=OF         *)
  | X_LE     => orb3(vi_eq (rs#ZF) Vone) (negb3 (vi_eq (rs#SF) (rs#OF)))(**r ZF=1 \/ SF=/=OF *)
  | X_NE     => vi_eq (rs#ZF) Vzero                                     (**r ZF=0            *)
  | X_NS     => vi_eq (rs#SF) Vzero                                     (**r SF=0            *)
  | X_ENP    => andb3(vi_eq (rs#ZF) Vone) (vi_eq (rs#PF) Vzero)    (**r PSEUDO: ZF=1 /\ PF=0 *)
  | X_NEP    => orb3 (vi_eq (rs#ZF) Vzero) (vi_eq (rs#PF) Vone)    (**r PSEUDO: ZF=0 \/ PF=1 *)
end.

(** ** Execution of one instruction *)

(** NB For a machine code semantics, we'd have to pass the instruction
    opcode length len in as a parameter here because it is not
    determined by the instruction; there may be a LOCK prefix. In
    CompCert, EIP stores instruction indices, not addresses, so that's
    not necessary. 
*)

Definition code_pointer_from_function_ident (id: ident) : val :=
  match Genv.find_symbol ge id with
    | Some (Ptr b ofs) => Vptr (Ptr (Int.unsigned ofs) Int.zero)
    | None => Vundef
  end.

Definition memarg_of_location_asm rs sp l := 
  match l with
    | R r => inr _ (Pregmap.get (preg_of r) rs)
    | S (Incoming ofs ty) => 
        inl _ (MPtr.add sp (Int.repr (4 * ofs)), chunk_of_ty ty)
    | _ => inr _ Vundef
  end.

Definition memarglist_from_sig_asm (rs : regset) (sp : pointer) (sig : signature)
                           : list (pointer * memory_chunk + val) :=
  map (memarg_of_location_asm rs sp) (Conventions.loc_parameters sig).

Definition exec_instr (i: instruction) (rs:regset) (stkr: arange) : cl_step_res := 
  match i with
  | Xbinop binop_name ds => 
      read_int_dest_src rs ds
        (write_int_binop (nextinstr rs) binop_name (int_rm_dest ds) stkr) 
  | Xbinopf binop_name ds => 
      read_float_dest_src rs ds
        (write_float_binop (nextinstr rs) binop_name (float_rm_dest ds) stkr) 
  | Xmonop monop_name rm =>
      match monop_name with
      | Xdiv | Xidiv =>
         read_int_rm (rs#EDX <- Vundef) rm 
            (write_monop (nextinstr rs) monop_name rm stkr)
      | _ =>
         read_int_rm rs rm
            (write_monop (nextinstr rs) monop_name rm stkr)
      end
  | Xshift shiftop_name rm count =>
      read_int_rm rs rm
        (fun v => write_shift (nextinstr rs) 
           shiftop_name rm v (value_of_count rs count) stkr)
  | Xxor_self r =>
      Rtau (write_logical_result (nextinstr rs) (Xr r) Vzero stkr)
  | Xcltd => 
      Rtau (State ((nextinstr rs) # EDX <- (Val.sign (rs # EAX))) XPEdone stkr)
  | Xlea r m => 
      Rtau (State ((nextinstr rs) # r <- (ea rs m)) XPEdone stkr)
  | Xmov ds =>
      move_int_dest_src (nextinstr rs) ds stkr
  | Xmovx ex r rm => 
      read_low_int_rm (nextinstr rs) rm ex
         (fun v => State ((nextinstr rs) # r <- v) XPEdone stkr)
  | Xmovt ex m r =>
     write_ea (nextinstr rs) m (chunk_of_extend ex) (rs (ireg_of_low r)) stkr
  | Xmovsd ds => 
      move_float_dest_src (nextinstr rs) ds stkr
  | Xmovftr r1 r2 => 
      Rtau (State ((nextinstr rs) # r1 <- (Val.singleoffloat (rs # r2))) XPEdone stkr)
  | Xmovftm m r => 
      write_ea (nextinstr rs) m Mfloat32 ((*Val.singleoffloat*) (rs # r)) stkr
  | Xmovif r1 r2 => 
      Rtau (State ((nextinstr rs) # r1 <- (rs # r2)) XPEdone stkr)
  | Xmovfi r1 r2 => 
      Rtau (State ((nextinstr rs) # r1 <- (rs # r2)) XPEdone stkr)
  | Xmovstr fr =>
      Rtau (State ((nextinstr rs) # fr <- (rs ST0)) XPEdone stkr)
  | Xmovrst fr =>
      Rtau (State ((nextinstr rs) # ST0 <- (rs fr)) XPEdone stkr)
  | Xset c r => 
      Rtau (State ((nextinstr rs) # ECX <- Vundef
                                  # EDX <- Vundef 
                                  # r <- 
         (match (read_cond rs c) with
          | b3_true    => Vone
          | b3_false   => Vzero
          | b3_unknown => Vundef
          end)) XPEdone stkr)
  | Xcmov c r rm =>
      match read_cond rs c with
        | b3_true =>
        read_int_rm rs rm
          (fun v => State ((nextinstr rs) # r <- v) XPEdone stkr)
        | b3_false =>
          Rtau (State (nextinstr rs) XPEdone stkr)
        | b3_unknown => Rnostep
      end
  | Xjump cond lbl =>
      match read_cond rs cond with
        | b3_true => goto_label lbl rs stkr 
        | b3_false => Rtau (State (nextinstr rs) XPEdone stkr)
        | b3_unknown => Rnostep
      end
  | Xlabel l =>
      Rtau (State (nextinstr rs) XPEdone stkr)
  | Xcall ident =>
      let v_new_eip := code_pointer_from_function_ident ident in
      let v_next_eip := Val.add (rs EIP) Vone in
      let v_new_esp := Val.sub (rs ESP) (Vint (Int.repr 4)) in
      match v_new_esp with
        | Vptr p => 
            if range_inside_dec (p, Int.zero) stkr 
            then write_mem ((rs#EIP<-v_new_eip)#ESP<-v_new_esp) v_new_esp Mint32 v_next_eip stkr
            else Routofmemory Exitstate
        | _ => write_mem ((rs#EIP<-v_new_eip)#ESP<-v_new_esp) v_new_esp Mint32 v_next_eip stkr
      end
  | Xcallreg r =>
      match rs r with
      | Vptr (Ptr b ofs) =>
          let v_new_eip := Vptr (Ptr (Int.unsigned ofs) Int.zero) in
          let v_next_eip := Val.add (rs EIP) Vone in
          let v_new_esp := Val.sub (rs ESP) (Vint (Int.repr 4)) in
          match v_new_esp with
          | Vptr p => 
              if range_inside_dec (p, Int.zero) stkr 
              then write_mem ((rs#EIP<-v_new_eip)#ESP<-v_new_esp) v_new_esp Mint32 v_next_eip stkr
              else Routofmemory Exitstate
          | _ => write_mem ((rs#EIP<-v_new_eip)#ESP<-v_new_esp) v_new_esp Mint32 v_next_eip stkr
          end
        | _ => Rnostep
      end
  | Xret imm =>
      let v_extra_pop := value_of_imm imm in
      let v_new_esp := Val.add (rs ESP) (Val.add v_extra_pop (Vint (Int.repr 4))) in
      read_mem (rs ESP) Mint32 
        (fun v_new_eip => 
          if Val.eq_dec v_new_eip (Vptr nullptr)
          then Freestackstate stkr
          else State ((rs#EIP<-v_new_eip)#ESP<-v_new_esp) XPEdone stkr)

  | Xfloatconst r v  => 
     Rtau (State ((nextinstr rs) # r <- (Vfloat v)) XPEdone stkr)
  | Xcvttsd2si ir fr =>
      Rtau (State ((nextinstr rs) # ir <- (Val.intoffloat rs#fr)) XPEdone stkr)
  | Xcvtsi2sd fr ir =>
      Rtau (State ((nextinstr rs) # fr <- (Val.floatofint rs#ir)) XPEdone stkr)
  | Xcvtss2sd fr m =>
      read_ea rs m Mfloat32 (fun v => State ((nextinstr rs) # fr <- v) XPEdone stkr)
  | Xnegf fr => 
      Rtau (State ((nextinstr rs) # fr <- (Val.negf rs#fr)) XPEdone stkr)
  | Xfctiu ir fr => 
      Rtau (State ((nextinstr rs) # ir <- (Val.intuoffloat rs#fr) 
                                  # XMM7 <- Vundef # XMM6 <- Vundef) XPEdone stkr)
  | Xiuctf fr ir   => 
      Rtau (State ((nextinstr rs) # fr <- (Val.floatofintu rs#ir)) XPEdone stkr)
  | Xfstpl m => 
      write_float_rm (nextinstr rs) (Xfmm m) (rs#ST0) stkr
  | Xfldl m => 
      read_float_rm rs (Xfmm m) (fun v =>
        State ((nextinstr rs) # ST0 <- v) XPEdone stkr)
  | Xmfence => 
      Rmfence (State (nextinstr rs) XPEdone stkr)
  | Xthreadcreate =>
      match (rs ESP) with
      | Vptr p =>
        match memarglist_from_sig_asm rs p thread_create_sig with
        | fn :: args => Rstart fn args (State (nextinstr rs) XPEdone stkr)
        | _ => Rnostep (* never happens *)
        end
      | _ => Rnostep 
      end
  | Xxadd m r =>
      match ea rs m with
      | Vptr p => 
          Rmxadd p Mint32 (rs#r)
            (fun v => State ((nextinstr rs) # r <- v) XPEdone stkr)
      | _ => Rnostep
      end
  | Xcmpxchg m r =>
      match ea rs m with
      | Vptr p => 
          Rmcmpxchg p Mint32 (rs#EAX) (rs#r) (fun v => 
            State (if Val.eq_dec v (rs#EAX) 
                   then (erase_eflags (nextinstr rs)) # ZF <- Vtrue
                   else ((erase_eflags (nextinstr rs)) # EAX <- v) # ZF <- Vfalse)
                  XPEdone stkr)
      | _ => Rnostep
      end

    (* | Xpush irm => *)
    (*   let v_new_esp := Val.sub (rs ESP) (Vint (Int.repr 4)) in *)
    (*   read_imm_rm rs irm Mint32 *)
    (*     (fun v => State ((nextinstr rs)#ESP<-v_new_esp) (XPEstorem v_new_esp Mint32 v)) *)
    (* | Xpop rm => *)
    (*   let v_new_esp := Val.add (rs ESP) (Vint (Int.repr 4)) in *)
    (*   read_mem (rs ESP) Mint32 *)
    (*     (fun v => State ((nextinstr rs)#ESP<-v_new_esp) (XPEstore rm Mint32 v)) *)
end.

Definition funsig (f : fundef) := 
  match f with
    | External ef => ef.(ef_sig)
    | Internal (sg, _) => sg
  end.

Definition eval_of_val_memarg (v : pointer * memory_chunk + val) 
                            : option (pointer * memory_chunk + eventval) :=
  match v with 
    | inl pc => Some (inl _ pc)
    | inr v => match eval_of_val v with Some ev => Some (inr _ ev) | None => None end
  end.

Fixpoint map_eval_of_val_memarg (vl : list (pointer * memory_chunk + val)) 
                            : option (list (pointer * memory_chunk + eventval)) :=
  match vl with
    | nil => Some nil
    | v::vl => 
      match eval_of_val_memarg v with 
        | Some ev => match map_eval_of_val_memarg vl with
                       | Some evl => Some (ev :: evl)
                       | None => None
                     end
        | None => None
      end
  end.

Definition align_stack p :=
  let '(Ptr b ofs) := p in
  let nofs := (Int.unsigned ofs / 16) * 16 in
   Ptr b (Int.repr nofs).

Definition rm_eq_esp rm :=
  match rm with 
    | Xr ESP => true
    | _ => false
  end.

Definition exec_pex_instr (s:state) : cl_step_res := 
  match s with
    | State rs i stkr =>
      match i with
        | XPEdone => 
          match rs EIP with
            | Vptr (Ptr b ofs) =>
              match Genv.find_funct_ptr ge (Ptr 0 (Int.repr b)) with
                | Some (Internal (_, c)) =>
                  match find_instr (Int.unsigned ofs) c with
                    | Some i => exec_instr i rs stkr
                    | None   => Rnostep
                  end
                | Some (External ef) => 
                  match rs ESP with
                    | Vptr sp =>
                        let memargs := memarglist_from_sig_asm rs 
                             (MPtr.add sp (Int.repr Stacklayout.fe_retaddrsize)) ef.(ef_sig) in
                        match map_eval_of_val_memarg memargs with
                          |  Some extmemargs =>
                            Rexternalcallmem ef.(ef_id) extmemargs
                                    (Blockedstate rs stkr ef.(ef_sig))
                          | _ => Rnostep
                        end
                    | _ => Rnostep
                  end
                | _ => Rnostep
              end
            | _ => Rnostep
          end
        | XPEstorei rm v => 
            if (rm_eq_esp rm) then
              match v with
                | Vptr p =>
                    if range_inside_dec (p, Int.zero) stkr 
                    then write_int_rm rs rm v stkr
                    else Routofmemory Exitstate
                | _ => Rnostep
              end
            else write_int_rm rs rm v stkr
        | XPEstoref rm v => write_float_rm rs rm v stkr
        | XPEstorem p chunk v => write_mem rs p chunk v stkr
      end

    | Blockedstate rs stkr efsig =>
       let ty := match sig_res efsig with Some x => x | None => Tint end in
       Rreturn ty (fun v => 
         ReturnExternal (rs#(preg_of (Conventions.loc_result efsig)) <- v) stkr)

    | ReturnExternal rs stkr =>
       let v_new_esp := Val.add (rs ESP) (Vint (Int.repr 4)) in
       read_mem (rs ESP) Mint32 
        (fun v_new_eip => 
          if Val.eq_dec v_new_eip (Vptr nullptr)
          then Freestackstate stkr
          else State ((rs#EIP<-v_new_eip)#ESP<-v_new_esp) XPEdone stkr)

    | Initstate f args =>
      match Genv.find_funct_ptr ge f with
        | Some fn =>
          let size := 4 * Conventions.size_arguments (funsig fn) in 
          if zle (size + 15 + Stacklayout.fe_retaddrsize) Stacklayout.thread_stack_size
          then
          Ralloc (Int.repr Stacklayout.thread_stack_size) MObjStack 
                 (fun stkp => 
                   let sp := MPtr.add stkp (Int.repr (Stacklayout.thread_stack_size - size)) in
                   let asp := align_stack sp in
                   Initargsstate
                   f args (Conventions.loc_parameters (funsig fn))
                   (stkp, Int.repr Stacklayout.thread_stack_size) 
          ((Pregmap.init Vundef)
             # ESP <- (Vptr (MPtr.sub_int asp (Int.repr Stacklayout.fe_retaddrsize)))))
          else Routofmemory s
        | None => Rnostep  
       end

    | Initargsstate (Ptr b ofs) nil nil stkr rs =>
        match rs ESP with
          | Vptr sp =>
            let rs' := rs # EIP <- (Vptr (Ptr (Int.unsigned ofs) Int.zero)) in
              Rwrite sp Mint32 (Vptr nullptr)
              (State rs' XPEdone stkr)
          | _ => Rnostep
        end

    | Initargsstate f (arg::args) (S (Incoming ofs ty) :: locs) stkr rs =>
        match rs ESP with
          | Vptr sp =>
              let argp := MPtr.add sp (Int.repr (4 * ofs + Stacklayout.fe_retaddrsize)) in
              Rwrite argp (chunk_of_ty ty) arg
              (Initargsstate f args locs stkr rs)
          | _ => Rnostep
        end
    | Initargsstate f (arg::args) ((R r) :: locs) stkr rs =>
        Rtau
        (Initargsstate f args locs stkr (rs# (preg_of r)<-arg))
    | Initargsstate f _ _ stkr rs =>
        Rnostep
      
    | Freestackstate stkr =>
        Rfree (fst stkr) MObjStack Exitstate

    | Exitstate =>
        Rexit Exitstate
  
  end.

(** ** Execution of the instruction at [rs#EIP] *)

Definition xstep_fn (s : state) (te : thread_event) : option state :=
  match exec_pex_instr s with
  | Rnostep => None
  | Rtau s => if thread_event_eq_dec te TEtau then Some s else None
  | Rwrite p c v  s => if thread_event_eq_dec te (TEmem (MEwrite p c v)) then Some s else None
  | Routofmemory s => if thread_event_eq_dec te TEoutofmem then Some s else None
  | Rexternalcallmem id args s => 
      if thread_event_eq_dec te (TEexternalcallmem id args) then Some s else None
  | Rfree p ok s => if thread_event_eq_dec te (TEmem (MEfree p ok)) then Some s else None
  | Rexit s => if thread_event_eq_dec te TEexit then Some s else None
  | Rstart fn args s => if thread_event_eq_dec te (TEstartmem fn args) then Some s else None
  | Rread   p c f =>
      match te with
      | TEmem (MEread p' c' v) =>
           if MPtr.eq_dec p p' then
             if memory_chunk_eq_dec c c' then
               if Val.has_type v (type_of_chunk c) then Some (f v)
               else None
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
  | Rmfence s => 
      if thread_event_eq_dec te (TEmem MEfence) then Some s else None
  | Rmxadd p c vadd f =>
      match te with
      | TEmem (MErmw p' c' vret ao) =>
          if MPtr.eq_dec p p' then
            if memory_chunk_eq_dec c c' then
              if rmw_instr_dec ao (rmw_ADD vadd) then
                if Val.has_type vret (type_of_chunk c) then Some (f vret)
                else None
              else None
            else None
          else None
     | _ => None
     end
  | Rmcmpxchg p c vold vnew f =>
      match te with
      | TEmem (MErmw p' c' vret ao) =>
          if MPtr.eq_dec p p' then
            if memory_chunk_eq_dec c c' then
              if rmw_instr_dec ao (rmw_CAS vold vnew) then
                if Val.has_type vret (type_of_chunk c) then Some (f vret)
                else None
              else None
            else None
          else None
     | _ => None
     end
  end.

(** ** Initialization *)

Definition x86_init  (p : pointer) (vs : list val) : option state :=
  match Genv.find_funct_ptr ge p with
   | Some (Internal f)  => 
       if beq_nat (length vs) (length (fst f).(sig_args))
         then Some (Initstate p (Val.conv_list vs (fst f).(sig_args)))
         else None
   | _ => None
  end.

End x86semantics.

Definition x86_ge_init (p : program) (ge : genv) (m : Mem.mem) :=
  Genv.globalenv_initmem p ge low_mem_restr m.

(** * TSO machine set up *)

Section X86_TSO.

Definition x86_step := fun ge s l s' => xstep_fn ge s l = Some s'.

Lemma x86_receptive :
  forall ge l l' s s',
    x86_step ge s l s' ->
    te_samekind l' l ->
    exists s'', x86_step ge s l' s''.
Proof.
  unfold x86_step, xstep_fn.
  intros g l l' s s' Step Te_Samekind.
  destruct (exec_pex_instr g s) as [] _eqn: X; clarify;
    destruct l as [[] | [] | | | | | |]; clarify;
     destruct l' as [[] | [] | | | | | |]; simpl in Te_Samekind;
       repeat match goal with
              | H : _ /\ _ |- _ => destruct H; clarify
            end;
     clarify; vauto;
  repeat (destruct thread_event_eq_dec; clarify; vauto);
  repeat (destruct MPtr.eq_dec; clarify; vauto);
  repeat (destruct Int.eq_dec; clarify; vauto);
  repeat (destruct memory_chunk_eq_dec; clarify; vauto);
  repeat (destruct mobject_kind_eq_dec; clarify; vauto);
  repeat (destruct typ_eq_dec; clarify; vauto);
  repeat (destruct list_eq_dec; clarify; vauto);
  repeat (destruct rmw_instr_dec; clarify; vauto);
  simpl in *; repeat match goal with
              | H : _ /\ _ |- _ => destruct H; clarify
            end;
  by do 2 destruct (Val.has_type); clarify; exploit H0; clarify; vauto.
Qed.

Lemma x86_determinate:
  forall ge s s' s'' l l',
    x86_step ge s l s' ->
    x86_step ge s l' s'' ->
    (te_samekind l l' /\ (l = l' -> s' = s'')).
Proof.
  unfold x86_step, xstep_fn.
  intros g s s' s'' l l' ST1 ST2.
    destruct (exec_pex_instr); clarify;
  repeat (destruct thread_event_eq_dec; clarify; vauto);
  try (by destruct t as [[] | [] | | | |]);
    destruct l as [[] | [] | | | | | |]; clarify;
     destruct l' as [[] | [] | | | | | |];
     clarify; simpl;
  repeat (destruct MPtr.eq_dec; clarify; vauto);
  repeat (destruct Int.eq_dec; clarify; vauto);
  repeat (destruct memory_chunk_eq_dec; clarify; vauto);
  repeat (destruct mobject_kind_eq_dec; clarify; vauto);
  repeat (destruct typ_eq_dec; clarify; vauto); simpl.
  by do 2 (destruct Val.has_type; clarify); split; intros; clarify.
  split; try destruct Val.has_type; intros; clarify;
    by do 3 (destruct Val.has_type; clarify); try split; intros; clarify.
  by split; intros; clarify.
  repeat split;
    [ repeat (destruct rmw_instr_dec; clarify; vauto) 
    | do 2 (destruct Val.has_type; clarify); destruct rmw_instr_dec; inv ST1
    | intros; clarify'].
  repeat split;
    [ repeat (destruct rmw_instr_dec; clarify; vauto) 
    | do 2 (destruct Val.has_type; clarify); destruct rmw_instr_dec; inv ST1
    | intros; clarify'].
Qed.

Require Import Classical.

Lemma x86_progress_dec:
    forall ge s, (forall s' l', ~ x86_step ge s l' s') \/
      (exists l', exists s', x86_step ge s l' s').
Proof.
  intros g s.
  set (P := exists l' : thread_event, exists s' : state, x86_step g s l' s').
  destruct (classic P). auto.
  left. intros s' l'. revert s'. apply not_ex_all_not.
  revert l'. apply not_ex_all_not. auto.
Qed.


Definition x86_sem : SEM := 
  mkSEM state genv program x86_ge_init (@prog_main _ _) (@Genv.find_symbol _) 
  x86_step x86_init x86_progress_dec x86_receptive x86_determinate.

End X86_TSO.
