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

open Printf
open Datatypes
open Camlcoq 
open Ast
open Asm

(* Recognition of target ABI and asm syntax *)

type target = ELF | AOUT | MacOS

let target = 
  (* environment variable to override Configuration.system so that we
  can test whether we produce syntactically well-formed .s files on
  linux despite only having a macosx x86 CompCert *)
  let c = 
    try Sys.getenv "PRINTASM_CONFIG" with
    | Not_found -> Configuration.system in 
  match c with
  | "macosx" -> MacOS
  | "linux"  -> ELF
  | _        -> invalid_arg ("System " ^ Configuration.system ^ " not supported")

(* On-the-fly label renaming *)

let next_label = ref 100

let new_label() =
  let lbl = !next_label in incr next_label; lbl

let current_function_labels = (Hashtbl.create 39 : (label, int) Hashtbl.t)

let transl_label lbl =
  try
    Hashtbl.find current_function_labels lbl
  with Not_found ->
    let lbl' = new_label() in
    Hashtbl.add current_function_labels lbl lbl';
    lbl'

(* Record identifiers of functions that need a special stub *)
(* module IdentSet = Set.Make(struct type t = ident let compare = compare end) *)
(* let stubbed_functions = ref IdentSet.empty *)
(* let remove_variadic_prefix name = *)
(*   try String.sub name 0 (String.index name '$') *)
(*   with Not_found -> name *)

(* Basic printing functions *)

let coqint oc n =
  fprintf oc "%ld" (camlint_of_coqint n)

let raw_symbol oc s =
  match target with
  | ELF -> fprintf oc "%s" s
  | MacOS | AOUT -> fprintf oc "_%s" s

let re_variadic_stub = Str.regexp "\\(.*\\)\\$[if]*$"

let symbol oc symb =
  let s = extern_atom symb in
  if Str.string_match re_variadic_stub s 0
  then raw_symbol oc (Str.matched_group 1 s)
  else raw_symbol oc s

let symbol_offset oc (symb, ofs) =
  symbol oc symb;
  if ofs <> 0l then fprintf oc " + %ld" ofs

let label oc lbl =
  match target with
  | ELF -> fprintf oc ".L%d" lbl
  | MacOS | AOUT -> fprintf oc "L%d" lbl

let comment = "#"

let section oc name =
  fprintf oc "	%s\n" name

(* Names of sections *)

let (text, data, const_data, float_literal, jumptable_literal) =
  match target with
  | ELF ->
      (".text",
       ".data",
       ".section	.rodata",
       ".section	.rodata.cst8,\"a\",@progbits",
       ".text")
  | MacOS ->
      (".text",
       ".data",
       ".const",
       ".const_data",
       ".text")
  | AOUT ->
      (".text",
       ".data",
       ".section	.rdata,\"dr\"",
       ".section	.rdata,\"dr\"",
       ".text")

(* Base-2 log of a Caml integer *)

let rec log2 n =
  assert (n > 0);
  if n = 1 then 0 else 1 + log2 (n lsr 1)

(* Emit a align directive *)

let print_align oc n =
  match target with
  | ELF          -> fprintf oc "	.align	%d\n" n
  | AOUT | MacOS -> fprintf oc "	.align	%d\n" (log2 n)

let need_masks = ref false

(* Built-in functions *)

let re_builtin_function = Str.regexp "__builtin_"

let is_builtin_function s =
  Str.string_match re_builtin_function (extern_atom s) 0

let print_builtin_function oc s =
  fprintf oc "%s begin %s\n" comment (extern_atom s);
  fprintf oc "BUILTIN FUNCTION TODO\n"

(* Printing of instructions *)

module Labelset = Set.Make(struct type t = label let compare = compare end) 

let float_literals : (int * int64) list ref = ref []

(* *) 
let rec labels_of_code accu = function
  | [] ->
      accu
  | Xjump(_, lbl) :: c -> 
      labels_of_code (Labelset.add lbl accu) c
  (* | Xbtbl(_, tbl) :: c ->  *)
  (*     labels_of_code (List.fold_right Labelset.add tbl accu) c  *)
  | _ :: c ->
      labels_of_code accu c

(* floatconsts *)
(* let rec floatconsts_of_code accu = function *)
(*   | [] -> *)
(*       accu *)
(*   | Xfloatconst(_, f) :: c ->  *)
(*       let lbl = new_label() in *)
(*       floatconsts_of_code ((f,lbl)::accu) c *)
(*   | _ :: c -> *)
(*       floatconsts_of_code accu c *)

(* let rec floatconsts_of_functs fl =  *)
(*   List.concat  *)
(*     (List.map  *)
(*        (function Coq_pair(name, defn) ->  *)
(*          match defn with Internal fn -> floatconsts_of_code [] fn | _ -> [])  *)
(*        fl) *)

(** x86 *) 

let print_extend = function
 | ZX_I8  -> "zbl"
 | ZX_I16 -> "zwl"
 | SX_I8  -> "sbl"
 | SX_I16 -> "swl"

let print_size = function 
  | ZX_I8  -> "b"
  | ZX_I16 -> "w"
  | SX_I8  -> "b" 
  | SX_I16 -> "w" 

let ireg32 = function
  | EAX -> "%eax" 
  | EBX -> "%ebx"
  | ECX -> "%ecx"
  | EDX -> "%edx"
  | ESP -> "%esp"
  | EBP -> "%ebp"
  | ESI -> "%esi"
  | EDI -> "%edi"

let low_ireg ex r : string = 
  (match r with
    | AX -> "%a"
    | BX -> "%b"
    | CX -> "%c"
    | DX -> "%d") ^ 
  (match ex with
    | ZX_I8 | SX_I8   -> "l"
    | ZX_I16 | SX_I16 -> "x")

let freg64 : freg -> string = function
  | XMM0 -> "%xmm0"
  | XMM1 -> "%xmm1"
  | XMM2 -> "%xmm2"
  | XMM3 -> "%xmm3"
  | XMM4 -> "%xmm4"
  | XMM5 -> "%xmm5"
  | XMM6 -> "%xmm6"
  | XMM7 -> "%xmm7"

let eflags_strings = [
  (CF,"CF");
  (PF,"PF");
  (AF,"AF");
  (ZF,"ZF");
  (SF,"SF");
  (OF,"OF")]

let eflags oc = function f -> 
  output_string oc (List.assoc f eflags_strings)

let init_data_queue = ref []

let print_init oc = function
  | Init_int8 n ->
      fprintf oc "	.byte	%ld\n" (camlint_of_coqint n)
  | Init_int16 n ->
      fprintf oc "	.short	%ld\n" (camlint_of_coqint n)
  | Init_int32 n ->
      fprintf oc "	.long	%ld\n" (camlint_of_coqint n)
  | Init_float32 n ->
      fprintf oc "	.long	%ld %s %.18g\n" (Int32.bits_of_float n) comment n
  | Init_float64 n ->
      (* .quad not working on all versions of the MacOSX assembler *)
      (* FZ changed endianess wrt Power *)
      let b = Int64.bits_of_float n in
      fprintf oc "	.long	%Ld, %Ld %s %.18g\n"
                 (Int64.logand b 0xFFFFFFFFL)
                 (Int64.shift_right_logical b 32)
                 comment n
  | Init_space n ->
      let n = camlint_of_z n in
      if n > 0l then fprintf oc "	.space	%ld\n" n
  | Init_pointer id ->
      let lbl = new_label() in
      fprintf oc "	.long	%a\n" label lbl;
      init_data_queue := (lbl, id) :: !init_data_queue

let print_init_data oc name id =
 init_data_queue := [];
 if Str.string_match PrintCsyntax.re_string_literal (extern_atom name) 0
 && List.for_all (function Init_int8 _ -> true | _ -> false) id
 then
   fprintf oc "        .ascii  \"%s\"\n" (PrintCsyntax.string_of_init id)
 else
   List.iter (print_init oc) id;
 let rec print_remainder () =
   match !init_data_queue with
   | [] -> ()
   | (lbl, id) :: rem ->
       init_data_queue := rem;
       fprintf oc "%a:\n" label lbl;
       List.iter (print_init oc) id;
       print_remainder()
 in print_remainder()

(* let print_init_data oc name id =
  if Str.string_match PrintCsyntax.re_string_literal (extern_atom name) 0
  && List.for_all (function Init_int8 _ -> true | _ -> false) id
  then
    fprintf oc "	.ascii	\"%s\"\n" (PrintCsyntax.string_of_init id) 
  else
    List.iter (print_init oc) id *)

let print_var oc (Coq_pair(Coq_pair(name, init_data), _)) =
  match init_data with
  | [] -> ()
  | _  ->
      section oc data;
      print_align oc 8;
      if not (Cil2Csyntax.atom_is_static name) then
        fprintf oc "	.globl	%a\n" symbol name;
      fprintf oc "%a:\n" symbol name;
      print_init_data oc name init_data;
      if target = ELF then begin
        fprintf oc "	.type	%a, @object\n" symbol name;
        fprintf oc "	.size	%a, . - %a\n" symbol name symbol name
      end

let print_imm oc = function
  |  Cint d -> fprintf oc "$%a" coqint d 
  |  Csymbol (symb,ofs) -> fprintf oc "**print_imm of Csymbol**" (* symbol oc symb *)

let print_rm_base oc = function
  | None -> ()
  | Some r -> fprintf oc "%s" (ireg32 r) 

let fact_of_index s = 
  match (s.hi, s.lo) with
  | (true,true)   -> 8
  | (true,false)  -> 4
  | (false,true)  -> 2
  | (false,false) -> 1
        
let print_index_of_s oc s = 
  match (s.hi, s.lo) with
  | (false,false) -> output_string oc ""
  | (_,_)   -> fprintf oc ", %d" (fact_of_index s)

let print_rm_index oc = function
  Coq_pair (s,r) -> fprintf oc "%s%a" (ireg32 r) print_index_of_s s 

let print_rm_comma oc = function
  | Some _, Some _ -> output_string oc ", "
  | _,_ -> ()

let print_xm oc = function
  | Xm(i,b,d) -> 
      begin match d with 
      | Cint n -> 
          let n = camlint_of_coqint n in
          fprintf oc "%ld" n
      | Csymbol(s,o) ->
          let o = camlint_of_coqint o in
          if o = 0l 
          then symbol oc s
          else fprintf oc "(%a + %ld)" symbol s o
      end;
      begin match i,b with
      | None, None -> ()
      | None, Some r -> fprintf oc "(%s)" (ireg32 r)
      | Some i, None -> fprintf oc "(,%a)" print_rm_index i
      | Some i, Some r -> fprintf oc "(%s,%a)" (ireg32 r) print_rm_index i
      end

let print_irm oc = function
  | Xr r   -> output_string oc (ireg32 r)
  | Xmm xm -> print_xm oc xm

let print_low_irm ex oc = function
  | Xlr r   -> output_string oc (low_ireg ex r)
  | Xlmm xm -> print_xm oc xm

let print_frm oc = function
  | Xfr r   -> output_string oc (freg64 r)
  | Xfmm xm -> print_xm oc xm

let print_irm32 oc = print_irm oc
let print_frm32 oc = print_frm oc

let print_int_dest_src32 oc = function
  | Xri(r,imm) -> fprintf oc "%a, %s" print_imm imm    (ireg32 r)
  | Xrr(r1,r2) -> fprintf oc "%s, %s" (ireg32 r2)      (ireg32 r1)
  | Xrm(r,m)   -> fprintf oc "%a, %s" print_xm m       (ireg32 r)     
  | Xmr(m,r)   -> fprintf oc "%s, %a" (ireg32 r)       print_xm m 

let print_float_dest_src oc = function
  | Xfrr(r1,r2) -> fprintf oc "%s, %s" (freg64 r2)     (freg64 r1)
  | Xfrm(r,m)   -> fprintf oc "%a, %s" print_xm m      (freg64 r)
  | Xfmr(m,r)   -> fprintf oc "%s, %a" (freg64 r)      print_xm m

let print_count oc = function
  | Xc_imm(imm)   -> print_imm oc imm
  | Xc_CL         -> output_string oc "%cl"

let print_int_binop_name = function
  | Xadd  -> "addl" 
  | Xsub  -> "subl" 
  | Xand  -> "andl" 
  | Xcmp  -> "cmpl" 
  | Xor   -> "orl" 
  | Xxor  -> "xorl" 
  | Ximul -> "imull" 
  | Xtest -> "test"

let print_float_binop_name = function
  | Xaddf -> "addsd"
  | Xsubf -> "subsd"
  | Xmulf -> "mulsd"
  | Xdivf -> "divsd"
  | Xcomisd -> "ucomisd"

let print_shiftop_name = function
  | Xshr  -> "shrl" 
  | Xsal  -> "sall"
  | Xsar  -> "sarl" 
  | Xrol  -> "roll" 
  | Xror  -> "rorl"

let print_monop_name = function
  | Xnot -> "notl" 
  | Xneg -> "negl"
  | Xdiv -> "divl" 
  | Xidiv -> "idivl" 

let print_cond = function
  | X_ALWAYS -> "mp"
  | X_E  -> "e "
  | X_NE -> "ne"
  | X_L  -> "l "
  | X_B  -> "b "
  | X_LE -> "le"
  | X_BE -> "be"
  | X_G  -> "g "
  | X_A  -> "a "
  | X_GE -> "ge"
  | X_AE -> "ae"
  | X_NS -> "ns"
  | X_ENP | X_NEP -> assert false (* treated specially *)

let print_instruction expand_pseudo oc labels = function
  | Xbinop(binop_name,ds) ->  
      fprintf oc "      %s   %a\n"       
        (print_int_binop_name binop_name) print_int_dest_src32 ds
  | Xbinopf(binop_name,ds) ->  
      fprintf oc "      %s   %a\n"       
        (print_float_binop_name binop_name) print_float_dest_src ds
  | Xshift(shiftop_name,rm,c) ->
      fprintf oc "      %s   %a, %a\n"       
        (print_shiftop_name shiftop_name) print_count c print_irm32 rm 
  | Xmonop(monop_name,rm) ->  
      fprintf oc "      %s    %a\n"      
        (print_monop_name monop_name) print_irm32 rm
  | Xxor_self(r) ->  
      fprintf oc "      xorl    %s, %s\n" (ireg32 r) (ireg32 r)
  | Xcltd ->
      fprintf oc "      cltd\n"
  (* | Xcwtl -> *)
  (*     fprintf oc "      cwtl\n" *)
  | Xmov(ds) -> 
      fprintf oc "      movl   %a\n"  print_int_dest_src32 ds 
  | Xmovt(ex,m,r) -> 
      fprintf oc "      mov%s   %s, %a\n" 
         (print_size ex) (low_ireg ex r) print_xm m 
  | Xmovx(ex,r,irm) ->      
      fprintf oc "      mov%s   %a, %s\n"
        (print_extend ex) (print_low_irm ex) irm (ireg32 r)
  | Xmovsd(ds) -> 
      fprintf oc "      movsd   %a\n" print_float_dest_src ds 
  | Xmovftr(r1,r2) -> 
      fprintf oc "      cvtsd2ss   %s, %s\n" (freg64 r2) (freg64 r1);
      fprintf oc "      cvtss2sd   %s, %s\n" (freg64 r1) (freg64 r1)
  | Xmovftm(m,r) -> 
      fprintf oc "      cvtsd2ss   %s, %%xmm7\n" (freg64 r);
      fprintf oc "      movss      %%xmm7, %a\n" print_xm m
  | Xmovfi(ir,fr) -> 
      fprintf oc "      movd   %s, %s\n" (freg64 fr) (ireg32 ir)
  | Xmovif(fr,ir) -> 
      fprintf oc "      movd   %s, %s\n" (ireg32 ir) (freg64 fr)
  | Xmovrst(fr) -> 
      fprintf oc "      movsd  %s, -8(%%esp)\n" (freg64 fr);
      fprintf oc "      fldl   -8(%%esp)\n"
  (* Xmovsd (Xfmr (Xm None (Some ESP) (Cint (Int.repr (-8)))) fr) :: *)
  (* Xfldl (Xm None (Some ESP) (Cint (Int.repr (-8)))) :: k. *)
  | Xmovstr(fr) -> 
      fprintf oc "      fstpl  -8(%%esp)\n";
      fprintf oc "      movsd  -8(%%esp), %s\n" (freg64 fr)
  | Xset(c, rd) ->
      begin match c with
      | X_NEP ->
          fprintf oc "	setne	%%cl\n";
          fprintf oc "	setp	%%dl\n";
          fprintf oc "	orb	%%dl, %%cl\n"
      | X_ENP ->
          fprintf oc "	sete	%%cl\n";
          fprintf oc "	setnp	%%dl\n";
          fprintf oc "	andb	%%dl, %%cl\n"
      | _ ->
          fprintf oc "	set%s	%%cl\n" (print_cond c)
      end;
      fprintf oc "      movzbl  %%cl, %s\n" (ireg32 rd)
  | Xcmov(cond,r,irm) ->  (* should go? *)
      fprintf oc "      cmov%s   %s, %a\n"   
        (print_cond cond) (ireg32 r)  print_irm32 irm
  (* | Xpush(imm_rm) -> *)
  (*     fprintf oc "      push%s  %a\n" *)
  (*       "l" print_imm_rm32 imm_rm  *)
  (* | Xpop(rm) -> *)
  (*     fprintf oc "      pop%s   %a\n" *)
  (*       "l" print_rm32 rm  *)
  | Xlea(r,m) ->
      fprintf oc "      leal   %a, %s\n" print_xm m   (ireg32 r)
  (* | Xxchg(rm,r) -> *)
  (*     fprintf oc "      %s%s    %a, %a\n"  "xchg" *)
  (*       "l" ireg32 r           print_rm32 rm  *)
  | Xmfence ->
      fprintf oc "      mfence\n" 
  | Xcmpxchg(m,r) ->
      fprintf oc "      lock cmpxchgl    %s, %a\n" (ireg32 r) print_xm m
  | Xxadd(m,r) ->
      fprintf oc "      lock xaddl  %s, %a\n" (ireg32 r) print_xm m
  (* | Xlkinc(m) -> *)
  (*     fprintf oc "      lock incl %a\n"  print_xm m *)
  (* | Xleave ->  *)
  (*     fprintf oc "      leave\n"  *)
  | Xret(imm) ->
     if imm= Cint BinInt.Z0 then 
       fprintf oc "      ret\n"                                       
     else
       fprintf oc "      ret    %a\n"
         print_imm imm
  | Xjump(c,lbl) ->
      let l = transl_label lbl in
      begin match c with
      | X_NEP ->
          fprintf oc "	jp	%a\n" label l;
          fprintf oc "	jne	%a\n" label l
      | X_ENP ->
          let l' = new_label() in
          fprintf oc "	jp	%a\n" label l';
          fprintf oc "	je	%a\n" label l;
          fprintf oc "%a:\n" label l'
      | _ ->
          fprintf oc "	j%s	%a\n" (print_cond c) label l
      end
  | Xcall(l) ->
      if not (is_builtin_function l) then
        fprintf oc "      call   %a\n" symbol l
      else
        print_builtin_function oc l
  | Xcallreg(r) ->
        fprintf oc "      call   *%s\n" (ireg32 r)
  (* | Xallocframe (lo, hi, ofs) ->  *)
  (*     let lo = camlint_of_coqint lo *)
  (*     and hi = camlint_of_coqint hi *)
  (*     and ofs = camlint_of_coqint ofs in *)
  (*     let sz = Int32.sub hi lo in *)
  (*     (\* Keep stack 16-aligned *\) *)
  (*     let sz16 = (Int32.sub (Int32.logand (Int32.add sz 15l) 0xFFFF_FFF0l) (Int32.of_int 8)) in *)
  (*     if expand_pseudo then   *)
  (*       fprintf oc "      subl   $%ld, %s\n" sz16 "%esp"  *)
  (*     else *)
  (*       fprintf oc "      [allocframe]    (%ld,%ld,%ld)\n" lo hi ofs *)
  (* floating point *)
  | Xfloatconst (r, f) ->
      let b = Int64.bits_of_float f in
      if b = 0L then (* +0.0 *)
        fprintf oc "	xorpd	%s, %s %s +0.0\n" (freg64 r) (freg64 r) comment
      else begin
        let lbl = new_label() in
        fprintf oc "	movsd	%a, %s %s %.18g\n" label lbl (freg64 r) comment f;
        float_literals := (lbl, b) :: !float_literals
      end
  | Xcvtsi2sd (fr,ir) ->
      fprintf oc "      cvtsi2sd    %s, %s\n" (ireg32 ir) (freg64 fr)
  | Xcvttsd2si (ir,fr) ->
      fprintf oc "      cvttsd2si    %s, %s\n" (freg64 fr) (ireg32 ir)
  | Xcvtss2sd (fr,frm) ->
      fprintf oc "      cvtss2sd     %a, %s\n" print_xm frm   (freg64 fr)
  | Xiuctf (fr,ir) -> (* floatofuint *)
      let lbl = new_label() in
      fprintf oc "      subl    $2147483648, %s\n" (ireg32 ir);
      fprintf oc "      cvtsi2sd     %s, %s\n" (ireg32 ir) (freg64 fr);
      fprintf oc "      addsd        %a, %s\n" label lbl (freg64 fr);
      fprintf oc "      .data\n";
      print_align oc 16;
      fprintf oc "%a:" label lbl;
      fprintf oc "      .long   0, 1105199104, 0 ,0\n";
      fprintf oc "      .text\n"
  | Xfctiu (ir,fr) -> (* uintoffloat *)
      let lbl0 = new_label() in
      let lbl1 = new_label() in
      (* save xmm0-1*)
      fprintf oc "      movsd  %%xmm1, -8(%%esp)\n";
      fprintf oc "      movsd  %%xmm0, -16(%%esp)\n";
      (* move fr to xmm0 *)
      ( match fr with | XMM0 -> () 
      | _ -> fprintf oc "      movsd   %s, %%xmm0\n" (freg64 fr) );
      (* this code, copied from what gcc generates, destroys xmm0,
         xmm1, xmm6, xmm7, and supposes the fr is xmm0 *)
      fprintf oc "       movapd  %a, %%xmm1\n" label lbl0;
      fprintf oc "       movapd  %%xmm1, %%xmm6\n";
      fprintf oc "       cmplesd %%xmm0, %%xmm1\n";
      fprintf oc "       minsd   %a, %%xmm0\n" label lbl1;
      fprintf oc "       xorpd   %%xmm7, %%xmm7\n";
      fprintf oc "       maxsd   %%xmm7, %%xmm0\n";
      fprintf oc "       andpd   %%xmm6, %%xmm1\n";
      fprintf oc "       subpd   %%xmm1, %%xmm0\n";
      fprintf oc "       cvttpd2dq %%xmm0, %%xmm0\n";
      fprintf oc "       psllq   $31, %%xmm6\n";
      fprintf oc "       pxor    %%xmm6, %%xmm0\n";
      fprintf oc "       movd    %%xmm0, %s\n" (ireg32 ir);
      (* restore xmm0-1 *)
      fprintf oc "      movsd  -16(%%esp), %%xmm0\n";
      fprintf oc "      movsd  -8(%%esp), %%xmm1\n";
      (* constants *)
      fprintf oc "       .data\n";
      print_align oc 16;
      fprintf oc "%a:" label lbl0;
      fprintf oc "      .long   0, 1105199104, 0, 0\n";
      print_align oc 16;
      fprintf oc "%a:" label lbl1;
      fprintf oc "      .long   4292870144, 1106247679, 0, 0\n";
      fprintf oc "      .text\n"
  | Xnegf (r) ->
      need_masks := true;
      fprintf oc "	xorpd	%a, %s\n" raw_symbol "__negd_mask" (freg64 r)
      (* let lbl = new_label() in *)
      (* fprintf oc "      .data\n"; *)
      (* print_align oc 16; *)
      (* fprintf oc "%a:" label lbl; *)
      (* fprintf oc "	.long 0x80000000, 0, 0, 0\n";  *)
      (* fprintf oc "      .text\n"; *)
      (* fprintf oc "      xorpd %a, %a\n" label lbl freg r *)
(*  | Xabsf (r) ->  *)
(*      need_masks := true; *)
(*      fprintf oc "	andpd	%a, %s\n" raw_symbol "__absd_mask" (freg64 r) *)
      (* let lbl = new_label() in *)
      (* fprintf oc "      .data\n"; *)
      (* print_align oc 16; *)
      (* fprintf oc "%a:" label lbl; *)
      (* fprintf oc "	.long  0x7FFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF\n";  *)
      (* fprintf oc "      .text\n"; *)
      (* fprintf oc "      andpd  %a, %a\n" label lbl freg r *)
  | Xfstpl (m) ->
      fprintf oc "      fstpl  %a\n" print_xm m
  | Xfldl (m) ->
      fprintf oc "      fldl   %a\n" print_xm m
  | Xlabel lbl ->
      if Labelset.mem lbl labels || not expand_pseudo then
        fprintf oc "%a:\n" label (transl_label lbl)
  | Xthreadcreate ->
      fprintf oc "      call _compcert_thread_create\n"
        

  (* | Xbtbl (r, tbl) ->  *)
  (*     let lbl = new_label() in *)
  (*     fprintf oc "	jmp *%a(,%a,4)\n" label lbl ireg32 r; *)
  (*     fprintf oc "      .data\n"; *)
  (*     fprintf oc "%a:" label lbl; *)
  (*     List.iter *)
  (*       (fun l -> fprintf oc "	.long	%a\n" label (transl_label l)) *)
  (*       tbl; *)
  (*     fprintf oc "      .text\n" *)
  (* | Xcomment(s) ->  *)
  (*     fprintf oc "# %s\n" (Camlcoq.camlstring_of_coqstring s) *)

(* used inside the interpreter to print the just-executed instruction
- hence the expand_pseudo, false here, so that one can see Xallocframe
and such like in the way that the opsem will see them, not in the way
that the assembler will (the code=[] is just a temporary hack). *)
let print_instruction_plain oc i = 
  print_instruction false oc (labels_of_code Labelset.empty [] (*code*)) i

(* all together *)

let print_literal oc (lbl, n) =
  fprintf oc "%a:	.quad	0x%Lx\n" label lbl n

let print_function oc name code =
  Hashtbl.clear current_function_labels;
  float_literals := [];
  section oc text;
  print_align oc 16;
  if not (Cil2Csyntax.atom_is_static name) then
    fprintf oc "	.globl %a\n" symbol name;
  fprintf oc "%a:\n" symbol name;
  List.iter (print_instruction true oc (labels_of_code Labelset.empty code)) code;
  if target = ELF then begin
    fprintf oc "	.type	%a, @function\n" symbol name;
    fprintf oc "	.size	%a, . - %a\n" symbol name symbol name
  end;
  if !float_literals <> [] then begin
    section oc float_literal;
    print_align oc 8;
    List.iter (print_literal oc) !float_literals;
    float_literals := []
  end

(* Generation of stub functions *)

(* let re_variadic_stub = Str.regexp "\\(.*\\\)\\$[if]*$" *)

(* (\* Stubs for MacOS X *\) *)

(* module Stubs_MacOS = struct *)

(* (\* Generation of stub code for variadic functions, e.g. printf. *\) *)

(* let variadic_stub oc name = *)
(*   fprintf oc "      .indirect_symbol _%s\n" (remove_variadic_prefix name); *)
(*   fprintf oc "      hlt ; hlt ; hlt ; hlt ; hlt\n" *)
  
(* (\* Stubs for fixed-type functions *\) *)

(* let non_variadic_stub oc name =  *)
(*   fprintf oc "      .indirect_symbol _%s\n" name; *)
(*   fprintf oc "      hlt ; hlt ; hlt ; hlt ; hlt\n" *)

(* let stub_function oc name ef = *)
(*   let name = extern_atom name in *)
(*   if Str.string_match re_variadic_stub name 0 *)
(*   then begin *)
(*     fprintf oc "L%s$stub:\n" (remove_variadic_prefix name); *)
(*     variadic_stub oc name; *)
(*   end else begin *)
(*     fprintf oc "L%s$stub:\n" name; *)
(*     non_variadic_stub oc name; *)
(*   end *)

(* let function_needs_stub name = true *)

(* end *)

(* (\* Stubs for EABI - experimental *\) *)

(* module Stubs_EABI = struct *)

(* let variadic_stub oc stub_name fun_name args = *)
(*   fprintf oc "	.text\n"; *)
(*   print_align oc 2; *)
(*   fprintf oc ".L%s$stub:\n" stub_name; *)
(*   fprintf oc "	jmp	%s\n" fun_name *)

(* let stub_function oc name ef = *)
(*   let name = extern_atom name in *)
(*   (\* Only variadic functions need a stub *\) *)
(*   if Str.string_match re_variadic_stub name 0 *)
(*   then variadic_stub oc name (Str.matched_group 1 name) ef.ef_sig.sig_args *)

(* let function_needs_stub name = *)
(*   Str.string_match re_variadic_stub (extern_atom name) 0 *)

(* end *)

(* let function_needs_stub = *)
(*   match target with *)
(*   | MacOS      -> Stubs_MacOS.function_needs_stub *)
(*   | Linux|Diab -> Stubs_EABI.function_needs_stub *)

(* let stub_function = *)
(*   match target with *)
(*   | MacOS       -> Stubs_MacOS.stub_function *)
(*   | Linux|Diab  -> Stubs_EABI.stub_function *)

let print_fundef oc (Coq_pair(name, defn)) =
  match defn with
  | Internal (Coq_pair (_,code)) -> print_function oc name code
  | External ef -> () (* if not(is_builtin_function name) then stub_function oc name ef  *)

(* let stubbed (Coq_pair(name, defn)) =  *)
(*   match defn with *)
(*   | Internal _ -> false *)
(*   | External _ ->  *)
(*       if function_needs_stub name && not (is_builtin_function name) then begin *)
(* 	stubbed_functions := IdentSet.add name !stubbed_functions; true  *)
(*       end else false *)

(* let filter_stubbed_functs l = *)
(*   List.partition stubbed l  *)


(* we get duplicated stubs for each distinct variadic suffix $iiff;
   here we remove the duplicates.  This code should be rewritten. *)
(* let rec remove_duplicated_stubs stubs = *)
(*   match stubs with *)
(*   | [] -> [] *)
(*   | (Coq_pair(n1,_)) as s :: t ->  *)
(*       if List.exists *)
(* 	  (fun (Coq_pair(n2,_)) -> *)
(* 	    if String.compare  *)
(* 		(remove_variadic_prefix (extern_atom n1))  *)
(* 		(remove_variadic_prefix (extern_atom n2)) = 0  *)
(* 	    then true else false) *)
(* 	  t *)
(*       then remove_duplicated_stubs t *)
(*       else s :: remove_duplicated_stubs t *)

(* let print_stubs oc stubs = *)
(*   if not(stubs=[]) then begin *)
(*     (match target with  *)
(*        | MacOS -> fprintf oc "      .section __IMPORT,__jump_table,symbol_stubs,self_modifying_code+pure_instructions,5\n" *)
(*        | _ -> ()); *)
(*     List.iter (print_fundef oc) (remove_duplicated_stubs stubs);  *)
(*   end; *)
(*   match target with *)
(*   | MacOS -> fprintf oc "      .subsections_via_symbols\n" *)
(*   | _ -> ()    *)

let print_program oc p =
  need_masks := false;
  List.iter (print_var oc) p.prog_vars;
  List.iter (print_fundef oc) p.prog_funct;
  if !need_masks then begin
    section oc float_literal;
    print_align oc 16;
    fprintf oc "%a:	.quad   0x8000000000000000, 0\n" raw_symbol "__negd_mask";
(*    fprintf oc "%a:	.quad   0x7FFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF\n" raw_symbol "__absd_mask" *)
  end

(* let print_program oc p = *)
(*   (\* pre-process *\) *)
(*   stubbed_functions := IdentSet.empty; *)
(*   let stubs,functs = filter_stubbed_functs p.prog_funct in *)
(*   (\* print *\) *)
(*   List.iter (print_var oc) p.prog_vars; *)
(*   List.iter (print_fundef oc) functs; *)
(*   print_stubs oc stubs *)
