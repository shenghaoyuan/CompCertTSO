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

open Pointers
open Camlcoq
open List0
open Datatypes
open Globalenvs
open Csyntax
open Ast
open Csem
open Events
open Printf
open Values
open Printf
open Format
open Clflags 


let expr_of_lhs (Coq_pair(id,ty)) = Expr (Evar id, ty)

(* Location of the standard library *)

let stdlib_path = ref(
  try
    Sys.getenv "COMPCERT_LIBRARY"
  with Not_found ->
    Configuration.stdlib_path)

let command cmd =
  if !option_v then begin
    prerr_string "+ "; prerr_string cmd; prerr_endline ""
  end;
  Sys.command cmd

let quote_options opts =
  String.concat " " (List.rev_map Filename.quote opts)

let safe_remove file =
  try Sys.remove file with Sys_error _ -> ()

(* Printing of error messages *)

let print_error oc msg =
  let print_one_error = function
  | Errors.MSG s -> output_string oc (Camlcoq.camlstring_of_coqstring s)
  | Errors.CTX i -> output_string oc (Camlcoq.extern_atom i)
  in
    List.iter print_one_error msg;
    output_char oc '\n'

(* For the CIL -> Csyntax translator:

  * The meaning of some type specifiers may depend on compiler options:
      the size of an int or the default signedness of char, for instance.

  * Those type conversions may be parameterized thanks to a functor.

  * Remark: [None] means that the type specifier is not supported
      (that is, an Unsupported exception will be raised if that type
      specifier is encountered in the program).
*)

module TypeSpecifierTranslator = struct
  
  open Cil
  open Csyntax
    
  (** Convert a Cil.ikind into an (intsize * signedness) option *)
  let convertIkind = function
    | IChar      -> Some (I8, Unsigned)
    | ISChar     -> Some (I8, Signed)
    | IUChar     -> Some (I8, Unsigned)
    | IInt       -> Some (I32, Signed)
    | IUInt      -> Some (I32, Unsigned)
    | IShort     -> Some (I16, Signed)
    | IUShort    -> Some (I16, Unsigned)
    | ILong      -> Some (I32, Signed)
    | IULong     -> Some (I32, Unsigned)
    | ILongLong  -> if !option_flonglong then Some (I32, Signed) else None
    | IULongLong -> if !option_flonglong then Some (I32, Unsigned) else None
	
  (** Convert a Cil.fkind into an floatsize option *)
  let convertFkind = function
    | FFloat      -> Some F32
    | FDouble     -> Some F64
    | FLongDouble -> if !option_flonglong then Some F64 else None
	
end
 
module Cil2CsyntaxTranslator = Cil2Csyntax.Make(TypeSpecifierTranslator)

(* From C to preprocessed C *)

let preprocess ifile ofile =
  let cmd =
    sprintf "%s -D__COMPCERT__ -I%s %s %s > %s"
      Configuration.prepro
      !stdlib_path
      (quote_options !prepro_options)
      ifile ofile in
  if command cmd <> 0 then begin
    safe_remove ofile;
    eprintf "Error during preprocessing.@.";
    exit 2
  end

(* From preprocessed C to asm *)
let get_c_syntax sourcename ifile =
  (* Parsing and production of a CIL.file *)
  let cil =
    try
      Frontc.parse ifile ()
    with
    | Frontc.ParseError msg ->
        eprintf "Error during parsing: %s@." msg;
        exit 2
    | Errormsg.Error ->
        exit 2 in
  (* Remove preprocessed file (always a temp file) *)
  safe_remove ifile;
  (* Restore original source file name *)
  cil.Cil.fileName <- sourcename;
  (* Cleanup in the CIL.file *)
  Rmtmps.removeUnusedTemps ~isRoot:Rmtmps.isExportedRoot cil;
  (* Conversion to Csyntax *)
  let csyntax =
    try
      Cil2CsyntaxTranslator.convertFile cil
    with
    | Cil2CsyntaxTranslator.Unsupported msg ->
        eprintf "%s@." msg;
        exit 2
    | Cil2CsyntaxTranslator.Internal_error msg ->
        eprintf "%s@.Please report it.@." msg;
        exit 2 in
  (* Save Csyntax if requested *)
  if !option_dclight then begin
    let targetname = Filename.chop_suffix sourcename ".c" in
    let oc = open_out (targetname ^ ".light.c") in
    PrintCsyntax.print_program (Format.formatter_of_out_channel oc) csyntax;
    close_out oc
  end; csyntax

(* Processing of events *)
let z0 = BinInt.Z0
let ptr_of_int i = Ptr((z_of_camlint i), z0)

		     
type 'a parse_res =
  | NoParse of int
  | ParseRes of 'a * int;;

(* Parsing *)
let parse_events =
  let int_re = Str.regexp "\\([0-9]+\\)" in
  let ws_re = Str.regexp "\\([ \t\n]*\\)" in
  let alnum_re = Str.regexp "\\([a-zA-Z_][a-zA-Z_0-9$]+\\)" in
  let parse_event s =
    let get_re r i = 
      if Str.string_match r s i 
      then ParseRes(Str.matched_group 1 s, Str.group_end 1)
      else NoParse i in
    let str r i = 
      if String.length r + i <= String.length s &&
         String.sub s i (String.length r) = r 
      then ParseRes(r, String.length r + i)
      else NoParse i in
    let (>>) p f i = match p i with
	ParseRes(r, ni) -> ParseRes(f r, ni)
      | NoParse i -> NoParse i in
    let (++) p1 p2 i = match p1 i with
	ParseRes(r1, ni1) -> 
	  (match p2 ni1 with
	       ParseRes(r2, ni2) -> ParseRes((r1, r2), ni2)
	     | NoParse ni2 -> NoParse ni2)
      | NoParse ni1 -> NoParse ni1 in
    let (++>) p1 p2 = (p1 ++ p2) >> Pervasives.snd in 
    let (<++) p1 p2 = (p1 ++ p2) >> Pervasives.fst in 
    let (||) p1 p2 i = match p1 i with 
	ParseRes(r1, ni1) -> ParseRes(r1, ni1)
      | NoParse _ -> p2 i in
    let parse_eof i = 
      if i >= String.length s then ParseRes((), i)
      else NoParse i in
    let id r i = ParseRes(r, i) in
    let tryp p d = p || (id d) in
    let rec repeat p i = tryp (p ++ repeat p >> (fun (h, t) -> h :: t)) [] i in 
    let (>>>) p1 x = p1 >> (fun _ -> x) in
    let parse_int = (get_re int_re) >> Int32.of_string >> coqint_of_camlint in
    let parse_ptr = (str "p" ++> parse_int) >> (fun p -> Ptr(p, z0)) in
    let parse_vundef = str "U" >>> Vundef in
    let parse_vint = (str "I" ++> parse_int) >> (fun i -> Vint i) in
    let parse_vptr = (str "P" ++> parse_ptr) >> (fun p -> Vptr p) in
    let parse_val = parse_vundef || parse_vint || parse_vptr in
    let parse_extval = (str "I" ++> parse_int) >> (fun i -> EVint i) in
    let ident_parser = get_re alnum_re >> intern_string in
    let ws = get_re ws_re in
    let ws_p p = ws ++> (p <++ ws) in
    let parse_cparen d p = (str d ++ ws ++ str "(") ++> (p <++ str ")") in 
    let parse_call = parse_cparen "C"
      (ws_p ident_parser ++ (repeat (str "," ++> ws_p parse_extval))) >>
      (fun (id, vl) -> Ecall(id, vl)) in 
    let parse_return = parse_cparen "R" (ws_p parse_extval) >>
      (fun v -> Ereturn (Tint, v)) in
    let parse_exit = parse_cparen "X" (ws_p parse_int) >>
      (fun i -> Eexit i) in
    let parse_fail = str "Efail" >>> Efail in
    let parse_exte = parse_call || parse_return || parse_exit ||
                     parse_fail in
    let i8s_parser = str "I8S" >>> Mint8signed in
    let i8u_parser = str "I8U" >>> Mint8unsigned in
    let i16s_parser = str "I16S" >>> Mint16signed in
    let i16u_parser = str "I16U" >>> Mint16unsigned in
    let i32_parser = str "I32" >>> Mint32 in
    let f32_parser = str "F32" >>> Mfloat32 in
    let f64_parser = str "F64" >>> Mfloat64 in
    let parse_chunk = i8s_parser || i8u_parser || i16s_parser || 
      i16u_parser || i32_parser || f32_parser || f64_parser in
(*    let parse_lock = str "Lk" >>> MElock in *)
(*    let parse_unlock = str "Ul" >>> MEunlock in *)
    let parse_write = parse_cparen "Wr" 
      ((ws_p parse_ptr <++ str ",") ++ (ws_p parse_chunk <++ str ",") ++
	 ws_p parse_val) >> (fun ((p, c), v) -> MEwrite(p, c, v)) in
    let parse_read = parse_cparen "Rd" 
      ((ws_p parse_ptr <++ str ",") ++ (ws_p parse_chunk <++ str ",") ++
	 ws_p parse_val) >> (fun ((p, c), v) -> MEwrite(p, c, v)) in
    let parse_kind = (str "Stack" >>> MObjStack) ||
                     (str "Heap" >>> MObjHeap) ||
                     (str "Global" >>> MObjGlobal) in
    let parse_alloc = parse_cparen "Al" 
      ((ws_p parse_ptr <++ str ",") ++ (ws_p parse_int <++ str "'") ++ 
       ws_p parse_kind) >> (fun ((p, s), k) -> MEalloc(p, s, k)) in 
    let parse_free = parse_cparen "Fr" 
      ((ws_p parse_ptr <++ str ",") ++ ws_p parse_kind) 
      >> (fun(p, k) -> MEfree(p, k)) in 
    let parse_mevent = (* parse_lock || parse_unlock ||*) parse_write || 
                       parse_read || parse_alloc  || parse_free in
    let parse_ext = parse_cparen "EXT" (ws_p parse_exte) >> (fun e -> TEext e) in
    let parse_mem = parse_cparen "MEM" (ws_p parse_mevent) >> (fun e -> TEmem e) in
    let parse_tau = str "TAU" >>> TEtau in
    let parse_exit = str "EXIT" >>> TEexit in
    let parse_start = parse_cparen "START"
      (ws_p parse_ptr ++ 
	 (repeat (str "," ++> ws_p parse_val))) >>
      (fun (p, vl) -> TEstart(p, vl)) in 
    let parse_tevent = parse_ext || parse_mem || parse_tau || parse_exit ||
                       parse_start in
    let parse_tevents = repeat (ws ++> parse_tevent) <++ (ws ++ parse_eof) in 
      parse_tevents in
    parse_event;;

let parse_event_file fname =
  let f = open_in fname in
  let rec rd i acc =
    try
      let l = input_line f in
	if String.length l = 0 or String.get l 0 <> '#'
	then match parse_events l 0 with
	  | NoParse j -> failwith (sprintf "%s:%i:%i Parsing failed."
                                            fname i j)
	  | ParseRes(evs, i) -> rd (i + 1) (acc @ evs)
	else rd (i + 1) acc 
    with End_of_file -> acc in
    rd 0 [];;

(* Tests 
parse_events "EXT(C(main, I1, Pp123)) EXT(C(run))" 0;;
parse_event "EXT(C(run))" 0;;
parse_event "EXT(R(I5))" 0;;
parse_event "EXT(Efail)" 0;;
parse_event "EXT(X(0))" 0;;
parse_event "MEM(Lk)" 0;;
parse_event "MEM(Ul)" 0;;
parse_event "MEM(Rd(p23, I32, I1))" 0;;
parse_event "MEM(Wr(p45, I32, I3))" 0;;
parse_event "MEM(Al(p34, 4, Stack))" 0;;
parse_event "MEM(Fr(p34, Stack))" 0;;
parse_event "TAU" 0;;
parse_event "EXIT" 0;;
parse_event "START(2, p1, I1, I2)" 0;;
parse_event "START(notid, p4)" 0;; *)


(* Pointer *)
let string_of_ptr (Ptr(b, o)) =
  sprintf "p%ld" (camlint_of_coqint b);;

(* Values *)
let string_of_val v = match v with
  | Vundef -> "U"
  | Vint x -> sprintf "I%ld" (camlint_of_coqint x)
  | Vfloat x -> sprintf "F%F" x
  | Vptr x -> "P" ^ (string_of_ptr x);;

(* Value list *)
let string_of_vlist vl =
  let cf s v = s ^ ", " ^ (string_of_val v) in
    List.fold_left cf "" vl;;

(* External event *)
let string_of_event e = match e with
  | Ecall(id, args) -> sprintf "C(%s%s)" 
                               (extern_atom id)
                               (string_of_vlist (map val_of_eval args))
  | Ereturn(typ,rv) -> sprintf "R(%s)" (string_of_val (val_of_eval rv))
  | Eexit ev -> sprintf "X(%ld)" (camlint_of_coqint ev)
  | Efail -> "Efail"

(* Memory chunk *)
let string_of_chunk c = match c with
  | Mint8signed -> "I8S"
  | Mint8unsigned -> "I8U"
  | Mint16signed -> "I16S"
  | Mint16unsigned -> "I16U"
  | Mint32 -> "I32" 
  | Mfloat32 -> "F32"
  | Mfloat64 -> "F64";;

let string_of_kind k = match k with
  | MObjStack -> "Stack"
  | MObjGlobal -> "Global"
  | MObjHeap -> "Heap";;

let string_of_rmw_instr i = match i with
| rmw_ADD -> "ADD";;

(* Memory event *)
let string_of_mem_event e = match e with
  | MEfence -> "Mf"
  | MErmw(p, c, v, f) -> sprintf "Rmw(%s, %s, %s, %s)"
                                (string_of_ptr p)
                                (string_of_chunk c)
                                (string_of_val v)
                                (string_of_rmw_instr f)
  | MEwrite(p, c, v) -> sprintf "Wr(%s, %s, %s)"
                                (string_of_ptr p)
                                (string_of_chunk c)
                                (string_of_val v)
  | MEread(p, c, v) -> sprintf "Rd(%s, %s, %s)"
                                (string_of_ptr p)
                                (string_of_chunk c)
                                (string_of_val v)
  | MEalloc(p, s, k) -> sprintf "Al(%s, %ld, %s)"
                                (string_of_ptr p)
                                (camlint_of_coqint s)
                                (string_of_kind k)
  | MEfree(p, k) -> sprintf "Fr(%s, %s)"
                             (string_of_ptr p)
                             (string_of_kind k);;

(* Thread id *)
let string_of_tidopt tido = match tido with 
  | Some tid -> sprintf "%ld" (camlint_of_positive tid)
  | None -> "notid"

(* Thread event *)
let string_of_thread_event e = match e with
  | TEext ex -> sprintf "EXT(%s)" (string_of_event ex)
  | TEmem m -> sprintf "MEM(%s)" (string_of_mem_event m)
  | TEtau -> "TAU"
  | TEexit -> "EXIT"
  | TEstart(p, args) -> sprintf "START(%s%s)"
                                (string_of_ptr p)
                                (string_of_vlist args)
  | TEstartmem(p, args) -> "STARTMEM" (* not used by Clight *)
  | TEexternalcallmem(id, args) -> "EXTMEM" (* not used by Clight *)
  | TEoutofmem -> "OOM" (* not used by Clight *)


let string_of_tevlist evl =
  let cf s e = s ^ "\n" ^ (string_of_thread_event e) in
    List.fold_left cf "" evl;;

(* Printing state *)
let print_vlist isfirst p vl =
  match vl with 
      [] -> ()
    | h :: t ->
	let l = 
	  if isfirst then (fprintf p "%s" (string_of_val h); t)
	  else vl in
	  List.iter (fun v -> fprintf p ",@ %s" (string_of_val v)) l

let print_ptrlist isfirst p vl =
  match vl with 
      [] -> ()
    | h :: t ->
	let l = 
	  if isfirst then (fprintf p "%s" (string_of_ptr h); t)
	  else vl in
	  List.iter (fun v -> fprintf p ",@ %s" (string_of_ptr v)) l


let rec print_k i isfirst p k = 
  if i >= 0
  then begin
    if not isfirst then fprintf p ";@ ";
    match k with 
      | Clight.Kstop -> fprintf p "Kstop"
      | Clight.Kseq(stmt, k) -> 
	  fprintf p "Kseq"; 
	  print_k (i-1) false p k
      | Clight.Kwhile(expr, stmt, k) -> 
	  fprintf p "Kwhile";
	  print_k (i-1) false p k
      | Clight.Kdowhile(expr, stmt, k) -> 
 	  fprintf p "Kdowhile"; 
 	  print_k (i-1) false p k  
(*       | Clight.Kfor(expr, stmt1, stmt2, k) ->  *)
(* 	  fprintf p "Kfor"; *)
(* 	  print_k (i-1) false p k *)
      | Clight.KforIncr(expr, stmt1, stmt2, k) -> 
	  fprintf p "KforIncr";
	  print_k (i-1) false p k
      | Clight.KforCond(expr, stmt1, stmt2, k) -> 
	  fprintf p "KforlCond";
	  print_k (i-1) false p k
      | Clight.Kcall(po_ty_opt, fndef, env, k) -> 
	  fprintf p "Kcall";
	  print_k (i-1) false p k
      | Clight.Kfree(pl, valopt, k) ->  
	  fprintf p "Kfree(%a)"
	    (print_ptrlist true) pl;
	  print_k (i-1) false p k
      | Clight.Kswitch(_) ->
      fprintf p "Kswitch";
	  print_k (i-1) false p k
  end else fprintf p ";..."

let rec print_ek i isfirst p ek = 
  if i >= 0
  then begin
    if not isfirst then fprintf p ";@ ";
    match ek with
      | Clight.EKunop(uop, ty, ek) -> 
	  fprintf p "EKunop";
	  print_ek (i-1) false p ek
      | Clight.EKbinop1(binop,ty1,ty2,ty, expr, ek) -> 
	  fprintf p "EKbinop1";
	  print_ek (i-1) false p ek
      | Clight.EKbinop2(binop,ty1,ty2,ty, v, ek) -> 
	  fprintf p "EKbinop2";
	  print_ek (i-1) false p ek
      | Clight.EKcast(ty1, ty2, ek) -> 
	  fprintf p "EKcast";
	  print_ek (i-1) false p ek 
      | Clight.EKcondition(e1, e2, ty, ek) ->
	  fprintf p "EKcondition";
	  print_ek (i-1) false p ek
(*       | Clight.EKandbool(ty, e, ek) ->  *)
(* 	  fprintf p "EKandbool"; *)
(* 	  print_ek (i-1) false p ek *)
(*       | Clight.EKorbool(ty, e, ek) ->  *)
(* 	  fprintf p "EKorbool"; *)
(* 	  print_ek (i-1) false p ek  *)
(*       | Clight.EKboolofval(ty, ek) ->  *)
(* 	  fprintf p "EKboolofval"; *)
(* 	  print_ek (i-1) false p ek *)
      | Clight.EKfield(fldid, ek) -> 
	  fprintf p "EKfield";
	  print_ek (i-1) false p ek
      | Clight.EKlval(ty, ek) -> 
	  fprintf p "EKlval";
	  print_ek (i-1) false p ek
(*      | Clight.EKload(ek) -> 
	  fprintf p "EKload";
	  print_ek (i-1) false p ek *)
      | Clight.EKassign1(expr, ty, k) -> 
	  fprintf p "EKassign1";
	  print_k (i-1) false p k
      | Clight.EKassign2(v, ty, k) -> 
	  fprintf p "EKassign2";
	  print_k (i-1) false p k
      | Clight.EKcall(po_ty_opt, ty, el, k) -> 
	  fprintf p "EKcall";
	  print_k (i-1) false p k
(*      | Clight.EKsome(expr, ty1, el, k) ->  *)
(*	  fprintf p "EKsome";
	  print_k (i-1) false p k
 *)     | Clight.EKargs(po_ty_opt, v, ty, vl, el, k) -> 
	  fprintf p "EKargs";
	  print_k (i-1) false p k
      | Clight.EKatargs(op, ty, vl, el, k) -> 
	  fprintf p "EKatargs";
	  print_k (i-1) false p k
      | Clight.EKcond(ty, stmt1, stmt2, k) -> 
	  fprintf p "EKcond";
	  print_k (i-1) false p k
      | Clight.EKreturn(k) -> 
	  fprintf p "EKreturn";
	  print_k (i-1) false p k
      | Clight.EKswitch(labeled_statements, k) -> 
	  fprintf p "EKswitch";
	  print_k (i-1) false p k
      | Clight.EKthread1(efn, k) -> 
	  fprintf p "EKthread";
	  print_k (i-1) false p k
      | Clight.EKthread2(eargs, k) -> 
	  fprintf p "EKthread";
	  print_k (i-1) false p k
      | Clight.EKwhile(expr, statement, k) ->  
 	  fprintf p "EKwhile"; 
 	  print_k (i-1) false p k 
      | Clight.EKdowhile(expr, statement, k) ->  
 	  fprintf p "EKdowhile"; 
 	  print_k (i-1) false p k 
       | Clight.EKforTest(expr, stmt1, stmt2, k) ->  
 	  fprintf p "EKforTest"; 
 	  print_k (i-1) false p k 
  end else fprintf p ";..."

let print_state p st = 
  fprintf p "@[<hv> State: ";
  begin
    match st with
    | Clight.SKlval(expr, env, ek) -> 
	fprintf p "SKlval %a @[<hov 1>[@,%a]@]" 
	  PrintCsyntax.print_expr expr
	  (print_ek 3 true) ek
    | Clight.SKexpr(expr, env, ek) -> 
	fprintf p "SKexpr %a @[<hov 1>[@,%a]@]" 
	  PrintCsyntax.print_expr expr
	  (print_ek 3 true) ek
    | Clight.SKval(v, env, ek) -> 
	fprintf p "SKval %s@ @[<hov 1>[@,%a]@]" 
	  (string_of_val v)
	  (print_ek 3 true) ek
    | Clight.SKstmt(stmt, env, k) -> 
	fprintf p "SKstmt %a@ @[<hov 1>[@,%a]@]"
	  PrintCsyntax.print_stmt stmt
	  (print_k 3 true) k
    | Clight.SKcall(vl, k) -> 
	fprintf p "SKcall (@[<hov 0>%a@])@ @[<hov 1>[@,%a]@]"
	  (print_vlist true) vl
	  (print_k 3 true) k
(*     | Clight.SKnextstmt(env, k) ->  *)
(* 	fprintf p "SKnextstmt @ @[<hov 1>[@,%a]@]" *)
(* 	  (print_k 3 true) k *)
    | Clight.SKbind(fn, vl, id_tyl, env, k) -> 
	fprintf p "SKbind @ @[<hov 1>[%a]@]"
	  (print_k 3 true) k
    | Clight.SKalloc(vl, id_tyl, env, k) -> 
	fprintf p "SKalloc @ @[<hov 1>[%a]@]"
	  (print_k 3 true) k
    | Clight.SKExternal(_ret_ty, ptr_ty_opt, env, k) -> 
	fprintf p "SKexternal @ @[<hov 1>[%a]@]"
	  (print_k 3 true) k
    | Clight.SKoptstorevar(oid, v, env, k) ->
    fprintf p "SKoptstorevar @ @[<hov 1>[%a]@]"
           (print_k 3 true) k 
  end;
  fprintf p "@]@."


(* Initialization of the semantics *)
let next_ptr = ref 1l;;
let get_next_ptr () = 
  next_ptr := Int32.add !next_ptr 1l;
  ptr_of_int !next_ptr;;

let add_fun_env e (Coq_pair (fn, fb)) =
  let p = get_next_ptr () in
  let e1 = Genv.add_funct (Coq_pair (fn, fb)) p e in
    Genv.add_symbol fn p e1;;

let add_var_env e (Coq_pair(Coq_pair(vn, _), _)) =
  let p = get_next_ptr () in
    Genv.add_symbol vn p e;;

let env_of_prog p =
  let e = Genv.empty in
  let e1 = fold_left add_fun_env (prog_funct p) e in
  let e2 = fold_left add_var_env (prog_vars p) e1 in
    e2;;

let main_fn_ptr p e =
  match Genv.find_symbol e (prog_main p) with
    | None -> failwith "Could not find main"
    | Some mptr -> mptr;;

let rec runtaus env s =
  match Clight.cl_step_fn env s TEtau with
    | None -> s
    | Some s' -> runtaus env s';;

(* Execute a C program with SC semantics *)

module MemMap = Map.Make(struct type t = pointer let compare = compare end) 

type extstate = {memmap : coq_val MemMap.t; nextalloc : BinInt.coq_Z; 
		 inputs : eventval list}

let delim = Str.regexp "[ \t\n]+"
let init_estate istr = 
  let is = List.map (fun i -> EVint (z_of_camlint (Int32.of_string i))) (Str.split delim istr) in
    {memmap = MemMap.empty; nextalloc = BinInt.Zpos BinPos.Coq_xH; inputs = is}

let perform_event s e = 
  match e with
  | TEmem (MEwrite(p, c, v)) -> 
      { memmap = MemMap.add p v s.memmap; 
	nextalloc = s.nextalloc; inputs = s.inputs}
  | _ -> s

let get_read_val s p c =
  let rv = try MemMap.find p s.memmap 
           with Not_found -> Vundef in
    rv, TEmem (MEread(p, c, rv))

let zero = z_of_camlint (Int32.of_string "0")

let get_return_val s =
  let v, is = match s.inputs with 
    | [] -> EVint zero, []
    | v :: t -> v, t in
    v, {s  with inputs = is}, TEext (Ereturn (Tint, v))

let get_alloc_ptr s size k =
  let p = Ptr(s.nextalloc, z0) in
    p, {s with nextalloc = BinInt.coq_Zsucc s.nextalloc}, TEmem (MEalloc(p, size, k))

let get_rmw s p c i =
  let rv = try MemMap.find p s.memmap 
           with Not_found -> Vundef in
  let nv = rmw_instr_semantics i rv in
    (nv, { memmap = MemMap.add p nv s.memmap; 
  	       nextalloc = s.nextalloc; inputs = s.inputs}, 
           TEmem (MErmw(p, c, rv, i)));;

let get_tid s p args =
  (None, TEstart(p, args))

let do_step ge ps exts =
  match Clight.cl_step_fn1 ge ps with
    | Clight.Rnostep -> None
    | Clight.Rsimple(te, ns) ->
	let nexts = perform_event exts te in
	  Some(ns, nexts, te)
    | Clight.Rread(p, c, f) -> 
	let v, nev = get_read_val exts p c in
	  Some(f v, exts, nev)
    | Clight.Rreturn (typ, f) -> 
	let v, nexts, te = get_return_val exts in
	  Some(f (val_of_eval v), nexts, te)
    | Clight.Ralloc(size, k, f) ->
	let v, nexts, te = get_alloc_ptr exts size k in
	  Some(f v, nexts, te)
    | Clight.Rrmw(p, c, i, f) ->
    let v, nexts, te = get_rmw exts p c i in
      Some(f v, nexts, te)

let print_expected_event ge ps =
  match Clight.cl_step_fn1 ge ps with
    | Clight.Rnostep -> printf "Stuck state.@."
    | Clight.Rsimple(te, ns) ->
	printf "Expected event: %s.@." (string_of_thread_event te)
    | Clight.Rread(p, c, f) -> 
	printf "Expected event kind: %s.@." 
	  (string_of_thread_event (TEmem (MEread(p, c, Vundef))))
    | Clight.Rreturn (typ, f) -> 
	printf "Expected event kind: %s.@." 
	  (string_of_thread_event (TEext (Ereturn (Tint, EVint zero))))
    | Clight.Ralloc(size, k, f) ->
	printf "Expected event kind: %s.@." 
	  (string_of_thread_event (TEmem (MEalloc(Ptr(z0, z0), size, k))))
    | Clight.Rrmw(p, c, i, f) ->
	printf "Expected event kind: %s.@." 
	  (string_of_thread_event (TEmem (MErmw(p, c, Vundef, i))))

let runprog_sc inputstr maxstep (output_ev, output_stuck, output_max) p =
  let env = env_of_prog p in
  let main_ptr = main_fn_ptr p env in
  let extstate = init_estate inputstr in
  let rec runsteps i ts xs = 
    if !option_v then print_state std_formatter ts;
    if i < maxstep then
      match do_step env ts xs with
	| None -> 
	    output_stuck ();
	| Some(nts, nxs, ev) ->
	    output_ev ev i;
	    (match ev with
		 TEexit -> ()
	       | TEext (Eexit ec) -> ()
	       | _ -> runsteps (i + 1) nts nxs)
    else output_max maxstep in
  let args = [Vint z0; Vint z0] in
    match Clight.cl_init env main_ptr args with
      | None -> failwith "Could not initialize main."
      | Some inits -> runsteps 0 inits extstate;;    

(* Execute a C program against a given trace of events *)
let runevent env s e =
  let ns = runtaus env s in
  let estr = string_of_thread_event e in
    match Clight.cl_step_fn env ns e with
      | None ->
          printf "Event '%s' not accepted.@." estr;
	  print_expected_event env ns;
	  if !option_v then begin
	    print_endline "State: ";
	    print_state std_formatter ns; 
	    print_newline ()
	  end;
	  None
      | Some s' -> printf "Accepted '%s'.@." estr; 
	  Some s';;

let runprog events p =
  let env = env_of_prog p in
  let main_ptr = main_fn_ptr p env in
  let rec runevents evs s = match evs with
       | [] -> printf "Done.@."
       | e :: t -> 
	   (match runevent env s e with
		None -> ()
	      | Some s' -> runevents t s' )in
  let args = [Vint z0; Vint z0] in
    match Clight.cl_init env main_ptr args with
      | None -> failwith "Could not initialize main."
      | Some inits -> runevents events inits;;

let run_c_file sourcename runner =
  (* let events = parse_event_file evname in *)
  (* let prefixname = Filename.chop_suffix sourcename ".c" in *)
  let preproname = Filename.temp_file "compcert" ".i" in
    preprocess sourcename preproname;
    let csyntax = get_c_syntax sourcename preproname in
      runner csyntax;;

(* Command-line parsing *)

let starts_with s1 s2 =
  String.length s1 >= String.length s2 &&
  String.sub s1 0 (String.length s2) = s2

let usage_string =
"ccomp [options] <C source file>
Preprocessing options:
  -I<dir>        Add <dir> to search path for #include files
  -D<symb>=<val> Define preprocessor symbol
  -U<symb>       Undefine preprocessor symbol
Compilation options:
  -flonglong     Treat 'long long' as 'long' and 'long double' as 'double'
  -dclight       Save generated Clight in <file>.light.c
Event output options:
  -i <intlist>   Feeds <intlist> as return values from external functions
  -e <file>      Matches the generated events with the content of <file>
  -max-steps <i> Performs at most <i> steps in the operational semantics
  -plain         Outputs the generated event trace in plain format that
                 can be consumed by the -e option
  -no-tau        Does not output tau events
  -no-memory     Does not output memory events
  -external-only Only outputs external events
General options:
  -stdlib <dir>  Set the path of the Compcert run-time library
  -v             Verbose output
"

let src = ref ""

let rec parse_cmdline i =
  if i < Array.length Sys.argv then begin
    let s = Sys.argv.(i) in
    if starts_with s "-I" || starts_with s "-D" || starts_with s "-U"
    then begin
      prepro_options := s :: !prepro_options;
      parse_cmdline (i + 1)
    end else 
    if s = "-e" && i + 1 < Array.length Sys.argv then begin
      event_name := Sys.argv.(i + 1);
      parse_cmdline (i + 2)
    end else
    if s = "-max-steps" && i + 1 < Array.length Sys.argv then begin
      max_steps := int_of_string (Sys.argv.(i + 1));
      parse_cmdline (i + 2)
    end else
    if s = "-stdlib" && i + 1 < Array.length Sys.argv then begin
      stdlib_path := Sys.argv.(i + 1);
      parse_cmdline (i + 2)
    end else
    if s = "-flonglong" then begin
      option_flonglong := true;
      parse_cmdline (i + 1)
    end else
    if s = "-dclight" then begin
      option_dclight := true;
      parse_cmdline (i + 1)
    end else
    if s = "-plain" then begin
      plain_output := true;
      event_filter := (fun e -> match e with TEtau -> false | _ -> true);
      parse_cmdline (i + 1)
    end else
    if s = "-no-tau" then begin
      let ef = !event_filter in
      event_filter := (fun e -> match e with TEtau -> false | _ -> ef e);
      parse_cmdline (i + 1)
    end else
    if s = "-no-memory" then begin
      let ef = !event_filter in
      event_filter := (fun e -> match e with TEmem _ -> false | _ -> ef e);
      parse_cmdline (i + 1)
    end else
    if s = "-external-only" then begin
      let nf e = (match e with TEext _ -> true | _ -> false) in
      event_filter := nf;
      parse_cmdline (i + 1)
    end else
    if s = "-v" then begin
      option_v := true;
      parse_cmdline (i + 1)
    end else
    if Filename.check_suffix s ".c" then begin
      if !src = "" 
      then begin src := s; parse_cmdline (i + 1) end
      else begin eprintf "Cannot execute more than one c file"; exit 3 end
    end else begin
      eprintf "Unknown argument `%s'@." s;
      eprintf "Usage: %s" usage_string;
      exit 2
    end
  end
	

let _ = 
  parse_cmdline 1;
  if !src = "" 
  then begin eprintf "Missing c file."; exit 3 
  end else if !event_name <> "" then begin
    let events = parse_event_file !event_name in
      run_c_file !src (runprog events)
  end else
    let out_ev ev i =
      if !event_filter ev
      then if !plain_output 
      then printf "%s@." (string_of_thread_event ev)
      else begin
	printf "Step %i: Performed '%s'.@." i (string_of_thread_event ev);
	match ev with
	    TEexit -> printf "Done (step %i). Thread exited.@." i
	  | TEext (Eexit ec) -> 
	      printf "Done (step %i). Program exit (exit code %ld).@." 
		i (camlint_of_coqint ec)
	  | _ -> ()
      end in
    let out_stuck () = 
      if not !plain_output 
      then printf "Stuck.@." in
    let out_max i = 
      if not !plain_output 
      then printf "Reached maximum number of steps (%i).@." i in
      run_c_file !src (runprog_sc !input_list !max_steps (out_ev, out_stuck, out_max))
  
