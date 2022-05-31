#========================================================================#
#                                                                        #
#                    CompcertTSO                                         #
#                                                                        #
#          Jaroslav Sevcik, University of Cambridge                      #
#          Viktor Vafeiadis, University of Cambridge                     #
#          Francesco Zappa Nardelli, INRIA Rocquencourt                  #
#          Suresh Jagannathan, Purdue University                         #
#          Peter Sewell, University of Cambridge                         #
#                                                                        #
#          (building on CompCert 1.5 and a 1.8 pre-release)              #
#                                                                        #
#  This document and the CompCertTSO sources are copyright 2005, 2006,   #
#  2007, 2008, 2009, 2010, 2011 Institut National de Recherche en        #
#  Informatique et en Automatique (INRIA), and Suresh Jagannathan,       #
#  Jaroslav Sevcik, Peter Sewell and Viktor Vafeiadis.                   #
#                                                                        #
#  All rights reserved.  This file is distributed under the terms of     #
#  the INRIA Non-Commercial License Agreement.                           #
#                                                                        #
#                                                                        #
#                                                                        #
#                                                                        #
#                                                                        #
#========================================================================#

#######################################################################
#                                                                     #
#              The Compcert verified compiler                         #
#                                                                     #
#          Xavier Leroy, INRIA Paris-Rocquencourt                     #
#                                                                     #
#  Copyright Institut National de Recherche en Informatique et en     #
#  Automatique.  All rights reserved.  This file is distributed       #
#  under the terms of the INRIA Non-Commercial License Agreement.     #
#                                                                     #
#######################################################################

include Makefile.config

DIRS_ARCH_INDEP=lib common backend cfrontend \
     clightTSO clightTSO/clight_src driver

DIRS=$(DIRS_ARCH_INDEP) $(ARCH)/$(VARIANT) $(ARCH)

DIRS_INTERPRETER=lib common $(ARCH)/$(VARIANT) $(ARCH) backend cfrontend \
         clightTSO clightTSO/clight_src interpreter

INCLUDES=$(patsubst %,-I %, $(DIRS))

INCLUDES_INTERPRETER=$(patsubst %,-I %, $(DIRS_INTERPRETER))

COQC=coqc $(INCLUDES) 
COQDEP=coqdep $(INCLUDES)
COQDOC=coqdoc
COQEXEC=coqtop $(INCLUDES) -batch -load-vernac-source

OCAMLBUILD=ocamlbuild
OCB_OPTIONS=\
  -no-hygiene \
  -no-links \
  -I extraction $(INCLUDES) \
  -cflags -I,`pwd`/cil/obj/$(ARCHOS) \
  -lflags -I,`pwd`/cil/obj/$(ARCHOS) \
  -libs unix,str,cil

OCB_OPTIONS_INTERPRETER=\
  -no-hygiene \
  -no-links \
  -I extraction $(INCLUDES_INTERPRETER) \
  -cflags -I,`pwd`/cil/obj/$(ARCHOS) \
  -lflags -I,`pwd`/cil/obj/$(ARCHOS) \
  -libs unix,str,cil

VPATH=$(DIRS)
GPATH=$(DIRS)

# General-purpose libraries (in lib/)

LIB=Vlib.v Coqlib.v Maps.v Lattice.v Ordered.v Mergesort.v \
    Iteration.v Integers.v Floats.v Parmov.v UnionFind.v

# Parts common to the front-ends and the back-end (in common/)

COMMON=Errors.v Ast.v Libtactics.v Pointers.v Events.v Values.v Simulations.v \
       Mem.v Memaux.v Globalenvs.v Memcomp.v MCsimulation.v TSOmachine.v Memeq.v Switch.v TSOsimulation.v \
       Smallstep.v Traces.v 

BACKEND=\
  Cminor.v \
  CminorSel.v \
  Selection.v \
  CminorP.v Selectionproof.v \
  Registers.v RTL.v RTLtyping.v \
  RTLgen.v RTLgenspec.v RTLgenproof.v \
  Kildall.v \
  Constprop.v Constpropproof.v \
  CSE.v CSEproof.v \
  Fenceintro2.v Fenceintro2proof.v \
  Fenceelim.v Fenceelim2.v Fenceelimproof.v Fenceelim2proof.v \
  Locations.v LTL.v LTLtyping.v \
  InterfGraph.v Coloring.v Coloringproof.v \
  Allocation.v Allocproof.v Alloctyping.v \
  Tunneling.v Tunnelingproof.v Tunnelingtyping.v \
  LTLin.v LTLintyping.v \
  Linearize.v Linearizeproof.v Linearizetyping.v \
  Linear.v Lineartyping.v \
  Parallelmove.v Reload.v Reloadproof.v Reloadtyping.v \
  Mach.v Machabstr.v Machtyping.v \
  Bounds.v Stacking.v Stackingproof.v Stackingtyping.v \
  Machconcr.v \
  MMproofaux.v MMperthreadsimdef.v MMperthreadsimproof.v \
  MMtsoaux.v MMtsosimproof.v MMproof.v

ARCHFILES=\
  Op.v SelectOp.v SelectOpproof.v \
  Machregs.v Conventions.v \
  ConstpropOp.v ConstpropOpproof.v \
  Asmgenretaddr.v \
  Asm.v Asmgen.v Asmgenproof1.v Asmgenproof.v 

ARCHOSFILES= Stacklayout.v  

CLIGHTTSO= Csyntax.v Csem.v

FRONTEND= Csharpminor.v Cminorgen.v Cminorops.v Cminorgenproof.v \
  Cshmgen.v \
  Ctyping.v \
  Cstacked.v \
  Cstackedproofsimdef.v Cstackedproofunbuffer.v \
  Cstackedproofalloc.v  Cstackedprooffree.v \
  Cstackedprooftau.v    Cstackedproof.v \
  Cshmgenproof1.v Cshmgenproof2.v Cshmgenproof3.v

# Putting everything together (in driver/)

DRIVER=Compiler.v 

# All source files
FILES=$(LIB) $(COMMON) $(BACKEND) $(FRONTEND) $(CLIGHTTSO) $(DRIVER)\
	  $(ARCHFILES) $(ARCHOSFILES)

proof:  $(FILES:.v=.vo) clightTSO/clight_src/Csyntax.v clightTSO/clight_src/Csem.v

extraction:
	rm -f extraction/*.ml extraction/*.mli
	$(COQEXEC) extraction/extraction.v
#	cd extraction && ./fixextract   FZ: we do not need Kildall at all

cil:
	$(MAKE) -j1 -C cil

# building Csyntax.v and Csem.v
CLIGHT_SOURCES = \
clightTSO/clight_src/Csyntax1.ott \
clightTSO/clight_src/Csyntax2.v \
clightTSO/clight_src/Csem1.v \
clightTSO/clight_src/Csem2.ott \
clightTSO/clight_src/Csem3.v

clightTSO/clight_src/Csyntax.v clightTSO/clight_src/Csem.v: $(CLIGHT_SOURCES)
	cd clightTSO/clight_src; make

clightTSO/clight_src/out.pdf: $(CLIGHT_SOURCES)
	cd clightTSO/clight_src; make out.pdf

interpreter/Configuration.ml: Makefile.config
	(echo 'let stdlib_path = "$(LIBDIR)"'; \
         echo 'let prepro = "$(CPREPRO)"'; \
         echo 'let asm = "$(CASM)"'; \
         echo 'let linker = "$(CLINKER)"'; \
         echo 'let arch = "$(ARCH)"'; \
         echo 'let variant = "$(VARIANT)"'; \
         echo 'let system = "$(SYSTEM)"') \
        > interpreter/Configuration.ml

clighti: interpreter/Configuration.ml # extraction
	$(OCAMLBUILD) $(OCB_OPTIONS_INTERPRETER) Interpreter.native \
        && rm -f clighti && ln -s _build/interpreter/Interpreter.native clighti

clighti.byte: interpreter/Configuration.ml # extraction
	$(OCAMLBUILD) $(OCB_OPTIONS_INTERPRETER) Interpreter.byte \
        && rm -f clighti.byte && ln -s _build/interpreter/Interpreter.byte clighti.byte

ccomp: driver/Configuration.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) Driver.native \
        && rm -f ccomp && ln -s _build/driver/Driver.native ccomp

ccomp.prof: driver/Configuration.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) Driver.p.native \
        && rm -f ccomp.prof && ln -s _build/driver/Driver.p.native ccomp.prof

ccomp.byte: driver/Configuration.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) Driver.d.byte \
        && rm -f ccomp.byte && ln -s _build/driver/Driver.d.byte ccomp.byte

runtime:
	$(MAKE) -C runtime

.PHONY: proof extraction clighti cil ccomp ccomp.prof ccomp.byte runtime

all:
	$(MAKE) proof
	$(MAKE) documentation
	$(MAKE) cil
	$(MAKE) extraction
	$(MAKE) clighti
	$(MAKE) extraction
	$(MAKE) ccomp
	$(MAKE) runtime

documentation: doc/coq2html clightTSO/clight_src/out.pdf $(CLIGHT_SOURCES) $(FILES)
	mkdir -p doc/html
	mkdir -p doc/clight_src
	cp $(CLIGHT_SOURCES) doc/clight_src/
	cp clightTSO/clight_src/out.pdf doc/clightTSO.pdf
	rm -f doc/html/*.html
	cp LICENSE doc/
	doc/coq2html -o 'doc/html/%.html' doc/*.glob \
          $(filter-out doc/coq2html clightTSO/clight_src/out.pdf $(CLIGHT_SOURCES), $^)
	cp doc/coq2html.css doc/coq2html.js doc/html/

doc/coq2html: doc/coq2html.ml
	ocamlopt -o doc/coq2html str.cmxa doc/coq2html.ml

doc/coq2html.ml: doc/coq2html.mll
	ocamllex doc/coq2html.mll

latexdoc:
	cd doc; $(COQDOC) --latex -o doc/doc.tex -g $(FILES)

.SUFFIXES: .v .vo

.v.vo:
	@rm -f doc/glob/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob doc/$(*F).glob $*.v

driver/Configuration.ml: Makefile.config
	(echo 'let stdlib_path = "$(LIBDIR)"'; \
         echo 'let prepro = "$(CPREPRO)"'; \
         echo 'let asm = "$(CASM)"'; \
         echo 'let linker = "$(CLINKER)"'; \
         echo 'let arch = "$(ARCH)"'; \
         echo 'let variant = "$(VARIANT)"'; \
         echo 'let system = "$(SYSTEM)"') \
        > driver/Configuration.ml

depend: clightTSO/clight_src/Csyntax.v clightTSO/clight_src/Csem.v
	$(COQDEP) $(patsubst %, %/*.v, $(DIRS)) \
        | sed -e 's|$(ARCH)/$(VARIANT)/|$$(ARCH)/$$(VARIANT)/|g' \
              -e 's|$(ARCH)/|$$(ARCH)/|g' \
        > .depend



install:
	install -d $(BINDIR)
	install ./ccomp $(BINDIR)
	$(MAKE) -C runtime install

clean:
	rm -f $(patsubst %, %/*.vo, $(DIRS))
	rm -f ccomp ccomp.byte clighti clighti.byte
	rm -rf _build
	rm -rf doc/html doc/*.glob
	rm -f doc/removeproofs.ml doc/removeproofs
	rm -f driver/Configuration.ml
	rm -f extraction/*.ml extraction/*.mli
	cd clightTSO/clight_src; make clean
#	$(MAKE) -C runtime clean
#	$(MAKE) -C test/cminor clean
#	$(MAKE) -C test/c clean

distclean:
	$(MAKE) clean
	rm -f Makefile.config
#	rm -rf cil

include .depend

FORCE:

