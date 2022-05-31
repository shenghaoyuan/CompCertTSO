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

FILES= intel_defns.h portable_defns.h ptst.h ptst.c gc.h gc.c \
       random.h set.h set_harness.c skip_cas.c 

OPTIONSGCC = -m32 -DINTEL -DGCC -O1 -D_XOPEN_SOURCE

OPTIONSCCOMP = -lpthread -DINTEL -DCCOMP -dasm -D_XOPEN_SOURCE

all: skiplist.ccomp replay.ccomp

%.gcc.o: %.c
	gcc $(OPTIONSGCC) -save-temps -o $@ -c $<

%.ccomp.o: %.c
	../../ccomp $(OPTIONSCCOMP) -dasm -stdlib ../../runtime -o $@ -c $<

skiplist.gcc: ptst.gcc.o gc.gcc.o set_harness.gcc.o skip_cas.gcc.o
	gcc -m32 $(OPTIONSGCC) -o skiplist.gcc -lpthread \
                 ptst.gcc.o gc.gcc.o set_harness.gcc.o skip_cas.gcc.o

skiplist.ccomp: ptst.ccomp.o gc.ccomp.o set_harness.ccomp.o skip_cas.ccomp.o
	../../ccomp -stdlib ../../runtime $(OPTIONSCCOMP) -o skiplist.ccomp \
                   ptst.o gc.o set_harness.o skip_cas.o

replay.ccomp: replay.c
	../../ccomp $(OPTIONSCCOMP) -stdlib ../../runtime -o replay.ccomp replay.c

clean:
	rm -f *~ *.o *.s *.i skiplist.gcc skiplist.ccomp replay.ccomp

