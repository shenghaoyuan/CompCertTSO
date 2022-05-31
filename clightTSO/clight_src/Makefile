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

all: out.ps Csem.v Csyntax.v 

# to generate the Coq Csyntax.v and Csem.v (and a typeset version of Csem)

out.tex Csyntax.v Csem.unlinebreaked.v: Csyntax1.ott Csyntax2.v Csem1.v Csem2.ott Csem3.v 
	rm -rf Csyntax.v Csem.unlinebreaked.v 
	ott                                      			    \
                -coq_names_in_rules false                                   \
                -i Csyntax1.ott -i Csyntax2.v       -o Csyntax.v            \
                -i Csem1.v -i Csem2.ott -i Csem3.v  -o Csem.unlinebreaked.v \
                -o out.tex                                                  \
                -coq_avoid 0                                                \
                -tex_show_meta false                                        \
                -merge false                                            
	chmod ugo-w Csyntax.v Csem.unlinebreaked.v 

Csem.v: Csem.unlinebreaked.v 
	rm -rf Csem.v 
	sed -f sed_linebreak_script < Csem.unlinebreaked.v > Csem.unlinebreaked.tmp.v
	sed -f sed_linebreak_script2 < Csem.unlinebreaked.tmp.v > Csem.v
	chmod ugo-w Csem.v 

# to generate LaTeX inclusions for paper

clight-inc.tex sims.tex: Csyntax1.ott Csyntax2.v Csem1.v Csem2.ott Csem3.v  sims.mng sed_script
	rm -rf Csyntax.v Csem.unlinebreaked.v clight-inc.tex sims.tex
	ott                                      			    \
                -coq_names_in_rules false                                   \
                -i Csyntax1.ott -i Csyntax2.v       -o Csyntax.v            \
                -i Csem1.v -i Csem2.ott -i Csem3.v  -o Csem.unlinebreaked.v \
                -o clight-inc.tex                                           \
                -coq_avoid 0                                                \
		-tex_show_meta false                                        \
                -merge false                                                \
		-tex_wrap false                                             \
		-tex_filter  sims.mng sims.tex                    
	chmod ugo-w Csyntax.v Csem.unlinebreaked.v 
	chmod ugo-w sims.tex
	sed -f sed_script < clight-inc.tex >  clight-inc.sed.tex
	cp clight-inc.sed.tex clight-inc.tex
	rm -rf ../../../doc/clight-inc.tex
	cp  clight-inc.tex ../../../doc
	rm -rf ../../../doc/sims.tex
	cp  sims.tex ../../../doc

#  code to make Csemp.v from Csem1.v and Csem2.ott, to use for interactive
#  development in Csem3.v
#
#Csyntax.v Csem.unlinebreaked.v outp.tex: Csyntax1.ott Csyntax2.v Csem1.v Csem2p.ott #Csem3.v
#	rm -rf Csyntax.v Csem.unlinebreaked.v 
#	ott      							\
#		-coq_avoid 0 						\
#                -tex_show_meta false                                    \
#		-merge false                                            \
#                -i Csyntax1.ott -i Csyntax2.v        -o Csyntax.v	\
#                -i Csem1.v -i Csem2p.ott -o Csem.unlinebreaked.v       \
#		-o outp.tex
#	chmod ugo-w Csyntax.v Csem.unlinebreaked.v 



%.dvi: %.tex
	latex $<

%.ps: %.dvi
	dvips -Ppdf -j0 -G0 -t a4 $<

%.pdf: %.ps
	ps2pdf $<

clean:
	rm -rf clight-inc.tex clight-inc.sed.tex sims.tex Csem.unlinebreaked.v Csyntax.v Csem.v 
	rm -rf out.dvi  out.ps  out.v out.aux  out.log  out.pdf  out.tex texput.log
	rm -rf *~
#	rm -rf outp.dvi  outp.ps  outp.v  texput.log outp.aux  outp.log  outp.pdf  outp.tex 
#	rm -rf splitfile.cmo splitfile.cmi splitfile 
#	rm -rf out.linebreaked.v split_default_out

.PRECIOUS: *.tex *.dvi *.ps *.v


# splitfile: splitfile.ml
# 	ocamlc -g -o splitfile str.cma splitfile.ml
