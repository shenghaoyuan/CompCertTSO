/*========================================================================*/
/*                                                                        */
/*                    CompcertTSO                                         */
/*                                                                        */
/*          Jaroslav Sevcik, University of Cambridge                      */
/*          Viktor Vafeiadis, University of Cambridge                     */
/*          Francesco Zappa Nardelli, INRIA Rocquencourt                  */
/*          Suresh Jagannathan, Purdue University                         */
/*          Peter Sewell, University of Cambridge                         */
/*                                                                        */
/*          (building on CompCert 1.5 and a 1.8 pre-release)              */
/*                                                                        */
/*  This document and the CompCertTSO sources are copyright 2005, 2006,   */
/*  2007, 2008, 2009, 2010, 2011 Institut National de Recherche en        */
/*  Informatique et en Automatique (INRIA), and Suresh Jagannathan,       */
/*  Jaroslav Sevcik, Peter Sewell and Viktor Vafeiadis.                   */
/*                                                                        */
/*  All rights reserved.  This file is distributed under the terms of     */
/*  the INRIA Non-Commercial License Agreement.                           */
/*                                                                        */
/*                                                                        */
/*                                                                        */
/*                                                                        */
/*                                                                        */
/*========================================================================*/

#include <stdio.h>

void extfnnopar(void) {
    printf("EXT(C(extfnnopar))\n");
    printf("EXT(R(I0))\n");
}

void extfn(int i) {
    printf("EXT(C(extfn, I%i))\n", i);
    printf("EXT(R(I0))\n");
}


void extfn2(int i, int j) {
    printf("EXT(C(extfn2, I%i, I%i))\n", i, j);
    printf("EXT(R(I0))\n");
}
