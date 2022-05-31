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

void extfn(int);

int retmiddle(int a, int b) {
    if (a == 0) return b;
    return a;
}

int retfor(int i) {
    int j;
    for(j = 0; j < 10; j++) {
        if (i == j) return j;
    }
    return 0;
}

int main(int argc, char **argv) {
  extfn(retmiddle(0, 2)); // expected 2
  extfn(retmiddle(1, 2)); // expected 1
  extfn(retfor(5)); // expected 5 
  extfn(retfor(15)); // expected 0 
  return 1;
}
