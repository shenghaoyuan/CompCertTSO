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

/* 1 if the spinlock is taken, 0 if it is free */ 
int pinglock = 1; 
int ponglock = 1;

void lock(int *exclusion) {
  while (CAS(exclusion, 1, 0))
    while (*exclusion)
      ;
}

void unlock(int *exclusion) {
  *exclusion = 0;
}

/* ping and pong */

void *ping(void *tid) {
  for (int i=0; i<20; i++) {
    lock(&pinglock);
    printf("ping     (pinglock = %d, ponglock = %d)\n", pinglock, ponglock);
    unlock(&ponglock);
  };
}

void *pong(void *tid) {
  for (int i=0; i<20; i++) {
    lock(&ponglock);
    printf("  pong   (pinglock = %d, ponglock = %d)\n", pinglock, ponglock);
    unlock(&pinglock);
  };
}

int main() {
  long t;

  thread_create(ping, (void *)t);
  printf("main: ping created\n");
  thread_create(pong, (void *)t);
  printf("main: pong created\n");

  unlock (&ponglock);

  sleep (2);
  return 0;
}
