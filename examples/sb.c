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

#include <pthread.h>
#include <stdio.h>

extern void exit (int);

/* message passing without synchronisation */

volatile int x=0;
volatile int y=0;

/* producer and consumer */

void *thread0(void *tid) {
  int r0;
  x=1;
  printf("Thread 0: %d\n", y);
  return(0);
}

void *thread1(void *tid) {
  y=1;
  printf("Thread 1: %d\n", x);
  return(0);
}

int main() {
  pthread_t tid[2];
  long t;
  pthread_create(&tid[1], NULL, thread0, (void *)t);
  pthread_create(&tid[2], NULL, thread1, (void *)t);

  pthread_exit(NULL);

  return 0;
}
