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
// #include <stdlib.h>

extern void exit (int);

/* message passing without synchronisation */

volatile int channel;
/* 1 if the channel is full, 0 if it is empty */ 
volatile int flag = 0;

/* Producer and consumer */

void *producer(void *tid) {
  int i;
  for (i=0; i<10000000; i++) {
    channel = channel + 1;
    flag = 1;
    while (flag) ;
  }
  printf("result: %d\n", channel);
  exit(0);
}

void *consumer(void *tid) {
  while (1) {
    while (flag == 0) ;
    channel = channel + 1;
    flag = 0;
  }
}

int main() {
  long t;
  
  thread_create(producer, (void *)t);
  thread_create(consumer, (void *)t);

  sleep(2);

  return 0;
}
