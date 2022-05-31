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

volatile int channel[1024];
/* 1 if the channel is full, 0 if it is empty */ 
volatile int flag = 0;

/* producer and consumer */

void *producer(void *tid) {
  int i, j;
  for (i=0; i<100000; i++) {
    for (j=0; j<1024; j++) channel[j] = channel[j] + 1;
    flag = 1;
    while (flag) ;
  }
  printf("result: %d\n", channel[100]);
  exit(0);
}

void *consumer(void *tid) {
  int j;
  while (1) {
    while (flag == 0) ;
    for (j=0; j<1024; j++) channel[j] = channel[j] + 1;
    flag = 0;
  }
}

int main() {
  pthread_t tid[2];
  long t;
  int j;
  for (j=0; j<1024; j++) channel[j] = j;
  
  pthread_create(&tid[1], NULL, producer, (void *)t);
  pthread_create(&tid[2], NULL, consumer, (void *)t);

  pthread_exit(NULL);

  return 0;
}
