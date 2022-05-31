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

/* message passing without synchronisation */

int channel;
/* 1 if the channel is full, 0 if it is empty */ 
int flag = 0;

/* producer and consumer */

void *producer(void *tid) {
  for (int i=0; i<10; i++) {
    printf("producer: sending message: %d\n",i);
    channel = i;
    flag = 1;
    while (flag)
      ;
  };
  printf("producer: done\n");
}

void *consumer(void *tid) {
  for (int i=0; i<10; i++) {
    while (flag == 0) 
      ;
    printf("consumer: received message: %d\n", channel);
    flag = 0;
  };
  printf("consumer: done\n");
}

int main() {
  long t;

  thread_create(producer, (void *)t);
  printf("main: producer created\n");
  thread_create(consumer, (void *)t);
  printf("main: consumer created\n");

  sleep (2);

  return 0;
}
