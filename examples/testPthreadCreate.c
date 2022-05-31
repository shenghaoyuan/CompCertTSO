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
#define NUM_THREADS    25


void *PrintHello(void *threadid)
{
   long tid;
   tid = (long)threadid;
   printf("Hello World! It's me, thread #%ld!\n", tid);
   pthread_exit(NULL);
}

int main (int argc, char *argv[])
{
   pthread_t threads[NUM_THREADS];
   int rc;
   long t;
   for(t=0; t<NUM_THREADS; t++){
      printf("In main: creating thread %ld\n", t);
      rc = pthread_create(&threads[t], NULL, PrintHello, (void *)t);
      if (rc){
         printf("ERROR; return code from pthread_create() is %d\n", rc);
         exit(-1);
      }
   }
   pthread_exit(NULL);
}
