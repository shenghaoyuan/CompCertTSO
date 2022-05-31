/* *********************************************************************/
/*                                                                     */
/*              The Compcert verified compiler                         */
/*                                                                     */
/*          Xavier Leroy, INRIA Paris-Rocquencourt                     */
/*                                                                     */
/*  Copyright Institut National de Recherche en Informatique et en     */
/*  Automatique.  All rights reserved.  This file is distributed       */
/*  under the terms of the GNU General Public License as published by  */
/*  the Free Software Foundation, either version 2 of the License, or  */
/*  (at your option) any later version.  This file is also distributed */
/*  under the terms of the INRIA Non-Commercial License Agreement.     */
/*                                                                     */
/* *********************************************************************/

#ifndef _COMPCERT_STDIO_H
#define _COMPCERT_STDIO_H

#ifdef __GNUC__
#include_next "stdio.h"
#else
#include "/usr/include/stdio.h"
#endif

typedef struct compcert_FILE_ { void * fstr; } compcert_FILE;

extern compcert_FILE * compcert_stdin;
extern compcert_FILE * compcert_stdout;
extern compcert_FILE * compcert_stderr;
extern void	 compcert_clearerr(compcert_FILE *);
extern int	 compcert_fclose(compcert_FILE *);
extern int	 compcert_feof(compcert_FILE *);
extern int	 compcert_ferror(compcert_FILE *);
extern int	 compcert_fflush(compcert_FILE *);
extern int	 compcert_fgetc(compcert_FILE *);
extern char	*compcert_fgets(char * , int, compcert_FILE *);
extern compcert_FILE	*compcert_fopen(const char * , const char * );
extern int	 compcert_fprintf(compcert_FILE * , const char * , ...);
extern int	 compcert_fputc(int, compcert_FILE *);
extern int	 compcert_fputs(const char * , compcert_FILE * );
extern size_t	 compcert_fread(void * , size_t, size_t, compcert_FILE * );
extern compcert_FILE	*compcert_freopen(const char * , const char * ,
                                          compcert_FILE * );
extern int	 compcert_fscanf(compcert_FILE * , const char * , ...);
extern int	 compcert_fseek(compcert_FILE *, long, int);
extern long	 compcert_ftell(compcert_FILE *);
extern size_t	 compcert_fwrite(const void * , size_t, size_t, compcert_FILE * );
extern int	 compcert_getc(compcert_FILE *);
extern int	 compcert_putc(int, compcert_FILE *);
extern void	 compcert_rewind(compcert_FILE *);
extern int	 compcert_ungetc(int, compcert_FILE *);

#ifndef _INSIDE_COMPCERT_COMPATIBILITY_LIBRARY
#define FILE compcert_FILE
#undef stdin
#define stdin compcert_stdin
#undef stdout
#define stdout compcert_stdout
#undef stderr
#define stderr compcert_stderr
#undef clearerr
#define clearerr compcert_clearerr
#undef fclose
#define fclose compcert_fclose
#undef feof
#define feof compcert_feof
#undef ferror
#define ferror compcert_ferror
#undef fflush
#define fflush compcert_fflush
#undef fgetc
#define fgetc compcert_fgetc
#undef fgets
#define fgets compcert_fgets
#undef fopen
#define fopen compcert_fopen
#undef fprintf
#define fprintf compcert_fprintf
#undef fputc
#define fputc compcert_fputc
#undef fputs
#define fputs compcert_fputs
#undef fread
#define fread compcert_fread
#undef freopen
#define freopen compcert_freopen
#undef fscanf
#define fscanf compcert_fscanf
#undef fseek
#define fseek compcert_fseek
#undef ftell
#define ftell compcert_ftell
#undef fwrite
#define fwrite compcert_fwrite
#undef getc
#define getc compcert_getc
#undef getchar
#define getchar() compcert_getc(compcert_stdin)
#undef putc
#define putc compcert_putc
#undef putchar
#define putchar(c) compcert_putc(c, compcert_stdout)
#undef rewind
#define rewind compcert_rewind
#undef ungetc
#define ungetc compcert_ungetc
#endif

#endif
