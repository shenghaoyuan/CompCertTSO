// Treiber's stack.
//
// See:
//   R. K. Treiber. Systems programming: Coping with parallelism.
//   Technical report RJ 5118. IBM Almaden Research Center. April 1986.
// 

// #include <stdlib.h>

#define NIL 0

typedef struct node_st {
  struct node *m_next;
  int val;
} node;

node *top = NIL;

// -----------------------------------------------------------------------------
// Push an element onto the stack
// -----------------------------------------------------------------------------

void push(int e) {
  node *y;
  node *n; 
  y = (node *) malloc(sizeof (struct node));
  y->val = e;

  n = top;
  y->m_next = n;

  while(1) {
    if (CAS(&top, y, n) == n)
      break;

    n = top;
    y->m_next = n;
  }
  
}

// -----------------------------------------------------------------------------
// Pop an element off the stack (non-blocking)
// -----------------------------------------------------------------------------


int pop() {
  node *y;
  node *z;

  while(1) {
    y = top;
    if (y==NIL) {
      return -1;
    } else {
      z = y->m_next;

      if (CAS(&top, z, y) == y)
        break;
    }
  };
  return y->val;
}
