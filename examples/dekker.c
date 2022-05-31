int flag0 = 0;
int flag1 = 0;
int turn = 0;

void acquire_0() {
  flag0 = 1;
  while (flag1) {
    if (turn != 0) {
      flag0 = 0;
      while (turn != 0);
      flag0 = 1;
    }
  }
}

void release_0() {
  turn = 1;
  flag0 = 0;
}
