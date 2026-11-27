//@ optimize O1
int log2ish(int n) {
  int k = 0;
  int p = 1;
  while (p < n) {
    p = p * 2;
    k = k + 1;
  }
  return k;
}
