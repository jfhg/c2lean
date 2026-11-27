//@ optimize O1
int localarr(int n) {
  int a[8];
  for (int i = 0; i < 8; i++) a[i] = i * i;
  return a[n];
}
