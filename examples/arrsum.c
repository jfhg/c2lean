//@ optimize O1
//@ requires validAt c:a c:n && c:n <= 8 && SumAt old c:a c:n < 4294967296;
//@ ensures  result == SumAt old c:a c:n;
int arrsum(int *a, int n) {
  int s = 0;
  for (int i = 0; i < n; i++) s += a[i];
  return s;
}
