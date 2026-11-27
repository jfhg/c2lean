//@ requires c:x < 2147483648;
//@ ensures  result == 2 * c:x;
int twice(int x) { return x + x; }

//@ requires c:a < 1073741824 && c:b < 1073741824;
//@ ensures  result == 2 * c:a + 2 * c:b;
int addtwice(int a, int b) { return twice(a) + twice(b); }
