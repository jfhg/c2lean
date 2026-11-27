int fact(int n);   /* cross-file call target: declared here, defined in fact.c */

//@ requires c:n >= 2 && c:n <= 5;
//@ ensures  result == c:n * factN (c:n - 1);
int fact2(int n) { return n * fact(n - 1); }
