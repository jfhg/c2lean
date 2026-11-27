//@ requires 0 <= c:n && c:n <= 12;
//@ ensures  result == factN c:n;
int fact(int n) {
    if (n <= 1) return 1;
    return n * fact(n - 1);
}
