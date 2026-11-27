int counter = 0;
int table[4] = {10, 20, 30, 40};

//@ requires c:i < 4 && m₀.next < 1048576;
//@ ensures  result == getAt old table c:i;
int get(int i) { return table[i]; }

//@ requires old counter < 4294967295;
//@ ensures  cur counter == old counter + 1;
void bump(void) { counter++; }

//@ ensures  result == old counter;
int read_counter(void) { return counter; }
