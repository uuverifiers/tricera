int in;
int out;

int read_input() {
    return in;
}

void write_output(int x) {
    out = x;
}

int saturate(int x, int lim) {
    if (x > lim)
        return lim;
    else
        return x ;
}

/*@
  requires in >= 0;
  ensures in <= 10 ==> out == in * in && in > 10 ==> out == 100;
*/
void main () {
    int tmp = read_input();
    tmp = saturate (tmp, 10);
    tmp = tmp * tmp;
    write_output (tmp);
}
