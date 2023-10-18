int main() {
    int x = 0;
    int y = 3;
    while(x <= 2) {
        x++;
        y = x;
    }
    assert(x==y);
}

