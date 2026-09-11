struct A {
    int x;
    int y;
};

struct B {
    struct A first;
    struct A second;
    int tail;
};

struct C {
    struct B b;
    int tail;
};

int main() {
    struct A aa = {4, 7};
    struct B bb = {aa, {8, 9}, 2};
    struct C cc = {bb, 3};
    aa.x = 11;
    bb.second.y = 12;
    assert(bb.first.x == 4 && bb.first.y == 7);
    assert(cc.b.first.x == 4 && cc.b.first.y == 7);
    assert(cc.b.second.x == 8 && cc.b.second.y == 9);
    assert(cc.b.tail == 2 && cc.tail == 3);

    struct B partial = {aa};
    assert(partial.first.x == 11 && partial.first.y == 7);
    assert(partial.second.x == 0 && partial.second.y == 0);
    assert(partial.tail == 0);

    struct B fields = {cc.b.second, aa, 6};
    assert(fields.first.x == 8 && fields.first.y == 9);
    assert(fields.second.x == 11 && fields.second.y == 7);
    assert(fields.tail == 6);

    struct B flat = {1, 2, 3, 4, 5};
    assert(flat.first.x == 1 && flat.first.y == 2);
    assert(flat.second.x == 3 && flat.second.y == 4);
    assert(flat.tail == 5);

    struct {
        struct {
            int x;
            int y;
        } a;
        int tail;
    } source = {{13, 14}, 15}, copy = {source.a, 16};
    assert(copy.a.x == 13 && copy.a.y == 14);
    assert(copy.tail == 16);
    return 0;
}
