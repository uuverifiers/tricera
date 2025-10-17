int id(int x)
{
	return x;
}

int inc(int x)
{
	return x + 1;
}

int main()
{
    id(1);
    inc(1);

    int (*f1)() = id;
    int (*g1)() = id;
    int (*h1)() = inc;

    int (*f2)(int x) = id;
    int (*g2)(int x) = id;
    int (*h2)(int x) = inc;

    assert(f1 == f1);
    assert(g1 == g1);
    assert(h1 == h1);

    assert(f2 == f2);
    assert(g2 == g2);
    assert(h2 == h2);

    assert(f1 == g1);
    assert(f1 == f2);
    assert(f1 == g2);

    assert(g1 == f2);
    assert(g1 == g2);

    assert(f2 == g2);

    assert(h1 == h2);
}
