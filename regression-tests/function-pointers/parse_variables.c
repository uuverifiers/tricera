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

    int (*f1)();
    int (*g1)();
    int (*h1)();

    int (*f2)() = id;
    int (*g2)() = id;
    int (*h2)() = inc;

    int (*f3)(int x);
    int (*g3)(int x);
    int (*h3)(int x);

    int (*f4)(int x) = id;
    int (*g4)(int x) = id;
    int (*h4)(int x) = inc;
}
