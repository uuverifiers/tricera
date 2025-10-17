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
    // ensure that preprocessor does not remove functions
    id(0);
    inc(0);
    // test begin here
    int (*f)() = inc;
    int (*g)() = id;
    int x = 2;
    int not_five = g(f(g(g(f(x)))));
    assert(not_five == 5);
}
