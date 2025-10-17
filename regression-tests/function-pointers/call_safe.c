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
    int (*f)() = id;
    int (*g)() = inc;
    int x = 2;
    int two = f(x);
    int three = g(x);
    assert(two == 2);
    assert(three == 3);
}