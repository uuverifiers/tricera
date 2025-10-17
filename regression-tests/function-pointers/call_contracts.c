/*@ contract @*/
int id(int x)
{
	return x;
}

/*@ contract @*/
int inc(int x)
{
	return x + 1;
}

/*@ contract @*/
int two()
{
    return 2;
}

/*@ contract @*/
int main()
{
    // ensure that preprocessor does not remove functions
    id(0);
    inc(0);
    two();
    // test begin here
    int (*f)() = inc;
    int (*g)() = two;
    int three = f(g());
    assert(three == 3);
}
