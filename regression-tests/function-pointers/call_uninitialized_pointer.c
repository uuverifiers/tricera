int add(int a, int b)
{
	return a + b;
}

int main()
{
    // ensure that preprocessor does not remove functions
	add(2, 3);
    // test begin here
	int (*fp)();
	int x = fp(2, 3);
}
