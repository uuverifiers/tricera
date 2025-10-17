int max(int a, int b)
{
	if (a > b)
		return a;
	else
		return b;
}

int min(int a , int b)
{
	if (a < b)
		return a;
	else
		return b;
}

int select_one(int a, int b, int (*select) (int, int))
{
	return select(a, b);
}

int main()
{
    // ensure that preprocessor does not remove functions
    min(2, 3);
    max(2, 3);
    // test begin here
	int a = select_one(2, 3, max);
	int b = select_one(2, 3, min);
	assert(a + b == 5);
}
