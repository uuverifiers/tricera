struct s {
    int val;
    int (*mutator)(int x);
};

int inc(int x)
{
    return x + 1;
}

int id(int x)
{
    return x;
}

int global = 5;

int multiply_by_global(int x)
{
    return global * x;
}

int main()
{
    // ensure that preprocessor does not remove functions
    inc(0);
    id(0);
    multiply_by_global(0);
    // test begin here
    struct s m;
    m.val = 2;
    m.mutator = id;
    m.val = m.mutator(m.val);
    assert(m.val == 2);
    m.mutator = inc;
    m.val = m.mutator(m.val);
    assert(m.val == 3);
    m.mutator = multiply_by_global;
    m.val = m.mutator(m.val);
    assert(m.val == 15);
    global = 2;
    m.val = m.mutator(m.val);
    assert(m.val == 30);
    m.mutator = id;
    m.val = m.mutator(m.val);
    assert(m.val == 30);
}