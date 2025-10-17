int id(int x)
{
	return x;
}

int main()
{
    id(1);

    assert(id == &id);
    assert(id == *id);
    assert(id == *******id);
    assert(id == ******&id);
    assert(id == &*****&id);
    assert(id == **&***&id);
    assert(id == **&*&*&id);
    assert(id == &*&*&*&id);
}
