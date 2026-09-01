enum RecordSlot {
    RECORD_LOW = 0,
    RECORD_HIGH = 1
};

struct SlotRecord {
    int level;
    int status;
};

struct SlotRecord records[2] = {
    {3, 0},
    {8, 1}
};

/*@contract@*/
int helper_read_level(enum RecordSlot slot)
{
    return records[slot].level;
}

int entry(void)
{
    int level = helper_read_level(RECORD_HIGH);
    assert(level == 8);
}
