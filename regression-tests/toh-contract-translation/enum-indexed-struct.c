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
struct SlotRecord helper_read_record(enum RecordSlot slot)
{
    return records[slot];
}

int entry(void)
{
    struct SlotRecord selected = helper_read_record(RECORD_HIGH);
    assert(selected.level == 8);
}
