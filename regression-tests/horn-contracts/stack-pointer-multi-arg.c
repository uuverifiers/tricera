typedef struct {
    unsigned int val1;
    int val2;
    long int val3;
    /* a lot more values goes here ... */
} tLargeDataSet;

typedef struct {
    unsigned int val;
    /* some other values goes here */
} tMyStruct;

typedef struct {
    long int val;
    /* some other values goes here */
} tMyOtherStruct;

/*@contract@*/ 
void mod(tMyStruct* s, tMyOtherStruct* t) {
    s->val++;
    t->val--;
}

/* Think about this as a large set of common data. */
tLargeDataSet g_commonData;

 
/*@
    requires g_commonData.val1 <= 1000;
    requires g_commonData.val1 >= 0;

    assigns g_commonData;
 
    ensures g_commonData.val1 == \old(g_commonData.val1) + 1;
*/
int main() {
    tMyStruct myStruct;
    tMyOtherStruct* myOtherStructPtr;
    tMyOtherStruct* myOtherStruct = myOtherStructPtr;
    myStruct.val = g_commonData.val1;

    mod(&myStruct, myOtherStruct);

    g_commonData.val1 = myStruct.val;

    return 0;
}