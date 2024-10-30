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

/*@contract@*/
void decr(tMyStruct* s) {
  s->val--;
}

/*@contract@*/ 
int incr(tMyStruct* s) {
    s->val++;
    decr(s);
    return 1;
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
    myStruct.val = g_commonData.val1;
 
    incr(&myStruct);

    g_commonData.val1 = myStruct.val;

    /*

      Complex statements like

      if (checkStructs(&someStruct, &otherStruct) != 0) {
        ...
      }
      else {
        ... 
      }

      should be replaced with (h_checkStructs will be inlined by TriCera)

      h_checkStructs(tp1* struct1, tp2* struct2) {
        tMyStruct saved_g_checkStructs_someStruct = g_checkStructs_someStruct;
        tMyStruct saved_g_checkStructs_otherStruct = g_checkStructs_otherStruct;
        g_checkStructs_someStruct = someStruct;
        g_checkStructs_otherStruct = otherStruct;

        result = g_checkStructs();

        otherStruct = g_checkStructs_otherStruct;
        someStruct = g_checkStructs_someStruct;
        g_checkStructs_otherStruct = tMyStruct saved_g_checkStructs_otherStruct;
        g_checkStructs_someStruct = tMyStruct saved_g_checkStructs_someStruct;

        return result;
      }

      if (h_checkStructs() != 0) {
        ...
      }
      else {
        ... 
      }

      =================
      
      a = b(1, 2+c(&d))

      a = b(1, 2+h_c())
    */

/*
    tMyStruct* myPtr = &myStruct;
    incr(myPtr);
*/
    return 0;
}