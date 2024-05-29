typedef struct {
    unsigned int val;
} tMyStruct;
 
void incr(tMyStruct* s) {
    s->val++;
}
 
tMyStruct g_myStruct;

tMyStruct g_incr_myStruct;

void g_incr() {
    g_incr_myStruct.val++;
}

/*@
    requires g_myStruct.val <= 1000;
    requires g_myStruct.val >= 0;
 
    assigns g_myStruct;

    ensures g_myStruct.val == \old(g_myStruct.val) + 1;
*/
int main() {
    tMyStruct myStruct;
 
    myStruct = g_myStruct;

    tMyStruct saved = g_incr_myStruct;
    g_incr_myStruct = myStruct;
    g_incr();
    myStruct = g_incr_myStruct;
    g_incr_myStruct = saved;
 
    g_myStruct = myStruct;

    return 0;
}