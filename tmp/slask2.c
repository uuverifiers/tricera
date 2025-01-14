struct tLargeDataSet
{
  unsigned int val1;
  int val2;
  long int val3;
};
struct tMyStruct
{
  unsigned int val;
};
struct tLargeDataSet g_commonData;

/*@contract@*/
void incr (struct tMyStruct * s)
{
  s-> val ++;
}
struct tMyStruct global_incr_0_s;

void wrapped_incr_0 (struct tMyStruct * s);

/*@contract@*/
void global_incr_0 ()
{
  global_incr_0_s. val ++;
}

void wrapped_incr_0 (struct tMyStruct * s)
{
  struct tMyStruct saved_global_incr_0_s_0 = global_incr_0_s;
  global_incr_0_s= * s;
  global_incr_0();
  * s= global_incr_0_s;
  global_incr_0_s= saved_global_incr_0_s_0;
  return;
}

/*@
    requires g_commonData.val1 <= 1000;
    requires g_commonData.val1 >= 0;

    assigns g_commonData;
 
    ensures g_commonData.val1 == \old(g_commonData.val1) + 1;
*/
int main ()
{
  struct tMyStruct myStruct;
  myStruct. val = g_commonData. val1;
  wrapped_incr_0(& myStruct);
  g_commonData. val1 = myStruct. val;
  return 0;
}