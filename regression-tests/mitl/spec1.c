MITL_SPEC ": {1}F@(0,1)(x > 1)" ;
RANKING "1: (3 - x)" ;


int x = 0;
thread A {
  clock c = 0;
  while(1) {
    progress(c < 2);  
    assume(c >= 2);
    x = x+1;
    c = 0;
  }
}


//T0@ConfS3(C, accCntr, rank1, rankValid1, x:8, S0, q0, T0@c, T0@step

// (Clause(T0@ConfS1(C, newAccCntr, newRank1, newRankValid1, x:8, S0, q0, C, C),
// List(),(((((true & (S0 = false)) & true) & ((q0 = true) <-> (((x:8 + -3) + -1) >= 0))) & true) & 
// ((((newRankValid1 = true) & (newRank1 = (3 + -1 * x:8))) & (newAccCntr = 0)) & (S0 = false)))),
// NoSync),
