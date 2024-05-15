#include <stdio.h>
//Global variables 'acting' as return variables
float return_modMin;
float return_modMax;
int return_modStatus;

int mod0_status;
int mod1_status;

float mod0_min;
float mod1_min;

float mod0_max;
float mod1_max;

float batt_min_output;
float batt_max_output;
int batt_status_output;

/*@contract@*/
void modStatus(int idx) {
    if (idx == 0) {
      return_modStatus = mod0_status;
    } else {
      return_modStatus = mod1_status;
    }
}

/*@contract@*/
void modMin(int idx) {
    if (idx == 0) {
      return_modMin = mod0_min;
    } else {
      return_modMin = mod1_min;
    }
}

/*@contract@*/
void modMax(int idx) {
    if (idx == 0) {
      return_modMax = mod0_max;
    } else {
      return_modMax = mod1_max;
    }
}

/*@contract@*/
void moduleDiag(int idx) {
  modMin(idx);
  modMax(idx);
  modStatus(idx);

  //Update the status
  if (return_modStatus == 1) {
    batt_status_output = 1;
  } else {
    batt_status_output = batt_status_output;
  }

  //Update the max value
  if (return_modMax > batt_max_output) {
    batt_max_output = return_modMax;
  } else {
    batt_max_output = batt_max_output;
  }

  //Update the min value
  if (return_modMin < batt_min_output) {
    batt_min_output = return_modMin;
  } else {
    batt_min_output = batt_min_output;
  }
}

void batteryDiag(int dummy)
{
    //Initializing the battery values
    batt_max_output = 5.0f;
    batt_min_output = -5.0f;
    batt_status_output = 0;

    //Run the diagnostics, one module at the time
    moduleDiag(0);
    moduleDiag(1);
}
int extern non_det();

int main()
{
  //Non-det assignment of all global C variables
  // return_modMin = 0.0f;
  // return_modMax = 0.0f;
  // return_modStatus = 0;
  mod0_status = 0;
  mod1_status = 1;
  mod0_min = -1.0f;
  mod1_min = -1.0f;
  mod0_max = 2.0f;
  mod1_max = 2.0f;
  // batt_max_output = -200.0f;
  //batt_min_output = 200.0f;
  // batt_status_output = 0;

  //Declare the paramters of the function to be called
  int dummy = 0;

  //Initialization of logical old-variables
  // int old_mod0_status;
  // int old_mod1_status;
  // int old_batt_status_output;
  // assume(old_mod0_status == mod0_status);
  // assume(old_mod1_status == mod1_status);
  // assume(old_batt_status_output == batt_status_output);

  //Function call that the harness function verifies
  batteryDiag(dummy);

  //The 'ensures'-clauses translated into asserts
  //  assert((!(((old_mod0_status == 0) && (old_mod1_status == 0)) &&
  //    !(batt_status_output == 0)) && !(((old_mod0_status == 1) ||
  //    (old_mod1_status == 1)) && !(batt_status_output == 1))));
  printf("%f", batt_max_output);
  return 0;
}
