//Global variables 'acting' as return variables
int return_modMin;
int return_modMax;
int return_modStatus;

int mod0_status;
int mod1_status;

int mod0_min;
int mod1_min;

int mod0_max;
int mod1_max;

int batt_min_output;
int batt_max_output;
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
    batt_max_output = -2147483648;
    batt_min_output = 2147483647;
    batt_status_output = 0;

    //Run the diagnostics, one module at the time
    moduleDiag(0);
    moduleDiag(1);
}

extern int non_det();

void main()
{
  //Non-det assignment of all global C variables
  return_modMin = non_det();
  return_modMax = non_det();
  return_modStatus = non_det();
  mod0_status = non_det();
  mod1_status = non_det();
  mod0_min = non_det();
  mod1_min = non_det();
  mod0_max = non_det();
  mod1_max = non_det();
  batt_min_output = non_det();
  batt_max_output = non_det();
  batt_status_output = non_det();

  //Declare the paramters of the function to be called
  int dummy;

  //Initialization of logical old-variables
  int old_mod0_status;
  int old_mod1_status;
  int old_batt_status_output;
  assume(old_mod0_status == mod0_status);
  assume(old_mod1_status == mod1_status);
  assume(old_batt_status_output == batt_status_output);

  //Function call that the harness function verifies
  batteryDiag(dummy);

  //The 'ensures'-clauses translated into asserts
  assert((!(((old_mod0_status == 0) && (old_mod1_status == 0)) &&
    !(batt_status_output == 0)) && !(((old_mod0_status == 1) ||
    (old_mod1_status == 1)) && !(batt_status_output == 1))));
}
