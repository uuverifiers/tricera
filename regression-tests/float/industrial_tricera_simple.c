//Global variables 'acting' as return variables
float return_modMin;
float return_modMax;

int return_modStatus;

float mod0_status;

float mod0_min;

float mod0_max;

float batt_min_output;
float batt_max_output;
int batt_status_output;

void modStatus() {
  return_modStatus = mod0_status;
}

void modMin() {
  return_modMin = mod0_min;
}

void modMax() {
  return_modMax = mod0_max;
}

void moduleDiag(int idx) {
  modMin();
  modMax();
  modStatus();

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

void batteryDiag()
{
    //Initializing the battery values
    batt_max_output = 3000.25f;
    batt_min_output = -3000.25f;
    batt_status_output = 0;

    //Run the diagnostics, one module at the time
    moduleDiag(0);
}


void main()
{
  //Non-det assignment of all global C variables
  return_modMin = 0.0f;
  return_modMax = 0.0f;
  return_modStatus = 0;
  mod0_status = 0;
  mod0_min = 0.0f;
  mod0_max = 0.0f;

  //Declare the paramters of the function to be called

  //Function call that the harness function verifies
  batteryDiag();

  //The 'ensures'-clauses translated into asserts
  //assert((!(((old_mod0_status == 0) && (old_mod1_status == 0)) &&
    //!(batt_status_output == 0)) && !(((old_mod0_status == 1) ||
    //(old_mod1_status == 1)) && !(batt_status_output == 1))));
  assert(batt_max_output <= 3000.25f);
}
