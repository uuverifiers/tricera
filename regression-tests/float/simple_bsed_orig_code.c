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

void modStatus(int idx) {
    if (idx == 0) {
      return_modStatus = mod0_status;
    } else {
      return_modStatus = mod1_status;
    }
}

void modMin(int idx) {
    if (idx == 0) {
      return_modMin = mod0_min;
    } else {
      return_modMin = mod1_min;
    }
}

void modMax(int idx) {
    if (idx == 0) {
      return_modMax = mod0_max;
    } else {
      return_modMax = mod1_max;
    }
}

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

/*@
  assigns return_modMax, return_modMin, return_modStatus, batt_min_output,
          batt_max_output, batt_status_output;
  ensures
    ((\old(mod0_status) == 0 && \old(mod1_status) == 0) ==> batt_status_output == 0) &&
    ((\old(mod0_status) == 1 || \old(mod1_status) == 1) ==> batt_status_output == 1);
*/
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
