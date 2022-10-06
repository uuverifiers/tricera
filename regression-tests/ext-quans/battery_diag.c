#include <assert.h>

typedef struct {
    int batt_voltages[10]; //Maximum voltage value in battery
    int max_voltage;
} BATTERY_PACK;

BATTERY_PACK bpack;

void calc_pack_max() {
  bpack.max_voltage = bpack.batt_voltages[0];
  int i = 0;
  while(i < 10) {
    if (bpack.batt_voltages[i] > bpack.max_voltage) {
      bpack.max_voltage = bpack.batt_voltages[i];
    }
    i++;
  }
  assert(bpack.max_voltage == \max(bpack.batt_voltages, 0, 10));
}

BATTERY_PACK bpack;
extern int non_det();
void main() {

  int i = 0;
  BATTERY_PACK bpack;
  while (i < 10) {
    int t = _;
    bpack.batt_voltages[i] = t;
    i++;
  }

  bpack.max_voltage = bpack.batt_voltages[0];
  i = 0;
  while(i < 10) {
    if (bpack.batt_voltages[i] > bpack.max_voltage) {
      bpack.max_voltage = bpack.batt_voltages[i];
    }
    i++;
    }
    assert(bpack.max_voltage == \max(bpack.batt_voltages, 0, 10));
  //calc_pack_max();
}
