#include <assert.h>


typedef struct {
    int cells[_]; //Voltage value for each cell
    int max_value;//Maximum voltage value in battery
    int min_value;
} BATTERY;


void main() {
  BATTERY batt;
  batt.max_value = batt.cells[0];
  int i = 0;
  while(i < 10) {
    if (batt.cells[i] > batt.max_value) {
      batt.max_value = batt.cells[i];
    }
    i++;
  }
  assert(batt.max_value == \max(batt.cells, 0, 10));
}
