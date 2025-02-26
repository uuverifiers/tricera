#include <stdlib.h>


int driver_distance;

typedef struct Human {
    int distance_driven;
} *HumanPtr;

/*@contract@*/
void tick(struct Human* h) {
    h->distance_driven++;
}

extern int non_det_int();

void main()
{
  //Non-det assignment of global variables
  driver_distance = non_det_int();

  assume(1);

  HumanPtr driver = (HumanPtr) malloc(sizeof(*driver));
  driver->distance_driven = 0;

  tick(driver);
//  tick(driver);

  driver_distance = driver->distance_driven;

  assert((driver_distance == 1));
}
