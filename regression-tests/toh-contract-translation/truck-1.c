
int driver_distance;
int r_cab_position;

typedef struct Human {
    int distance_driven;
} Human;

typedef struct Truck {
    int x;
    struct Human driver;
} *TruckPtr;

/*@contract@*/
void tick(TruckPtr t) {
    t->x++;
    t->driver.distance_driven++;
}

extern int non_det_int();

void main()
{
  //Non-det assignment of global variables
  driver_distance = non_det_int();
  r_cab_position = non_det_int();

  assume(1);

  TruckPtr r_cab = malloc(sizeof(*r_cab));
  r_cab->x = 0;
  r_cab->driver.distance_driven = 0;
  tick(r_cab);
  tick(r_cab);

  driver_distance = r_cab->driver.distance_driven;
  r_cab_position = r_cab->x;

  assert((driver_distance == 2));
  assert((r_cab_position == 2));
}
