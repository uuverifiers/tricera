
int driver1_distance;
int driver2_distance;
int r_cab_position;

typedef struct Human {
    int distance_driven;
} *HumanPtr;

typedef struct Truck {
    int x;
    struct Human* driver;
} *TruckPtr;

//No inferred contract found for tick
void tick(TruckPtr t) {
    t->x++;
    t->driver->distance_driven++;
}

/*@
  requires \true;
  ensures driver1_distance == 2 && driver2_distance == 3;
  ensures r_cab_position == driver1_distance + driver2_distance;
  assigns driver1_distance, driver2_distance, r_cab_position;
*/
int main(void) {
    TruckPtr r_cab = malloc(sizeof(*r_cab));
    HumanPtr driver1 = malloc(sizeof(*driver1));
    HumanPtr driver2 = malloc(sizeof(*driver2));
    r_cab->x = 0;
    driver1->distance_driven = 0;
    driver2->distance_driven = 0;
    
    r_cab->driver = driver1;
    tick(r_cab);
    tick(r_cab);

    r_cab->driver = driver2;
    tick(r_cab);
    tick(r_cab);
    tick(r_cab);

    driver1_distance = driver1->distance_driven;
    driver2_distance = driver2->distance_driven;
    r_cab_position = r_cab->x;
}
