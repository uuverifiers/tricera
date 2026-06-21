class Coords {
  public:
    int* int_ptr;
    int x;
    int y;

    Coords(int *ptr, int val1, int val2) {
      int_ptr = ptr;
      x = val1;
      y = val2;
    }

    ~Coords() {
      delete int_ptr;
    }

    void reset_coords() {
      x = 0;
      y = 0;
    }
};


int main() {
  Coords *coords = new Coords(new int(0), 5, 10);
  coords->x = coords->x + 1;

  assert(coords->x == 6 && coords->y == 10);
  assert(*(coords->int_ptr) == 0);

  coords->reset_coords();

  // Following line is buggy, predicate generation fails
  // if comparisons aren't enclosed with parenthases
  assert((coords->x == 6) && (coords->y == 10));
  assert(*(coords->int_ptr) == 0);

  delete coords;
  return 0;
}
