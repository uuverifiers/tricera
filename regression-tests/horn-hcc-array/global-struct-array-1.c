typedef struct {
  int f;
} S;

S sArr[2] = {{10}, {20}};

void main() {
  assert(sArr[0].f == 0);
  sArr[1].f++;
  assert(sArr[1].f == 1);
}
