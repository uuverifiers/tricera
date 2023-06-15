int main() {
  float f;
  for(f = 0.0f; f != 0.3f; f += 0.1f);
  assert(f == 0.3f);
}
