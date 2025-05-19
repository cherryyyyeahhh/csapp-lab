#include <stdio.h>
int main() {
  int a = 0xffffffff;
  a = ~a;
  printf("%d\n", a + a);
  return 0;
}
