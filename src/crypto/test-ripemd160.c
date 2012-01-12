#include "ripemd160.h"
#include <string.h>
#include <stdlib.h>
#include <stdio.h>

int main(void)
{
  char *bla=malloc(1000000);
  memset(bla,'a',1000000);
  unsigned char hash[20];
  ripemd160(bla,1000000,hash);
  for (int i=0; i<20; i++) {
    printf("%02x", hash[i]);
  }
  printf("\n");
  return 0;
}
