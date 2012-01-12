#include "sha512.h"
#include <string.h>
#include <stdio.h>

int main(void)
{
  const char *bla="Once upon a midnight dreary, while I pondered weak and weary over many a quant and curious volume of forgotten lore. While i nodded, nearly napping, suddenly there came a tapping\n";
  unsigned char hash[64];
  sha512(bla,strlen(bla),hash);
  for (int i=0; i<64; i++) {
    printf("%02x", hash[i]);
  }
  return 0;
}
