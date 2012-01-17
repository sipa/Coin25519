#include "sha256.h"
#include <string.h>
#include <stdio.h>

int main(void)
{
  const char *bla="Now, I even I would celebrate in rhythms unapt the great immortal Syracusan rivaled nevermore who in his wondrous lore passed on before gave men his guidance how to circles mensurate.\n";
  unsigned char hash[32];
  sha256(bla,strlen(bla),hash);
  for (int i=0; i<32; i++) {
    printf("%02x", hash[i]);
  }
  printf("\n");
  return 0;
}
