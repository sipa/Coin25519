#include "ed25519.h"

#include <stdlib.h>
#include <string.h>
#include <stdio.h>

void randbytes(void* data, int len) {
  unsigned char *c = data;
  for (int i=0; i<len; i++) {
    c[i] = rand() % 256;
  }
}

int main(void) {
  for (int i=0; i<100; i++) {
    ed25519_secret_key sk;
    randbytes(&sk, 32);
    ed25519_public_key pk;
    ed25519_derive_public_key(&sk,&pk);
    unsigned char msg[64];
    randbytes(msg,64);
    ed25519_signature sign;
    ed25519_sign(&sk,&sign,msg,64);
    ed25519_public_key pk2;
    for (int j=0; j<100; j++)
      ed25519_recover(&pk2,&sign,msg,64);
    if (memcmp(&pk,&pk2,32) != 0) printf("Failure!!!\n");
  }
  return 0;
}
