#include <string.h>

#include "lib/ge25519.h"
#include "../sha512.h"
#include "sign.h"

int ed25519_derive_public_key(const ed25519_secret_key *seckey, ed25519_public_key *pubkey) {
  unsigned char lhrh[64];
  sha512(&seckey->sk,sizeof(seckey->sk),lhrh);
  lhrh[0] &= 248;
  lhrh[31] &= 127;
  lhrh[31] |= 64;
  sc25519 scA;
  sc25519_from32bytes(&scA,lhrh);
  ge25519 geA;
  ge25519_scalarmult_base(&geA, &scA);
  ge25519_pack(pubkey->pk, &geA);
  return 1;
}

int ed25519_sign(const ed25519_secret_key *seckey, ed25519_signature *sign, unsigned char *m, int mlen) {
  unsigned char lhrh[64];
  sha512(&seckey->sk,sizeof(seckey->sk),lhrh);
  lhrh[0] &= 248;
  lhrh[31] &= 127;
  lhrh[31] |= 64;
  sha512_state md;
  sha512_init(&md);
  sha512_process(&md,lhrh+32,32);
  sha512_process(&md,m,mlen);
  unsigned char k[64];
  sha512_done(&md,k);
  sc25519 scK;
  sc25519_from64bytes(&scK,k);
  ge25519 geR;
  ge25519_scalarmult_base(&geR, &scK);
  ge25519_pack(sign->r, &geR);
  sha512_init(&md);
  sha512_process(&md,&sign->r,32);
  sha512_process(&md,m,mlen);
  unsigned char h[64];
  sha512_done(&md,h);
  sc25519 scS;
  sc25519_from64bytes(&scS,h);
  sc25519_mul(&scS,&scS,&scK);
  sc25519 scA;
  sc25519_from32bytes(&scA,lhrh);
  sc25519_add(&scS,&scS,&scA);
  sc25519_to32bytes(sign->s,&scS);
  return 1;
}

int ed25519_recover(ed25519_public_key *pubkey, const ed25519_signature *sign, unsigned char *m, int mlen) {
  sha512_state md;
  sha512_init(&md);
  sha512_process(&md,&sign->r,32);
  sha512_process(&md,m,mlen);
  unsigned char h[64];
  sha512_done(&md,h);
  ge25519 geNR;
  ge25519_unpackneg_vartime(&geNR,sign->r);
  sc25519 scS;
  sc25519_from32bytes(&scS,sign->s);
  sc25519 scH;
  sc25519_from64bytes(&scH,h);
  ge25519 geA;
//  ge25519_double_scalarmult_vartime(&geA, &geNR, &scH, &ge25519_base, &scS);
  ge25519_double_scalarmult_vartime(&geA, &geNR, &scH, &scS);
  ge25519_pack(pubkey->pk, &geA);
  return 1;
}

int ed25519_verify(const ed25519_public_key *pubkey, const ed25519_signature *sign, unsigned char *m, int mlen) {
  ed25519_public_key pubkey2;
  ed25519_recover(&pubkey2, sign, m, mlen);
  return memcmp(&pubkey2.pk, &pubkey->pk, 32) == 0;
}
