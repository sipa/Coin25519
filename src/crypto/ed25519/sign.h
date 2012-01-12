#ifndef _ED25519_SIGN_H_
#define _ED25519_SIGN_H_ 1

typedef struct {
  unsigned char sk[32];
} ed25519_secret_key;

typedef struct {
  unsigned char pk[32];
} ed25519_public_key;

typedef struct {
  unsigned char r[32], s[32];
} ed25519_signature;

int ed25519_derive_public_key(const ed25519_secret_key *seckey, ed25519_public_key *pubkey);
int ed25519_sign(const ed25519_secret_key *seckey, ed25519_signature *sign, unsigned char *m, int mlen);
int ed25519_recover(ed25519_public_key *pubkey, const ed25519_signature *sign, unsigned char *m, int mlen);
int ed25519_verify(const ed25519_public_key *pubkey, const ed25519_signature *sign, unsigned char *m, int mlen);

#endif
