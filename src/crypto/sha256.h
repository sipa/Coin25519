#ifndef _SHA256_H_
#define _SHA256_H_

#include <stdint.h>

typedef struct {
  uint64_t length;
  uint32_t state[8];
  uint32_t curlen;
  unsigned char buf[64];
} sha256_state;


#ifndef _SHA256_C_
int sha256_init(sha256_state * md);
int sha256_process(sha256_state * md, const void *in, unsigned long inlen);
int sha256_done(sha256_state * md, void *out);
int sha256(const void *in, unsigned long inlen, void *out);
#endif

#endif
