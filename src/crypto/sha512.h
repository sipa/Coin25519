#ifndef _SHA512_H_
#define _SHA512_H_

#include <stdint.h>

typedef struct {
  uint64_t length;
  uint64_t state[8];
  uint32_t curlen;
  unsigned char buf[128];
} sha512_state;

#ifndef _SHA512_C_
int sha512_init(sha512_state * md);
int sha512_process(sha512_state * md, const void *in, unsigned long inlen);
int sha512_done(sha512_state * md, void *out);
int sha512(const void *in, unsigned long inlen, void *out);
#endif

#endif
