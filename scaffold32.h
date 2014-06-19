#ifndef SCAFFOLD32_h
#define SCAFFOLD32_h

#include <time.h>

#define WORDBYTES 4 // bytes per word
#define WORDBITS 32 // bits per word

//mpz import/export parameters
#define NAILS 0 //bit padding, usually 0
#define ORDER -1 //most significant word first, -1 for least first
#define ENDIAN 0 // native endianness

extern void Product32(void *a, void *b, void *c, unsigned int wa,
            unsigned int ba, unsigned int wb, unsigned int bb, unsigned
            int *wc, unsigned int *bc);

extern double mytime (void);

#endif
