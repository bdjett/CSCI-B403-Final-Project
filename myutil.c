#include <time.h>
#include <gmp.h>

double mytime (void)
{
  int flag;
  clockid_t cid = CLOCK_REALTIME; // CLOCK_MONOTONE might be better
  struct timespec tp;
  double timing;

  flag = clock_gettime(cid, &tp);
  if (flag == 0) timing = tp.tv_sec + 1.0e-9*tp.tv_nsec;
  else           timing = -17.0;

    return(timing);
};

int mynbits (mpz_t x) {
  return mpz_sizeinbase(x,2);
}
