#include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>
#include <assert.h>

#include "../bn_rsample.h"


void print(uint64_t *array)
{
  int i;

  for(i=0; i<(NLIMBS-1); i++)
  { printf("0x%016" PRIx64 ", ", array[i]); }
  printf("0x%016" PRIx64 "\n", array[NLIMBS-1]);
}

int main(void)
{
  bignum random_number_p;

  __bn_rsample(random_number_p);
  printf("\Random number:\n");  
  print(random_number_p);

  __bn_rsample1(random_number_p);
  printf("\Random number:\n");  
  print(random_number_p);


  return 0;
}
