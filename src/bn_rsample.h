#define NLIMBS 32

typedef uint64_t bignum[NLIMBS];

extern void __bn_rsample(
   uint64_t *random_number_p     /* NLIMBS output  */
);

extern void __bn_rsample1(
   uint64_t *random_number_p     /* NLIMBS output  */
);

