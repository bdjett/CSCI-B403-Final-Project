/* test framework code
   ./mainX [bitsize of operand x] [bitsize of operand y] [number of tests] [base to print]
   defaults are 1000, 1000, 100, and 0

   0 base means no printing.  2 base is binary, 10 base is decimal, 16
   is hex.  1 base is an error.  printing is of the randomly generated
   operands and the multiplication results from the code and GMP.  A
   summary of the run is always printed.
   */

#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <gmp.h>
#include <unistd.h>
#include "scaffold32.h"


int main(int argc, char **argv){
    int xbits = 1000;
    int ybits = 1000;
    int number_of_tests = 100;
    int printing=0; // whether to print, and the base to print in
    
    if(argc >=2)  // recall that first 'argument' is the program name
      xbits = atoi(argv[1]);
    if(argc >=3)
      ybits = atoi(argv[2]); 
    if(argc >=4)
      number_of_tests = atoi(argv[3]);
    if(argc >=5)
      printing = atoi(argv[4]);
      /*
    if(argc >=6)
      truncation = atoi(argv[5]);
      */


     //operands
    mpz_t x; mpz_init(x);
    mpz_t y; mpz_init(y);
    mpz_t xsize_z; mpz_init(xsize_z); //for random number generation
    mpz_t ysize_z; mpz_init(ysize_z); //for random number generation

    //GMP random state
    gmp_randstate_t randstate; gmp_randinit_default(randstate);
    gmp_randseed_ui(randstate, time(NULL));

    srand(time(NULL)); //for non-GMP random numbers
    
    int number_of_bits = (xbits > ybits) ? xbits : ybits;  // the greater one between x_bits and y_bits
    int i,j;  // loop variables
    
    double start, finish, elapsed, elapsed_gmp = 0; //timing
    int num_correct = 0, num_wrong = 0; //correctness
    
    //allocate memory for printing to avoid memory leaks.  Use of
    //number_of_bits is enough to print in binary.
    char *x_str = (char *) malloc((1 + number_of_bits)*sizeof(char)); 
    char *y_str = (char *) malloc((1 + number_of_bits)*sizeof(char)); 
    char *z_str = (char *) malloc((1 + 2*number_of_bits)*sizeof(char)); 
    char *res_str = (char *) malloc((1 + 2*number_of_bits)*sizeof(char)); 

      void *x_address;
      void *y_address;
      size_t *x_size = malloc(sizeof(size_t));
      size_t *y_size = malloc(sizeof(size_t));
      size_t *z_size = malloc(sizeof(size_t));
      size_t x_bits, y_bits; //used for size of final operands from GMP
      size_t *z_bits = malloc(sizeof(size_t));

      for(j = 0; j < number_of_tests; j++){
          mpz_ui_pow_ui(xsize_z, 2, xbits); //numsize = 2^numbits
          mpz_ui_pow_ui(ysize_z, 2, ybits); //numsize = 2^numbits
          mpz_urandomm(x, randstate, xsize_z); //actually makes x and y
          mpz_urandomm(y, randstate, ysize_z);
          if (printing)
             printf("x %s\ny %s\n",mpz_get_str(x_str,printing,x),
                    mpz_get_str(y_str,printing,y));

          x_address = mpz_export(NULL, x_size, ORDER, WORDBYTES, ENDIAN, NAILS, x);
          y_address = mpz_export(NULL, y_size, ORDER, WORDBYTES, ENDIAN, NAILS, y);
          void *z_address = malloc((*x_size + *y_size)*WORDBYTES);

          x_bits=mynbits(x);
          y_bits=mynbits(y);
          start = mytime();
          Product32(x_address, y_address, z_address, *x_size, x_bits,
                    *y_size, y_bits, z_size, z_bits);
          finish = mytime();
          elapsed += finish-start;
          
          mpz_t z;
          mpz_init(z);

          mpz_import(z, *z_size, ORDER, WORDBYTES, ENDIAN, NAILS, z_address);
          if (printing)
             printf("code x*y %s\n", mpz_get_str(z_str,printing,z));
             
          mpz_t result;
          mpz_init(result);
          start = mytime();
          mpz_mul(result,x,y);
          finish = mytime();
          elapsed_gmp += finish-start;
          if (printing)
             printf("GMP  x*y %s\n", mpz_get_str(res_str,printing,result));

          if(mpz_cmp(result,z) == 0)
             num_correct ++;
          else
              num_wrong ++;

          mpz_clear(z);
          mpz_clear(result);
          free(x_address);
          free(y_address);
          free(z_address);
    }
    
    mpz_clear(x);
    mpz_clear(y);
    mpz_clear(xsize_z);
    mpz_clear(ysize_z);
    
    printf("============================================================\n");
    printf("\n\n");
    printf("Number of bits in x: %d\n", xbits);
    printf("Number of bits in y: %d\n", ybits);
    printf("Number of multiplications done: %d\n", number_of_tests);
    printf("Number of correct multiplication: %d\n", num_correct);
    printf("Number of wrong multiplication: %d\n", num_wrong);
    printf("Total time elapsed (code):  %lf seconds\n", ((double) (elapsed)));
    printf("Total time elapsed (GMP):  %lf seconds\n", ((double)
          (elapsed_gmp)));
    printf("Total time ratio (code/GMP):  %lf \n",
        elapsed/elapsed_gmp);
    printf("\n\n");
    printf("============================================================\n");
    return 0;    
}
