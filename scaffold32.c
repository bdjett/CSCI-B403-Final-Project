/**********************************************************************************
 * scaffold32.c
 *
 * Implementation of algorithm 1.8 and 5.2 to multiply very large integers using
 * 32-bit words
 *
 * Created by: Brian Jett
 * Created on: 25 February 2014
 * Last modified by: Brian Jett
 * Last modified on: 23 April 2014
 * Part of: B403 Project
 */

#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <gmp.h>
#include <time.h>
#include "scaffold32.h"

#define POWER32 4294967296

/* Algorithm 1.4
   Input: int_a (address of a)
          int_b (address of b)
		  int_c (address of c)
		  wa (words in a)
		  wb (words in b)
		  wc (address of words in c to be stored)
   Output: None
*/
void add32(unsigned int *int_a, unsigned int *int_b, unsigned int *int_c,
		   unsigned int wa, unsigned int wb, unsigned int *wc) {

	int i; // loop invariant
    unsigned int c = 0; // carry; Step 1
    unsigned int *tmp; // temp for switch int_a and int_b
    unsigned long long s; // holding result of additions

	if (wb > wa) {
        // b is longer than a
        // swap b into a so that longest number is in a
		tmp = int_a;
		int_a = int_b;
		int_b = tmp;
		*tmp = wa;
		wa = wb;
		wb = *tmp;
	}

	for (i = 0; i < wa; i++) {
        // Step 2
        // for every word in a
		if (i < wb) {
            // Step 3
            // if current word is less than words in b
            // add the two words together with the carry
			s = (unsigned long long) int_a[i] + int_b[i] + c;
		} else {
            // else
            // just add the carry to the word in a
			s = (unsigned long long) int_a[i] + c;
		}
        // Step 4
        // compute word for c
		int_c[i] = s % POWER32;
        // set carry
		c = s / POWER32;
	}

	while (c > 0) {
        // carry is greater than 0
        // set carry to s and repeat adding carry to end of int_c
		s = (unsigned long long) c;
		int_c[i] = s % POWER32;
		c = s / POWER32;
		i++;
	}

    // total number of words in c is equal to the loop invariant
	*wc = i;
}

/* Algorithm 1.4
   Input: int_a (address of a)
          int_b (address of b)
		  int_d (address of d)
		  int_c (address of c to be stored)
		  wa (words in a)
		  wb (words in b)
		  wd (words in d)
		  wc (address of words in c to be stored)
   Output: None
   Performs c = a - b - d
*/
void subtract32(unsigned int *int_a, unsigned int *int_b, unsigned int *int_d, unsigned int *int_c,
				unsigned int wa, unsigned int wb, unsigned int wd, unsigned int *wc) {

	int i; // loop invariant
	long long sum = 0, a, b, d;
	unsigned long sum1, sum2;

	// Arguments must be in this order d < b < a
	
	// a - b - d until end of d
	for (i = 0; i < wd; ++i) {
		a = int_a[i];
		b = int_b[i];
		d = int_d[i];
		sum = a - b - d + (sum >> 32);
		int_c[i] = sum;
	}

	// a - b until end of b
	for (i = wd; i < wb; ++i) {
		a = int_a[i];
		b = int_b[i];
		sum = a - b + (sum >> 32);
		int_c[i] = sum;
	}

	// add borrow
	while (i < wa && sum < 0) {
		a = int_a[i];
		sum = a + (sum >> 32);
		int_c[i++] = sum;
	}

	// place rest of a into c
	while (i < wa) {
		int_c[i++] = int_a[i];
	}

	*wc = wa;
}

/* Algorithm 1.8
   Input: int_a (address of a)
          int_b (address of b)
		  int_c (address of c to be stored)
		  wa (words in a)
		  wb (words in b)
		  wc (address of words in c to be stored)
   Output: None
*/
void multiply32(unsigned int *int_a, unsigned int *int_b,
				unsigned int *int_c, unsigned int wa, unsigned int wb, unsigned int *wc) {

	int i, j; // loop invariants
	unsigned int c = 0; // carry
	unsigned long long p;

	// initialization loop
	for (i = 0; i < (*wc = wa + wb); i++) {
		int_c[i] = 0;
	}

	// do multiplication
	for (i = 0; i < wa; i++) {
		c = 0;
		for (j = 0; j < wb; j++) {
			p = (unsigned long long)int_a[i] * int_b[j] + int_c[i+j] + c;
			int_c[i+j] = p % POWER32;
			c = p >> 32;
		}
		int_c[i+wb] = c;
	}
}

/* Algorithm 5.2
   Input: int_a (address of a)
          int_b (address of b)
		  int_c (address of c to be stored)
		  wa (words in a)
		  wb (words in b)
		  wc (address of words in c to be stored)
   Output: None
*/
void karatsuba32(unsigned int *int_a, unsigned int *int_b,
				 unsigned int *int_c, unsigned int wa, unsigned int wb, unsigned int *wc) {

	unsigned int *u1, *u2, *v1, *v2, *w1, *w2, *w3, *w4, *c, *t1, *t2; // intermediate steps
	unsigned int wu1, wv1, wt1, wt2, ww1, ww2, ww3, ww4, n; // sizes of intermediate steps in words

	if (wa < wb) {
		// a is longer than b, set the dividing point at half of a
		n = wa / 2;
	} else {
		// else set the dividing point at half of b
		n = wb / 2;
	}

	// set the upper n words into u1 and the lower n words into u2
	u2 = int_a;
	u1 = int_a + n;
	wu1 = (wa - n); // size of u1 is equal to the size of a minus the dividing point (which is u2)

	// set the upper n words of b into v1 and the lower n words into v2
	v2 = int_b;
	v1 = int_b + n;
	wv1 = wb - n; // size of v1 is equal to the size of b minus the dividing point (which is v2)

	// allocate memory for t1 and set pointer for t2 
	t1 = (unsigned int *)calloc(sizeof(unsigned int), wu1 + wv1 + 2);
	t2 = t1 + wu1 + 1;

	// Step 1
	// t1 = u1 + u2
	add32(u1, u2, t1, wu1, n, &wt1);

	// Step 2
	// t2 = v1 + v2
	add32(v1, v2, t2, wv1, n, &wt2);

	// Step 3
	// w3 = t1 * t2
	w3 = (unsigned int *)calloc(sizeof(unsigned int), wt1 + wt2);
	decide(t1, t2, w3, wt1, wt2, &ww3);

	// Step 4
	// w2 = u1 * v1
	w2 = (unsigned int *)calloc(sizeof(unsigned int), wu1 + wv1);
	decide(u1, v1, w2, wu1, wv1, &ww2);

	// Step 5
	// w4 = u2 * v2
	w4 = int_c;
	decide(u2, v2, w4, n, n, &ww4);

	// Step 6
	// w3 = w3 - w2 - w4
	if (ww2 > ww4) {
		// Ensure than if w2 is longer than w4 it is passed first to fulfill argument order
		// requirements
		subtract32(w3, w2, w4, w3, ww3, ww2, ww4, &ww3);
	} else {
		// Other way around is ww4 is greater than ww2
		subtract32(w3, w4, w2, w3, ww3, ww4, ww2, &ww3);
	}

	// Step 7
	c = w4 + n;

	// Step 8
	// w3 = w3 + c
	add32(w3, c, int_c + n, ww3, ww4 - n, &ww3);

	// Step 9
	// w2 = w2 + c
	add32(w2, int_c + (2 * n), int_c + (2 * n), ww2, (ww3 - n), &ww2);

	free(w2);
	free(w3);
	free(t1);

	*wc = (3 * n) + (ww2 - n);
}
	
int decide(unsigned int *int_a, unsigned int *int_b, unsigned int *int_c,
		   unsigned int wa, unsigned int wb, unsigned int *wc) {
	
	if (wb == 0 || wa == 0) {
		// one of the multiplcands is 0
		*wc = 0;
	} else if (wa < 27 || wb < 27) {
		multiply32(int_a, int_b, int_c, wa, wb, wc);
	} else {
        karatsuba32(int_a, int_b, int_c, wa, wb, wc);
    }
}

/* wa is word length of a, ba is bit length of a */
void Product32(void *a, void *b, void *c, unsigned int wa,
        unsigned int ba, unsigned int wb, unsigned int bb, unsigned int
        *wc, unsigned int *bc){

	unsigned int *int_a = (unsigned int *) a;
	unsigned int *int_b = (unsigned int *) b;
	unsigned int *int_c = (unsigned int *) c;

	memset(int_c, 0, (wa + wb) * sizeof(unsigned int));
	
	decide(int_a, int_b, int_c, wa, wb, wc);
}
