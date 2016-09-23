/***********************************************************
 Implementation of bloom filter goes here 
 **********************************************************/

#include "bloom.h"

/* Constants for bloom filter implementation */
const int H1PRIME = 4189793;
const int H2PRIME = 3296731;
const int BLOOM_HASH_NUM = 10;

/* The hash function used by the bloom filter */
int
hash_i(int i, /* which of the BLOOM_HASH_NUM hashes to use */ 
       long long x /* a long long value to be hashed */)
{
	return ((x % H1PRIME) + i*(x % H2PRIME) + 1 + i*i);
}

/* Initialize a bloom filter by allocating a character array that can pack bsz bits.
   (each char represents 8 bits)
   Furthermore, clear all bits for the allocated character array. 
   Hint:  use the malloc and bzero library function 
	 Return value is the newly initialized bloom_filter struct.*/
bloom_filter 
bloom_init(int bsz /* size of bitmap to allocate in bits*/ )
{
  bloom_filter f;
  f.bsz = bsz;
  int i;
  /*Change bitsize to the correct number of Char* needed(Char * is 8 bits)*/
  if (bsz % 8) bsz = (bsz >> 3) + 1;
  else bsz = (bsz >> 3);
  /*Allocate the appropriate amount of memory for based on bit size*/
  f.buf = (char *) malloc(bsz);
  /* Set all the Char* to NULL (00000000 in Binary)*/
  for(i = 0; i < bsz; i++)
  {
    f.buf[i] =  NULL;
  }
  return f;
}

/* Add elm into the given bloom filter*/
void
bloom_add(bloom_filter f,
          long long elm /* the element to be added (a RK hash value) */)
{
  int i; 
  int bit;
  /* Loop over each hash function*/
  for (i = 0; i < BLOOM_HASH_NUM; i++)
  {
    bit = hash_i(i, elm) % f.bsz;
    /* In the correct Char * for the bit
       place a 1 in the bit slot with bitwise or*/
    f.buf[bit >> 3] |= 1 << (7 - bit % 8);
  }
  return;
}

/* Query if elm is probably in the given bloom filter */ 
int
bloom_query(bloom_filter f,
            long long elm /* the query element */ )
{	
  int i; 
  int bit;
  /* Loop over each hash function*/
  for (i = 0; i < BLOOM_HASH_NUM; i++)
  {
    bit = hash_i(i, elm) % f.bsz;
    /* If there is a zero in any bit slot which the query hash has a 1,
       or vice versa return 0 (the function is performed by doing & 
       which returns False unless both Char* have the same value*/
    if (!((f.buf[bit >> 3]) & (1 << (7 - bit % 8))))
    {
      return 0;
    }
  }
  return 1;
}

void 
bloom_free(bloom_filter *f)
{
	free(f->buf);
	f->buf = f->bsz = 0;
}

/* print out the first count bits in the bloom filter */
void
bloom_print(bloom_filter f,
            int count     /* number of bits to display*/ )
{
	int i;

	assert(count % 8 == 0);

	for(i=0; i< (f.bsz>>3) && i < (count>>3); i++) {
		printf("%02x ", (unsigned char)(f.buf[i]));
	}
	printf("\n");
	return;
}

