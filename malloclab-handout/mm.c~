/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
  /* Team name */
  "HeldInConfidence",
  /* First member's full name */
  "William Held",
  /* First member's email address */
  "wbh230@nyu.edu",
  /* Second member's full name (leave blank if none) */
  "",
  /* Second member's email address (leave blank if none) */
  ""
};

/*  single word (4) or double word (8) alignment  */
/* #define ALIGNMENT 8 */

/*  rounds up to the nearest multiple of ALIGNMENT  */
/* #define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7) */

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic macros from Textbook */
/* Basic constants and macros */
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)  
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Global variables */
static char *startPointer = 0;  /* Rename of book heap_listp to clarify meaning */  
static char *seat = 0;     /* Location that you previously placed in*/

/* Static definitions for functions*/
static void *extendHeap(size_t words);
static void place(void *bp, size_t asize);
static void *findFit(size_t asize);
static void *coalesce(void *bp);


int mm_init(void) 
{
  /* create the initial empty heap */
  if ((startPointer = mem_sbrk(4*WSIZE)) == (void *)-1)
    return -1;
  PUT(startPointer, 0);                        /* alignment padding */
  PUT(startPointer+WSIZE, PACK(OVERHEAD, 1));  /* prologue header */ 
  PUT(startPointer+DSIZE, PACK(OVERHEAD, 1));  /* prologue footer */ 
  PUT(startPointer+WSIZE+DSIZE, PACK(0, 1));   /* epilogue header */
  startPointer += DSIZE;

  seat = startPointer;

  /* Extend the empty heap with a free block of CHUNKSIZE bytes */
  if (extendHeap(CHUNKSIZE/WSIZE) == NULL)
    return -1;
  return 0;
}

static void *extendHeap(size_t words) 
{
  char *bp;
  size_t size;
	
  /* Allocate an even number of words to maintain alignment */
  size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
  if ((bp = mem_sbrk(size)) == (void *)-1) 
    return NULL;

  /* Initialize free block header/footer and the epilogue header */
  PUT(HDRP(bp), PACK(size, 0));         /* free block header */
  PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

  /* Coalesce if the previous block was free */
  return coalesce(bp);
}

void mm_free(void *bp)
{
  size_t size = GET_SIZE(HDRP(bp));

  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  coalesce(bp);
}

static void *coalesce(void *bp) 
{
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  if (prev_alloc && next_alloc) {            /* Case 1 */
    return bp;
  }

  else if (prev_alloc && !next_alloc) {      /* Case 2 */
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size,0));
  }

  else if (!prev_alloc && next_alloc) {      /* Case 3 */
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }

  else {                                     /* Case 4 */
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
      GET_SIZE(FTRP(NEXT_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }


  if ((seat > (char *)bp) && (seat < NEXT_BLKP(bp))) 
    seat = bp;

  return bp;
}

static void *findFit(size_t asize)
{
    
  char *previousSeat = seat;

  /* First fit search from Book
     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
     if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
     return bp;
     }
  */
  for ( ; GET_SIZE(HDRP(seat)) > 0; seat = NEXT_BLKP(seat))
    if (!GET_ALLOC(HDRP(seat)) && (asize <= GET_SIZE(HDRP(seat))))
      return seat;

  for (seat = startPointer; seat < previousSeat; seat = NEXT_BLKP(seat))
    if (!GET_ALLOC(HDRP(seat)) && (asize <= GET_SIZE(HDRP(seat))))
      return seat;

  return NULL;
}


static void place(void *bp, size_t asize)
{
  size_t csize = GET_SIZE(HDRP(bp));   

  if ((csize - asize) >= (DSIZE + OVERHEAD)) { 
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(csize-asize, 0));
    PUT(FTRP(bp), PACK(csize-asize, 0));
  }
  else { 
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
  }
}


void *mm_malloc(size_t size) 
{
  size_t asize;      /* adjusted block size */
  size_t extendsize; /* amount to extend heap if no fit */
  char *bp;      

  /* Ignore spurious requests */
  if (size <= 0)
    return NULL;

  /* Adjust block size to include overhead and alignment reqs. */
  if (size <= DSIZE)
    asize = DSIZE + OVERHEAD;
  else
    asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE);
    
  /* Search the free list for a fit */
  if ((bp = findFit(asize)) != NULL) {
    place(bp, asize);
    return bp;
  }

  /* No fit found. Get more memory and place the block */
  extendsize = MAX(asize,CHUNKSIZE);
  if ((bp = extendHeap(extendsize/WSIZE)) == NULL)
    return NULL;
  place(bp, asize);
  return bp;
} 

void *mm_realloc(void *ptr, size_t size)
{
  void *oldptr = ptr;
  void *newptr;
  size_t copySize;

  newptr = mm_malloc(size);
  if (newptr == NULL)
    return NULL;
  copySize = GET_SIZE(HDRP(ptr));
  //copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
  if (size < copySize)
    copySize = size;
  memcpy(newptr, oldptr, copySize);
  mm_free(oldptr);
  return newptr;
}
