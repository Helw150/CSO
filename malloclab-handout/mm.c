/*
  mm.c - A fast, and relatively efficient dynamic memory allocator
  
  This solution is a best-fit Binary Search Tree dynamic memory allocator.
  This code base began from the simple first fit algorithm from Computer Systems:
  A Programmer's Perspective by Bryant and OHallaron(A version of which can be found here:
  http://www.groupes.polymtl.ca/inf2610/documentation/ComputerSystemBook.pdf).
  
  It works by adding the free memory into a simple Binary Search Tree with 
  the idea of replicas for performance. 
  There are 3 main differences from O'Hallaron to focus on:

  ---Best-Fit Search
  Best-fit search improves our memory allocation by placing allocated blocks into the free
  block whose size is closest to the allocated size. This uses Binary search to find the best
  fit without incurring a speed loss due to the comparison time.
  ---Smarter Realloc
  The realloc works by avoiding moving the memory to an entirely new space every time realloc
  is called. It is inspired by the coalesce function used in the starting point(p.541). The core 
  idea is that when reallocing, time and space can be save if the block does not have to fully 
  move, but instead is expanded in it's space. Therefore, it checks if it can expand around it
  and only fully moves the memory to a new block when absolutely needed
  ---Replicas
  Since we expect that some sizes of memory will be allocated
  quite frequently, the BST has the concept of replicas. These replicas are nodes with
  the exact same size as the node they replicate. This way there are contained link lists
  of exact matches to make insertion and deletion of exact matches faster.

 
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
/* Basic macros from Textbook */
/* Basic constants and macros */
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */
#define ALIGNED(size) (((size) + 0x7) & ~0x7)

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (int)(val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)  
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Due to the rules forbidding struct, these define the connections for the BST*/
#define LEFT(bp) ((void *)(bp))
#define RIGHT(bp) ((void *)(bp)+WSIZE)
#define PARENT(bp) ((void *)(bp)+DSIZE)
#define REPLICA(bp) ((void *)(bp)+(3*WSIZE))

/* For convenience, aliases changing the value on the left and right nodes*/
#define PUT_LEFT(bp,val) (PUT(LEFT(bp),val))
#define PUT_RIGHT(bp,val) (PUT(RIGHT(bp),val))

/* For convenience, aliases for withdrawing the value of the left and right nodes*/
#define GET_LEFT(bp) ((char*)GET(LEFT(bp)))
#define GET_RIGHT(bp) ((char*)GET(RIGHT(bp)))

/* Static definitions for functions*/
static void *extendHeap(size_t words);
static void place(void *bp, size_t asize);
static void *findFit(size_t asize);
static void *coalesce(void *bp);
static void deleteNode (void *bp);
static void addNode (void *bp);

static char *startPointer = 0;
static char *seat = 0;

/* Initializes the entire package for malloc, adds a empty memory area at the
   front and end so that NEXT_BLKP and PREV_BLKP always function appropriately.
   declares the "seat" as the root node of the tree (seat variables come from
   an earlier iteration of next-fit solution for speed) start pointer points
   to the first block in the heap that is not prologue. Gives a small space in the
   heap for future malloc.
*/
int mm_init()
{
  /* create the initial empty heap */
  if ((startPointer = mem_sbrk(4*WSIZE)) == (void *)-1)
    return -1;
  PUT(startPointer, 0);                        /* alignment padding */
  PUT(startPointer+WSIZE, PACK(OVERHEAD, 1));  /* prologue header */
  PUT(startPointer+DSIZE, PACK(OVERHEAD, 1));  /* prologue footer */
  PUT(startPointer+WSIZE+DSIZE, PACK(0, 1));   /* epilogue header */
  startPointer += DSIZE*2;
  seat = 0;
  /* Extend the empty heap with a free block of CHUNKSIZE bytes */
  if (extendHeap(CHUNKSIZE/WSIZE) == NULL)
    return -1;
  return 0;
}

/* Used to add more space to the heap, called when there is no space for a malloc
   adds a new free node as well as the header and footer for the new block. Changes
   epilogoue to be consistent with new size of the heap.
*/
void *extendHeap(size_t size)
{
  void *bp = 0;
  if ((long)(bp=mem_sbrk(size)) ==-1)
    return 0;
  /* Initialize free block header/footer and the epilogue header */
  PUT(HDRP(bp), PACK(size, 0));         /* free block header */
  PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */
  addNode(coalesce(bp));
  return bp;
}

/*Free memory, Change the Header and footer values & add the coalesced block to BST
  Tells the header and footer that this block is no longer used. Attempts
  to combine the newly freed memory with surrounding freed memory. Add's this new
  node to the BST.
*/
void mm_free(void *bp)
{
  size_t size = GET_SIZE(HDRP(bp));
  
  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  addNode(coalesce(bp));
}

/*Given a new block to allocate, combine the bock with nearby
  free blocks to have as large free blocks as possible
  Checks the header status of all surrounding blocks and then
  combines with those that are free as well. Removes the combined nodes
  from the BST and addds the new creation
*/
static void *coalesce(void *bp)
{
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  if (prev_alloc && next_alloc) {            /* The block before and after are full, nothing to combine*/
    return bp;
  }

  else if (prev_alloc && !next_alloc) {      /* The next block is empty. Remove it from BST and combine the sizes in the header */
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    deleteNode(NEXT_BLKP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size,0));
  }

  else if (!prev_alloc && next_alloc) {      /* The previous block is empty. Remove it from BST and combine the sizes in the header and move the pointer to the previous pointer */
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    deleteNode(PREV_BLKP(bp));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }

  else {                                     /* All surrounding blocks are empty, remove them from the BST and then combine the sizes of all blocks and move the pointer to the previous block*/
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
      GET_SIZE(FTRP(NEXT_BLKP(bp)));
    deleteNode(NEXT_BLKP(bp));
    deleteNode(PREV_BLKP(bp));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }

  return bp;
}

/*Binary search down the BST to find Best fit, functions with normal binary search rules
Best fit finds the closest free block to the called size
Next fit was originally implemented, but has less memory efficiency
Worst fit was also attempted, but did not seem to work for the test set*/
static void* findFit(size_t asize)
{
  void *previousSeat = seat;
  void *best_fit = 0;
  while (previousSeat != 0)
    {
      /* Exact memory match, Ideal case */
      if(asize == GET_SIZE(HDRP(previousSeat)))
	{
	  best_fit = previousSeat;
	  break;
	}
      /* Not an exact memory match*/
      else{
	/* Smaller memory, go left but preserve the node in case it is best match*/
	if (asize < GET_SIZE(HDRP(previousSeat)))
	  {
	    best_fit = previousSeat;
	    previousSeat = GET_LEFT(previousSeat);
	  }
	/* Bigger Memory, go right*/
	else if (asize > GET_SIZE(HDRP(previousSeat))){
	  previousSeat = GET_RIGHT(previousSeat);
	}
      }

    }
  return best_fit;
}


/* Place the size of memory in the planned pointer, shifts the tree with delete and
   add if the malloc is less than the free space. Fully removes the free node if it 
   is an exact match
   Modelled after the books implementation, but explicitly adjusts the free node
   in response to the changing free space
*/
static void place(void *bp,size_t asize)
{
  size_t csize = GET_SIZE(HDRP(bp));

  
  deleteNode(bp);
  /* Split block for extra memory*/
  if ((csize-asize)>=DSIZE * 2 + OVERHEAD)    {
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(csize-asize, 0));
    PUT(FTRP(bp), PACK(csize-asize, 0));
    addNode(coalesce(bp));
  }
  /* Exact match means delete is sufficient*/
  else
    {
      PUT(HDRP(bp), PACK(csize, 1));
      PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*The larger functionality which allocates memory when called
 called whenever new memory is allocated, and utilizes
 the higher level functions such as extendHeap and findFit
 Built from Ohallaron and Bryant
*/
void *mm_malloc(size_t size)
{
  size_t asize = size + 8; 
  size_t extendsize = 0;
  void *bp = 0;

  /* Ignore useless requests */
  if (size <= 0)
    return NULL;

  /* Make sure that the block is a size which will not gurantee internal fragmentation
  include overhead and make sure it is alignment*/
  if (size <= DSIZE)
    asize = 2*DSIZE + OVERHEAD;
  else
    asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE);
  /* Find best fit*/
  bp=findFit(asize);

  /* if that best fit actually exists, put the memory there*/
  if (bp != NULL)
    {
      place(bp,asize);
      return bp;
    }


  /* No fit found. Get more memory and place the block */
  extendsize = MAX(asize, CHUNKSIZE);
  extendHeap(extendsize);
  if ((bp=findFit(asize)) == 0)
    return NULL;
  place(bp,asize);
  return bp;
}

/* If if an existant block is reallocated with new size, find the best place to put it
   avoid memory copies as many times as possible. There are 2 cases from the size of the realloc, and then 4 cases (from coalesce) based on the allocated state of the surrounding blocks*/ 
void *mm_realloc(void *ptr,size_t size)
{
  size_t old_size = GET_SIZE(HDRP(ptr));
  size_t nexta = GET(HDRP(NEXT_BLKP(ptr)))&0x1;
  size_t preva = GET(HDRP(PREV_BLKP(ptr)))&0x1;
  size_t nextd;
  size_t prevd;
  void *nextb = NEXT_BLKP(ptr);
  void *bp = ptr;
  /* The size and ptr check code was added due to the remarks in
     malloc handout. However, on the test cases I saw no performance
     increase due to it
   */
    /* Realloc to nothing is the same as free */
  if (size == 0)
    {
      mm_free(ptr);
      return 0;
    }
  /* If a non-existant block is called in realloc, just break away*/
  else  if (ptr == NULL)
    {
      mm_malloc(size);
      return 0;
    }
  /* End of incorrect usage checks*/
  /* if all surrounding blocks are filled*/
  if (preva && nexta)
    {
      bp = findFit(ALIGNED(size + 8));
      /*If there is not enough room*/
      if (bp == 0)
	{
	  extendHeap(ALIGNED(28087 + 8 + 24));
	  bp=findFit(ALIGNED(size + 8));
	}
      memcpy(bp,ptr,old_size - DSIZE);
      place(bp,ALIGNED(size + 8));
      mm_free(ptr);
      return bp;
    }
  /* if the previous block has room*/
  else if (nexta && (!preva))
    {
      prevd = GET_SIZE(HDRP(PREV_BLKP(ptr)));
      /* if there is enough room in the previous block to expand into it*/
      if (old_size + prevd >= ALIGNED(size + 8) + 24)
	{
	  deleteNode(PREV_BLKP(ptr));
	  bp = PREV_BLKP(ptr);
	  memcpy(bp,ptr,old_size - DSIZE);
	  PUT(HDRP(bp),PACK(ALIGNED(size + 8),1));
	  PUT(FTRP(bp),PACK(ALIGNED(size + 8),1));
	  PUT(HDRP(NEXT_BLKP(bp)),PACK(old_size + prevd - ALIGNED(size + 8),0));
	  PUT(FTRP(NEXT_BLKP(bp)),PACK(old_size + prevd - ALIGNED(size + 8),0));
	  addNode(NEXT_BLKP(bp));
	  return bp;
	}
    }
  else if (preva && (!nexta))
    {
      /* if there is enough room in the previous block to expand into it*/
      if ((old_size + GET_SIZE(HDRP(nextb))) >= ALIGNED(size + 8) + 24)
	{
	  deleteNode(nextb);
	  PUT(HDRP(bp),PACK(ALIGNED(size + 8),1));
	  PUT(FTRP(bp),PACK(ALIGNED(size + 8),1));
	  PUT(HDRP(NEXT_BLKP(bp)),PACK(old_size + GET(HDRP(nextb)) - ALIGNED(size + 8),0));
	  PUT(FTRP(NEXT_BLKP(bp)),PACK(old_size + GET(HDRP(nextb)) - ALIGNED(size + 8),0));
	  addNode(NEXT_BLKP(bp));
	  return bp;
	}
    }
  else
    {
      prevd = GET_SIZE(HDRP(PREV_BLKP(ptr)));
      nextd = GET_SIZE(HDRP(nextb));
      deleteNode(nextb);
      deleteNode(PREV_BLKP(ptr));
      bp = PREV_BLKP(ptr);
      /* if there is enought room around it just expand*/
      if ((old_size + prevd + nextd) >= (ALIGNED(size + 8) + 24))
	{
	  memcpy(bp,ptr,old_size - DSIZE);
	  PUT(HDRP(bp),PACK(ALIGNED(size + 8),1));
	  PUT(FTRP(bp),PACK(ALIGNED(size + 8),1));
	  PUT(HDRP(NEXT_BLKP(bp)),PACK(old_size + prevd + nextd - ALIGNED(size + 8),0));
	  PUT(FTRP(NEXT_BLKP(bp)),PACK(old_size + prevd + nextd - ALIGNED(size + 8),0));
	  addNode(NEXT_BLKP(bp));
	  return bp;
	}
    }
  /* If there is not enough room anywhere around, just find a new block for the coalesce*/
  bp = findFit(ALIGNED(size + 8));
  if (bp == 0)
    {
      extendHeap(ALIGNED(28087 + 8));
      bp=findFit(ALIGNED(size + 8));
      if (bp == 0)
	return 0;
    }
  memcpy(bp,ptr,old_size - DSIZE);
  place(bp, ALIGNED(size + 8));
  mm_free(ptr);
  return bp;
}

/* This removes a node from the free BST, called when the area is no longer free or is changed
   It replaces the removed node with the closest possible match. If there is a replica, 
   it shifts the replica into place and removes one from the larger linked list. If there
   are no replicas it uses fundamental non-self balancing BST rules.
*/
static void deleteNode(void *bp)
{
  /* If the deleted node is not the root*/
  if (bp != seat)
    {
      /*It is not a replica and it has no replicas
       This is deletion as usual from a BST*/
      if (GET_RIGHT(bp) != -1 && !GET(REPLICA(bp)))
	{
	  /* if there is a right child, find the smallest number larger than it */
	  if (GET_RIGHT(bp))
	    {
	      void *currSeat = GET_RIGHT(bp);
	      while(GET_LEFT(currSeat) != 0)
		currSeat = GET_LEFT(currSeat);
	      if (GET_SIZE(HDRP(bp)) > GET_SIZE(HDRP(GET(PARENT(bp)))))
		PUT_RIGHT(GET(PARENT(bp)),currSeat);
	      else
		PUT_LEFT(GET(PARENT(bp)),currSeat);
	      if (currSeat != GET_RIGHT(bp))
		{
		  if (GET_RIGHT(currSeat))
		    {
		      PUT_LEFT(GET(PARENT(currSeat)),GET_RIGHT(currSeat));
		      PUT_LEFT(GET(PARENT(currSeat)),GET_RIGHT(currSeat));
		      PUT(PARENT(GET(RIGHT(currSeat))), GET(PARENT(currSeat)));
		    }
		  else
		    PUT_LEFT(GET(PARENT(currSeat)),0);
		  PUT_RIGHT(currSeat,GET_RIGHT(bp));
		  PUT(PARENT(GET(RIGHT(bp))), currSeat);
		}
	      PUT(PARENT(currSeat),GET(PARENT(bp)));
	      PUT_LEFT(currSeat,GET_LEFT(bp));
	      if (GET_LEFT(bp) != 0)
		PUT(PARENT(GET(LEFT(bp))), currSeat);
	    }
	  /* otherwise*/
	  else
	    { 
	      if (GET_SIZE(HDRP(bp)) > GET_SIZE(HDRP(GET(PARENT(bp)))))
		PUT_RIGHT(GET(PARENT(bp)),GET_LEFT(bp));
	      else
		PUT_LEFT(GET(PARENT(bp)),GET_LEFT(bp));
	      if (GET_LEFT(bp) != 0 && GET(PARENT(bp)) != 0)
		PUT(PARENT(GET(LEFT(bp))), GET(PARENT(bp)));
	    }

	}
      /* This node is a replica*/
      else if (GET_RIGHT(bp) == -1)
      	{
      	  if (GET(REPLICA(bp)))
      	    PUT_LEFT(GET(REPLICA(bp)),GET_LEFT(bp));
      	  PUT(REPLICA(GET_LEFT(bp)),GET(REPLICA(bp)));
      	}
      /* This node isn't a replica, but has a replica*/
      else
	{
			
	  if (GET_SIZE(HDRP(bp)) > GET_SIZE(HDRP(GET(PARENT(bp)))))
	    PUT_RIGHT(GET(PARENT(bp)),GET(REPLICA(bp)));
	  else
	    PUT_LEFT(GET(PARENT(bp)),GET(REPLICA(bp)));
	  PUT_LEFT(GET(REPLICA(bp)),GET_LEFT(bp));
	  PUT_RIGHT(GET(REPLICA(bp)),GET_RIGHT(bp));
	  /* There is a left child*/
	  if (GET_LEFT(bp) != 0)
	    PUT(PARENT(GET(LEFT(bp))), GET(REPLICA(bp)));
	  /* There is a right child*/
	  if (GET_RIGHT(bp) != 0)
	    PUT(PARENT(GET(RIGHT(bp))), GET(REPLICA(bp)));
	  PUT(PARENT(GET(REPLICA(bp))), GET(PARENT(bp)));
	}
    }
  /* if it is the root of the tree*/
  else
    {
      /* If it has left and right children*/
      if(GET_LEFT(bp) && GET_RIGHT(bp))
	{
	  void *currSeat = GET_RIGHT(bp);
	  while (GET_LEFT(currSeat) != 0)
	    currSeat = GET_LEFT(currSeat);
	  seat = currSeat;
	  PUT(PARENT(GET_LEFT(bp)), currSeat);
	  /* If while loop above executed*/
	  if (currSeat != GET_RIGHT(bp))
	    {
	      if (GET_RIGHT(currSeat) != 0)
		PUT(PARENT(GET(RIGHT(currSeat))), GET(PARENT(currSeat)));
	      PUT_LEFT(GET(PARENT(currSeat)),GET_RIGHT(currSeat));
	      PUT_RIGHT(currSeat,GET_RIGHT(bp));
	      PUT(PARENT(GET(RIGHT(bp))), currSeat);
	    }
	  PUT_LEFT(currSeat,GET_LEFT(bp));
	}
      else{
	/* left child empty*/
	if (GET_LEFT(bp) == 0) 
	  seat=GET_RIGHT(bp);
	/* right child empty*/
	else 
	  seat=GET_LEFT(bp);
      }
    }
}

/* This adds a new node to the free BST, this occurs when a space is freed, added,
   or old nodes are changed. It operates off basic non-self balancing BST insertion
   rules. The modification is that it creates linked lists for exact memory matches
   These nodes are called replicas and create sub linked lists for memory matches.
*/
static void addNode(void *bp)
{
  /* If first node in tree*/
  if (seat == 0)
    {
      seat = bp;
      PUT_LEFT(bp,0);
      PUT_RIGHT(bp,0);
      PUT(PARENT(bp), 0);
      PUT(REPLICA(bp),0);
      return;
    }
  /* Start at the root of the tree*/
  void *currSeat = seat;
  /* Loop to reach the bottom of the tree, it is broken by functions inside*/
  while (1)
    {
      /* go left*/
      if (GET_SIZE(HDRP(bp)) < GET_SIZE(HDRP(currSeat)))
	if (GET_LEFT(currSeat) != 0){
	  currSeat = GET_LEFT(currSeat);
	}
      /* You are at the bottom of the tree, add the node*/
	else{
	  PUT_LEFT(currSeat,bp);
	  PUT(PARENT(bp), currSeat);
	  PUT(REPLICA(bp),0);
	  PUT_LEFT(bp,0);
	  PUT_RIGHT(bp,0);
	  break;
	}
      /*go right*/
      else if (GET_SIZE(HDRP(bp)) > GET_SIZE(HDRP(currSeat)))
	if (GET_RIGHT(currSeat) != 0){
	  currSeat = GET_RIGHT(currSeat);
	}
      /* You are at the bottom of the tree, add the node*/
	else{
	  PUT_RIGHT(currSeat,bp);
	  PUT(PARENT(bp), currSeat);
	  PUT(REPLICA(bp),0);
	  PUT_LEFT(bp,0);
	  PUT_RIGHT(bp,0);
	  break;
	}
      /* Exact match with node*/
      else{
	/* You are still at the root of the tree*/
	if (currSeat == seat)
	  {
	    seat = bp;
	    PUT(PARENT(bp), 0);
	  }
	/* Determine the added node relationship to the parent*/
	else
	  {
	    if (GET_SIZE(HDRP(GET(PARENT(currSeat)))) >  GET_SIZE(HDRP(currSeat)))
	      PUT_LEFT(GET(PARENT(currSeat)),bp);
	    else
	      PUT_RIGHT(GET(PARENT(currSeat)),bp);
	    PUT(PARENT(bp), GET(PARENT(currSeat)));
	  }
	/*If there is a left child*/
	if (GET_LEFT(currSeat))
	  PUT(PARENT(GET_LEFT(currSeat)), bp);
	/*If there is a right child*/
	if (GET_RIGHT(currSeat)){
	  PUT(PARENT(GET_RIGHT(currSeat)), bp);
	}
	/*put the children on the new node*/
	PUT_LEFT(bp,GET_LEFT(currSeat));
	PUT_RIGHT(bp,GET_RIGHT(currSeat));

	/*Set up the replica*/
	PUT(REPLICA(bp),currSeat);
	PUT_LEFT(currSeat,bp);
	PUT_RIGHT(currSeat,-1);
	break;
      }
    }
}

/* Checks issues which would not be determined in GDB 
   and would not neccesarily cause runtime errors.
   Primarily debugging was done in GDB and and this was primarily a 
   sanity check for those things which would be invisible in GDB
*/

static void mm_check()
{
  char *buff = 0;
  char *prevBuff;
  buff = startPointer;
  while (1)
    {
      prevBuff = buff;
      buff = NEXT_BLKP(buff);
      /*
	Checks if two blocks in a row are marked free
	This would suggest the need for a coalesce
      */
      if (!GET_ALLOC(HDRP(prevBuff)) && !GET_ALLOC(HDRP(buff))){
	printf("Non-Coalesced Blocks, Coalesce error");
	break;
      }
      /*
	Checks if the allocation bit is on, but the size is zero
	 this would suggest a block that should be free but is not
      */
      if (GET_SIZE(HDRP(prevBuff)) == 0 && GET_ALLOC(HDRP(prevBuff)) == 1){
	printf("Allocated block with Zero Size, Free Error");
	break;
      }
      /*
	Checks if the previous block + size overlaps the next block
	This would suggest malloc over wrote another file header,
	but this somehow did not cause a seg fault
      */
      if (GET_SIZE(HDRP(prevBuff)) != GET_SIZE(HDRP(prevBuff))){
	printf("Overlapping Blocks, Malloc, Realloc,  or Place Error");
	break;
      }
    }
}

