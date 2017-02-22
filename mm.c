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
 *
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
 * provide your team information in below _AND_ in the
 * struct that follows.
 *
 * Note: This comment is parsed. Please do not change the
 *       Format!
 *
 * === User information ===
 * Group: CURLY_BRAINS
 * User 1: tinnats15
 * SSN: 0106902859
 * User 2: birkirb15
 * SSN: 0205882179
 * User 3: juliao15
 * SSN: 1808962449
 * === End User Information ===
 ********************************************************/
team_t team = {
    /* Group name */
    "CURLY_BRAINS",
    /* First member's full name */
    "Tinna Þuríður Sigurðardóttir",
    /* First member's email address */
    "tinnats15@ru.is",
    /* Second member's full name (leave blank if none) */
    "Birkir Brynjarsson",
    /* Second member's email address (leave blank if none) */
    "birkirb15@ru.is",
    /* Third full name (leave blank if none) */
    "Júlía Oddsdóttir",
    /* Third member's email address (leave blank if none) */
    "juliao15@ru.is"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*Basic constraints and macros*/
#define WSIZE		4	/* Word and header/footer size in bytes*/
#define DSIZE		8	/* Double word size in bytes */
#define CHUNKSIZE	(1<<12) /* Original size of heap. Also extends the heap by this amount. */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/*Pack a size and allocated bit into a word. Value of header and footer*/
#define PACK(size, alloc) ((size) | (alloc))

/*Read and write a word at address p. p is a void ptr*/
#define GET(p)	(*(unsigned int *)(p))
#define PUT(p)	(*(unsigned int *)(p) = (val))

/*Read the size and allocated fields from address p*/
#define GET_SIZE(p)	(GET(p) & ~0x7)  /*Return size from header/footer*/
#define GET_ALLOC(p)	(GET(p) & 0x1)   /*Return alloc from header/footer*/
#define GET_NEXTFREE(p) (GET(p) & 0x2)
#define GET_PREVFREE(p) (GET(p) & 0x4)

/*Given block ptr bp, compute address of its header and footer*/
#define HDRP(bp)	((char *)(bp) - WSIZE)
#define FTRP(bp)	((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/*Given block ptr bp, compute address of next and previous blocks*/
#define NEXT_BLKP(bp)	((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)	((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/*Get the previous and next free pointer*/
#define PREV_FREE(bp) ((HDRP(bp)) + WSIZE)
#define NEXT_FREE(bp) ((FTRP(bp)) - WSIZE)

/*Global variables*/
char *heap_start = 0x0; 
char *free_start = 0x0;
/*
 * mm_init - initialize the malloc package.
 * ---
 * Before calling mm_malloc mm_realloc or mm_free, the application program
 * calls mm_init to perform any necessary initializations,
 * such as allocating the initial heap area.
 * The return value should be -1 if there was a problem
 * in performing the initialization, 0 otherwise.
 */
int mm_init(void)
{
    /* Create inital emoty heap. Doing this now so I can use start_ptr */
    if((heap_start = mem_sbrk(4*WSIZE)) == (void *)-1) {
	return -1;
    }

    free_start = heap_start;
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 * Always allocate a block whose size is a multiple of the alignment.
 * ---
 * The mm_malloc routine returns a pointer to an allocated block payload
 * of at least size bytes. The entire allocated block should lie within
 * the heap region and should not overlap with any other allocated chunk.
 * We will be comparing your implementation to the version of malloc supplied
 * in the standard C library (libc). Since the libc malloc always returns
 * payload pointers that are aligned to 8 bytes, your malloc implementation
 * should do likewise and always return 8-byte aligned pointers.
 */
void *mm_malloc(size_t size)
{
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1) {
        return NULL;
    }
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
}

/*
 * mm_free - Freeing a block does nothing.
 * ---
 * The mm free routine frees the block pointed to by ptr.
 * It returns nothing. This routine is only guaranteed to work when
 * the passed pointer (ptr) was returned by an earlier call to mm_malloc
 * or mm_realloc and has not yet been freed.
 */
void mm_free(void *ptr)
{
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 * ---
 * The mm realloc routine returns a pointer to an allocated region
 * of at least size bytes with the following constraints:
 *     if ptr is NULL, the call is equivalent to mm malloc(size);
 *     if size is equal to zero, the call is equivalent to mm free(ptr);
 *
 *     if ptr is not NULL:
 *     it must have been returned by an earlier call to mm_malloc or mm_realloc.
 *     The call to mm_realloc changes the size of the memory block
 *     pointed to by ptr (the old block) to size bytes and returns
 *     the address of the new block.
 *     Notice that the address of the new block might be the same as the old block,
 *     or it might be different, depending on your implementation,
 *     the amount of internal fragmentation in the old block,
 *     and the size of the realloc request.
 *     The contents of the new block are the same as those of the old ptr block,
 *     up to the minimum of the old and new sizes. Everything else is uninitialized.
 *     For example, if the old block is 8 bytes and the new block is 12 bytes,
 *     then the first 8 bytes of the new block are identical to the first 8 bytes
 *     of the old block and the last 4 bytes are uninitialized.
 *     Similarly, if the old block is 8 bytes and the new block is 4 bytes,
 *     then the contents of the new block are identical to the first 4 bytes
 *     of the old block.
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL) {
        return NULL;
    }
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize) {
        copySize = size;
    }
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

/*
 * REMOVE ANY CALLS TO THIS BEFORE HANDIN
 * Consistency checker, for our own debugging during development.
 * Print error messages when mm_check fails.
 * Style points are given for this function.
 * Put in comments and document what we are checking.
 * Returns a non zero value (true) if and only if our heap is consistent
 */
int mm_check(void){
    
    printf("Is every block in the free list actually free?\n");
    char* iter;

    for(iter = free_start; iter != NULL; iter = NEXT_FREE(iter)) {
	iter = HDRP(iter);
	if(GET_ALLOC(iter) != 0x1) {
	    printf("Block at location %s is in free list but not free\n", iter);
	    exit(-1);  //Should I exit?
	}
    } 


    printf("Are there any contiguous free blocks that somehow escaped coalescing?\n");
    
    /* Going through free list, checking both previous and next blocks. If they are free, then they have ecaped coalescing.*/
    
    iter = free_start; 
    while(iter != NULL) {
	int isnextalloc = GET_NEXTFREE(iter);
	int isprevalloc = GET_PREVFREE(iter);

	if(!isnextalloc) {
	    printf("Both current block and next block are free. Escpaed coalescing.\n");
	}
	if(!isprevalloc) {
	    printf("Both current block and previous block are free. Escaped coalescing.\n");
	}

	iter = NEXT_FREE(iter);
    }


    /* For each free block, go through free list, see if there is a match. If not, there is a free block not in the free list.*/
    printf("Is every free block actually in the free list? \n");
    
    iter = heap_start;
    while (iter != NULL) {
	int isalloc = GET_ALLOC(iter);

	if(!isalloc) {
	    int found = 0; 
	    for(char* freeiter = free_start; iter != NULL; iter = NEXT_FREE(iter)) {
		if(iter == freeiter) {
		    found = 1;
		    break;
		}
	    }
	    
	    if(!found) {
	    	printf("Block at location %s is free but not in the free list.", iter);
	    }
	}
	iter = NEXT_BLKP(iter);
    }

    /*Check if there are any corrupted blocks. If the size in the header and footer are not the same, there has been an overlap. */

    printf("Do any allocd blocks overlap?\n");

    iter = heap_start; 
    while (iter != NULL) {
	int headersize = GET_SIZE(iter);
	char* footer = FTRP(iter);
	int footersize = GET_SIZE(footer);

	if(headersize != footersize) {
	    printf("The header and footer do not have the same size. There has been an overlap.\n");
	}

	iter = NEXT_BLKP(iter);
    }
    return 0;
}
