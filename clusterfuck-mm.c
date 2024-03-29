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
#define WSIZE       4   /* Word and header/footer size in bytes*/
#define DSIZE       8   /* Double word size in bytes */
#define CHUNKSIZE   (1<<12) /* Original size of heap. Also extends the heap by this amount. */
#define OVERHEAD    8   /* overhead of header and footer */


#define MAX(x, y) ((x) > (y)? (x) : (y))

/*Pack a size and allocated bit into a word. Value of header and footer*/
//#define PACK(size, alloc) ((size) | (alloc))
//#define PACK(size, prev_alloc, next_alloc, alloc) ((size)|((prev_alloc) << 2) |((next_alloc) << 1)|(alloc)))
#define PACK(size, prev_alloc, next_alloc, alloc) ((size)| ((prev_alloc) << 2) | ((next_alloc) << 1)|(alloc))


/*Read and write a word at address p. p is a void ptr*/
#define GET(p)  (*(unsigned int *)(p))
#define PUT(p, val)    (*(unsigned int *)(p) = (val))

/*Read the size and allocated fields from address p*/
#define GET_SIZE(p) (GET(p) & ~0x7)  /*Return size from header/footer*/
#define GET_ALLOC(p)    (GET(p) & 0x1)   /*Return alloc from header/footer*/
#define GET_NEXTFREE(p) ((GET(p) & 0x2) >> 1)
#define GET_PREVFREE(p) ((GET(p) & 0x4) >> 2)

/*Given block ptr bp, compute address of its header and footer*/
#define HDRP(bp)    ((char *)(bp) - WSIZE)
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/*Given block ptr bp, compute address of next and previous blocks*/
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/*Get the previous and next free pointer*/
#define PREV_FREE(bp) ((HDRP(bp)) + WSIZE)
#define NEXT_FREE(bp) ((FTRP(bp)) - WSIZE)

/*Global variables*/
char *heap_start = 0x0;
char *free_start = 0x0;
char *heap_end = 0x0;
char *free_end = 0x0;
// mm-firstfit
//char *heap_listp;

/* Function declerations */
int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *ptr);
void *mm_realloc(void *ptr, size_t size);

/* function prototypes for internal helper routines -- From mm-firstfit.c */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp);
static void checkblock(void *bp);

int mm_check(void);

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

    free_start = heap_start + WSIZE;   //Word behind header
    heap_end = mem_heap_hi();        //is this correct? hi returns brk-1, so last footer would be brk-4 = (brk - 1)-3?
    free_end = heap_end - WSIZE;       //Word in front of footer
    
    //Initializing header and footer
    //Using size DSIZE, since the only space is reserved for the prev and next pointers, DSIZE = 8 bytes.
    PUT(heap_start, PACK(DSIZE, 1, 1, 0));
    PUT(heap_end, PACK(DSIZE, 1, 1, 0));

 
    // Extend the empty heap with a free block of CHUNKSIZE bytes 
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }
    printf("Reached end of mm_init\n");
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
    printf("MALLOC %d BYTES\n", size);
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1) {
    //     return NULL;
    // }
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }

    /* FROM mm_firstfit.c */
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size <= 0) {
        return NULL;
    }

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE) {
        asize = DSIZE + OVERHEAD;
    }
    else {
        asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE);
    }
    
    printf("Aligned size: %d\n", asize);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        printf("Finds fit, before place\n");
	place(bp, asize);
	printf("Free fit found, block placed\n");
        return bp;
    }

    printf("Free fit not found, need to extend heap\n");    
    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, asize);

    printf("Reached end of malloc\n");
    printblock(bp);
    return bp;
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
    //If ptr is NULL
    if (!ptr) 
	return;

    /* FROM mm_firstfit.c */
    size_t size = GET_SIZE(HDRP(ptr));
    printf("FREE %d BYTES\n", size);
    //TODO, what if there is no prev or next block
    // Letting adjacent blocks know about our freeness
    // WHAT IF PREV_PTR IS OUT OF BOUNDS BUT NOT NULL??
    void* prev_ptr = PREV_BLKP(ptr);
    if(prev_ptr != NULL) {
        size_t prev_head = GET(HDRP(prev_ptr)); //prev_head_ptr
        size_t new_prev_head = prev_head & ~0x2;
        PUT(HDRP(prev_ptr), new_prev_head);
        PUT(FTRP(prev_ptr), new_prev_head);
    }

    void* next_ptr = NEXT_BLKP(ptr);
    if(next_ptr != NULL) {
        size_t next_head = GET(HDRP(next_ptr));
        size_t new_next_head = next_head & ~0x4;
        PUT(HDRP(next_ptr), new_next_head);
        PUT(FTRP(next_ptr), new_next_head);
    }

    PUT(HDRP(ptr), (PACK(size, GET_PREVFREE(HDRP(ptr)), GET_NEXTFREE(HDRP(ptr)), 0)));
    PUT(FTRP(ptr), (PACK(size, GET_PREVFREE(HDRP(ptr)), GET_NEXTFREE(HDRP(ptr)), 0)));

    printf("End of free, need to coalesce\n");    

    coalesce(ptr);
	
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
    // void *oldptr = ptr;
    // void *newptr;
    // size_t copySize;

    // newptr = mm_malloc(size);
    // if (newptr == NULL) {
    //     return NULL;
    // }
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    // if (size < copySize) {
    //     copySize = size;
    // }
    // memcpy(newptr, oldptr, copySize);
    // mm_free(oldptr);
    // return newptr;

    /* FROM mm_firstfit.c */
    void *newp;
    size_t copySize;

    if ((newp = mm_malloc(size)) == NULL) {
        printf("ERROR: mm_malloc failed in mm_realloc\n");
        exit(1);
    }
    copySize = GET_SIZE(HDRP(ptr));
    if (size < copySize) {
        copySize = size;
    }
    memcpy(newp, ptr, copySize);
    mm_free(ptr);
    return newp;
}

/*
 * REMOVE ANY CALLS TO THIS BEFORE HANDIN
 * Consistency checker, for our own debugging during development.
 * Print error messages when mm_check fails.
 * Style points are given for this function.
 * Put in comments and document what we are checking.
 * Returns a non zero value (true) if and only if our heap is consistent
 */
int mm_check(void)
{
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

    /*Check if pointers in heap point to valid addresses. If they are less than heap_start or greater than heap_end, then they are invalid.*/

    printf("Do pointers in heap point to valid addresses? \n");

    iter = free_start;
    while(iter != NULL) {
        char* next = NEXT_FREE(iter);

        if(next < heap_start || next > heap_end) {
        printf("Pointer in blcok %s points out of bounds.", iter);
        }
	   iter = next;
    }

    iter = free_end;
    while(iter != NULL) {
        char* prev = PREV_FREE(iter);

        if(prev < heap_start || prev > heap_end) {
            printf("Pointer in block %s points out of bounds.", iter);
        }
        iter = prev;
    }
    return 0;
}

/*
 * mm_checkheap - Check the heap for consistency
 */
void mm_checkheap(int verbose)
{
    char *bp = heap_start;

    if (verbose) {
        printf("Heap (%p):\n", heap_start);
    }

    if ((GET_SIZE(HDRP(heap_start)) != DSIZE) || !GET_ALLOC(HDRP(heap_start))) {
        printf("Bad prologue header\n");
    }
    checkblock(heap_start);

    for (bp = heap_start; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose) {
            printblock(bp);
    }
        checkblock(bp);
    }

    if (verbose) {
        printblock(bp);
    }
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))) {
        printf("Bad epilogue header\n");
    }
}

/* The remaining routines are internal helper routines */

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;    
    
    printf("Heap_end: %p  - heap_start: %p  - Space between: %d\n", heap_end, heap_start, (heap_end-heap_start));

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((bp = mem_sbrk(size)) == (void *)-1) {
        return NULL;
    }
    
    //WHAT IF HEAP SIZE IS 16 BEFORE EXTENSION? Then there is no need to change previous block, everything is free
    printf("Extending heap by %d bytes\n", size);
    printf("old bp: %p\n", bp);


    //Place bp right in front of its uninitalised header
    bp += WSIZE;

    printf("old bp + WSIZE: %p\n", bp);
    printf("prev block pointer: %p\n", bp - DSIZE);


    //Initializing free block header/footer
    PUT(HDRP(bp), PACK(size, GET_ALLOC(bp - DSIZE), 1, 0));
    PUT(FTRP(bp), PACK(size, GET_ALLOC(bp - DSIZE), 1, 0));
     
    void* prev_ptr = bp - DSIZE;
    printf("prev ptr: %p\n", prev_ptr);
    printf("prev ptr value: %d\n", GET(prev_ptr));
    //Let previous block know that we are free
    size_t new_prev_head = GET(HDRP(prev_ptr)) & ~0x2;
    PUT(HDRP(prev_ptr), new_prev_head);
    PUT(FTRP(prev_ptr), new_prev_head);
    printf("Finished updating the previous header and footer pointers \n ");    
    //Relocate heap_end
    heap_end = mem_heap_hi();
    printf("Reached end of extend_heap\n");
    /* Coalesce if the previous block was free */
    return coalesce(bp);
}
/* $end mmextendheap */

/*
 * place - Place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *bp, size_t asize)
/* $end mmplace-proto */
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (DSIZE + OVERHEAD)) {
        PUT(HDRP(bp), PACK(asize, 1, 0, 1));
        PUT(FTRP(bp), PACK(asize, 1, 0, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 1, 1, 0));
        PUT(FTRP(bp), PACK(csize-asize, 1, 1, 0));
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1, 1, 1));
        PUT(FTRP(bp), PACK(csize, 1, 1, 1));
    }
}
/* $end mmplace */

/*
 * find_fit - Find a fit for a block with asize bytes
 */
static void *find_fit(size_t asize)
{
    /* first fit search */
    void *bp;

    for (bp = heap_start; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL; /* no fit */
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp)
{
    printf("Entering coalesce\n");
    void *head = HDRP(bp);
    size_t prev_alloc = GET_PREVFREE(head);
    size_t next_alloc = GET_NEXTFREE(head);
    size_t size = GET_SIZE(head);

    if (prev_alloc && next_alloc) {            /* Case 1 */
        printf("Case 1, return bp\n");
	return bp;
    }
    else if (prev_alloc && !next_alloc) {      /* Case 2 */
	printf("Case 2, next block free\n");
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 1, 1, 0));
        PUT(FTRP(bp), PACK(size, 1, 1, 0));
    }
    else if (!prev_alloc && next_alloc) {      /* Case 3 */
	printf("Case 3, previous block free\n");
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 1, 1, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 1, 1, 0));
        bp = PREV_BLKP(bp);
    }
    else if (!prev_alloc && !next_alloc) {                                     /* Case 4 */
	printf("Case 4, both blocks free\n");
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 1, 1, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 1, 1, 0));
        bp = PREV_BLKP(bp);
    }
    printf("Returning from coalesce \n");
    return bp;
}


static void printblock(void *bp)
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));

    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp,
           hsize, (halloc ? 'a' : 'f'),
           fsize, (falloc ? 'a' : 'f'));
}

static void checkblock(void *bp)
{
    if ((size_t)bp % 8) {
        printf("Error: %p is not doubleword aligned\n", bp);
    }
    if (GET(HDRP(bp)) != GET(FTRP(bp))) {
        printf("Error: header does not match footer\n");
    }
}
