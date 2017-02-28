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


// single word (4) or double word (8) alignment 
#define ALIGNMENT 8

// rounds up to the nearest multiple of ALIGNMENT 
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define MAX(x, y)  ((x) > (y) ? (x) : (y))

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE       4   // Word and header/footer size in bytes
#define DSIZE       8   // Double word size in bytes 
#define OVERHEAD    8   // overhead of header and footer 
#define CHUNKSIZE   (1<<12) // original size of heap and the smallest extension size

#define PACK(size, prev_alloc, next_alloc, alloc) ((size)| ((prev_alloc) << 2) | ((next_alloc) << 1)|(alloc))
// Read and write a word at address p. p is a void ptr
#define GET(p)  (*(unsigned int *)(p))
#define PUT(p, val)    (*(unsigned int *)(p) = (val))

// Read the size and allocated fields from address p
#define GET_SIZE(p) (GET(p) & ~0x7)  // Return size from header/footer
#define GET_ALLOC(p)    (GET(p) & 0x1)   // Return alloc from header/footer
#define GET_NEXTFREE(p) ((GET(p) & 0x2) >> 1)
#define GET_PREVFREE(p) ((GET(p) & 0x4) >> 2)

// Given block ptr bp, compute address of its header and footer
#define HDRP(bp)    ((char *)(bp) - WSIZE)
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// Given block ptr bp, compute address of next and previous blocks
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

// Get the previous and next free pointer
#define PREV_FREE(bp) (*(void **)((HDRP(bp)) + WSIZE))
#define NEXT_FREE(bp) (*(void **)((FTRP(bp)) - WSIZE))

// Global variables
char *heap_start = 0x0;
char *free_start = 0x0;
char *heap_end = 0x0;
char *free_end = 0x0;

// Function declerations 
int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *ptr);
void *mm_realloc(void *ptr, size_t size);

// function prototypes for internal helper routines -- From mm-firstfit.c 
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void remove_from_free(void* bp); 

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // set the start and end pointers
    if((heap_start = mem_sbrk(CHUNKSIZE+OVERHEAD)) == (void *)-1){
        return -1;
    }
    heap_end = mem_heap_hi();

    // set head and foot
    void *first_free = heap_start + WSIZE;

    // initialize free list
    free_start = first_free;
    free_end = free_start;
    PUT(heap_start, PACK(CHUNKSIZE, 1, 1, 0));
    PUT(FTRP(first_free), PACK(CHUNKSIZE, 1, 1, 0));
    
    // PUT(PREV_FREE(first_free), 0);
    // PUT(NEXT_FREE(first_free), 0);

    printf("heap_start %p\n", heap_start);
    printf("first free: %p\n", first_free);
    

    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 * Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    /*int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1) {
        return NULL;
    }
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }*/

    size_t alignedSize; 
    size_t extendSize; 
    char* bp; 

    //Ignore empty requests
    if(size <= 0) {
        return NULL;
    }

    //Adjust block size to include overhead and alignment
    alignedSize = MAX(ALIGN(size), (OVERHEAD + DSIZE));

    //Search free list for a fit. If it's there, place the block down. 
    if((bp = find_fit(alignedSize)) != NULL) {
	    place(bp, alignedSize);
	    return bp;
    }       

    //Since there is no fit found, we need to extend the heap. Find size to extend for.
    extendSize = MAX(alignedSize, CHUNKSIZE);

    //No fit found, get more memory by extending heap and place the block.
    if((bp = extend_heap(extendSize/WSIZE)) == NULL) {
	    return NULL;
    }

    //Now we can place, since the heap is larger
    place(bp, alignedSize);

    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
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

static void *find_fit(size_t size) {

    //Pointer to search through the free list
    void *bp; 


    //Traverse the free list. Not sure about the middle condition?? 
    for (bp = free_start; NEXT_FREE(bp) != 0; bp = NEXT_FREE(bp)) {

	//If our size is smaller than the size of the block, return that block
	    if (size <= GET_SIZE(HDRP(bp))+OVERHEAD) {
	        return bp; 
	    }
    }

    //No fit, need to extend.
    return NULL; 
}

static void place(void* bp, size_t size) {
    
    size_t blockSize = GET_SIZE(HDRP(bp)); 

    //Free block is larger than the space needed
    if((blockSize - size) >= (OVERHEAD + DSIZE)) {
        PUT(HDRP(bp), PACK(size, 1, 0, 1));  //Prev block alloc, next block free, current block alloc
        PUT(FTRP(bp), PACK(size, 1, 0, 1));
	
	//Remove the current block from free list
	    remove_from_free(bp);

	//Fetch the next block to resize
	    bp = NEXT_BLKP(bp);
	    PUT(HDRP(bp), PACK(blockSize - size, 1, 1, 0)); //Prev block alloc, next block alloc, current block free
	    PUT(FTRP(bp), PACK(blockSize - size, 1, 1, 0));
	//TODO: ADD IT TO FREE LIST, coalesce? 
    }
    //Block fits perfectly
    else {
	    PUT(HDRP(bp), PACK(size, 1, 1, 1)); 
	    PUT(FTRP(bp), PACK(size, 1, 1, 1));
	    remove_from_free(bp);
    }
}

static void remove_from_free(void* bp) {

    // If there is a previous free block, make it point to the header of the next block
    if (PREV_FREE(bp)) { // must remember to set bp as 0 when removing
	    NEXT_FREE(PREV_FREE(bp)) = HDRP(NEXT_FREE(bp));
    }
    // If not, then it is the new start of the list
    else {
	    free_start = HDRP(NEXT_FREE(bp));
        PUT(NEXT_FREE(free_start), 0);
    }

    // If there is a next block, make it point to the header of the previous block
    if(NEXT_FREE(bp)) {
	    PREV_FREE(NEXT_FREE(bp)) = HDRP(PREV_FREE(bp));
    }
    else {
	    free_end = HDRP(PREV_FREE(bp));
    }
    
}
