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
#define OVERHEAD    8  // overhead of header and footer
#define CHUNKSIZE   (1<<12) // original size of heap and the smallest extension size

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

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
#define PREV_FREE(bp) (*(void **)((bp)))
#define NEXT_FREE(bp) (*(void **)((bp) + WSIZE))


// Global variables
char *heap_start = 0x0;        // points to the beginning of the heap
char *heap_end = 0x0;          // points to the end of the heap
size_t largest;                // size of the largest freeblock
char *free_start = 0x0;        // points to the beginning of the freelist
char *free_end = 0x0;          // points to the end of the freelist
size_t free_length;            // length of freelist

// Function declerations
int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *ptr);
void *mm_realloc(void *ptr, size_t size);

/* function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
void newfree(void *bp);
void removefree(void *bp);
static void *find_fit(size_t size);
static void place(void *bp, size_t asize);
static void updateLargest();
static void printblock(void *bp);
static void printfreelist();

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if((heap_start = mem_sbrk(6*WSIZE)) == (void *)-1){
        return -1;
    }

    PUT(heap_start, 0); // WSIZE Padding before we move the heap_start
    heap_start += DSIZE;
    PUT(HDRP(heap_start), PACK(DSIZE+OVERHEAD, 1));
    free_start = NULL;
    free_end = NULL;
    // largest = 0;
    free_length = 0;
    NEXT_FREE(heap_start) = NULL;
    PREV_FREE(heap_start) = NULL;
    PUT(FTRP(heap_start), PACK(DSIZE+OVERHEAD, 1));
    PUT(HDRP(NEXT_BLKP(heap_start)), PACK(0, 1)); // epilogue (End)

    /* EXTEND */
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }
    // printf("\n\n\n\nNEW LIST\nPrologue: ");
    // printblock(heap_start);
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 * Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    // printf("mm_malloc() Allocationg size: %d\n", size); fflush(stdout);
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size <= 0) {
        return NULL;
    }

    // printfreelist();

    asize = ALIGN(size + SIZE_T_SIZE);

    if((bp = find_fit(asize)) == NULL){
        extendsize = MAX(asize,CHUNKSIZE);
        // printf("EXTENDING, no fit found\n");
        if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
            return NULL;
        }
    }

    // printf("Found fit in:\n");
    // printblock(bp);
    // printf("\n");

    // if(asize > largest){
    //     extendsize = MAX(asize,CHUNKSIZE);
    //     if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
    //         return NULL;
    //     }
    // }
    // // Double checking that we actually find a fit in the free list
    // else if((bp = find_fit(asize)) == NULL){
    //     return NULL;
    // }

    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    // printf("mm_free() freeing Block: \n"); fflush(stdout); printblock(bp);
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    newfree(bp);
    coalesce(bp);
    // printfreelist();
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *newptr;
    size_t asize = ALIGN(size + SIZE_T_SIZE);
    size_t currSize = GET_SIZE(HDRP(ptr));
    void *next;
    void *prev;

    if (size <= 0) {
        printf("Size <= 0\n"); fflush(stdout);
        mm_free(ptr);
        return 0x0;
    }

    if (ptr == NULL) {
        printf("ptr == null\n"); fflush(stdout);
        return mm_malloc(size);
    }

    if (asize == currSize) {
        // printf("alignedsize == currsize\n"); fflush(stdout);
        return ptr;
    }

    // What if asize is smaller than current size?

    size_t prevSize = GET_SIZE(HDRP(PREV_BLKP(ptr)));
    size_t nextSize = GET_SIZE(HDRP(NEXT_BLKP(ptr)));

    //If the next block is free, and there is enough space for the new size in the current block and next block combined, extend the block
    if(!GET_ALLOC(HDRP(NEXT_BLKP(ptr)))){
        size_t bsize = currSize + nextSize;
        if(asize <= bsize){
            if ((bsize - asize) >= (DSIZE + OVERHEAD)) {
                removefree(NEXT_BLKP(ptr));
                PUT(HDRP(ptr), PACK(asize, 1));
                PUT(FTRP(ptr), PACK(asize, 1));
                next = NEXT_BLKP(ptr);
                PUT(HDRP(next), PACK(bsize-asize, 0));
                PUT(FTRP(next), PACK(bsize-asize, 0));
                newfree(next);
                return ptr;
            }
            else {
                removefree(NEXT_BLKP(ptr));
                PUT(HDRP(ptr), PACK(bsize, 1));
                PUT(FTRP(ptr), PACK(bsize, 1));
                return ptr;
            }
        }
    }

    if(!GET_ALLOC(HDRP(PREV_BLKP(ptr)))){
        size_t bsize = currSize + prevSize;
        if(asize <= bsize){
            if ((bsize - asize) >= (DSIZE + OVERHEAD)) {
                prev = PREV_BLKP(ptr);
                removefree(prev);
                PUT(HDRP(prev), PACK(asize, 1));
                memcpy(prev, ptr, currSize);
                PUT(FTRP(prev), PACK(asize, 1));
                next = NEXT_BLKP(prev);
                PUT(HDRP(next), PACK(bsize-asize, 0));
                PUT(FTRP(next), PACK(bsize-asize, 0));
                newfree(next);
                coalesce(next);
                return prev;
            }
            else {
                prev = PREV_BLKP(ptr);
                removefree(prev);
                PUT(HDRP(prev), PACK(bsize, 1));
                memcpy(prev, ptr, currSize);
                PUT(FTRP(prev), PACK(bsize, 1));
                return prev;
            }
        }
    }

    if(!GET_ALLOC(HDRP(PREV_BLKP(ptr))) &&
       !GET_ALLOC(HDRP(NEXT_BLKP(ptr)))){
        size_t bsize = prevSize + currSize + nextSize;
        if(asize <= bsize){
            if((bsize - asize) >= (DSIZE + OVERHEAD)){
                prev = PREV_BLKP(ptr);
                next = NEXT_BLKP(ptr);
                removefree(prev);
                removefree(next);
                PUT(HDRP(prev), PACK(asize, 1));
                memcpy(prev, ptr, currSize);
                PUT(FTRP(prev), PACK(asize, 1));
                next = NEXT_BLKP(prev);
                PUT(HDRP(next), PACK(bsize-asize, 0));
                PUT(FTRP(next), PACK(bsize-asize, 0));
                newfree(next);
                return prev;
            }
            else {
                prev = PREV_BLKP(ptr);
                next = NEXT_BLKP(ptr);
                removefree(prev);
                removefree(next);
                PUT(HDRP(prev), PACK(bsize, 1));
                memcpy(prev, ptr, currSize);
                PUT(FTRP(prev), PACK(bsize, 1));
                return prev;
            }
        }
    }

    newptr = mm_malloc(asize);
    // Not copying DSIZE becuase preserving new Footer and possibly Head of next block.
    memcpy(newptr, ptr, (asize - OVERHEAD));
    mm_free(ptr);

    return newptr;
}

static void *find_fit(size_t size) {

    //Pointer to search through the free list
    void* bp;
    void* fit = NULL;
    size_t count = 0;

    //Traverse the free list
    for (bp = free_start; bp != NULL && count < 3; bp = NEXT_FREE(bp)) {
    //If our size is smaller than the size of the block, return that block
        if (size <= ((size_t)GET_SIZE(HDRP(bp)))) {
            if(fit == NULL){
                fit = bp;
            }
            else if(GET_SIZE(HDRP(bp)) < GET_SIZE(HDRP(fit))){
                fit = bp;
            }
            count++;
        }
    }

    //No fit, need to extend... Somethings wrong with the largest global var
    return fit;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    // TODO, minimum size == OVERHEAD
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if((bp = mem_sbrk(size)) == (void *)-1){
        return NULL;
    }

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

    newfree(bp);

    /* Coalesce if the previous block was free */
    return coalesce(bp);

}

static void place(void *bp, size_t asize)
{
    size_t bsize = GET_SIZE(HDRP(bp));

    // More room, split into new free block
    if ((bsize - asize) >= (DSIZE + OVERHEAD)) {
        removefree(bp);
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(bsize-asize, 0));
        PUT(FTRP(bp), PACK(bsize-asize, 0));
        newfree(bp);
    }
    else {
        removefree(bp);
        PUT(HDRP(bp), PACK(bsize, 1));
        PUT(FTRP(bp), PACK(bsize, 1));
    }
    // if(bsize >= largest){
    //     updateLargest();
    // }
}

void newfree(void *bp)
{
    /* Get old first pointer on free list */
    void *old_freestart = free_start;

    /* newFree points to old first free */
    NEXT_FREE(bp) = old_freestart;

    /* Previous free to new free block is 0 (end) */
    PREV_FREE(bp) = NULL;

    // Put largest free block size in Prolouge Header
    // largest = MAX(largest, GET_SIZE(HDRP(bp)));

    /* Old first free previous free points to new free block */
    if (old_freestart != NULL){
        PREV_FREE(old_freestart) = bp;
    }
    /* Prolouge header points to new free block */
    free_start = bp;
    // if the length of the freelist is 0, free_start and free_end are the same block
    if (free_length == 0) {
        free_end = free_start;
    }
    free_length++;
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // next and prev are both allocated, nothing to coalesce
    if (prev_alloc && next_alloc) {         /* Case 1 */
        return bp;
    }
    // next is free, remove/bypass it from freelist before coalescing
    else if (prev_alloc && !next_alloc){    /* Case 2 */
        removefree(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    // previous is free, remove/bypass it from freelist before coalescing
    else if (!prev_alloc && next_alloc){    /* Case 3 */
        removefree(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        NEXT_FREE(PREV_BLKP(bp)) = NEXT_FREE(bp);
        PREV_FREE(PREV_BLKP(bp)) = NULL;
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        if(NEXT_FREE(bp) != NULL){
            PREV_FREE(NEXT_FREE(bp)) = bp;
        }
        // NEXT_FREE(heap_start) = bp;
        free_start = bp;
        if(free_length <= 1){
            free_end = bp;
        }
    }
    // both next and prev are free, remove/bypass both from freelist before coalescing
    else {                                  /* Case 4 */
        removefree(NEXT_BLKP(bp));
        removefree(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        NEXT_FREE(PREV_BLKP(bp)) = NEXT_FREE(bp);
        PREV_FREE(PREV_BLKP(bp)) = NULL;
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        if(NEXT_FREE(bp) != NULL){
            PREV_FREE(NEXT_FREE(bp)) = bp;
        }
        // NEXT_FREE(heap_start) = bp;
        free_start = bp;
        if(free_length <= 1){
            free_end = bp;
        }
    }
    // largest = MAX(largest, size);
    return bp;
}

void removefree(void *bp){
    // if(free_start == bp){
    //     free_start = NEXT_FREE(bp);
    // }
    if(PREV_FREE(bp) != NULL){
        NEXT_FREE(PREV_FREE(bp)) = NEXT_FREE(bp);
    }
    else {
        free_start = NEXT_FREE(bp);
    }
    if(NEXT_FREE(bp) != NULL){
        PREV_FREE(NEXT_FREE(bp)) = PREV_FREE(bp);
    }
    if (bp == free_end) {
        free_end = PREV_FREE(bp);
    }

    // SET values in block to NULL that we are removing (might be unneccessary)
    PREV_FREE(bp) = NULL;
    NEXT_FREE(bp) = NULL;
    free_length--;
}

static void updateLargest() {
    void *bp;
    largest = 0;
    for (bp = free_start; bp != NULL; bp = NEXT_FREE(bp)) {
        if (GET_SIZE(HDRP(bp)) > largest) {
            largest = GET_SIZE(HDRP(bp));
        }
    }
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

    printf("%p: header: [%d:%c] prev_free[%p] next_free[%p] footer: [%d:%c]\n", bp,
           hsize, (halloc ? 'a' : 'f'),
           PREV_FREE(bp), NEXT_FREE(bp),
           fsize, (falloc ? 'a' : 'f'));
}

static void printfreelist()
{
    printf("--- PRINTING ENTIRE FREE LIST FOR GODS SAKE ---\n");
    printf("Largest Free: %d\n", largest);
    printf("free_start: %p free_end: %p\n", free_start, free_end);
    char *bp;
    for(bp = free_start; bp != NULL; bp = NEXT_FREE(bp)){
        printblock(bp);
    }
    printf("--- FINISHED PRINTING ENTIRE FREE LIST FGS ---\n\n");
    fflush(stdout);
}
