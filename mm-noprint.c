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
char *heap_start = 0x0;
char *free_start = 0x0;
size_t largest;
char *heap_end = 0x0;
char *free_end = 0x0;

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
    largest = 0;
    NEXT_FREE(heap_start) = NULL;
    PREV_FREE(heap_start) = NULL;
    // PUT(NEXT_FREE(heap_start), 0); // Pointer to first free block
    // PUT(PREV_FREE(heap_start), 0); // Stores size of largest free block
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

    // asize = ALIGN(size + SIZE_T_SIZE);
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
    // TODO: update largest if needed, iterate through freelist
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    // printf("mm_free() freeing Block: %p\n", bp); fflush(stdout); printblock(bp);
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    newfree(bp);
    coalesce(bp);
    printfreelist();
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
    for (bp = free_start; bp != NULL; bp = NEXT_FREE(bp)) {
    //If our size is smaller than the size of the block, return that block
        if (size <= ((size_t)GET_SIZE(HDRP(bp)) /* + OVERHEAD */)) {
            return bp;
        }
    }

    //No fit, need to extend... Somethings wrong with the largest global var
    return NULL;
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
    if(bsize >= largest){
        updateLargest();
    }
}

void newfree(void *bp)
{
    /* Get old first pointer on free list */
    // void *old_firstfree = NEXT_FREE(heap_start);
    void *old_freestart = free_start;

    /* newFree points to old first free */
    NEXT_FREE(bp) = old_freestart;

    /* Previous free to new free block is 0 (end) */
    PREV_FREE(bp) = NULL;

    // Put largest free block size in Prolouge Header
    largest = MAX(largest, GET_SIZE(HDRP(bp)));
    // PUT(PREV_FREE(heap_start), MAX(GET(PREV_FREE(heap_start)), GET_SIZE(bp)));

    /* Old first free previous free points to new free block */
    if (old_freestart != NULL){
        PREV_FREE(old_freestart) = bp;
    }
    /* Prolouge header points to new free block */
    free_start = bp;
    // NEXT_FREE(heap_start) = bp;
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
    }
    largest = MAX(largest, size);
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

    // SET values in block to NULL that we are removing (might be unneccessary)
    PREV_FREE(bp) = NULL;
    NEXT_FREE(bp) = NULL;
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
    char *bp;
    for(bp = free_start; bp != NULL; bp = NEXT_FREE(bp)){
        printblock(bp);
    }
    printf("--- FINISHED PRINTING ENTIRE FREE LIST FGS ---\n\n");
    fflush(stdout);
}