/*
 * Implements segregated explicit free list
 * by creating doubly linked free lists
 * with a previous and next pointer in every free block,
 * 
 * The lists are segregated by length in powers of two:
 * Free blocks of length 1-4 are in the first list `segs[0]`
 * 4-8 in `segs[1]`
 * 8-16 in `segs[2]`
 * and so on
 * 
 * In this approach, a block contains a heacer, payload, and a footer.
 * Part of the payload points to the previous and next block. 
 * Realloc is implemented directly using mm_malloc and mm_free.
 *
 * Before arriving at the segregated free lists implemetation, we tried
 * implicit free blocks implementation and free lists implementation without
 * segregation
 * 
 * As a starting point for our implementation we used the code from 
 * the textbook CSAPP which we found at this link
 *
 * http://csapp.cs.cmu.edu/3e/ics3/code/vm/malloc/mm.c
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
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Guruprerana Shabadi",
    /* First member's email address */
    "guruprerana.shabadi@polytechnique.edu",
    /* Second member's full name (leave blank if none) */
    "Maika Edberg",
    /* Second member's email address (leave blank if none) */
    "maika.edberg@polytechnique.edu"
};

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ //line:vm:mm:beginconst
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<6)  /* Extend heap by this amount (bytes) */  //line:vm:mm:endconst 

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) //line:vm:mm:pack

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            //line:vm:mm:get
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    //line:vm:mm:put

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   //line:vm:mm:getsize
#define GET_ALLOC(p) (GET(p) & 0x1)                    //line:vm:mm:getalloc

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      //line:vm:mm:hdrp
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //line:vm:mm:ftrp

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) //line:vm:mm:nextblkp
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) //line:vm:mm:prevblkp

#define PREV_FREE(bp) (*(char **)(bp))
#define NEXT_FREE(bp) (*(char **)(bp + WSIZE))

/* Set this to DEBUG to run the consistency checker */
#define DEBUGx

/* $end mallocmacros */

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */

#define N_SEGMENTS 20

/* Array of fixed size to store the pointers to first blocks
 * in each segregated free list
 */
static char *segs[N_SEGMENTS];

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void link_prev_to_next(void *bp);
static int get_segment(size_t size);
static void insert_block(char *bp, size_t size);
static void printblock(void *bp); 
static void checkheap(int verbose);
static void checkblock(void *bp);

/* get_segment - This function computes the segment index to use
 * for a particular block given its block size
 */
static int get_segment(size_t size) {
    int seg = 0;
    size = size >> 2;
    while (size && seg < (N_SEGMENTS - 1)) {
        size = size >> 1;
        seg++;
    }
    return seg;
}

/* insert_block - This function inserts a free block into the
 * right segment given a pointer to it and its size
 */
static void insert_block(char *bp, size_t size) {
    int seg = get_segment(size);
    PREV_FREE(bp) = NULL;
    if (segs[seg] != NULL) {
        PREV_FREE(segs[seg]) = bp;
        NEXT_FREE(bp) = segs[seg];
    } else {
        NEXT_FREE(bp) = NULL;
    }
    segs[seg] = bp;
}

/* 
 * mm_init - Initialize the memory manager, specifically leaving space for 
 * the header and the footer, and the payload.
 * Also initializes the segmented free lists pointers
 */
/* $begin mminit */
int mm_init(void) 
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) //line:vm:mm:begininit
        return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);                     //line:vm:mm:endinit  
    /* $end mminit */

    /* $begin mminit */

    int seg;
    for (seg = 0; seg < N_SEGMENTS; seg++) {
        segs[seg] = NULL;
    }

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */    
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1;
    
    return 0;
}
/* $end mminit */

/* 
 * mm_malloc - Allocate a block with sufficient size
 * searching the list through a doubly linked list,
 * described more specifically in the find_fit function.
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size) 
{
    //printf("Malloc called with %d\n", size);
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;      

    /* $end mmmalloc */
    if (heap_listp == 0){
        mm_init();
    }
    /* $begin mmmalloc */
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)                                          //line:vm:mm:sizeadjust1
        asize = 2*DSIZE;                                        //line:vm:mm:sizeadjust2
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); //line:vm:mm:sizeadjust3

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {  //line:vm:mm:findfitcall
        place(bp, asize);                  //line:vm:mm:findfitplace
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);                 //line:vm:mm:growheap1
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
        return NULL;                                  //line:vm:mm:growheap2
    //add_between_linked_list(bp, asize);
    place(bp, asize);                                 //line:vm:mm:growheap3
    
    #ifdef DEBUG
        mm_check();
    #endif
    return bp;
} 
/* $end mmmalloc */

/* 
 * mm_free - Frees the block,
 * ensuring that the alloction in the header and footer
 * are set to 0, then coalesces as needed.
 */
/* $begin mmfree */
void mm_free(void *bp)
{
    //printf("Free called with %p\n", bp);
    /* $end mmfree */
    if (bp == 0) 
        return;

    /* $begin mmfree */
    size_t size = GET_SIZE(HDRP(bp));
    /* $end mmfree */
    if (heap_listp == 0){
        mm_init();
    }
    /* $begin mmfree */

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
    
    #ifdef DEBUG
        mm_check();
    #endif
}

/* $end mmfree */
/*
 * coalesces block
 * uses a LIFO policy, so regardless of the case, ensures that
 * ensures that the empty block is on the head of the linked list
 * (i.e. it is the first element in the linked list
 *       there is no previous block, 
 *       next points to what was first previously
 *       prev of what was first previously points to it)
 * to coalesce proprely deals with 3 cases.
 * 1. both blocks allocated
 *      no coalescing necessary
 * 2/3. one adjacent block is allocated, the other is not
 *      then the free block and the unallocated block is coalesced
 *      as a result, 
 *      e.g. is left block is free, then the 
 *      left's previous pointer now points next to the right block
 *      and the right block's previous pointer now points to the left's previous
 * 4. neither blocks allocated
 *      then in this case, 
 *      the left's previous pointer's next pointer now points
 *      to the next pointer of the rightmost block
 *      the right's next pointer's previous pointer now points
 *      to the previous pointer of the leftmost block
 */
/* $begin mmfree */
static void *coalesce(void *bp) 
{
    int prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    int next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && !next_alloc) {      /* Case 1 */
        link_prev_to_next(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    }

    else if (!prev_alloc && next_alloc) { /* Case 2 */
        link_prev_to_next(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
    }

    else if (!prev_alloc && !next_alloc) {  /* Case 3 */
        link_prev_to_next(PREV_BLKP(bp));
        link_prev_to_next(NEXT_BLKP(bp));
        
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(HDRP(NEXT_BLKP(bp)));

        bp = PREV_BLKP(bp);
    }
    /* $end mmfree */

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    insert_block(bp, size);
    /* $begin mmfree */
    return bp;
}
/* $end mmfree */

/* function written as to do the pointer operation
*  necessary during coalesccing as explained in the comment above
*  the coalescing function
*  It removes the block pointed by bp from the linked list
*/
static void link_prev_to_next(void *bp) {
    if (bp == NULL)
        return;
    
    if (PREV_FREE(bp) != NULL) {
        NEXT_FREE(PREV_FREE(bp)) = NEXT_FREE(bp);
    } else {
        segs[get_segment(GET_SIZE(HDRP(bp)))] = NEXT_FREE(bp);
    }
    
    if (NEXT_FREE(bp) != NULL) {
        PREV_FREE(NEXT_FREE(bp)) = PREV_FREE(bp);
    }
}

/*
 * mm_realloc - Naive implementation of realloc
 * using mm_malloc and mm_free only
 */
void *mm_realloc(void *ptr, size_t size)
{
    //printf("Realloc called with %p, %d\n", ptr, size);
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        mm_free(ptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
        return mm_malloc(size);
    }

    newptr = mm_malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(ptr));
    if(size < oldsize) oldsize = size;
    memcpy(newptr, ptr, oldsize);

    /* Free the old block. */
    mm_free(ptr);
    
    #ifdef DEBUG
        mm_check();
    #endif

    return newptr;
}

/* 
 * mm_checkheap - Check the heap for correctness
 */
void mm_checkheap(int verbose)  
{ 
    checkheap(verbose);
}

/* 
 * The remaining routines are internal helper routines 
 */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; //line:vm:mm:beginextend
    if ((long)(bp = mem_sbrk(size)) == -1)  
        return NULL;                                        //line:vm:mm:endextend

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */   //line:vm:mm:freeblockhdr
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */   //line:vm:mm:freeblockftr
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ //line:vm:mm:newepihdr
    
    return coalesce(bp);                                          //line:vm:mm:returnblock
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

    if ((csize - asize) >= (2*DSIZE)) {
        link_prev_to_next(bp);

        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        
        coalesce(bp);
    }
    else { 
        link_prev_to_next(bp);
    
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
/* $end mmplace */

/* 
 * find_fit - Find a fit for a block with asize bytes 
 * simply traverses the linked lists, starting at the right linked list
 * then taking the next pointer until the next points to NULL
 * stopping when there is a free block with sufficient size
 * 
 * The right segment to search in is determined by using the get_segment function
 */
/* $begin mmfirstfit */
/* $begin mmfirstfit-proto */
static void *find_fit(size_t asize)
/* $end mmfirstfit-proto */
{
    /* $begin mmfirstfit */
    /* Linked list of free blocks search */
    void *bp;
    int seg;

    for (seg = get_segment(asize); seg < N_SEGMENTS; seg++) {
        for (bp = segs[seg]; bp != NULL; bp = NEXT_FREE(bp)) {
            if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
                return bp;
            }
        }
    }
    return NULL; /* No fit */
}
/* $end mmfirstfit */

static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    checkheap(0);
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  

    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%ld:%c] footer: [%ld:%c]\n", bp, 
           hsize, (halloc ? 'a' : 'f'), 
           fsize, (falloc ? 'a' : 'f')); 
}

static void checkblock(void *bp) 
{
    if ((size_t)bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}

/* 
 * checkheap - Minimal check of the heap for consistency 
 */
void checkheap(int verbose) 
{
    char *bp = heap_listp;

    if (verbose)
        printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose) 
            printblock(bp);
        checkblock(bp);
    }

    if (verbose)
        printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");
}
/* 
* performs a check
* on the structure of the memory
* answering the questionas indicated inside
* the commments of the function
*/


void mm_check(){

    // Is every block in the free list marked as free?
    // Do the pointers in a heap block point to valid heap addresses?
    void *bp_i, *prev;
    int seg;
    for (seg = 0; seg < N_SEGMENTS; seg++) {
        for (bp_i = segs[seg]; bp_i != NULL; bp_i = NEXT_FREE(bp_i)) {
            if (bp_i != segs[seg]){
                if (PREV_FREE(bp_i) != NULL){
                    prev = PREV_FREE(bp_i);
                    if (((int) prev <= (int) mem_heap_lo()) || ((int) prev >= (int) mem_heap_hi())){
                        printf("pointer %p is not a valid heap address", prev);
                    }
                }
            }
            if (((int) bp_i <= (int) mem_heap_lo()) || ((int) bp_i >= (int) mem_heap_hi())){
                printf("pointer %p is not a valid heap address", bp_i);
            }
            if (GET_ALLOC(HDRP(bp_i))){
                printf("An allocated block is marked as free");
            }
        }
    }

    //Are there any contiguous free blocks that somehow escaped coalescing?
    int prev_alloc = 1;
    int curr_alloc;
    for (bp_i = mem_heap_lo(); (int) bp_i <= (int) mem_heap_hi(); bp_i = NEXT_BLKP(bp_i)){
        curr_alloc = GET_ALLOC(HDRP(bp_i));
        if ((! prev_alloc) && (! curr_alloc)){
            printf("there are two contiguous free blocks");
        }
        prev_alloc = curr_alloc;
    }
}












