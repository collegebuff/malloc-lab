/*
 * mm.c - Malloc implementation using segregated fits with address-ordered
 *        explicit linked lists and reallocation heuristics
 *
 * Each block is wrapped in a 4-byte header and a 4-byte footer. Free blocks
 * are stored in one of many linked lists segregated by block size. The n-th
 * list contains blocks with a byte size that spans 2^n to 2^(n+1)-1. Within
 * each list, blocks are sorted by memory address in ascending order.
 * Coalescing is performed immediately after each heap extension and free
 * operation. Reallocation is performed in place, using a buffer and a
 * reallocation bit to ensure the availability of future block expansion.
 *
 * Header entries consist of the block size (all 32 bits), reallocation tag
 * (second-last bit), and allocation bit (last bit).
 *
 *   The following resourses have been used in this code the book "Computer Systems - A Programmer's Perspective" 
 * and online resourse from github user " mightydeveloper ". 
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
    " Mother Hen",
    /* First member's full name */
    " Bryce Strickland ",
    /* First member's email address */
    " brst8941@colorado.edu ",
    /* Second member's full name (leave blank if none) */
    " Nika Shafranov",
    /* Second member's email address (leave blank if none) */
    " nish1367@colorado.edu "
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


// My additional Macros
#define WSIZE     4          // word and header/footer size (bytes)
#define DSIZE     8          // double word size (bytes)
#define INITCHUNKSIZE (1<<6)
#define CHUNKSIZE (1<<12) /* Page size in bytes */

#define LISTLIMIT     20 /* Number of segregated lists */
#define REALLOC_BUFFER  (1<<7) /* Reallocation buffer */

static inline int MAX(int x, int y) { /* Maximum of two numbers */
    return x > y ? x : y;
}

static inline int MIN(int x, int y) { /* Minimum of two numbers */
    return x < y ? x : y;
}

//
// Pack a size and allocated bit into a word
// We mask of the "alloc" field to insure only
// the lower bit is used
//

static inline size_t PACK(size_t size, int alloc) {
    return ((size) | (alloc & 0x1));
}

/* Read and write a word at address p */
static inline size_t GET(void *p) {
    return  *(size_t *)p;
}

// Preserve reallocation bit
/*static inline void PUT( void *p, size_t val)
{
    (*((size_t *)p) = val) | GET_TAG(p);
} */

// Clear reallocation bit
static inline void PUT_NOTAG (void *p, size_t val){
  *((size_t *)p) = val;
}

/* Adjust reallocation tag */
static inline size_t REMOVE_RATAG(void *p){
    return GET(p) & 0x2;
}
static inline size_t SET_RATAG(void *p){
    return GET(p) | 0x2;
}


// Preserve reallocation bit
#define PUT(p, val)       (*(unsigned int *)(p) = (val) | GET_TAG(p))


// Store predecessor or successor pointer for free blocks
/*static inline void SET_PTR(void *p, size_t ptr){
     *((size_t *)p) = (size_t ptr);
}*/
#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))

// Read the size and allocation bit from address p
static inline size_t GET_SIZE( void *p )  {
    return GET(p) & ~0x7;
}

static inline int GET_ALLOC( void *p  ) {
    return GET(p) & 0x1;
}

static inline size_t GET_TAG( void *p )  {
    return GET(p) & 0x2;
}

//#define GET_TAG(p)   (GET(p) & 0x2)

// Address of block's header and footer
static inline void *HDRP(void *bp) {
    
    return ( (char *)bp) - WSIZE;
}

static inline void *FTRP(void *bp) {
    return ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE);
}


// Address of (physically) next and previous blocks
static inline void *NEXT_BLKP(void *ptr) {
    return  ((char *)(ptr) + GET_SIZE(((char *)(ptr) - WSIZE)));
}

static inline void* PREV_BLKP(void *ptr){
    return  ((char *)(ptr) - GET_SIZE(((char *)(ptr) - DSIZE)));
}


// Address of free block's predecessor and successor entries
static inline void* PRED_PTR(void *ptr){
    return ((char *)(ptr));
}

static inline void* SUCC_PTR(void *ptr){
    return ((char*)(ptr) + WSIZE);
}

// Address of free block's predecessor and successor on the segregated list
static inline void* PRED(void *ptr){
    return (*(char **)(ptr));
}

static inline void* SUCC(void *ptr){
    return (*(char **)(SUCC_PTR(ptr)));
}



// End of my additional macros


// Global var
void *segregated_free_lists[LISTLIMIT]; /* Array of pointers to segregated free lists */


// Functions
static void *extend_heap(size_t size);
static void *coalesce(void *ptr);
static void *place(void *ptr, size_t asize);
static void insert_node(void *ptr, size_t size);
static void delete_node(void *ptr);



///////////////////////////////// Block information /////////////////////////////////////////////////////////
/*
 
 A   : Allocated? (1: true, 0:false)
 RA  : Reallocation tag (1: true, 0:false)
 
 < Allocated Block >
 
 
 31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10  9  8  7  6  5  4  3  2  1  0
 +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Header :   |                              size of the block                                       |  |  | A|
 bp ---> +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 |                                                                                               |
 |                                                                                               |
 .                              Payload and padding                                              .
 .                                                                                               .
 .                                                                                               .
 +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Footer :   |                              size of the block                                       |     | A|
 +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 
 
 < Free block >
 
 31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10  9  8  7  6  5  4  3  2  1  0
 +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Header :   |                              size of the block                                       |  |RA| A|
 bp ---> +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 |                        pointer to its predecessor in Segregated list                          |
 bp+WSIZE--> +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 |                        pointer to its successor in Segregated list                            |
 +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 .                                                                                               .
 .                                                                                               .
 .                                                                                               .
 +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Footer :   |                              size of the block                                       |     | A|
 +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 
 
 */
///////////////////////////////// End of Block information /////////////////////////////////////////////////////////

//////////////////////////////////////// Helper functions //////////////////////////////////////////////////////////

/*
 * extend_heap - Extend the heap with a system call. Insert the newly
 *               requested free block into the appropriate list.
 */
static void *extend_heap(size_t size)
{
    void *ptr;   /* Pointer to newly allocated memory */
    size_t asize;  /*Adjusted size */
    
    asize = ALIGN(size); /* Maintain alignment*/
    
    /* Extend the heap */
    if ((ptr = mem_sbrk(asize)) == (void *)-1)
        return NULL;
    
    /* Set headers and footer */
    PUT_NOTAG(HDRP(ptr), PACK(asize, 0)); /* Free block header */
    PUT_NOTAG(FTRP(ptr), PACK(asize, 0)); /* Free block footer */
    PUT_NOTAG(HDRP(NEXT_BLKP(ptr)), PACK(0, 1));  /* Epilogue header */
    
    /* Insert new block into appropriate list */
    insert_node(ptr, asize);
    
    /* Coalesce if the previous block was free */
    return coalesce(ptr);
}

/*
 * insert_node - Insert a block pointer into a segregated list. Lists are
 *               segregated by byte size, with the n-th list spanning byte
 *               sizes 2^n to 2^(n+1)-1. Each individual list is sorted by
 *               pointer address in ascending order.
 */
static void insert_node(void *ptr, size_t size) {
    int list = 0;
    void *search_ptr = ptr;
    void *insert_ptr = NULL;
    
    /* Select segregated list*/
    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }
    
/* Select location on list to insert pointer while keeping list
     organized by byte size in ascending order. */
    search_ptr = segregated_free_lists[list];
    while ((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr)))) {
        insert_ptr = search_ptr;
        search_ptr = PRED(search_ptr);
    }
    
    // Set predecessor and successor
    if (search_ptr != NULL) {
        if (insert_ptr != NULL) {
            SET_PTR(PRED_PTR(ptr), search_ptr);
            SET_PTR(SUCC_PTR(search_ptr), ptr);
            SET_PTR(SUCC_PTR(ptr), insert_ptr);
            SET_PTR(PRED_PTR(insert_ptr), ptr);
        } else {
            SET_PTR(PRED_PTR(ptr), search_ptr);
            SET_PTR(SUCC_PTR(search_ptr), ptr);
            SET_PTR(SUCC_PTR(ptr), NULL);
            
            /* Add block to appropriate list */
            segregated_free_lists[list] = ptr;
        }
    } else {
        if (insert_ptr != NULL) {
            SET_PTR(PRED_PTR(ptr), NULL);
            SET_PTR(SUCC_PTR(ptr), insert_ptr);
            SET_PTR(PRED_PTR(insert_ptr), ptr);
        } else {
            SET_PTR(PRED_PTR(ptr), NULL);
            SET_PTR(SUCC_PTR(ptr), NULL);
            
            /* Add block to appropriate list */
            segregated_free_lists[list] = ptr;
        }
    }
    
    return;
}

/*
 * delete_node: Remove a free block pointer from a segregated list. If
 *              necessary, adjust pointers in predecessor and successor blocks
 *              or reset the list head.
 */

static void delete_node(void *ptr) {
    int list = 0;
    size_t size = GET_SIZE(HDRP(ptr));
    
    /* Select segregated list */
    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }
    
    if (PRED(ptr) != NULL) {
        if (SUCC(ptr) != NULL) {
            SET_PTR(SUCC_PTR(PRED(ptr)), SUCC(ptr));
            SET_PTR(PRED_PTR(SUCC(ptr)), PRED(ptr));
        } else {
            SET_PTR(SUCC_PTR(PRED(ptr)), NULL);
            segregated_free_lists[list] = PRED(ptr);
        }
    } else {
        if (SUCC(ptr) != NULL) {
            SET_PTR(PRED_PTR(SUCC(ptr)), NULL);
        } else {
            segregated_free_lists[list] = NULL;
        }
    }
    
    return;
}

/*
 * coalesce - Coalesce adjacent free blocks. Sort the new free block into the
 *            appropriate list.
 */
static void *coalesce(void *ptr)
{
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));
    
    
    // Do not coalesce with previous block if the previous block is tagged with Reallocation tag
    if (GET_TAG(HDRP(PREV_BLKP(ptr))))
        prev_alloc = 1;
    
    /* Return if previous and next blocks are allocated */
    if (prev_alloc && next_alloc) {
        return ptr;
    }
    else if (prev_alloc && !next_alloc) {  /* Detect free blocks and merge, if possible */
        delete_node(ptr);
        delete_node(NEXT_BLKP(ptr));
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {
        delete_node(ptr);
        delete_node(PREV_BLKP(ptr));
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        PUT(FTRP(ptr), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    } else {
        delete_node(ptr);
        delete_node(PREV_BLKP(ptr));
        delete_node(NEXT_BLKP(ptr));
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }
    
     /* Adjust segregated linked lists */
    insert_node(ptr, size);
    
    return ptr;
}

/*
 * place - Set headers and footers for newly allocated blocks. Split blocks
 *         if enough space is remaining.
 */
static void *place(void *ptr, size_t asize)
{
    size_t ptr_size = GET_SIZE(HDRP(ptr));
    size_t remainder = ptr_size - asize;
    
     /* Remove block from list */
    delete_node(ptr);
    
    /* Do not split block*/
    if (remainder <= DSIZE * 2) {
        PUT(HDRP(ptr), PACK(ptr_size, 1)); /* Block header */
        PUT(FTRP(ptr), PACK(ptr_size, 1)); /* Block footer */
    }
    
    else if (asize >= 100) {
        /* split block */
        PUT(HDRP(ptr), PACK(remainder, 0)); /* Block header */
        PUT(FTRP(ptr), PACK(remainder, 0)); /* Block footer */
        PUT_NOTAG(HDRP(NEXT_BLKP(ptr)), PACK(asize, 1)); /* Next header */
        PUT_NOTAG(FTRP(NEXT_BLKP(ptr)), PACK(asize, 1)); /* Next footer */
        insert_node(ptr, remainder);
        return NEXT_BLKP(ptr);
        
    }
    
    else {
        /* Split block */
        PUT(HDRP(ptr), PACK(asize, 1)); /* Block header */
        PUT(FTRP(ptr), PACK(asize, 1)); /* Block footer */
        PUT_NOTAG(HDRP(NEXT_BLKP(ptr)), PACK(remainder, 0)); /* Next header */
        PUT_NOTAG(FTRP(NEXT_BLKP(ptr)), PACK(remainder, 0)); /* Next footer */
        insert_node(NEXT_BLKP(ptr), remainder);
    }
    return ptr;
}



//////////////////////////////////////// End of Helper functions ////////////////////////////////////////






/*
 * mm_init - initialize the malloc package.
 * Before calling mm_malloc, mm_realloc, or mm_free,
 * the application program calls mm_init to perform any necessary initializations,
 * such as allocating the initial heap area.
 *
 * Return value : -1 if there was a problem, 0 otherwise.
 */
int mm_init(void)
{
    int list; /* List Counter*/
    char *heap_start; /* Pointer to beginning of heap */
    
    /* Initialize array of pointers to segregated free lists */
    for (list = 0; list < LISTLIMIT; list++) {
        segregated_free_lists[list] = NULL;
    }
    
    /* Allocate memory for the initial empty heap */
    if ((long)(heap_start = mem_sbrk(4 * WSIZE)) == -1)
        return -1;
    
    PUT_NOTAG(heap_start, 0);                            /* Alignment padding */
    PUT_NOTAG(heap_start + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT_NOTAG(heap_start + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT_NOTAG(heap_start + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    
    /* Extend the empty heap */
    if (extend_heap(INITCHUNKSIZE) == NULL)
        return -1;
    
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 *
 * Role :
 * 1. The mm_malloc routine returns a pointer to an allocated block payload.
 * 2. The entire allocated block should lie within the heap region.
 * 3. The entire allocated block should overlap with any other chunk.
 *
 * Return value : Always return the payload pointers that are alligned to 8 bytes.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    void *ptr = NULL;  /* Pointer */
    int list = 0; /* List counter */
    
    /* Ignore size 0 cases */
    if (size == 0)
        return NULL;
    
    /* Adjust block size to include boundary tags and alignment requirements */
    if (size <= DSIZE) {
        asize = 2 * DSIZE;
    } else {
        asize = ALIGN(size+DSIZE);
    }
    
    /* Select a free block of sufficient size from segregated list */
    size_t searchsize = asize;
    while (list < LISTLIMIT) {
        if ((list == LISTLIMIT - 1) || ((searchsize <= 1) && (segregated_free_lists[list] != NULL))) {
            ptr = segregated_free_lists[list];
            // Ignore blocks that are too small or marked with the reallocation bit
            while ((ptr != NULL) && ((asize > GET_SIZE(HDRP(ptr))) || (GET_TAG(HDRP(ptr)))))
            {
                ptr = PRED(ptr);
            }
            if (ptr != NULL)
                break;
        }
        
        searchsize >>= 1;
        list++;
    }
    
    /* Extend the heap if no free blocks of sufficient size are found */
    if (ptr == NULL) {
        extendsize = MAX(asize, CHUNKSIZE);
        
        if ((ptr = extend_heap(extendsize)) == NULL)
            return NULL;
    }
    
    /* Place and divide block */
    ptr = place(ptr, asize);
    
    
    /* Return pointer to newly allocated block */
    return ptr;
}

/*
 * mm_free - Freeing a block does nothing.
 *
 * Role : The mm_free routine frees the block pointed to by ptr
 *
 * Return value : returns nothing
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr)); /* Size of block */
    
    REMOVE_RATAG(HDRP(NEXT_BLKP(ptr))); /* Unset the reallocation tag on the next block */
   
    /* Adjust the allocation status in boundary tags */
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    
    /* Insert new block into appropriate list */
    insert_node(ptr, size);
    
    /* Coalesce free block */
    coalesce(ptr);
    
    return;
}

/*
 * mm_realloc - Reallocate a block in place, extending the heap if necessary.
 *              The new block is padded with a buffer to guarantee that the
 *              next reallocation can be done without extending the heap,
 *              assuming that the block is expanded by a constant number of bytes
 *              per reallocation.
 *
 *              If the buffer is not large enough for the next reallocation,
 *              mark the next block with the reallocation tag. Free blocks
 *              marked with this tag cannot be used for allocation or
 *              coalescing. The tag is cleared when the marked block is
 *              consumed by reallocation, when the heap is extended, or when
 *              the reallocated block is freed.
 *       
 *            Implemented simply in terms of mm_malloc and mm_free
 *
 * Role : The mm_realloc routine returns a pointer to an allocated
 *        region of at least size bytes with constraints.
 *
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *new_ptr = ptr;    /* Pointer to be returned */
    size_t new_size = size; /* Size of new block */
    int remainder;          /* Adequacy of block sizes */
    int extendsize;         /* Size of heap extension */
    int block_buffer;       /* Size of block buffer */
    
    /* Ignore invalid block size */
    if (size == 0)
        return NULL;
    
    /* Adjust block size to include boundary tag and alignment requirements */
    if (new_size <= DSIZE) {
        new_size = 2 * DSIZE;
    } else {
        new_size = ALIGN(size+DSIZE);
    }
    
    /* Add overhead requirements to block size */
    new_size += REALLOC_BUFFER;
    
    /* Calculate block buffer */
    block_buffer = GET_SIZE(HDRP(ptr)) - new_size;
    
    /* Allocate more space if overhead falls below the minimum */
    if (block_buffer < 0) {
        /* Check if next block is a free block or the epilogue block */
        if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) || !GET_SIZE(HDRP(NEXT_BLKP(ptr)))) {
            remainder = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))) - new_size;
            if (remainder < 0) {
                extendsize = MAX(-remainder, CHUNKSIZE);
                if (extend_heap(extendsize) == NULL)
                    return NULL;
                remainder += extendsize;
            }
            
            delete_node(NEXT_BLKP(ptr));
            
            // Do not split block
            PUT_NOTAG(HDRP(ptr), PACK(new_size + remainder, 1)); /* Block header */
            PUT_NOTAG(FTRP(ptr), PACK(new_size + remainder, 1)); /* Block footre */
        } else {
            new_ptr = mm_malloc(new_size - DSIZE);
            memcpy(new_ptr, ptr, MIN(size, new_size));
            mm_free(ptr);
        }
        block_buffer = GET_SIZE(HDRP(new_ptr)) - new_size;
    }
    
    /* Tag the next block if block overhead drops below twice the overhead */
    if (block_buffer < 2 * REALLOC_BUFFER)
        SET_RATAG(HDRP(NEXT_BLKP(new_ptr)));
    
    /* Return the reallocated block */
    return new_ptr;
}
