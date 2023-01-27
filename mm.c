/*
 * ========================================================================
 *  Autorka rozwiązania: Julia Noczyńska
 *  numer indeksu: 331013
 * ========================================================================
 */
/*
 * =========================================================================
 *                               DESCRITPION
 * =========================================================================
 * Segregated list of free blocks with optimized boundary tags.
 *
 * It contains 9 buckets storing free blocks of sizes:
 * 16, 32, (32.64], (64.128], (128, 256], (256, 512], (512, 1024], (1024, 2048],
 * and the last one with blocks bigger than 2048 bytes.
 *
 * The minimum size of the allocated/free block is 16 bytes,
 * because of the 16-byte alignment requirement.
 *
 * Free and allocated blocks contain 4 bytes header with the information about
 * the size, type of the block (alloc/free), and prevfree flag, which informs if
 * the previous file is free. It allows to remove the footer from the allocated
 * block, so only the free blocks will have the footer.
 *
 * Free blocks contain a number which is the distance of the previous/next block
 * from the beginning of the heap. Thanks to this, we don't need to store
 * pointers, which would increase the minimum block size to 32 bytes,
 * we only store two 4-byte numbers.
 *
 * In this approach, a block is allocated by searching for the best fit free
 * block on the segregated list. We search for the suitable bucket,
 * and then we search the list with the appropriate index
 * (if we don't find fit in that list, we search the next one).
 * Then place the new block on the place of this selected free block.
 * If there is no fit, then we extend the heap by incrementing the
 * brk pointer (taking into account the case when the last block is free, so we
 * can extend the heap by the smaller amount of bytes).
 *
 *  When we free a block, we coalesce it with the blocks next to it, if they are
 * free. We add the new free block at the front of the free_list of appropriate
 * index.
 *
 * Realloc function checks if the block on the left is free,
 * if so, it can be used when increasing the block size.
 * If the amount of free space is not enough but the block is at the end of the
 * heap, we execute extend heap, otherwise we execute malloc to allocate the new
 * block of the requested size and free the old block.
 * ============================================================================
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
#define debug(fmt, ...) printf("%s: " fmt "\n", __func__, __VA_ARGS__)
#define msg(...) printf(__VA_ARGS__)
#else
#define debug(fmt, ...)
#define msg(...)
#endif

/* do not change the following! */
#ifdef DRIVER

/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* --=[ global values and macros ]=------------------------------------------*/
/* Macros from CSAPP book */
#define WSIZE 4 /* Word and header/footer size (bytes) */

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Write a word at address p */
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* From mm-implicit.c file */
typedef int32_t word_t; /* Heap is bascially an array of 4-byte words. */

typedef enum {
  FREE = 0,     /* Block is free */
  USED = 1,     /* Block is used */
  PREVFREE = 2, /* Previous block is free (optimized boundary tags) */
} bt_flags;

/* global pointers */
static word_t *heap_start; /* Address of the first block */
static word_t *heap_end;   /* Address past last byte of last block */
static word_t *last;       /* Points at last block */

/* --=[ boundary tag handling ]=-------------------------------------------- */
/* from mm-implicit.c file */
static inline size_t bt_size(word_t *bt) {
  return *bt & ~(USED | PREVFREE);
}

static inline int bt_used(word_t *bt) {
  return *bt & USED;
}

static inline int bt_free(word_t *bt) {
  return !(*bt & USED);
}

/* Previous block free flag handling for optimized boundary tags. */
static inline bt_flags bt_get_prevfree(word_t *bt) {
  return *bt & PREVFREE;
}

/* clear prevfree flag */
static inline void bt_clr_prevfree(word_t *bt) {
  if (bt)
    *bt &= ~PREVFREE;
}

/* set prevfree flag */
static inline void bt_set_prevfree(word_t *bt) {
  *bt |= PREVFREE;
}

/* --=[ block handling procedures ]=----------------------------------------*/

/* Given boundary tag address calculate it's buddy address. */
static inline word_t *bt_footer(word_t *bt) {
  return (void *)bt + bt_size(bt) - sizeof(word_t);
}

/* Given payload pointer returns an address of boundary tag. */
static inline word_t *bt_header(void *ptr) {
  return (word_t *)ptr - 1;
}

/* Returns address of payload. */
static inline void *bt_payload(word_t *bt) {
  return bt + 1;
}

/* Returns address of next block or NULL. */
static inline word_t *bt_next(word_t *block_ptr) {
  word_t *next = (void *)block_ptr + bt_size(block_ptr);
  if (next <= heap_end)
    return next;

  return NULL;
}

/* Returns address of previous block or NULL. */
static inline word_t *bt_prev(word_t *block_ptr) {
  word_t *prev = (void *)block_ptr - bt_size(block_ptr - 1);
  if (prev >= heap_start)
    return prev;

  return NULL;
}

/* Creates boundary tag(s) for given block. */
static inline void bt_make(word_t *bt, size_t size, bt_flags flags) {
  /* create header*/
  PUT(bt, PACK(size, flags));
  /* if new block is allocated, clear the prevfree flag in the next block*/
  if (bt_used(bt)) {
    if (bt_next(bt))
      bt_clr_prevfree(bt_next(bt));
    return;
  }
  /* else set the prevfree flag in the next block*/
  if (bt_next(bt))
    bt_set_prevfree(bt_next(bt));

  /*and create footer */
  PUT(bt_footer(bt), PACK(size, flags));
}

/* round up the size to fulfill the alignment req. */
static size_t round_up(size_t size) {
  return (size_t)(size + ALIGNMENT - 1) & -ALIGNMENT;
}

/* --=[ explicit list handling ]=------------------------------------------ */
/* In the free block there is header, footer and two numbers representing the
 * distance from the heap_start pointer. If we add the first number to the
 * heap_start pointer, we get the address of the next free block, if we add the
 * second, we get the address of the previous block. */

/* Global pointers */
static word_t **segregated_list;
static word_t *free_list_start;
static word_t *last_free;
/* Returns address of next free block or NULL. */
static inline word_t *get_free_next(word_t *block_ptr) {
  word_t next = *(block_ptr + 1);
  if (next < 0)
    return NULL;

  return heap_start + next;
}

/* Returns address of previous free block or NULL. */
static inline word_t *get_free_prev(word_t *block_ptr) {
  word_t prev = *(block_ptr + 2);
  if (prev < 0)
    return NULL;

  return heap_start + prev;
}

/* Set address of next free block */
static inline void set_free_next(word_t *block_ptr, word_t *next_block) {
  *(block_ptr + 1) = (word_t)(next_block - heap_start);
}

/* Set address of previous free block */
static inline void set_free_prev(word_t *block_ptr, word_t *prev_block) {
  *(block_ptr + 2) = (word_t)(prev_block - heap_start);
}

/* Add the new free block at the end of the free_list from segregated_list of
 * given index */
static inline void free_list_append(word_t *block_ptr, word_t index) {
  /* Prev block will return NULL */
  set_free_prev(block_ptr, heap_start - 1);
  /* If free list is empty set prev block to NULL (the distance from the
   * heap_start will be set to -1)*/
  if (segregated_list[index] == NULL) {
    set_free_next(block_ptr, heap_start - 1);
  } else { /* else set prev and next block */
    set_free_prev(segregated_list[index], block_ptr);
    set_free_next(block_ptr, segregated_list[index]);
  }
  /* It will be a new last block */
  segregated_list[index] = block_ptr;
}

/* Delete the block of the given address from the free_list from segregated_list
 * of given index */
static inline void free_list_delete(word_t *block_ptr, word_t index) {
  /* If the block was the only one on the list, the list will be empty now */
  if (segregated_list[index] == block_ptr && get_free_next(block_ptr) == NULL) {
    segregated_list[index] = NULL;
    return;
  }
  /* If that was the first block of the list we set the next block as the new
   * beginning of the list */
  if (segregated_list[index] == block_ptr) {
    set_free_prev(get_free_next(block_ptr), heap_start - 1);
    segregated_list[index] = get_free_next(block_ptr);
    return;
  }
  /* If we delete the block that is somewhere in the middle of the list, we need
   * to connect the previous block with the next one */
  if (segregated_list[index] != block_ptr && get_free_next(block_ptr) != NULL) {
    set_free_next(get_free_prev(block_ptr), get_free_next(block_ptr));
    set_free_prev(get_free_next(block_ptr), get_free_prev(block_ptr));
    return;
  }
  /* else, the block was the last one, so we set the next block of the previous
   * one to NULL, and that block will be the new last block */
  set_free_next(get_free_prev(block_ptr), heap_start - 1);
  last_free = get_free_prev(block_ptr);
}
/* --=[ segregated list ]=------------------------------------------ */

#define NUM_LIST 9 /* Number of buckets */

/* The following buckets consist of the following size of blocks (in the ranges:
 * e.g. 2 (segregated_list[2]) bucket are blocks in the range (32, 64] bytes*/
/*
#define SIZE0 16
#define SIZE1 32
#define SIZE2 64
#define SIZE3 128
#define SIZE4 256
#define SIZE5 512
#define SIZE6 1024
#define SIZE7 2048
#define SIZE8 4096*/

/* Binsearch to find the index of a list that contains blocks of a given size */
static inline word_t get_index(size_t size) {
  if (size <= 512) {
    if (size <= 64) {
      if (size == 16)
        return 0;
      if (size == 32)
        return 1;
      return 2;
    } else if (size <= 256) {
      if (size <= 128)
        return 3;
      return 4;
    }
    return 5;
  }
  if (size <= 2048) {
    if (size <= 1024)
      return 6;
    return 7;
  }
  return 8;
}

/* --=[ init procedures ]=------------------------------------------ */

static void place(word_t *bp, size_t asize);
static word_t *extend_heap(size_t words);
static word_t *find_fit(size_t asize);
static word_t *coalesce(word_t *bp);

/* --=[ mm_init - Called when a new trace starts. ]=--------------------*/
/* Sets global values */
int mm_init(void) {
  /* initialize segregated list that consist 9 pointers */
  if ((segregated_list = mem_sbrk(8 * NUM_LIST)) == (void *)-1)
    return -1;

  for (int i = 0; i < NUM_LIST; i++) {
    segregated_list[i] = NULL;
  }

  if ((heap_start = (word_t *)mem_sbrk(2 * ALIGNMENT)) == (void *)-1)
    return -1;
  /* Prologue and epilogue initialisation is from CSAPP book */
  PUT(heap_start, 0); /* Alignment padding */
  bt_make(
    heap_start, 20,
    USED); /* Prologue -> 20 bytes = header + footer + (12 bytes) payload */

  PUT(heap_start + 5, PACK(0, USED)); /* Epilogue header -> 4 bytes*/

  /* Set global pointers */
  heap_start += 5;
  heap_end = heap_start;
  last = NULL;

  free_list_start = NULL;
  last_free = NULL;

  return 0;
}

/* --=[ extend_heap]=------------------------------------------------------- */
/* Extend heap by requested amount of bytes, if the mem_sbrk fails, return NULL,
 * else - create a new allocated block and the new epilog. */
static word_t *extend_heap(size_t size) {
  if ((long)(mem_sbrk(size)) == -1)
    return NULL;

  word_t *block_ptr = heap_end; /* We need to overwrite epilogue*/

  /* If the last block was free, add it to the new allocated block */
  if (last != NULL && bt_free(last)) {
    block_ptr = last;
    free_list_delete(block_ptr, get_index(bt_size(last)));
    size += bt_size(last);
  }
  /* Create a new allocated block */
  bt_make(block_ptr, size, USED);

  PUT(((void *)block_ptr + size), PACK(0, USED)); /* New epilogue header */

  last = block_ptr; /* Pointer to the last block */

  heap_end = (void *)block_ptr + size; /* Pointer to the new epilogue*/

  return block_ptr;
}

/* --=[ malloc ]=----------------------------------------------------------- */
/* Search for a suitable free block, and place the new allocated block. If there
 * is no proper free block size - extend heap.
 * return a pointer to the payload */
void *malloc(size_t size) {
  size_t asize; /* Adjusted block size */
  word_t *block_ptr;

  /* Ignore spurious requests */
  if (size == 0)
    return NULL;

  /* Adjust block size to include header and alignment reqs. */
  asize = round_up(size + WSIZE);

  /* If there is a suitable block, place a new block there and return a pointer
   * to the payload */
  if ((block_ptr = find_fit(asize)) != NULL) {
    place(block_ptr, asize);
    return (void *)bt_payload(block_ptr);
  }

  /* No fit found. Get more memory and place the block */
  size_t extend_size = asize;

  /* If the last block is free, we can extend heap by smaller amount of
   * bytes, and place the new block in place of this free block */
  if (last != NULL && bt_free(last))
    extend_size -= bt_size(last);

  /* If extend_heap fails, return NULL */
  if ((block_ptr = extend_heap(extend_size)) == NULL)
    return NULL;
  /* extend_heap returned a pointer to the new allocated block*/
  return (void *)bt_payload(block_ptr);
}

/* --=[ place ]=---------------------------------------------------------- */
/* Place the new allocated block and split the free block if it's possible */
static void place(word_t *block_ptr, size_t asize) {
  /* size of the selected free block */
  size_t fsize = bt_size(block_ptr);

  /* We need to delete the free block t=from the list of free blocks */
  free_list_delete(block_ptr, get_index(fsize));

  /* split the block into allocated and free
   if the new free block satisfies the alignment */
  if ((fsize - asize) >= ALIGNMENT) {
    bt_make(block_ptr, asize, USED | bt_get_prevfree(block_ptr));
    block_ptr = bt_next(block_ptr);
    bt_make(block_ptr, fsize - asize, FREE);
    free_list_append(block_ptr, get_index(fsize - asize));
    /* If we changed the last block, the new free block will be the new last
     * block */
    if (last < block_ptr)
      last = block_ptr;
  } else {
    /* internal fragmentation
    because we can't create free block with size < ALIGNMENT*/
    bt_make(block_ptr, fsize, USED | bt_get_prevfree(block_ptr));
  }
}

/* --=[ find fit]=----------------------------------------------------------- */
/* First fit in segregated list - find free block that is suitable for the new
 * block that will be allocated */
static word_t *find_fit(size_t asize) {

  /* Best fit search */
  // word_t *ptr;
  word_t *best_fit = NULL;
  word_t index = get_index(asize);
  while (index < NUM_LIST) {
    for (word_t *ptr = segregated_list[index]; ptr != NULL;
         ptr = get_free_next(ptr)) {
      if (bt_size(ptr) >= asize) {
        if (best_fit == NULL || bt_size(ptr) < bt_size(best_fit)) {
          best_fit = ptr;
        }
      }
    }
    if (best_fit != NULL) {
      return best_fit;
    }

    index++;
  }

  return NULL;
}

/* --=[ free ]=------------------------------------------------------------- */
/* Create a new free block and run coalesce if there is another free block next
 * to it*/
void free(void *ptr) {
  /* If ptr is NULL there is no block to free */
  if (ptr == NULL)
    return;

  /* The argument is a pointer to the payload, so we need to get pointer to the
   * header */
  word_t *block_ptr = bt_header(ptr);
  /* We need to get the prevfree flag of an allocated block we want to free, to
   * know if we can coalesce the previous block with the new free block */
  bt_make(block_ptr, bt_size(block_ptr), FREE | bt_get_prevfree(block_ptr));

  /* Coalesce if possible*/
  if (bt_get_prevfree(block_ptr) || bt_free(bt_next(block_ptr))) {
    coalesce(block_ptr);
  } else {
    free_list_append(block_ptr, get_index(bt_size(block_ptr)));
  }
}

/* --=[ coalesce ]=---------------------------------------------------------- */
/* If there is another free block to the right or to the left of the new one,
 * coalesce them */
static word_t *coalesce(word_t *block_ptr) {

  word_t *prev_block = bt_prev(block_ptr);
  word_t *next_block = bt_next(block_ptr);
  word_t size = bt_size(block_ptr);

  int prev_free = bt_get_prevfree(block_ptr);
  int next_free = bt_free(next_block);

  /* Check if there is need to change the pointer to the last block */
  int change_last = (block_ptr == last || (next_block == last && next_free));

  if (next_free) {
    size += bt_size(next_block);
    free_list_delete(next_block, get_index(bt_size(next_block)));
  }

  if (prev_free) {
    size += bt_size(prev_block);
    block_ptr = prev_block;
    free_list_delete(block_ptr, get_index(bt_size(block_ptr)));
  }

  bt_make(block_ptr, size, FREE);
  free_list_append(block_ptr, get_index(size));

  if (change_last)
    last = block_ptr;

  return block_ptr;
}

/* --=[ realloc ]=---------------------------------------------------------- */
/* Check if there is enough space around the block to change the size,
 * if there is space- make a new allocated block and free block (if the split is
 * possible) if there is no space, but the block is at the end of the heap, we
 * can just extend heap, else we just need to malloc the new block and free the
 * old one. */
void *realloc(void *ptr, size_t size) {
  /* If ptr is NULL, then this is just malloc. */
  if (!ptr)
    return malloc(size);

  /* If size == 0 then this is just free, and we return NULL. */
  if (size == 0) {
    free(ptr);
    return NULL;
  }
  /* variables */
  word_t *block_ptr = bt_header(ptr);
  word_t *next = bt_next(block_ptr);

  /* free_size variable to check if there is free space to realloc without using
   * malloc or extend heap */
  size_t free_size = bt_size(block_ptr);
  size_t asize = round_up(size + WSIZE); /* new adjusted size */

  int next_free = bt_free(next);

  if (next_free)
    free_size += bt_size(next);

  int change_last = (block_ptr == last || (next == last && next_free));
  /* if the block is at the end of the heap, we can extend heap and change the
   * size of the block in the header */
  if (free_size < asize) {
    if (change_last) {
      if (extend_heap(asize - free_size) == NULL)
        return NULL;

      bt_make(block_ptr, asize, USED);
      last = block_ptr;
      return ptr;
    }

    /* if there is no space,
    we need to malloc the new block and free the old one  */
    void *new_ptr = malloc(size);
    /* If malloc() fails, the original block is left untouched. */
    if (!new_ptr)
      return NULL;

    /* Copy the old data. */
    memcpy(new_ptr, ptr, free_size - WSIZE);

    /* Free the old block. */
    free(ptr);

    return new_ptr;
  }

  /* We have enough space, but we must check if we can split it into used and
   * free blocks  */

  /* if next block is free, delete it, because it will be changed */
  if (next_free)
    free_list_delete(next, get_index(bt_size(next)));

  if ((free_size - asize) >= ALIGNMENT) {
    /* Split the block to used and free blocks */
    bt_make(block_ptr, asize, USED | bt_get_prevfree(block_ptr));
    block_ptr = bt_next(block_ptr);
    bt_make(block_ptr, free_size - asize, FREE);
    free_list_append(block_ptr, get_index(free_size - asize));
  } else {
    /* We can't create a new free block with size < ALIGNMENT */
    bt_make(block_ptr, free_size, USED | bt_get_prevfree(block_ptr));
  }

  if (change_last)
    last = block_ptr;

  return ptr;
}

/* --=[ calloc ]=---------------------------------------------------------- */

void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);

  /* If malloc() fails, skip zeroing out the memory. */
  if (new_ptr)
    memset(new_ptr, 0, bytes);

  return new_ptr;
}

/* --=[ checkheap ]=------------------------------------------------------- */
/* Prints the address of the block, flags, and the address where the next block
 * starts. There is also a separate list of free blocks*/
void mm_checkheap(int verbose) {
  word_t *bt;
  msg("Check Heap \n");
  for (bt = heap_start; bt && bt_size(bt) > 0; bt = bt_next(bt)) {
    msg("Block Address: %p Block Header Size: %ld Block Header type: %d Block "
        "PREVFREE type: %d Block ends at: %p\n",
        bt, bt_size(bt), bt_used(bt), bt_get_prevfree(bt), bt_next(bt));
  }
  msg("Heap start: %p Heap end: %p last: %p \n", heap_start, heap_end, last);
  msg("Check Heap End\n\n");

  msg("Check free list \n");
  for (int i = 0; i < NUM_LIST; i++) {
    msg("\n%d LIST\n", i);
    for (bt = segregated_list[i]; bt != NULL; bt = get_free_next(bt)) {
      msg(
        "Block Address: %p Block Header Size: %ld Block Header type: %d Block "
        "PREVFREE type: %d Block ends at: %p\n",
        bt, bt_size(bt), bt_used(bt), bt_get_prevfree(bt), bt_next(bt));
    }
  }

  msg("Heap start: %p Heap end: %p last: %p \n", heap_start, heap_end, last);
  msg("Check free list \n\n");
}
