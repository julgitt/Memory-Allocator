# Memory allocator using segregated lists, created as part of an Operating Systems course.
### The solution is in the file mm.c, the rest of the files, allowing to execute the program, and test it were created by the creator of the task, not by me.


1. ### Method used in short:
    Segregated list of free blocks with optimized boundary tags.

2. ### Segregated list structure:
    It contains 9 buckets storing free blocks of sizes:
    `16`, `32`, `(32.64]`, `(64.128]`, `(128, 256]`, `(256, 512]`, `(512, 1024]`, `(1024, 2048]`,
    and the last one with blocks bigger than 2048 bytes.

3. ### Minimum size of the blocks:
    The minimum size of the allocated/free block is 16 bytes,
    because of the 16-byte alignment requirement.

4. ### Headers and footers:
    Free and allocated blocks contain 4 bytes header with the information about
    the **size**, **type of the block** (alloc/free), and **prevfree flag**, which informs if
    the previous file is free. It allows to remove the footer from the allocated
    block, so only the free blocks will have the footer.
 
5. ### Pointer in free block compression to 4 bytes:
    Free blocks contain a number which is the distance of the previous/next block
    from the beginning of the heap. Thanks to this, we don't need to store
    pointers, which would increase the minimum block size to 32 bytes,
    we only store two 4-byte numbers.
 
6. ### Malloc function:
    In this approach, a block is allocated by searching for the **best fit** free
    block on the segregated list. We search for the suitable bucket,
    and then we search the list with the appropriate index
    *(if we don't find fit in that list, we search the next one)*.
    Then place the new block on the place of this selected free block.
    If there is no fit, then we extend the heap by incrementing the
    brk pointer *(taking into account the case when the last block is free, so we
    can extend the heap by the smaller amount of bytes)*.

7. ### Free function:
    When we free a block, we **coalesce** it with the blocks next to it, if they are
    free. We add the new free block at the front of the *free_list* of appropriate
    index.

8. ### Realloc function:
    Realloc function checks if the block on the left is free,
    if so, it can be used when increasing the block size.
    If the amount of free space is not enough but the block is at the end of the
    heap, we execute extend heap, otherwise we execute malloc to allocate the new
    block of the requested size and free the old block.
