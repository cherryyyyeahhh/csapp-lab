/*
1.分配堆空间 头部（标记位，长度） 有效荷载
2.满足对齐位置
3.额外分配堆空间
4.合并空闲位置 一但释放就合并，查找失败合并，最后依旧找不到去扩容
5.指针 头部 脚部 最小块
*/

#include <assert.h>
#include <bits/pthreadtypes.h>
#include <endian.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes) */
#define MINBLOCKSIZE 16

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc)                                                      \
  ((size) | (alloc)) /* Pack a size and allocated bit into a word */

#define GET(p) (*(unsigned int *)(p)) /* read a word at address p */
#define PUT(p, val)                                                            \
  (*(unsigned int *)(p) = (val)) /* write a word at address p */

#define GET_SIZE(p) (GET(p) & ~0x7) /* read the size field from address p */
#define GET_ALLOC(p) (GET(p) & 0x1) /* read the alloc field from address p */

#define HDRP(bp)                                                               \
  ((char *)(bp) - WSIZE) /* given block ptr bp, compute address of its header  \
                          */
#define FTRP(bp)                                                               \
  ((char *)(bp) + GET_SIZE(HDRP(bp)) -                                         \
   DSIZE) /* given block ptr bp, compute address of its footer */

#define NEXT_BLKP(bp)                                                          \
  ((char *)(bp) +                                                              \
   GET_SIZE(                                                                   \
       HDRP(bp))) /* given block ptr bp, compute address of next blocks */
#define PREV_BLKP(bp)                                                          \
  ((char *)(bp) -                                                              \
   GET_SIZE((char *)(bp) -                                                     \
            DSIZE)) /* given block ptr bp, compute address of prev blocks */
static char *head_listp;
static char *pre_listp;
// 4种情况 考虑遍历空闲块表，而不是整个堆
static void *coalesce(void *bp) {
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));
  // case1
  if (next_alloc && prev_alloc) {
    return bp;
  }
  // case2
  else if (prev_alloc && !next_alloc) {
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }
  // case3
  else if (!prev_alloc && next_alloc) {
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }
  // case4
  else {
    size += GET_SIZE(HDRP(NEXT_BLKP(bp))) + GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }
  if ((pre_listp > (char *)bp) &&
      (pre_listp < NEXT_BLKP(bp))) // 不要后面条件应该也行
    pre_listp = bp;                // 用于next_fit
  return bp;
}

static void *extend_heap(size_t words) {
  char *bp;
  size_t size;
  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
  if ((long)(bp = mem_sbrk(size)) == -1)
    return NULL;
  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
  return coalesce(bp); // 合并空闲块
}

/*static void *find_fit(size_t asize) {
  void *bp;
  for (bp = head_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    if (!GET_ALLOC(HDRP(bp)) && (GET_SIZE(HDRP(bp)) >= asize)) {
      return bp;
    }
  }
  return NULL;
}
*/
static void *next_fit(size_t asize) {
  char *old_pre = pre_listp;
  for (; GET_SIZE(HDRP(pre_listp)) > 0; pre_listp = NEXT_BLKP(pre_listp)) {
    if (!GET_ALLOC(HDRP(pre_listp)) && (asize <= GET_SIZE(HDRP(pre_listp)))) {
      return pre_listp;
    }
  }
  for (pre_listp = head_listp; pre_listp < old_pre;
       pre_listp = NEXT_BLKP(pre_listp)) {
    if (!GET_ALLOC(HDRP(pre_listp)) && (asize <= GET_SIZE(HDRP(pre_listp)))) {
      return pre_listp;
    }
  }
  return NULL;
}

/*static void *best_fit(size_t asize) {
  void *bp;
  void *best_bp = NULL;
  size_t min_size = 0;
  for (bp = head_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    if ((GET_SIZE(HDRP(bp)) >= asize) && (!GET_ALLOC(HDRP(bp)))) {
      if (min_size == 0 || min_size > GET_SIZE(HDRP(bp))) {
        min_size = GET_SIZE(HDRP(bp));
        best_bp = bp;
      }
    }
  }
  return best_bp;
}
*/
static void *place(void *bp, size_t asize) {
  size_t csize = GET_SIZE(HDRP(bp));
  if ((csize - asize) >= (2 * DSIZE)) {
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(csize - asize, 0));
    PUT(FTRP(bp), PACK(csize - asize, 0));
  } else {
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
  }
}

int mm_init(void) {

  if ((head_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) {
    return -1;
  }
  PUT(head_listp, 0);
  PUT(head_listp + WSIZE, PACK(DSIZE, 1));     // 序言块头部
  PUT(head_listp + 2 * WSIZE, PACK(DSIZE, 1)); // 序言块尾部
  PUT(head_listp + 3 * WSIZE, PACK(0, 1));
  head_listp += 2 * WSIZE;
  pre_listp = head_listp;
  if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
    return -1;
  }
  return 0;
}

void *mm_malloc(size_t size) {
  size_t asize;
  size_t extendsize;
  char *bp;
  if (size == 0)
    return NULL;
  if (size <= DSIZE)
    asize = 2 * DSIZE;
  else
    asize = DSIZE * ((size + DSIZE + DSIZE - 1) / DSIZE); // 向上取整
  if ((bp = next_fit(asize)) != NULL) {
    place(bp, asize);
    return bp;
  }
  extendsize = MAX(asize, CHUNKSIZE);
  if ((bp = extend_heap(extendsize / WSIZE)) == NULL) {
    return NULL;
  }
  place(bp, asize);
  return bp;
}

void mm_free(void *ptr) {
  size_t size = GET_SIZE(HDRP(ptr));
  PUT(HDRP(ptr), PACK(size, 0));
  PUT(FTRP(ptr), PACK(size, 0));
  coalesce(ptr); // 注意选择改变合并时机
}

void *mm_realloc(void *ptr, size_t size) {
  void *newptr;
  size_t copysize;

  if ((newptr = mm_malloc(size)) == NULL)
    return 0;
  copysize = GET_SIZE(HDRP(ptr));
  if (size < copysize)
    copysize = size;
  memcpy(newptr, ptr, copysize - WSIZE); // 减去头部才是有效荷载的内容
  mm_free(ptr);
  return newptr;
  // 考虑该块原本周围存在空闲块，是否可以合并
}
