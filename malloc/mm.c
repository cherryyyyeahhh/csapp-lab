/*使用分离适配（之后考虑伙伴系统实现
分为不同块大小，使用指针指向 考虑分割的实现
按照从小到大排放，在这种情形下first_fit即为best_fit
修改已存在的代码
考虑将剩余的块放入空闲链表中的实现 每个对应的一个小堆有一个空闲链表
使用链表来实现
*/
#include "mm.h"
#include "memlib.h"
#include <assert.h>
#include <bits/pthreadtypes.h>
#include <endian.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
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

#define GET_SUCC(bp) (*(unsigned int *)bp)
#define GET_PRED(bp) (*((unsigned int *)(bp) + 1))
#define PUT_SUCC(bp, val) (GET_SUCC(bp) = (unsigned int)(val))
#define PUT_PRED(bp, val) (GET_PRED(bp) = (unsigned int)(val))

static char *head_listp;
// static char *pre_listp; // 记录第二次适配的指针
static char *efree_listp;
static char *block_list_start;
static void *get_sfreeh(size_t size) {
  int i;
  if (size <= 32) {
    i = 0;
  } else if (size <= 64) {
    i = 1;
  } else if (size <= 128) {
    i = 2;
  } else if (size <= 256) {
    i = 3;
  } else if (size <= 512) {
    i = 4;
  } else if (size <= 1024) {
    i = 5;
  } else if (size <= 2048) {
    i = 6;
  } else if (size <= 4096) {
    i = 7;
  } else {
    i = 8;
  }
  return block_list_start + i * WSIZE;
}
static void remove_s_p(void *bp) {
  void *root = get_sfreeh(GET_SIZE(HDRP(bp)));
  void *pred = (void *)GET_PRED(bp);
  void *succ = (void *)GET_SUCC(bp);
  PUT_PRED(bp, NULL);
  PUT_SUCC(bp, NULL);
  if (pred == NULL) { // 第一次记录root小堆对应链表开始
    // NULL-> bp -> NULL
    PUT_SUCC(root, succ); // 前NULL后NULL时，succ也是NULL，可以直接用succ代替
    if (succ != NULL) {
      // NULL-> bp -> succ
      PUT_PRED(succ, root);
    }
  } else {
    // pred -> bp -> NULL
    PUT_SUCC(pred, succ);
    if (succ != NULL) {
      // pred -> bp -> succ
      PUT_PRED(succ, pred);
    }
  }
}

static void insert(void *new_first) {
  if (new_first == NULL) {
    return;
  }
  void *root = get_sfreeh(GET_SIZE(HDRP(new_first)));
  void *pred = root;
  void *succ = (void *)GET(root);
  while (succ != NULL) {
    if (GET_SIZE(HDRP(succ)) >= GET_SIZE(HDRP(new_first))) {
      break;
    }
    pred = succ;
    succ = (void *)GET_SUCC(succ);
  }
  if (pred == root) {
    PUT(root, (unsigned int)new_first);
    PUT_PRED(new_first, NULL);
    PUT_SUCC(new_first, succ);
    if (succ != NULL) {
      PUT_PRED(succ, new_first);
    }
  } else {
    PUT_PRED(new_first, pred);
    PUT_SUCC(new_first, succ);
    PUT_SUCC(pred, new_first);
    if (succ != NULL) {
      PUT_PRED(succ, new_first);
    }
  }
}

static void *coalesce(void *bp) {
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));
  // case1  alloc->bp->alloc
  if (next_alloc && prev_alloc) {
  }
  // case2  alloc->bp->free
  else if (prev_alloc && !next_alloc) {
    remove_s_p(NEXT_BLKP(
        bp)); // 意思是直接把临近的free块在链表中直接删除，然后修改size，最后insert（bp）把原来free块加上，之后情况同理
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }
  // case3  free-> bp ->alloc
  else if (!prev_alloc && next_alloc) {
    remove_s_p(PREV_BLKP(bp));
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }
  // case4  free-> bp ->free
  else {
    remove_s_p(NEXT_BLKP(bp));
    remove_s_p(PREV_BLKP(bp));
    size += GET_SIZE(HDRP(NEXT_BLKP(bp))) + GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }
  /* // 用于next_fit
  if ((pre_listp > (char *)bp) &&
      (pre_listp < NEXT_BLKP(bp))) // 不要后面条件应该也行11
    pre_listp = bp;
*/
  insert(bp);
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
  PUT_SUCC(bp, 0);
  PUT_PRED(bp, 0);
  return coalesce(bp); // 合并空闲块
}

static void *find_fit(size_t asize) {
  for (void *root = get_sfreeh(asize); root != (head_listp - WSIZE);
       root += WSIZE) {
    void *bp = (void *)GET(root);
    while (bp) {
      if (GET_SIZE(HDRP(bp)) >= asize) {
        return bp;
      }
      bp = (void *)GET_SUCC(bp);
    }
  }
  return NULL;
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
/*
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
*/
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
  remove_s_p(bp); // 被分配时，从链表中删除
  if ((csize - asize) >= (2 * DSIZE)) {
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(csize - asize, 0));
    PUT(FTRP(bp), PACK(csize - asize, 0));
    PUT_SUCC(bp, NULL);
    PUT_PRED(bp, NULL);
    coalesce(bp);
  } else {
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
  }
}

int mm_init(void) {
  efree_listp = NULL;
  if ((head_listp = mem_sbrk(12 * WSIZE)) == (void *)-1) {
    return -1;
  }
  // 分配不同大小块的指针
  PUT(head_listp, 0);                             /* block size <= 32 */
  PUT(head_listp + (1 * WSIZE), 0);               /* block size <= 64 */
  PUT(head_listp + (2 * WSIZE), 0);               /* block size <= 128 */
  PUT(head_listp + (3 * WSIZE), 0);               /* block size <= 256 */
  PUT(head_listp + (4 * WSIZE), 0);               /* block size <= 512 */
  PUT(head_listp + (5 * WSIZE), 0);               /* block size <= 1024 */
  PUT(head_listp + (6 * WSIZE), 0);               /* block size <= 2048 */
  PUT(head_listp + (7 * WSIZE), 0);               /* block size <= 4096 */
  PUT(head_listp + (8 * WSIZE), 0);               /* block size > 4096 */
  PUT(head_listp + (9 * WSIZE), PACK(DSIZE, 1));  // 序言块头部
  PUT(head_listp + (10 * WSIZE), PACK(DSIZE, 1)); // 序言块尾部
  PUT(head_listp + (11 * WSIZE), PACK(0, 1));
  block_list_start = head_listp;
  head_listp += 10 * WSIZE;
  // pre_listp = efree_listp;
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
  if ((bp = find_fit(asize)) != NULL) {
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
  PUT_PRED(ptr, NULL);
  PUT_SUCC(ptr, NULL);
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
