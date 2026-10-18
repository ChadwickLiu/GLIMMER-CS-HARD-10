#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>

/* ==================== 常量与对齐宏 ==================== */
#define ALIGNMENT 8  // 双字对齐
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~(ALIGNMENT-1)) // 对齐到ALIGNMENT的倍数

#define WSIZE       4  // 头部或尾部的字节数
#define DSIZE       8  // 双字大小
#define CHUNKSIZE  (1<<12)  // 扩展堆时的默认大小
#define MINBLOCK (DSIZE + 2*WSIZE)  // 最小块大小

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  // 返回最大值

/* ==================== 读写块字段的宏 ==================== */
#define PACK(size, alloc)  ((size) | (alloc))  // 将 size 和 allocated bit 合并为一个字

#define GET(p)        (*(unsigned int *)(p))  // 读地址p处的一个字
#define PUT(p, val)   (*(unsigned int *)(p) = (val))  // 向地址p处写一个字

#define GET_SIZE(p)   (GET(p) & ~0x07)  // 获取块的大小
#define GET_ALLOC(p)  (GET(p) & 0x1)  // 获取分配标志

#define HDRP(bp)     ((char*)(bp) - WSIZE)  // 获取头部指针(bp是一个块的有效荷载的起始地址)
#define FTRP(bp)     ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)  // 获取尾部指针

#define NEXT_BLKP(bp)    ((char*)(bp) + GET_SIZE((char*)(bp) - WSIZE))  // 获取下一个块的指针
#define PREV_BLKP(bp)    ((char*)(bp) - GET_SIZE((char*)(bp) - DSIZE))  // 获取前一个块的指针

/* ==================== 全局状态 ==================== */
static char *heap_listp;  // 堆的开始指针

#ifdef DEBUG
#define VERBOSE 1  // 在调试模式下启用调试信息输出
#else
#define VERBOSE 0  // 默认不输出调试信息
#endif

/* ==================== 前向声明 ==================== */
static void *extend_heap(size_t size);
static void *find_fit(size_t size);
static void place(char *bp, size_t asize);
static void *coalesce(void *bp);
static void print_heap_blocks(int verbose, const char *func);

/**
 * @brief 初始化内存分配器
 *
 * @return 成功时返回 0，失败时返回 -1
 */
int mm_init(void)
{
    // 初始化堆
    if ((heap_listp = sbrk(4*WSIZE)) == (void*)-1)
        return -1;

    // 初始化空闲链表
    PUT(heap_listp, 0);
    PUT(heap_listp + 1*WSIZE, PACK(8, 1));
    PUT(heap_listp + 2*WSIZE, PACK(8, 1));
    PUT(heap_listp, PACK(0, 1));
    heap_listp += (2*WSIZE);

    // 扩展堆
    if (extend_heap(CHUNKSIZE) == NULL)
        return -1;

    return 0;
}
/**
 * @brief 打印当前堆块的状态信息。
 *
 * 根据传入的 verbose 参数决定是否打印堆块信息。此函数用于调试，
 * 以检查堆内存布局、块大小及其分配状态。
 *
 * @param verbose  控制是否打印输出。当 verbose 为 1 时打印信息，为 0 时不打印。
 * @param func     表示调用此函数的上下文或函数名称，用于输出中标识当前的操作阶段。
 */
static void print_heap_blocks(int verbose, const char* func) {
    if (!verbose) return;  // 如果不需要输出调试信息，则直接返回

    char *curbp = (char *)heap_listp;

    printf("\n=========================== %s ===========================\n", func);

    while (GET_SIZE(HDRP(curbp)) > 0) {
        printf("Address: %p\n", curbp);
        printf("Size: %d\n", GET_SIZE(HDRP(curbp)));
        printf("Allocated: %d\n", GET_ALLOC(HDRP(curbp)));
        printf("\n");
        curbp = NEXT_BLKP(curbp);
    }

    printf("Address: %p\n", curbp); // Should point to the end of the heap
    printf("Size: 0\n");
    printf("Allocated: 1\n");
    printf("=========================== %s ===========================\n", func);
}


/**
 * @brief 扩展堆的大小以适应请求的内存。
 *
 * 这个函数通过调用 sbrk 来扩展堆的大小。扩展的大小会被调整为CHUNKSIZE的整数倍，以便更好地管理堆内存。
 *
 * @param size 需要扩展的内存大小（以字节为单位）。
 *
 * @note 初始调用mm_init时扩展一个CHUNKSIZE
 * @return 扩展后的内存块的指针，如果扩展失败则返回 NULL。
 */
static void *extend_heap(size_t size) {
    char* bp;
    size_t asize=ALIGN(size);
    size_t chunks=(CHUNKSIZE+asize-1)/CHUNKSIZE;
    size_t bsize=chunks*CHUNKSIZE;
    if((bp=sbrk(bsize))==(void*)-1){
        return NULL;
    }
    PUT(HDRP(bp),PACK(bsize,0));
    PUT(FTRP(bp),PACK(bsize,0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    return coalesce(bp);//尝试与相邻空闲块合并
}


/**
 * @brief 在堆中查找合适的空闲块。
 *
 * 这个函数遍历堆中的所有块，寻找一个大小足够且未分配的空闲块。
 *
 * @param size 需要分配的内存块的大小（以字节为单位）。
 *
 * @return 找到的合适的空闲块的指针，如果没有找到则返回 `NULL`。
 */
static void *find_fit(size_t size) {
    char* bp=heap_listp;
    while(GET_SIZE(HDRP(bp))>0){
        if(!GET_ALLOC(HDRP(bp))&&GET_SIZE(HDRP(bp))>=size){
            return bp;
        }
        bp=NEXT_BLKP(bp);
    }
    return NULL;
}


/**
 * @brief 将内存块分配给用户。
 *
 * 这个函数会根据请求的大小 asize(对齐后的size) 将一个内存块分配给用户。如果分配的块剩余的空间足够大，则将剩余的空间保留为一个新的空闲块。否则，将整个块都分配出去。
 *
 * @param bp 指向要分配的内存块的指针。
 * @param asize 需要分配的内存块的大小（以字节为单位）。
 */
static void place(char *bp, size_t asize) {
    size_t bsize=GET_SIZE(HDRP(bp));
    if(bsize-asize>=MINBLOCK){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(bsize - asize, 0));
        PUT(FTRP(bp), PACK(bsize - asize, 0));
    }else{
        PUT(HDRP(bp), PACK(bsize, 1));
        PUT(FTRP(bp), PACK(bsize, 1));
    }
}


/**
 * @brief 分配一个指定大小的内存块。
 *
 * 这个函数会根据请求的内存大小size来分配内存。如果请求的大小为零，则返回 NULL。首先，函数尝试从空闲块列表中找到一个合适的块，如果找到，则进行分配。如果没有找到合适的块，则会扩展堆的大小，并再次尝试分配内存。
 *
 * @param size 需要分配的内存大小（以字节为单位）。
 *
 * @return 指向分配的内存块的指针，如果分配失败则返回 `NULL`。
 */
void *mm_malloc(size_t size) {
    size_t asize;
    char* bp;
    if(size==0)return NULL;
    if(size<DSIZE){
        asize=2*DSIZE;
    }else{
        asize=ALIGN(size)+DSIZE;
    }
    if((bp=find_fit(asize))!=NULL){
        place(bp,asize);
        print_heap_blocks(VERBOSE,"mm_malloc");
        return bp;
    }else{
        size_t extendsize=MAX(asize, CHUNKSIZE);
        if((bp=extend_heap(extendsize))==NULL){
            return NULL;
        }else{
            place(bp,asize);
            print_heap_blocks(VERBOSE,"mm_malloc");
            return bp;
        }
    }
}


/**
 * @brief 合并相邻的空闲块。
 *
 * 这个函数检查指定块 bp 的前后相邻块的分配状态。如果相邻的块为空闲块，则将这些块合并成一个更大的空闲块，并更新其头部和尾部。函数会返回合并后的空闲块的指针。
 *
 * @param bp 指向要进行合并操作的内存块的指针。
 *
 * @return 合并后的空闲块的指针。
 */
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); 
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); 
    size_t size = GET_SIZE(HDRP(bp));
    if (prev_alloc && next_alloc) {
        return bp;
    } else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}


/**
 * @brief 释放一个已分配的内存块。
 *
 * 这个函数将指定的内存块 ptr 标记为未分配，并尝试将其与相邻的空闲块合并。
 *
 * @param ptr 指向要释放的内存块的指针。
 */
void mm_free(void *ptr) {
    if(!ptr)return;
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
    print_heap_blocks(VERBOSE, "mm_free");
}


//测试用例
int main() {

    if (mm_init() == -1) {
        printf("Memory manager initialization failed.\n");
        return -1;
    }

    void *p1 = mm_malloc(8000);
    void *p2 = mm_malloc(200);
    void *p3 = mm_malloc(50);

    mm_free(p2);

    void *p4 = mm_malloc(150);

    mm_free(p1);
    mm_free(p3);
    mm_free(p4);

    return 0;
}