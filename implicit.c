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
    "3team",
    /* First member's full name */
    "yeopto",
    /* First member's email address */
    "gunyeop530@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

#define WSIZE 4 // word and header footer 사이즈
#define DSIZE 8 // double word 사이즈
#define CHUNKSIZE (1<<12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc)) // 헤더에서 쓰기 위해(정보)

#define GET(p) (*(unsigned int*)(p))
#define PUT(p, val) (*(unsigned int *)(p)=(int)(val))

#define GET_SIZE(p) (GET(p) & ~0x7) // &비트연산으로 00000111을 역수 취해서 사이즈만 가져오겠다.
#define GET_ALLOC(p) (GET(p) & 0x1) // 헤더에서 가용여부만 가져오겠다.

#define HDRP(bp) ((char*)(bp) - WSIZE) // 블록 주소값 bp가 어디에 있던 헤더는 WSIZE만큼 앞에 위치한다.
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 헤더에서 정보가져와서 그만큼 더해주고 두칸 뒤로가면 푸터임

#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char*)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE)))
static char *heap_listp; // 힙 처음주소

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

int mm_init(void) { // 완전 처음에 heap을 시작할 때 0부터 시작
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void*)-1) { // 4만큼 늘려줌 old brk에서
        return -1;
    }
    PUT(heap_listp, 0); // 맨 처음 패딩은 값이 없기에 0을 넣어줌
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 블록 헤더 할당
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 블록 푸터 할당
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1)); // 에필로그 블록 헤더 할당
    // 초기 힙의 포인터를 prologue header 뒤로 옮긴다.
    heap_listp += (2 * WSIZE); // 포인터는 항상 어느 블록이든 헤더 뒤에 위치한다. 헤더를 읽어서 다른 블록의 값을 가지고 오거나 이동을 용이하게 하기 위해

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) { // extend heap을 통해 시작할 때 힙을 확장한다.
        return -1;
    }

    return 0;
}

static void *extend_heap(size_t words) {
    char *bp; // 블록 포인터
    size_t size; // 힙의 크기를 얼만큼 늘릴 것인가?
    
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // 홀수면 한칸 더 늘려서 더블워드경계를 맞춰서 크기 할당
    if((long)(bp = mem_sbrk(size)) == -1) { // mem_sbrk가 오류 일때 (void *) -1을 반환하는데 형을 맞춰주기 위해 long으로 
        return NULL;
    } /* mem_brk는 heap의 첫 주소, mem_sbrk 함수는 그 주소값을 기억하기 위해 임시변수 old_brk를 만들어주고
    전역변수인 mem_brk를 늘려주고 리턴은 old_brk를 반환 */

    PUT(HDRP(bp), PACK(size, 0)); // 가용 블록 헤더 만들기
    PUT(FTRP(bp), PACK(size, 0)); // 가용 블록 푸터 만들기
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 에필로그 헤더 위치 변경
    
    /* 세팅해주고 오류 단편화가 발생할 수 있으니까 free한 가용공간 
    합칠거 있으면 합쳐주기 위해 return을 coalesc로*/ 
    return coalesce(bp);
}

static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 현재기준 앞 블록 가용 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 현재기준 뒷 블록 가용 여부
    size_t size = GET_SIZE(HDRP(bp)); // 현재 사이즈

    if (prev_alloc && next_alloc) { // case1
        return bp;
    } else if (prev_alloc && !next_alloc) { // case2
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 사이즈 갱신
        PUT(HDRP(bp), PACK(size, 0)); // 헤더 갱신
        PUT(FTRP(bp), PACK(size, 0)); // 푸터 갱신
    } else if (!prev_alloc && next_alloc) { // case3
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else { // case4
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

void *mm_malloc(size_t size)
{
    size_t asize; // 블록 사이즈 조절
    size_t extendsize; // heap에 맞는 fit이 없을때 확장하기 위함
    char *bp;

    if (size == 0) return NULL;

    if (size <= DSIZE) {
        asize = 2 * DSIZE;
    } else {
        /* 말록할당은 payload부터. 필요한 공간은 
        헤더푸터를 포함해야되기에 더블워드(DSIZE)하나는 필수
        만약 size가 9라면 16만큼만 할당하면 되니까 더블 워드 두개가 필요한건데
        9에서 DSIZE - 1 만큼 더해주면 17이겠지? 8로나누면 2고 더블워드 두개는 즉 16이 된다.
        그럼 총 24바이트가 asize가 되어야하는 것.
        */
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }
    // fit에 맞는 free리스트 찾기
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }
    // fit 맞는게 없다 -> 메모리를 더 가져와 block을 위치시킴
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

// first fit으로 구현
static void *find_fit(size_t asize) {
    void *bp;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) { // 0인 블록이 나오면 탐색을 종료함.
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) { // 가용하고 내가 갖고 있는 asize를 담을 수 있으면
            return bp;
        }
    }
    return NULL;
}


static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록 사이즈
    if ((csize-asize) >= (2 * DSIZE)) { // csize 40 asize 24면 16은 쓸 수 있으니까 분할 해주어야함.
        PUT(HDRP(bp), PACK(asize, 1)); // 24 헤더 갱신
        PUT(FTRP(bp), PACK(asize, 1)); // 24 푸터 갱신
        bp = NEXT_BLKP(bp); // 분할해줄 블록으로
        PUT(HDRP(bp), PACK(csize - asize, 0)); // 그 블록 가용블록라는 정보를 헤더에
        PUT(FTRP(bp), PACK(csize - asize, 0)); // 푸터에
    } else {
        PUT(HDRP(bp), PACK(csize,1)); // 그 공간이 최소공간 16 보다 작으면 헤더 할당 갱신
        PUT(FTRP(bp), PACK(csize,1)); // 푸터 할당 갱신
    }
}

// free되면 가용블록끼리 합쳐주고 헤더, 푸터 갱신
void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size,0)); // 헤더 갱신
    PUT(FTRP(bp), PACK(size,0)); // 푸터 갱신
    coalesce(bp); // 합치기
}

// realloc은 말록으로 새로 할당하고 그 전에 있는 것은 프리해줌
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}