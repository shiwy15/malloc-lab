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
    "team_1",
    /* First member's full name */
    "권도희",
    /* First member's email address */
    "shiwy15@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/********************************************************/
/* 🚨 기본 상수 및 매크로 정의(추가) : CSAPP 그림 9.43 참고 🚨 */ 

#define WSIZE 4  // 워드와 header, footer의 크기(byte)
#define DSIZE 8  // double 워드의 크기(byte)
#define CHUNKSIZE (1<<12)  // 확장 heap에 사용할 기본 크기(byte) : 2^12

#define MAX(x,y) ((x) > (y) ? (x) : (y))  // x와 y 중 큰 값을 반환하는 매크로
#define PACK(size, alloc) ((size)|(alloc))  // 블록의 크기와 할당 비트를 합친 값을 반환하는 매크로
// bit or 연산자를 통해 하나의 word로 합침.
// 예) pack(16,1)은 16의 이진수값(10000) 끝에 1을합쳐 (10001)을 반환. 최종적으로는 0001 0001 (8비트로 표현) 왜???ㅋ...

#define GET(p) (*(unsigned int *)(p))  // 주소 p에서 워드를 읽어오는 매크로
#define PUT(p, val) (*(unsigned int *)(p) = (val))  // p가 가리키는 위치에 val값을 저장하는 매크로
// *(unsigned int *)(p) : p라는 포인터 변수를 unsigned int 타입으로 캐스팅. 
// 이후 *연산자가 해당 포인터가 가리키느 메모리 주소에 접근하고 unsigned int 타입(4byte)으로 값을 가져옴
// 즉, p가 가리키는 주소에 있는 4바이트 정수 값을 의미

/* 포인터 p에 저장된 값(헤더,푸터)에서 블록 size를 추출 */
#define GET_SIZE(p) (GET(p) & ~0x7)  // 16진수로 4비트 이상부터 추출(3비트 이하는 의미X). 즉, size 추출.
#define GET_ALLOC(p) (GET(p) & 0x1)  // 현재 블록의 가용여부 판단

/* 각각 (현재)블록 포인터가 주어지면 블록의 header와 footer를 가리키는 포인터를 리턴 */
#define HDRP(bp) ((char *)(bp) - WSIZE)  // bp에 저장된 새로운 메모리주소에서 1워드 뒤를 가리킴.(에필로그 헤더 앞으로 감)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)  // hdrp(bp) 포인터 위치에서 사이즈만큼 위로 간 뒤, 2워드 뒤를 가리킴.

/* 다음과 이전 블록의 포인터 반환 */  
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE((char *)(bp)-WSIZE)) 
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp)-DSIZE)) 

/* free list에서 전,후 가용블록 포인터 반환 */
#define PRED_P(bp) (*(void**)(bp))  // 이전 블록 bp 반환
#define SUCC_P(bp) (*(void**)((bp) + WSIZE))  // 다음 블록 bp 반환

/********************************************************/
/* 🚨 함수 선언 🚨 */

static void *heap_listp; // 초기 가상 메모리 공간의 시작주소를 저장하는 변수(포인터)
static void *extend_heap(size_t words);  // typedef unsigned long size_t (4byte)
static void *coalesce(void *bp);
static void *find_fit(size_t asize);  // 여기서 first와 next 코드가 달라짐.
static void place(void *bp, size_t asize);
static void remove_block(void *bp);  // 가용블럭 연결리스트를 끊어주는 함수
static void put_free_block(void *bp);

/********************************************************/

/* 🔥 초기화 함수 🔥 
  첫 워드에 pred, succ 추가 */
int mm_init(void)
{
  if ((heap_listp = mem_sbrk(6*WSIZE)) == (void *)-1)
    return -1;
  
  PUT(heap_listp, 0);  // 블록 정렬을 위한 padding
  PUT(heap_listp + (1 * WSIZE), PACK(2*DSIZE, 1));  // 두 번째 워드 : prologue block의 헤더
  PUT(heap_listp + (2 * WSIZE), heap_listp + (3 * WSIZE));  // heap_listp가 가리키는 블록의 네번째 워드(이전블록을 나타내는 포인터)를 가리킴
  PUT(heap_listp + (3 * WSIZE), heap_listp + (2 * WSIZE));  // heap_listp가 가리키는 블록의 세번째 워드(다음블록을 나타내는 포인터)를 가리킴
  PUT(heap_listp + (4 * WSIZE), PACK(2*DSIZE, 1));  // 다섯번째 워드 : prologue block의 푸터
  PUT(heap_listp + (5 * WSIZE), PACK(0, 1));  // 여섯번째 워드 : epilogue block의 헤더

  heap_listp += (2 * WSIZE); 

  if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    return -1; 
  
  return 0; 
}

/********************************************************/
/* 🔥 heap 메모리 확장 함수 🔥
  : mem_sbrk 함수를 이용하여 요청한 크기만큼 힙 메모리를 할당 후, 
  : 헤더와 푸터를 설정해주고, 블록을 합칠 수 있는지 확인하여 합치는 작업을 수행  */
static void *extend_heap(size_t words)
{
  char *bp;  // 새로 확장된 블록의 주소 저장
  size_t size;  // 확장할 크기 저장

  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
  
  if ((long)(bp = mem_sbrk(size)) == -1)  // mem_sbrk 함수를 호출, 힙을 확장
    return NULL; 

  // 새로 할당된 블록의 헤더와 푸터를 초기화.
  PUT(HDRP(bp), PACK(size, 0));  // free 블록 header에 내용 저장
  PUT(FTRP(bp), PACK(size, 0));  // free 블록 footer에 내용 저장
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  // 새로운 epilogue header

  return coalesce(bp);
}

/********************************************************/
/* 🔥 메모리 할당 함수 🔥 */
void *mm_malloc(size_t size)
{
  size_t asize;  // 할당할 블록의 총 크기 저장
  size_t extendsize;  // 힙을 확장할 크기 저장
  char *bp;  // 할당된 블록의 주소 저장

  if (size == 0)
    return NULL;

  if (size <= DSIZE)
    asize = 2*DSIZE;
  else
    asize = DSIZE * ((size + DSIZE + (DSIZE-1)) / DSIZE);
  
  if ((bp = find_fit(asize)) != NULL)  
  {
    place(bp, asize);  // place 함수로 블록 배치
    return bp;  // 해당 블록 주소 반환
  }

  extendsize = MAX(asize, CHUNKSIZE);  
  if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    return NULL;
  place(bp, asize); 
  return bp;
}

/********************************************************/
/* 🔥 메모리 해제 함수 🔥 */
void mm_free(void *bp)
{
  size_t size = GET_SIZE(HDRP(bp));  // 해당 포인터가 가리키는 블록의 헤더에서 사이즈 정보를 가져옴

  PUT(HDRP(bp), PACK(size, 0));  // 헤더의 가용정보를 0으로 변환
  PUT(FTRP(bp), PACK(size, 0));  // 푸터의 가용정보를 0으로 변환
  coalesce(bp);  // coalesce 함수 호출, 전후 가용메모리와 병합
}

/********************************************************/
/* 🔥 메모리 크기 조정 함수 🔥 */
void *mm_realloc(void *bp, size_t size)
{
  void *old_bp = bp;
  void *new_bp;  // 새로운 블록을 가리키는 포인터 선언
  size_t copySize;  // 이전 블록의 크기 정보를 저장할 변수 선언
  
  // 1) malloc으로 크기가 size인 새로운 블록을 할당하고 그 주소를 new_bp에 저장
  new_bp = mm_malloc(size);
  if (new_bp == NULL)  // 만약 malloc이 새로운 블록을 할당하지 못했다면 null값 반환
    return NULL;

  // 2) 이전 블록의 헤더에서 사이즈 정보 가져옴
  copySize = GET_SIZE(HDRP(old_bp));

  if (size < copySize)
    copySize = size;
  // 4) memcpy 함수를 호출하여 이전 블록에서 copysize만큼의 데이터를 새로 할당한 블록으로 복사
  memcpy(new_bp, old_bp, copySize);
  
  mm_free(old_bp);  // 이전 블록 해제
  return new_bp;  // 새로운 포인터 반환
}

/********************************************************/
/* 🔥 가용 블록 병합 함수 🔥
  : 현재 블록의 이전/이후 블록이 가용블록일 경우, 
  일단 free_list에서 제거한 후에 현재블록과 합쳐주고 다시 free_list에 추가함. */
static void *coalesce(void *bp)
{
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));// 이전 블록의 푸터에서 할당 여부 가져옴
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블럭의 헤더에서 할당 여부 가져옴
  size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 헤더에서 사이즈 정보를 가져옴

  // CASE 1) 전후 블록이 모두 할당
  // CASE 2) 전 블록은 할당, 후 블록 가용 상태 : 후 블록과 병합
  if(prev_alloc && !next_alloc) {    
    remove_block(NEXT_BLKP(bp));   
    size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록의 헤더에서 사이즈 가져와서 현재 블록 사이즈에 더함  
    PUT(HDRP(bp), PACK(size, 0));  // 현재 블록의 헤더에 사이즈/가용여부 정보 저장.
    PUT(FTRP(bp), PACK(size, 0));  // 위에 저장된 정보로 합쳐진 블록의 푸터를 찾아가서 정보 저장
  }
  // CASE 3) 전 블록이 가용, 후 블록 할당 : 전 블록과 병합
  else if(!prev_alloc && next_alloc) {
    remove_block(PREV_BLKP(bp));
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));  // 이전 블록의 푸터에서 사이즈를 가져와서 현재블록 사이즈에 더함
    PUT(FTRP(bp), PACK(size, 0));  // 현재블록의 푸터에 사이즈/가용 정보 저장
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));  // 이전 블록의 헤더에 사이즈/가용 정보 저장
    bp = PREV_BLKP(bp);  //  병합 후, 다시 이전 블록의 포인터 반환
  }
  // CASE 4) 전후 블록 모두 가용
  else if (!prev_alloc && !next_alloc) {
    remove_block(PREV_BLKP(bp)); 
    remove_block(NEXT_BLKP(bp)); 
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); 
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }

  put_free_block(bp);  // 연결된 새 가용블록을 free_list에 추가
  return bp;  // 포인터 반환
}

/********************************************************/
/* 🌸 가용 블록 검색 함수 : first_fit 🌸 */
static void *find_fit(size_t asize)  // 매개변수로 할당할 블록의 크기를 받음
{
  void *bp;  

  for (bp = SUCC_P(heap_listp); !GET_ALLOC(HDRP(bp)); bp = SUCC_P(bp)) {
    if (asize <= GET_SIZE(HDRP(bp))) {
      return bp;  
    }
  }
  return NULL;  
}

/********************************************************/
/* 🔥 블록 할당 함수 🔥 
  매개변수로 할당되는 블록의 포인터(bp)와 할당할 블록의 크기(asize)를 받음  */
static void place(void * bp, size_t asize) 
{
  // 1) bp가 가리키는 가용블록의 헤더에서 사이즈 정보를 가져와 변수에 저장
  size_t csize = GET_SIZE(HDRP(bp));  

  remove_block(bp);

  // 2) 만약 블록을 할당하고 남은 공간이 8byte보다 크다면, 블록을 분할함
  if ((csize - asize) >= (2*DSIZE)) {
    PUT(HDRP(bp), PACK(asize, 1));  // 가용블록의 헤더에 정보 저장
    PUT(FTRP(bp), PACK(asize, 1));  // 푸터 정보 저장
    bp = NEXT_BLKP(bp);  // 포인터를 다음 블록(분할한 남은 블록)으로 옮김
    PUT(HDRP(bp), PACK(csize - asize, 0));  // 가용블록의 헤더에 정보 저장
    PUT(FTRP(bp), PACK(csize - asize, 0));  // 가용블록의 푸터에 정보 저장
    // 분할된 블록은 coalesce함수 거쳐서 free_list에 추가
    put_free_block(bp);
  } 
  else {  
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
  }
}

/********************************************************/
/* 🔥 free_block 추가 함수 🔥 */
static void put_free_block(void *bp)
{
  SUCC_P(bp) = SUCC_P(heap_listp);
  PRED_P(bp) = heap_listp;
  PRED_P(SUCC_P(heap_listp)) = bp;
  SUCC_P(heap_listp) = bp;
}

/********************************************************/
/* 🌸 free_list 삭제 함수 🌸 */
static void remove_block(void *bp)
{
  if (bp == SUCC_P(heap_listp)) {
    PRED_P(SUCC_P(bp)) = PRED_P(bp);
    SUCC_P(heap_listp) = SUCC_P(bp);
    return;
  }
  SUCC_P(PRED_P(bp)) = SUCC_P(bp);
  PRED_P(SUCC_P(bp)) = PRED_P(bp);
}