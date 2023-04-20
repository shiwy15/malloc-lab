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

/********************************************************/
/* 🚨 함수 선언 🚨 */

static char *next_bp; // 다음 할당 위치를 저장하는 포인터
static void *heap_listp; // 초기 가상 메모리 공간의 시작주소를 저장하는 변수(포인터)
static void *extend_heap(size_t words);  // typedef unsigned long size_t (4byte)
static void *coalesce(void *bp);
static void *find_fit(size_t asize);  // 여기서 first와 next 코드가 달라짐.
static void place(void *bp, size_t asize);


/********************************************************/

/* 🔥 초기화 함수 🔥
  : 힙 메모리를 초기화, 초기 가용 블록 생성
  : 실행 도중 문제가 생긴다면 -1, 정상 종료되면 0을 리턴  */
int mm_init(void)
{
  // 1) mem_sbrk를 사용하여 초기 heap (가상 메모리)공간 할당하고 그것이 성공적으로 이루어졌는지 확인
  // mem_sbrk는 힙을 확장하고 그 시작 주소를 반환. 그 주소를 heap_listp에 저장
  // mem_sbrk의 결과값이 음수이거나 힙을 넘어가는 크기를 할당하려고 하면 (void *)-1 을 반환하고, 이는 메모리 할당 실패를 의미함.
  if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
    // 4*WSIZE = 초기 empty heap을 위해 필요한 총 워드 수
    return -1;
  
  // 2) 초기 힙 공간을 사용하기 위한 초기화 작업 수행
  // PUT 매크로를 사용하여 힙 공간의 첫 부분에 4워드의 공간을 만듦
  PUT(heap_listp, 0);  // 첫 번째 워드 : 바이트 정렬(2워드 단위로 블록 정렬)을 위한 padding
  // 책에서는 더블워드(8byte) 정렬조건
  // 만약 8byte를 확보하고 싶다면, 헤더(4)와 데이터(8)를 합친값은 12이므로 8의배수인 16이 될 수 있도록 패딩(4)하나를 추가하여 정렬해줌.

  // 두번째와 세번째 워드는 할당 요청에 대한 처리를 담당하며, 크기는 DSIZE여야 함.
  PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));  // 두 번째 워드 : prologue block의 헤더
  PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));  // 세 번째 워드 : prologue block의 푸터
  PUT(heap_listp + (3 * WSIZE), PACK(0, 1));  // 네 번째 워드 : epilogue block의 헤더

  heap_listp += (2 * WSIZE);  // 힙 리스트 포인터를 prologue footer 위치로 이동

  // 3) extend_heap 함수를 호출 : 초기 chunksize 바이트로 확장하고 가용 블록 생성
  // 이 블록은 free block으로 초기화 됨
  // chunksize는 byte 단위로, wsize로 나누면 워드 단위로 바뀜!
  if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    return -1;  // 만약 호출된 결과값이 NULL이라면 -1 반환

  // next_fit 사용시 next_bp 초기화!!
  next_bp = heap_listp;

  return 0;  // 초기화 작업 완료시 0 반환
}

/********************************************************/
/* 🔥 heap 메모리 확장 함수 🔥
  : mem_sbrk 함수를 이용하여 요청한 크기만큼 힙 메모리를 할당 후, 
  : 헤더와 푸터를 설정해주고, 블록을 합칠 수 있는지 확인하여 합치는 작업을 수행  */
static void *extend_heap(size_t words)
{
  // char타입 포인터 bp와 size_t타입 size 변수 선언
  char *bp;  // 새로 확장된 블록의 주소 저장
  size_t size;  // 확장할 크기 저장

  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
  // words가 2의 배수가 아니라면, words에 1을 더해서 2의 배수로 만들어 줌(더블워드 정렬)
  // WSIZE(4byte)를 곱해주는건 그냥 워드 단위를 다시 바이트 단위로 바꿔주는 것!
  // ? 연산자 --> rule ? a : b 일 때, rule이 참이면 a를, 거짓이면 b를 반환

  if ((long)(bp = mem_sbrk(size)) == -1)  // mem_sbrk 함수를 호출, 힙을 확장
    return NULL;  // 실패 시 NULL 반환
  // 성공시, bp에는 새로 할당된 메모리블록의 시작 주소가 저장되고, long 타입으로 캐스팅하여 반환
  // sbrk함수는 void* 타입의 주소를 반환하기 때문에 bp에 그대로 저장하면 타입이 맞지 않아서 오류 발생.  

  // 새로 할당된 블록의 헤더와 푸터를 초기화.
  PUT(HDRP(bp), PACK(size, 0));  // free 블록 header에 내용 저장
  PUT(FTRP(bp), PACK(size, 0));  // free 블록 footer에 내용 저장
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  // 새로운 epilogue header

  // 이전 힙이 가용블록으로 끝났다면, coalesce 함수로 두 개의 가용블록을 통합
  return coalesce(bp);
}

/********************************************************/
/* 🔥 가용 블록 병합 함수 🔥 */
static void *coalesce(void *bp)
{
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록의 푸터에서 할당 여부 가져옴
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블럭의 헤더에서 할당 여부 가져옴
  size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 헤더에서 사이즈 정보를 가져옴

  // CASE 1) 전후 블록이 모두 할당
  if (prev_alloc && next_alloc) {
    return bp;
  }
  // CASE 2) 전 블록은 할당, 후 블록 가용 상태 : 후 블록과 병합
  else if(prev_alloc && !next_alloc) {
    size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록의 헤더에서 사이즈 가져와서 현재 블록 사이즈에 더함

    PUT(HDRP(bp), PACK(size, 0));  // 현재 블록의 헤더에 사이즈/가용여부 정보 저장.
    PUT(FTRP(bp), PACK(size, 0));  // 위에 저장된 정보로 합쳐진 블록의 푸터를 찾아가서 정보 저장
  }
  // CASE 3) 전 블록이 가용, 후 블록 할당 : 전 블록과 병합
  else if(!prev_alloc && next_alloc) {
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));  // 이전 블록의 푸터에서 사이즈를 가져와서 현재블록 사이즈에 더함

    PUT(FTRP(bp), PACK(size, 0));  // 현재블록의 푸터에 사이즈/가용 정보 저장
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));  // 이전 블록의 헤더에 사이즈/가용 정보 저장

    bp = PREV_BLKP(bp);  //  병합 후, 다시 이전 블록의 포인터 반환
  }
  // CASE 4) 전후 블록 모두 가용
  else {
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));  // 이전블록의 푸터 + 다음블록의 헤더 + 현재블럭 사이즈

    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));

    bp = PREV_BLKP(bp);
  }
  
  // 추가) next fit
  // next fit 방식에서는 이전에 가용블록을 찾았던 위치부터 이어서 탐색을 진행하기 때문에, 탐색을 이어나갈 위치를 기억해야 함.(next_bp에 저장)
  // 그런데, coalesce 함수에서는 인접한 가용블록을 하나로 합쳐주는 작업을 수행하기 때문에,
  // next_bp가 합쳐지는 블록 사이에 자리하고 있다면, next_bp의 위치는 새롭게 합쳐진 블록의 시작 위치로 옮겨줘야 함.
  // 이로써 next fit 방식의 탐색을 유지할 수 있도록 해 줌.
  if ((next_bp > (char *)(bp)) && (next_bp < NEXT_BLKP(bp))) // next_bp가 중간에 낀 경우에
    next_bp = bp;  // 시작위치로 옮겨줌

  return bp;  // 포인터 반환
}

/********************************************************/
/* 🔥 메모리 할당 함수 🔥 */
void *mm_malloc(size_t size)
{
  size_t asize;  // 할당할 블록의 총 크기 저장
  size_t extendsize;  // 힙을 확장할 크기 저장
  char *bp;  // 할당된 블록의 주소 저장

  // 1) 요청한 메모리가 0이거나 음수이면 null값 반환
  if (size == 0)
    return NULL;

  // 2) 요청한 메모리가 DSIZE(8byte)보다 같거나 작으면, 블록의 최소 크기인 2*DSIZE(16byte)로 설정
  // 8바이트는 정렬 기준을 만족하기 위해, 나머지는 헤더(4byte)와 푸터(4byte)를 고려해야 하기 때문.
  if (size <= DSIZE)
    asize = 2 * DSIZE;
  // 3) 요청한 메모리가 DSIZE보다 큰 경우, DSIZE의 배수로 올림하여 계산
  else
    asize = DSIZE * ((size + DSIZE + (DSIZE-1)) / DSIZE);
    // 수식 설명 : 메모리 정렬 조건을 만족하면서, 요청한 크기에 최대한 가까운 블록 크기 제공
    // 요청한 메모리(size)에 DSIZE(8byte, 헤더/푸터)를 먼저 더하면 최소 블록 크기가 됨.
    // Dsize로 나눴을 때, 버림 연산을 수행하기 때문에 나머지가 나올 수 있는 범위내(7)에서 더해줌

  // 4) find_fit 함수(할당기)로 적절한 가용 블록 탐색 및 배치
  if ((bp = find_fit(asize)) != NULL)  // 탐색 성공 시
  {
    place(bp, asize);  // place 함수로 블록 배치
    return bp;  // 해당 블록 주소 반환
  }
  // 5) 적절한 가용 블록이 없을 경우, 힙 확장(새 가용블록 확보) 및 배치
  // 확장할 힙의 크기 결정. 요청한 크기와 chunksize 중 큰 값을 선택함
  extendsize = MAX(asize, CHUNKSIZE);  
  if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    return NULL;
  place(bp, asize); 
  return bp;
}

/********************************************************/
/* 🌸 가용 블록 검색 함수(1) : First_fit (54점) 🌸 */
// static void *find_fit(size_t asize)  // 매개변수로 할당할 블록의 크기를 받음
// {
//   void *bp;  // bp 포인터 선언. 할당 가능한 블록을 가리킴

//   // 1) heap_listp부터 모든 블록을 반복하여 할당 가능한 블록을 탐색
//   // 조건 1: bp는 heap_listp를 가리킴. heap_listp는 가상메모리 첫 번째 블록을 가리키는 포인터.
//   // 조건 2: 포인터가 가리키는 블록의 헤더 사이즈가 0보다 큰 경우, 즉 모든 블록을 탐색하겠다는 조건.(힙의 마지막 블록은 0을 가리키므로)
//   // 조건 3: 다음 블록의 주소를 bp에 저장하여 루프 반복
//   for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
//     // 2) 블록이 아직 할당되지 않았고, 요청한 크기(asize)보다 크거나 같은 공간이 있는지 확인
//     if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
//       return bp;  // 탐색 성공 시 해당 bp 반환
//     }
//   }
//   return NULL;  // 할당 가능한 블록을 찾지 못할 경우 NULL값 반환
// }

/* 🌸 가용 블록 검색 함수(2) : Next_fit (84점) 🌸 
  next_fit 방식으로 메모리 할당 가능한 공간을 찾아 반환하는 함수 */
static void *find_fit(size_t asize) {
  
  char *bp = next_bp; // 현재 할당 위치를 저장하는 포인터 next_bp를 bp에 저장

  /* 다음 할당 위치부터 블록의 끝까지 순회하며, asize보다 큰 공간을 찾음 */
  for (; GET_SIZE(HDRP(next_bp)) > 0; next_bp = NEXT_BLKP(next_bp)) {
    if (!GET_ALLOC(HDRP(next_bp)) && (asize <= GET_SIZE(HDRP(next_bp)))) {
      /* asize보다 큰 공간을 찾았을 경우, 해당 블록을 할당 가능한 블록으로 저장하고,
        * 다음 할당 위치를 해당 블록의 다음 블록으로 갱신 후 반환 */
      return next_bp;
    }
  }

  /* 할당 가능한 공간을 찾지 못한 경우, 처음부터 다시 순회 */
  for (next_bp = heap_listp; next_bp < bp; next_bp = NEXT_BLKP(next_bp)) {
    if (!GET_ALLOC(HDRP(next_bp)) && (asize <= GET_SIZE(HDRP(next_bp)))) {
      return next_bp;
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

  // 2) 만약 블록을 할당하고 남은 공간이 8byte보다 크다면, 블록을 분할함
  if ((csize - asize) >= (2*DSIZE)) {
    PUT(HDRP(bp), PACK(asize, 1));  // 가용블록의 헤더에 정보 저장
    PUT(FTRP(bp), PACK(asize, 1));  // 푸터 정보 저장
    bp = NEXT_BLKP(bp);  // 포인터를 다음 블록(분할한 남은 블록)으로 옮김
    PUT(HDRP(bp), PACK(csize - asize, 0));  // 가용블록의 헤더에 정보 저장
    PUT(FTRP(bp), PACK(csize - asize, 0));  // 가용블록의 푸터에 정보 저장
  } 
  else {  // 3) 블록을 할당하고 남은 공간이 8byte보다 작다면, 해당 가용공간을 모두 사용함
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
  }
}

/********************************************************/
/* 🔥 메모리 해제 함수 🔥 
  주어진 bp로 헤더와 푸터의 할당 정보를 free(0)으로 바꿔주며, 반환하는 값은 없음.
  인자로 받은 포인터가 이전에 malloc, realloc으로 할당된 메모리이고, 그것이 free되지 않았을 때에만 실행되어야 함. */
void mm_free(void *bp)
{
  size_t size = GET_SIZE(HDRP(bp));  // 해당 포인터가 가리키는 블록의 헤더에서 사이즈 정보를 가져옴

  PUT(HDRP(bp), PACK(size, 0));  // 헤더의 가용정보를 0으로 변환
  PUT(FTRP(bp), PACK(size, 0));  // 푸터의 가용정보를 0으로 변환
  coalesce(bp);  // coalesce 함수 호출, 전후 가용메모리와 병합
}

/********************************************************/
/* 🔥 메모리 크기 조정 함수 🔥 
  이미 할당된 메모리의 크기를 조정하고 싶을 때 사용하는 함수. 
  매개변수로 바꾸고 싶은 블록을 가리키는 포인터(bp)와 새로 바꾸고 싶은 크기(size)를 받음 */
void *mm_realloc(void *bp, size_t size)
{
  void *new_bp;  // 새로운 블록을 가리키는 포인터 선언
  size_t copySize;  // 이전 블록의 크기 정보를 저장할 변수 선언
  
  // 1) malloc으로 크기가 size인 새로운 블록을 할당하고 그 주소를 new_bp에 저장
  new_bp = mm_malloc(size);
  if (new_bp == NULL)  // 만약 malloc이 새로운 블록을 할당하지 못했다면 null값 반환
    return NULL;

  // 2) 이전 블록의 헤더에서 사이즈 정보 가져옴
  copySize = GET_SIZE(HDRP(bp));

  // 3) 만약 새로 요청한 크기(size)가 이전 블록의 size보다 작다면 copysize 변수에 size 저장
  if (size < copySize)
    copySize = size;
  // 4) memcpy 함수를 호출하여 이전 블록에서 copysize만큼의 데이터를 새로 할당한 블록으로 복사
  memcpy(new_bp, bp, copySize);
  /* memcpy : C표준 라이브러리 함수 중 하나. 메모리 블록을 복사하는 함수
    : 매개변수로 복사 대상 메모리의 시작주소, 복사할 데이터 블록의 시작주소, 복사할 데이터의 크기(byte)를 받음 
    : 여기서는 bp가 가리키는 메모리 블록의 데이터를 new_bp가 가리키는 메모리 블록으로 복사함. */
  
  mm_free(bp);  // 이전 블록 해제
  return new_bp;  // 새로운 포인터 반환
}

// 좀 더 경우의 수를 나눠서 짜봐도 될 것 같다.