/*
 * Piotr Stokłosa, numer inedksu 314987
 * Zaimplementowałem zoptymalizowane boundary tags wraz z optymalizowanym
 * reallociem. Funkcja malloc wykorzystuje politykę first-fit, a funckja free
 * gorliwie złącza wolne bloki
 *
 * Wolny blok zaczyna się i kończy słowem typu word_t, w którym znajdują się
 * informacje takie jak size, czy poprzedni blok jest wolny oraz wolny pierwszy
 * bit oznaczający, że jest on wolnym blokiem.
 *
 * Zajęty blok zaczyna się słowem typu word_t, w którym znajdują się informacje
 * takie jak size, czy poprzedni blok jest wolny oraz zajęty pierwszy bit
 * oznaczający, że jest on zajętym blokiem.
 *
 * Funkcja malloc najpierw wyszukuje najlepiej pasujący blok (za pomocą funkcji
 * find_fit). Jeżeli funkcja find_fit zwróciła NULL, oznacza to, że pasujący
 * blok nie istnieje i trzeba zaalokować go na końcu, używając funkcji morecore,
 * która daje nam do dyspozycji nową pamięć. Jeżeli funkcja find_fit zwróci nam
 * wartość inną niż NULL, wtedy alokujemy nowy blok w zwróconym przez nią wolnym
 * bloku.
 *
 * Funkcja free zwalnia podany blok, oraz sprawdza czy poprzedni/następny blok
 * jest wolny. Jeżeli tak, to łączy je.
 *
 * Funkcja realloc sprawdza kilka przypadków (każdy jest krótko opisany w samej
 * funkcji), które powodują optymalizacje samej funkcji (żeby uniknąć
 * wywoływania funkcji malloc). Jeżeli żaden przypadek nie zostanie obsłużony,
 * następuje wywołanie funkcji malloc, po której pamięc zostanie odpowiednio
 * skopiowana ze starego do nowego bloku. Na koniec zostanie zwolniony stary
 * blok.
 *
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
#define debug(...) printf(__VA_ARGS__)
#else
#define debug(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

typedef int32_t word_t; /* Heap is bascially an array of 4-byte words. */

typedef enum {
  FREE = 0,     /* Block is free */
  USED = 1,     /* Block is used */
  PREVFREE = 2, /* Previous block is free (optimized boundary tags) */
} bt_flags;

static word_t *heap_start; /* Address of the first block */
static word_t *last;       /* Points at last block */

static size_t round_up(size_t size) {
  return (size + ALIGNMENT - 1) & -ALIGNMENT;
}

static inline word_t bt_size(word_t *bt) {
  return *bt & ~(USED | PREVFREE);
}

static inline int bt_used(word_t *bt) {
  return *bt & USED;
}

static inline int bt_free(word_t *bt) {
  return !(*bt & USED);
}

static inline word_t *bt_footer(word_t *bt) {
  return (void *)bt + bt_size(bt) - sizeof(word_t);
}

static inline word_t *bt_fromptr(void *ptr) {
  return (word_t *)ptr - 1;
}

static inline word_t *bt_next(word_t *bt) {
  if (bt == last)
    return NULL;

  return (void *)bt + bt_size(bt);
}

static inline void bt_set_prevfree(word_t *bt) {
  *bt |= PREVFREE;
}

static inline void bt_clr_prevfree(word_t *bt) {
  if (bt)
    *bt &= ~PREVFREE;
}

static inline void bt_make_USED(word_t *bt, size_t size) {

  *bt = size | USED;

  if (bt != last)
    bt_clr_prevfree(bt_next(bt));
}

static inline void bt_make_FREE(word_t *bt, size_t size) {

  *bt = size;
  *bt_footer(bt) = size;

  if (bt != last)
    bt_set_prevfree(bt_next(bt));
}

static inline bt_flags bt_get_prevfree(word_t *bt) {
  if (bt == heap_start)
    return 0;

  return *bt & PREVFREE;
}

static inline void *bt_payload(word_t *bt) {
  return bt + 1;
}

static inline word_t *bt_prev(word_t *bt) {
  if (bt == heap_start)
    return NULL;

  return (void *)bt - bt_size((void *)bt - sizeof(word_t));
}

static void *morecore(size_t size) {
  void *ptr = mem_sbrk(size);
  if (ptr == (void *)-1)
    return NULL;
  return ptr;
}

int mm_init(void) {

  morecore(ALIGNMENT - sizeof(word_t));

  heap_start = morecore(ALIGNMENT);
  bt_make_FREE(heap_start, ALIGNMENT);
  last = heap_start;

  return 0;
}

/* Szuka pasującego wolnego bloku */

static word_t *find_fit(size_t reqsz) {

  for (word_t *i = heap_start; i != NULL; i = bt_next(i))
    if (bt_size(i) >= reqsz && bt_free(i))
      return i;

  return NULL;
}

void *malloc(size_t size) {

  size = round_up(size + sizeof(word_t));
  word_t *best = find_fit(size);

  if (best == NULL) /* alokacja na koncu */
  {

    if (bt_free(last)) /* na końcu jest wolny blok, więc alokuję tylko tyle
                          pamięci, ile brakuje do utworzenia bloku na końcu */
      morecore(size - bt_size(last));
    else
      last = morecore(size);

    bt_make_USED(last, size);

    return bt_payload(last);

  } /* alokacja w środku */

  size_t sizeBest = bt_size(best);
  bt_make_USED(best, size);

  if (size != sizeBest) { /* jeżeli po alokacji zostanie trochę wolnej pamięci w
                             pasującym bloku */

    word_t *next = (void *)best + bt_size(best);
    bt_make_FREE(next, sizeBest - size);

    if (last == best)
      last = (void *)best + size;
  }

  return bt_payload(best);
}

void free(void *ptr) {

  if (ptr == NULL || ptr < 0)
    return;

  ptr = ptr - sizeof(word_t);

  if (bt_get_prevfree(ptr)) { /* Jeżeli poprzedni blok jest wolny to łączę oba
                                 bloki i ustawiam połączony blok na free */

    if (ptr == last)
      last = bt_prev(ptr);

    ptr = bt_prev(ptr);
    bt_make_FREE(ptr, bt_size(ptr) + bt_size(ptr + bt_size(ptr)));
  }

  if (bt_next(ptr) != NULL &&
      bt_free(bt_next(ptr))) { /* Jeżeli następny blok jest wolny to łączę oba
                                  bloki i ustawiam połączony blok na free */

    if (bt_next(ptr) == last)
      last = ptr;

    bt_make_FREE(ptr, bt_size(ptr) + bt_size(ptr + bt_size(ptr)));
  }

  bt_make_FREE(ptr, bt_size(ptr));
}

void *realloc(void *old_ptr, size_t size) {

  if (old_ptr == NULL)
    return malloc(size);

  if (size == 0) {
    free(old_ptr);
    return NULL;
  }

  word_t *old_ptr_tag = old_ptr - sizeof(word_t);

  size_t new_size = round_up(size + sizeof(word_t));
  size_t old_size = bt_size(old_ptr_tag);

  if (new_size == old_size)
    return old_ptr;

  size_t size_next = 0;

  if (old_ptr_tag != last)
    size_next = bt_size(bt_next(old_ptr_tag));

  if (old_size > new_size) { /* Skracam zajęty blok */

    bt_make_USED(old_ptr_tag, new_size);
    bt_make_USED((void *)old_ptr_tag + new_size, old_size - new_size);

    if (old_ptr_tag == last)
      last = (void *)old_ptr_tag + bt_size(old_ptr_tag);

    free(bt_payload((void *)old_ptr_tag + new_size));

    return bt_payload(old_ptr_tag);
  }

  if (old_ptr_tag == last) /* alokuję pamięć na końcu */
  {

    morecore(new_size - old_size);
    bt_make_USED(old_ptr_tag, new_size);

    return bt_payload(old_ptr_tag);
  }

  if (bt_free(bt_next(old_ptr_tag)) &&
      bt_size(old_ptr_tag) + bt_size(bt_next(old_ptr_tag)) ==
        new_size) /* blok zajmuje dokładnie ten i kolejny wolny blok */
  {

    bt_make_USED(old_ptr_tag, new_size);

    return bt_payload(old_ptr_tag);
  }

  if (bt_free(bt_next(old_ptr_tag)) &&
      bt_size(old_ptr_tag) + bt_size(bt_next(old_ptr_tag)) >
        new_size) /* biorę trochę pamięci z następnego bloku */
  {

    bt_make_USED(old_ptr_tag, new_size);
    bt_make_FREE(bt_next(old_ptr_tag), old_size + size_next - new_size);

    if (last == (void *)old_ptr_tag + old_size)
      last = (void *)old_ptr_tag + new_size;

    return bt_payload(old_ptr_tag);
  }

  /* trzeba wywołać funkcję malloc */

  void *new_ptr = malloc(size);

  if (!new_ptr)
    return NULL;

  memcpy(new_ptr, old_ptr, size);

  free(old_ptr);

  return new_ptr;
}

void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);
  if (new_ptr)
    memset(new_ptr, 0, bytes);
  return new_ptr;
}

void mm_checkheap(int verbose) {
}
