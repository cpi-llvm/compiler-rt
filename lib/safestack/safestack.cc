//===-- safestack.cc --------------------------------------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the runtime support for the safe stack protection
// mechanism. The runtime manages allocation/deallocation of the unsafe stack
// for the main thread, as well as all pthreads threads that are
// created/destroyed during program execution.
//
//===----------------------------------------------------------------------===//

#include <stdio.h>
#include <assert.h>
#include <dlfcn.h>
#include <limits.h>
#include <sys/mman.h>
#include <sys/user.h>
#include <sys/resource.h>
#include <pthread.h>

#if defined(__linux__)
#include <unistd.h>
#include <sys/syscall.h>
#endif

/// Minimum stack alignment for the unsafe stack.
/// FIXME: is this in some header?
#define STACK_ALIGN 16

/// Default size of the unsafe stack. This value is only used if the stack
/// size rlimit is set to infinity.
#define DEFAULT_UNSAFE_STACK_SIZE 0x2800000

#include "interception/interception.h"

namespace __llvm__safestack {

// We don't know whether pthread is linked in or not, so we resolve
// all symbols from pthread that we use dynamically
#define __DECLARE_WRAPPER(fn) __typeof__(fn)* __d_ ## fn = NULL;

__DECLARE_WRAPPER(pthread_attr_init)
__DECLARE_WRAPPER(pthread_attr_destroy)
__DECLARE_WRAPPER(pthread_attr_getstacksize)
__DECLARE_WRAPPER(pthread_attr_getguardsize)
__DECLARE_WRAPPER(pthread_key_create)
__DECLARE_WRAPPER(pthread_setspecific)

// The unsafe stack pointer is stored in the TCB structure on these platforms
#if defined(__i386__)
# define MOVPTR "movl"
# ifdef __pic__
#  define IMM_MODE "nr"
# else
#  define IMM_MODE "ir"
# endif
#elif defined(__x86_64__)
# define MOVPTR "movq"
# define IMM_MODE "nr"
#endif

#if defined(__APPLE__) && (defined(__i386__) || defined(__x86_64__))

  /* On Darwin, we store the unsafe stack pointer in one of the
   * thread-specific data slots that are reserved for system libraries.
   * Such data slots are directly accessible through the %gs segment, and
   * are described in detail in pthreads/pthread_machdep.h in Darwin Libc.
   * As of Libc-825, slots 0 - 255 are reserved, but only slots 0 - 119
   * are actually used. We use slot 192, which is accessible as
   * %gs:(192 * sizeof(void*))
   */

# define __THREAD_GETMEM_L(slot)                            \
  __extension__ ({ unsigned long  __v;                      \
      asm volatile (MOVPTR " %%gs:%P1,%q0" : "=r" (__v)     \
                    : "i" ((slot) * sizeof(void*))); __v; })

# define __THREAD_SETMEM_L(slot, value)               \
  asm volatile (MOVPTR " %q0,%%gs:%P1" :              \
                : IMM_MODE ((unsigned long) (value)), \
                  "i" ((slot) * sizeof(void*)))

// The following locations are platform-specific
# define __GET_UNSAFE_STACK_PTR()         (void*) __THREAD_GETMEM_L(192)
# define __SET_UNSAFE_STACK_PTR(value)    __THREAD_SETMEM_L(192, value)

#else

  /* TODO: To make accessing the unsafe stack pointer faster, we plan to
   * eventually store it directly in the thread control block data structure on
   * platforms where this structure is pointed to by %fs or %gs. This is exactly
   * the same mechanism as currently being used by the traditional stack
   * protector pass to store the stack guard (see getStackCookieLocation()
   * function above). Doing so requires changing the tcbhead_t struct in glibc
   * on Linux and tcb struct in libc on FreeBSD.
   */

// The unsafe stack is stored in a thread-local variable on all other platforms
extern "C" {
  __attribute__((visibility ("default")))
  __thread void  *__llvm__unsafe_stack_ptr = 0;
}

# define __GET_UNSAFE_STACK_PTR()         __llvm__unsafe_stack_ptr
# define __SET_UNSAFE_STACK_PTR(value)    __llvm__unsafe_stack_ptr = (value)

#endif

// Per-thread unsafe stack information. It's not frequently accessed, so there
// it can be kept out of the tcb in normal thread-local variables.
__thread void  *unsafe_stack_start = 0;
__thread size_t unsafe_stack_size = 0;
__thread size_t unsafe_stack_guard = 0;

# define __GET_UNSAFE_STACK_START()       unsafe_stack_start
# define __SET_UNSAFE_STACK_START(value)  unsafe_stack_start = (value)

# define __GET_UNSAFE_STACK_SIZE()        unsafe_stack_size
# define __SET_UNSAFE_STACK_SIZE(value)   unsafe_stack_size = (value)

# define __GET_UNSAFE_STACK_GUARD()       unsafe_stack_guard
# define __SET_UNSAFE_STACK_GUARD(value)  unsafe_stack_guard = (value)

static inline void *unsafe_stack_alloc(size_t size, size_t guard) {
  void *addr =
#if defined(__APPLE__)
    mmap(
#else
    (void*) syscall(SYS_mmap,
#endif
              NULL, size + guard, PROT_WRITE  | PROT_READ,
              MAP_PRIVATE | MAP_ANON
#ifdef MAP_STACK
              | MAP_STACK
#endif
#ifdef MAP_GROWSDOWN
              | MAP_GROWSDOWN
#endif
              , -1, 0);
  mprotect(addr, guard, PROT_NONE);
  return (char*) addr + guard;
}

static inline void unsafe_stack_setup(void *start, size_t size, size_t guard) {
  void* stack_ptr = (char*) start + size;
  assert((((size_t)stack_ptr) & (STACK_ALIGN-1)) == 0);

  __SET_UNSAFE_STACK_PTR(stack_ptr);
  __SET_UNSAFE_STACK_START(start);
  __SET_UNSAFE_STACK_SIZE(size);
  __SET_UNSAFE_STACK_GUARD(guard);
}

static void unsafe_stack_free() {
  if (__GET_UNSAFE_STACK_START()) {
#if defined(__APPLE__)
    munmap(
#else
    syscall(SYS_munmap,
#endif
      (char*) __GET_UNSAFE_STACK_START() - __GET_UNSAFE_STACK_GUARD(),
      __GET_UNSAFE_STACK_SIZE() + __GET_UNSAFE_STACK_GUARD());
  }
  __SET_UNSAFE_STACK_START(0);
}

/// Thread data for the cleanup handler
pthread_key_t thread_cleanup_key;

/// Safe stack per-thread information passed to the thread_start function
struct tinfo {
  void *(*start_routine)(void*);
  void *start_routine_arg;

  void *unsafe_stack_start;
  size_t unsafe_stack_size;
  size_t unsafe_stack_guard;
};

/// Wrap the thread function in order to deallocate the unsafe stack when the
/// thread terminates by returning from its main function.
static void* thread_start(void *arg) {
  struct tinfo *tinfo = (struct tinfo*) arg;

  void *(*start_routine)(void*) = tinfo->start_routine;
  void *start_routine_arg = tinfo->start_routine_arg;

  // Setup the unsafe stack; this will destroy tinfo content
  unsafe_stack_setup(tinfo->unsafe_stack_start,
                     tinfo->unsafe_stack_size,
                     tinfo->unsafe_stack_guard);

  // Make sure out thread-specific destructor will be called
  // FIXME: we can do this only any other specific key is set by
  // intersepting the pthread_setspecific function itself
  __d_pthread_setspecific(thread_cleanup_key, (void*) 1);

  // Start the original thread rutine
  return start_routine(start_routine_arg);
}

/// Intercept thread creation operation to allocate and setup the unsafe stack
INTERCEPTOR(int, pthread_create, pthread_t *thread,
            const pthread_attr_t *attr,
            void *(*start_routine)(void*), void *arg) {

  size_t size = 0;
  size_t guard = 0;

  if (attr != NULL) {
    __d_pthread_attr_getstacksize(attr, &size);
    __d_pthread_attr_getguardsize(attr, &guard);
  } else {
    // get pthread default stack size
    pthread_attr_t tmpattr;
    __d_pthread_attr_init(&tmpattr);
    __d_pthread_attr_getstacksize(&tmpattr, &size);
    __d_pthread_attr_getguardsize(&tmpattr, &guard);
    __d_pthread_attr_destroy(&tmpattr);
  }

  assert(size != 0);
  assert((size & (STACK_ALIGN-1)) == 0);
  assert((guard & (PAGE_SIZE-1)) == 0);

  void *addr = unsafe_stack_alloc(size, guard);
  struct tinfo *tinfo = (struct tinfo*) (
        ((char*)addr) + size - sizeof(struct tinfo));
  tinfo->start_routine = start_routine;
  tinfo->start_routine_arg = arg;
  tinfo->unsafe_stack_start = addr;
  tinfo->unsafe_stack_size = size;
  tinfo->unsafe_stack_guard = guard;

  return REAL(pthread_create)(thread, attr, thread_start, tinfo);
}

/// Thread-specific data destructor
void thread_cleanup_handler(void* _iter) {
  // We want to free the unsafe stack only after all other destructors
  // have already run. We force this function to be called multiple times.
  size_t iter = (size_t) _iter;
  if (iter < PTHREAD_DESTRUCTOR_ITERATIONS) {
    __d_pthread_setspecific(thread_cleanup_key, (void*) (iter + 1));
  } else {
    // This is the last iteration
    unsafe_stack_free();
  }
}

int inited = 0;

extern "C"
__attribute__((visibility ("default")))
#ifndef __linux__
__attribute__((constructor(0)))
#endif
void __llvm__safestack_init() {
  if (inited)
    return;

  inited = 1;

  // Determine the stack size for the main thread.
  size_t size = DEFAULT_UNSAFE_STACK_SIZE;
  size_t guard = 4096;

  struct rlimit limit;
  if (getrlimit(RLIMIT_STACK, &limit) != 0
      || limit.rlim_cur == RLIM_INFINITY)
    size = limit.rlim_cur;

  // Allocate unsafe stack for main thread
  void *addr = unsafe_stack_alloc(size, guard);
  unsafe_stack_setup(addr, size, guard);

  // Initialize pthread interceptors for thread allocation
  INTERCEPT_FUNCTION(pthread_create);

  #define __FIND_FUNCTION(fn) \
    __d_ ## fn = __extension__ (__typeof__(__d_ ## fn)) dlsym(RTLD_DEFAULT, #fn);

  // Find pthread functions that we need
  __FIND_FUNCTION(pthread_attr_init)
  __FIND_FUNCTION(pthread_attr_destroy)
  __FIND_FUNCTION(pthread_attr_getstacksize)
  __FIND_FUNCTION(pthread_attr_getguardsize)
  __FIND_FUNCTION(pthread_key_create)
  __FIND_FUNCTION(pthread_setspecific)

  if (__d_pthread_key_create != NULL) {
    // We're using pthreads, setup the cleanup handler
    __d_pthread_key_create(&thread_cleanup_key, thread_cleanup_handler);
  }
}

#ifndef NDEBUG
extern "C"
__attribute__((visibility ("default")))
void __llvm__safestack_dump() {
  fprintf(stderr,
          "Unsafe stack addr = %p, ptr = %p, size = 0x%lx, guard = 0x%lx\n",
          __GET_UNSAFE_STACK_START(), __GET_UNSAFE_STACK_PTR(),
          __GET_UNSAFE_STACK_SIZE(), __GET_UNSAFE_STACK_GUARD());
}

#endif

extern "C"
__attribute__((visibility ("default")))
__attribute__((noinline))
void *__safestack_get_unsafe_stack_start() {
  return __GET_UNSAFE_STACK_START();
}

extern "C"
__attribute__((visibility ("default")))
__attribute__((noinline))
void *__safestack_get_unsafe_stack_ptr() {
  return __GET_UNSAFE_STACK_PTR();
}

extern "C"
__attribute__((visibility ("default")))
__attribute__((noinline))
void *__safestack_get_safe_stack_ptr() {
  return (char*) __builtin_frame_address(0) + 2*sizeof(void*);
}

#ifdef __linux__
// Run safestack initialization before any other constructors
// FIXME: can we do something similar on Mac or FreeBSD?
extern "C" {
__attribute__((section(".preinit_array"), used))
void (*__llvm__safestack_preinit)(void) = __llvm__safestack_init;
}
#endif

} // namespace __llvm__safestack
