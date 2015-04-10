// RUN: %clang_safestack %s -pthread -o %t
// RUN: %run ! %t

#include <stdlib.h>
#include <string.h>
#include <pthread.h>

#define BUFFER_SIZE (1 << 15)

void *t1_start(void *ptr)
{
  char buffer[BUFFER_SIZE];
  return buffer;
}

int main(int argc, char **argv)
{
  pthread_t t1;
  char *buffer = NULL;

  if (pthread_create(&t1, NULL, t1_start, NULL))
    abort();
  if (pthread_join(t1, &buffer))
    abort();

  // should segfault here
  memset(buffer, 0, BUFFER_SIZE);
  return 0;
}
