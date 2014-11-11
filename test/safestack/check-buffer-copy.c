// RUN: %clang %s -o %t
// RUN: %run %t

int main(int argc, char **argv)
{
  int i;
  char buffer[128];

  // check that we can write to a buffer
  for (i = 0; argv[0][i] && i < sizeof (buffer) - 1; ++i)
    buffer[i] = argv[0][i];
  buffer[i] = '\0';

  // check that we can read from a buffer
  for (i = 0; argv[0][i] && i < sizeof (buffer) - 1; ++i)
    if (buffer[i] != argv[0][i])
      return 1;
  return 0;
}
