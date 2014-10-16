// RUN: %clang_safestack %s -o %t
// RUN: %run %t

// RUN: %clang_nosafestack -fno-stack-protector %s -o %t
// RUN: %run ! %t

void fct(int *buffer)
{
  buffer[-1] = 36;
  buffer[6] = 36;
}

int main(int argc, char **argv)
{
  int value1 = 42;
  int buffer[5];
  int value2 = 42;
  fct(buffer);
  return value1 != 42 || value2 != 42;
}
