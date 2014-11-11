// RUN: %clang_safestack %s -o %t
// RUN: %run %t

// RUN: %clang_nosafestack %s -o %t
// RUN: %run ! %t

int main(int argc, char **argv)
{
  int value1 = 42;
  int buffer[5];
  int value2 = 42;
  buffer[-1] = 36;
  buffer[6] = 36;
  return value1 != 42 || value2 != 42;
}
