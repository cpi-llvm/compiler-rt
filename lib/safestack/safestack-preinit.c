#ifdef __ELF__
extern void __safestack_init(void);

// Run safestack initialization before any other constructors.
// FIXME: can we do something similar on non-ELF platforms, e.g., on Mac?
__attribute__((section(".preinit_array"), used))
void (*__safestack_preinit)(void) = __safestack_init;
#endif
