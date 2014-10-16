#ifndef SAFESTACK_INTERFACE_H
#define SAFESTACK_INTERFACE_H

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

void *__safestack_get_unsafe_stack_start();
void *__safestack_get_unsafe_stack_ptr();
size_t __safestack_get_unsafe_stack_size();

void *__safestack_get_safe_stack_ptr();

#ifdef __cplusplus
} // extern "C"
#endif

#endif // SAFESTACK_INTERFACE_H
