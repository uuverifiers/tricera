#ifndef MACROS_ILP32_H
#define MACROS_ILP32_H

#define CHAR_BIT 8

#define SCHAR_MIN (-128)
#define SCHAR_MAX 127
#define UCHAR_MAX 255

#define SHRT_MIN (-32768)
#define SHRT_MAX 32767
#define USHRT_MAX 65535

#define INT_MIN (-2147483648)
#define INT_MAX 2147483647
#define UINT_MAX 4294967295U

#define LONG_MIN (-2147483648L)
#define LONG_MAX 2147483647L
#define ULONG_MAX 4294967295UL

#define LLONG_MIN (-9223372036854775808LL)
#define LLONG_MAX 9223372036854775807LL
#define ULLONG_MAX 18446744073709551615ULL

#define SIZE_MAX 4294967295U

typedef unsigned int size_t;
typedef int ptrdiff_t;

#define NULL 0
#define EXIT_SUCCESS 0
#define EXIT_FAILURE 1

#ifndef __bool_true_false_are_defined
#define __bool_true_false_are_defined 1
#define bool _Bool
#define true 1
#define false 0
#endif /* __bool_true_false_are_defined */

#endif