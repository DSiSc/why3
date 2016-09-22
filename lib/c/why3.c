#ifndef WHY3
#define WHY3

#include <stdlib.h>
#include <stdbool.h>
#include <gc.h>
#include <gmp.h>
#include <setjmp.h>

typedef void* value;
typedef char const * exn_tag;
struct variant {int key; value* val;};
struct exn {exn_tag key; value val;};
struct closure {value f; value* env;};

__thread struct exn* Exn = NULL;

static void _int_finalizer(void* x, void* unused)
{
    mpz_clear(x);
}

mpz_ptr int_create()
{
    mpz_ptr res = GC_malloc(sizeof(mpz_t));

    GC_register_finalizer(res, _int_finalizer, NULL, NULL, NULL);
    mpz_init(res);

    return res;
}

mpz_ptr int_create_from_str(const char* str, int base)
{
    mpz_ptr res = GC_malloc(sizeof(mpz_t));

    GC_register_finalizer(res, _int_finalizer, NULL, NULL, NULL);
    mpz_init_set_str(res, str, base);

    return res;
}

mpz_ptr int_clone(value x)
{
    mpz_ptr res = GC_malloc(sizeof(mpz_t));

    GC_register_finalizer(res, _int_finalizer, NULL, NULL, NULL);
    mpz_init_set(res, x);

    return res;
}

#endif
