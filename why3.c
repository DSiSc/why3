#include <stdlib.h>
#include <stdbool.h>
#include <gc.h>
#include <gmp.h>

typedef void* value;
typedef char const * exn_tag;
struct variant {int key; value* val;};
struct exn {exn_tag key; value val;};
struct closure {value f; value* env;};

struct variant* why3__Bool__False;
struct variant* why3__Bool__True;

value int_add(value x, value y)
{
    mpz_ptr res = GC_malloc(sizeof(mpz_ptr));

    mpz_init(res);
    mpz_add(res, x, y);

    return res;
}

value int_sub(value x, value y)
{
    mpz_ptr res = GC_malloc(sizeof(mpz_ptr));

    mpz_init(res);
    mpz_sub(res, x, y);

    return res;
}

value int_mul(value x, value y)
{
    mpz_ptr res = GC_malloc(sizeof(mpz_ptr));

    mpz_init(res);
    mpz_mul(res, x, y);

    return res;
}

value int_cmp(value x, value y)
{
    if (mpz_cmp(x, y) == 0)
        return why3__Bool__True;
    else
        return why3__Bool__False;
}

static _GC_realloc_(void *old, size_t unused, size_t new_size) {
    GC_realloc(old, new_size);
}

static _GC_free_(void *old, size_t unused) {
    GC_free(old);
}

struct closure* test__Test__fact_rec;

int main(int argc, char** argv) {
    GC_init();
    mp_set_memory_functions(GC_malloc, _GC_realloc_, _GC_free_);
    struct closure* main = test__Test__fact_rec;
    value (*f)(value, value*) = main->f;
    mpz_t lol;
    mpz_init_set_str(lol, argv[1], 10);
    gmp_printf("%Zd\n", f(lol, NULL));
    return 0;
}
