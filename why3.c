#include <stdlib.h>
#include <stdbool.h>
#include <gc.h>
#include <gmp.h>

typedef void* value;
typedef char const * exn_tag;
struct variant {int key; value* val;};
struct exn {exn_tag key; value val;};
struct closure {value f; value* env;};

struct variant ___False = {0, NULL};
value why3__Bool__False = &___False;
struct variant ___True = {1, NULL};
value why3__Bool__True = &___True;
struct variant ___Tuple0 = {0, NULL};
value why3__Tuple0__Tuple0 = &___Tuple0;

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

value test__Test__fact_rec;
void Init();

int main() {
    GC_init();
    mp_set_memory_functions(GC_malloc, _GC_realloc_, _GC_free_);
    Init();
    struct closure* main = test__Test__fact_rec;
    value (*f)(value, value*) = main->f;
    mpz_t lol;
    mpz_init_set_str(lol, "4", 10);
    gmp_printf("%Zd\n", f(lol, NULL));
    return 0;
}
