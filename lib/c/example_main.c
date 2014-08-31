#include "why3.c"
#include "why3__Tuple0.c"
#include "demo__Demo.c"

static void *_GC_realloc_(void *old, size_t unused, size_t new_size) {
    return GC_realloc(old, new_size);
}

static void _GC_free_(void *old, size_t unused) {
    GC_free(old);
}

int main(int argc, char** argv) {
    GC_init();
    mp_set_memory_functions(GC_malloc, _GC_realloc_, _GC_free_);
    struct closure* main = M_demo__Demo__fact;
    value (*f)(value, value*) = main->f;
    mpz_t lol;
    mpz_init_set_str(lol, argv[1], 10);
    gmp_printf("%Zd\n", f(lol, NULL));
    return EXIT_SUCCESS;
}
