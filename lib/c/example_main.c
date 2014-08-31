#include "why3.c"
#include "why3__Tuple0.c"
#include "demo__Demo.c"

int main(int argc, char** argv) {
    GC_init();
    struct closure* main = M_demo__Demo__fact;
    value (*f)(value, value*) = main->f;
    mpz_t lol;
    mpz_init_set_str(lol, argv[1], 10);
    gmp_printf("%Zd\n", f(lol, NULL));
    return EXIT_SUCCESS;
}
