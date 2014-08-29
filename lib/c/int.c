#ifndef INT_DRV
#define INT_DRV

extern struct variant* T_why3__Bool__False;
extern struct variant* T_why3__Bool__True;

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

value int_eq(value x, value y)
{
    if (mpz_cmp(x, y) == 0)
        return T_why3__Bool__True;
    else
        return T_why3__Bool__False;
}

#endif
