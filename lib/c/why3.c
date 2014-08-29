#include <stdlib.h>
#include <stdbool.h>
#include <gc.h>
#include <gmp.h>

typedef void* value;
typedef char const * exn_tag;
struct variant {int key; value* val;};
struct exn {exn_tag key; value val;};
struct closure {value f; value* env;};
