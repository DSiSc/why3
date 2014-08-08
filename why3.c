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
