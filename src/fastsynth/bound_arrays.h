#ifndef CPROVER_FASTSYNTH_BOUND_ARRAYS_H_
#define CPROVER_FASTSYNTH_BOUND_ARRAYS_H_

#include <util/expr.h>

void bound_array_types(typet &type, std::size_t &bound);
void bound_array_exprs(exprt &expr, std::size_t bound);

#endif /*CPROVER_FASTSYNTH_BOUND_ARRAYS_H_*/