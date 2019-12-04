/*
 * array_cegis.h
 *
 *  Created on: 2 Dec 2019
 *      Author: elipol
 */

#ifndef SRC_FASTSYNTH_ARRAY_CEGIS_H_
#define SRC_FASTSYNTH_ARRAY_CEGIS_H_

#include <cstdlib>
#include <util/message.h>
#include "cegis.h"
#include "cegis_types.h"

int run_array_cegis(problemt &problem, cegist &cegis);
void bound_array_exprs(exprt &expr, std::size_t length);
void bound_array_symbols(exprt &expr, std::size_t length);


#endif /* SRC_FASTSYNTH_ARRAY_CEGIS_H_ */
