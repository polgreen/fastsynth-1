#include "array_cegis.h"
#include "verify.h"
#include "array_synth.h"
#include <util/namespace.h>
#include <util/symbol_table.h>

void array_syntht::array_synth_loop(sygus_parsert &parser, problemt &problem)
{
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);
    verifyt verify(ns, problem, get_message_handler());

    sygus_interface.doit(parser);







}