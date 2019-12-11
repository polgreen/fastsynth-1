#include "cvc4_interface.h"
#include "sygus_parser.h"
#include "verify.h"
#include <util/message.h>

class array_syntht : public messaget
{
    sygus_interfacet sygus_interface;
    void array_synth_loop(sygus_parsert &parser, problemt &problem);
};