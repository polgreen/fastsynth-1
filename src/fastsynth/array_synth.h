#include "cvc4_interface.h"
#include "verify.h"
#include <util/message.h>

class array_syntht : public messaget
{
public:
    array_syntht(
        message_handlert &_message_handler) : messaget(_message_handler),
                                              biggest_array_access(2u),
                                              original_word_length(32u)
    {
    }
    sygus_interfacet sygus_interface;
    solutiont solution;
    decision_proceduret::resultt array_synth_loop(sygus_parsert &parser, problemt &problem);

private:
    void bound_arrays(problemt &problem, std::size_t bound);
    void update_biggest_array_access(const exprt &expr);
    std::size_t biggest_array_access;
    std::size_t original_word_length;
    void unbound_arrays_in_solution(solutiont &solution);
};