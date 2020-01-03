#ifndef CPROVER_FASTSYNTH_ARRAY_SYNTH_H_
#define CPROVER_FASTSYNTH_ARRAY_SYNTH_H_

#include "sygus_interface.h"
#include "verify.h"
#include <util/message.h>

class array_syntht : public messaget
{
public:
    array_syntht(
        message_handlert &_message_handler) : messaget(_message_handler),

                                              original_word_length(32u),
                                              single_local_var(true)
    {
    }
    sygus_interfacet sygus_interface;
    solutiont solution;
    decision_proceduret::resultt array_synth_loop(sygus_parsert &parser, problemt &problem);
    solutiont fix_types(const problemt &problem, solutiont &solution);
    decision_proceduret::resultt array_synth_with_ints_loop(sygus_parsert &parser, problemt &problem);

private:
    void bound_arrays(problemt &problem, std::size_t bound);
    std::size_t original_word_length;
    void unbound_arrays_in_solution(solutiont &solution);
    std::map<symbol_exprt, std::size_t> original_array_sizes;
    void add_quantifiers_back(exprt &expr);

    // set of arrays that are indexed in an expr
    std::set<irep_idt> arrays_being_indexed;
    // location of array indices, stored as depth,distance_from_left
    std::vector<irep_idt> arrays_that_are_indexed;
    std::vector<std::pair<int, int>> location_of_array_indices;
    std::vector<symbol_exprt> quantifier_bindings;
    void clear_array_index_search();
    void find_array_indices(const exprt &expr, const std::size_t &depth, const std::size_t &distance_from_left);
    bool check_array_indices(const exprt &expr, const std::size_t &depth, const std::size_t &distance_from_left, std::size_t &vector_idx);
    void replace_array_indices_with_local_vars(exprt &expr, std::size_t &vector_idx);
    // map of arrays beubg indexed to their index type
    std::map<irep_idt, typet> array_index_map;
    bool single_local_var;

    // vector of symbol with the binary predicate that should be applied to them.
};

#endif /*CPROVER_FASTSYNTH_ARRAY_SYNTH_H_*/