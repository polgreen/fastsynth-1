#ifndef CPROVER_FASTSYNTH_ARRAY_SYNTH_H_
#define CPROVER_FASTSYNTH_ARRAY_SYNTH_H_

#include "sygus_interface.h"
#include "verify.h"
#include <util/message.h>

struct array_index_locst
{
    std::vector<irep_idt> names;
    std::vector<std::pair<int, int>> locations;
    std::vector<mp_integer> index_adjustments;
    mp_integer max_index_adjustment;
    std::vector<symbol_exprt> quantifier_bindings;
};

inline bool operator==(const array_index_locst &a, const array_index_locst &b)
{
    if (a.names != b.names)
        return false;
    if (a.locations != b.locations)
        return false;
    else
        return true;
};

class array_syntht : public messaget
{
public:
    array_syntht(
        message_handlert &_message_handler) : messaget(_message_handler),

                                              original_word_length(32u),
                                              max_array_index(2),
                                              max_quantifier_adjustment(0),
                                              single_local_var(true)
    {
    }
    sygus_interfacet sygus_interface;
    solutiont solution;
    decision_proceduret::resultt array_synth_loop(sygus_parsert &parser, problemt &problem);
    solutiont fix_types(const problemt &problem, solutiont &solution);
    decision_proceduret::resultt array_synth_with_ints_loop(sygus_parsert &parser, problemt &problem);
    void bound_array_types(typet &type, std::size_t &bound);
    void bound_array_exprs(exprt &expr, std::size_t bound);
    bool bound_bitvectors(exprt &expr, const std::size_t &bound);
    void expand_let_expressions(exprt &expr);

private:
    void remove_added_implication(exprt &expr);
    std::set<symbol_exprt> symbols_to_bound;
    void bound_arrays(problemt &problem, std::size_t bound);
    std::size_t original_word_length;
    mp_integer max_array_index;
    void unbound_arrays_in_solution(solutiont &solution);
    std::map<symbol_exprt, std::size_t> original_array_sizes;
    void add_quantifiers_back(exprt &expr);
    void normalise_quantifier_index_adjustments(array_index_locst &loc);

    std::vector<array_index_locst> array_index_locations;

    std::vector<symbol_exprt> quantifier_bindings;
    std::vector<irep_idt> arrays_that_are_indexed;
    std::vector<std::pair<int, int>> location_of_array_indices;
    mp_integer max_quantifier_adjustment;
    std::vector<mp_integer> quantifier_index_adjustment;
    void clear_array_index_search();
    bool find_array_indices(const exprt &expr, const std::size_t &depth, const std::size_t &distance_from_left, bool top_expr);
    // bool check_array_indices(const exprt &expr, const std::size_t &depth, const std::size_t &distance_from_left, std::size_t &vector_idx);
    void replace_array_indices_with_local_vars(exprt &expr, std::size_t &vector_idx, const array_index_locst &loc);
    // map of arrays being indexed to their index type
    std::map<irep_idt, typet> array_index_map;
    bool single_local_var;
    std::vector<exprt> added_implications;

    // vector of symbol with the binary predicate that should be applied to them.
};

#endif /*CPROVER_FASTSYNTH_ARRAY_SYNTH_H_*/