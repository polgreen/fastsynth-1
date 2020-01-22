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
                                              max_array_index(2),

                                              single_local_var(true),
                                              max_index_modifier(0)
    {
    }
    sygus_interfacet sygus_interface;
    solutiont solution;
    std::set<irep_idt> declared_variables;
    decision_proceduret::resultt array_synth_loop(sygus_parsert &parser, problemt &problem);

    bool bound_array_exprs(exprt &expr, std::size_t bound);
    void expand_let_expressions(exprt &expr);

private:
    void remove_added_implication(exprt &expr);
    std::set<exprt> symbols_to_bound;
    void initialise_variable_set(const problemt &problem);


    bool bound_arrays(problemt &problem, std::size_t bound);
    bool bound_arrays(exprt &expr, std::size_t bound);
    mp_integer max_array_index;
    void unbound_arrays_in_solution(solutiont &solution);
    void add_quantifiers_back(exprt &expr);
    void normalise_quantifier_index_adjustments(array_index_locst &loc);

    std::vector<array_index_locst> array_index_locations;

    bool find_array_indices(const exprt &expr, const std::size_t &depth, const std::size_t &distance_from_left, bool top_expr);
    void replace_array_indices_with_local_vars(exprt &expr, std::size_t &vector_idx, const array_index_locst &loc);

    bool single_local_var;
    std::set<exprt> added_implications;
    mp_integer max_index_modifier;
    void add_implication(exprt &expr);
    bool compare_expr(const exprt &expr1, const exprt &expr2);
    void bound_expression(const exprt & index_expr);
    void contains_variable(const exprt &expr, bool &contains_var, bool &constains_local_var);

};

#endif /*CPROVER_FASTSYNTH_ARRAY_SYNTH_H_*/