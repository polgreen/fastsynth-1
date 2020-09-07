#ifndef CPROVER_FASTSYNTH_ARRAY_SYNTH_H_
#define CPROVER_FASTSYNTH_ARRAY_SYNTH_H_

#include "sygus_interface.h"
#include "verify.h"
#include <util/message.h>
#include <iostream>

void expand_let_expressions(exprt &expr);

struct array_index_locst
{
    irep_idt name;
    std::vector<std::pair<int, int>> locations;
    std::vector<mp_integer> index_adjustments;
    std::vector<mp_integer> constant_adjustments;
    std::vector<mp_integer> original_index_values;
    symbol_exprt quantifier_binding;
    array_index_locst() : quantifier_binding(symbol_exprt("null", integer_typet()))
    {
    }
};

inline std::string output_expr_locs(const array_index_locst &a)
{
    std::string result;
    result = "Array index locst for array " + id2string(a.name);
    result += "\nLocations: ";
    for (const auto &l : a.locations)
        result += integer2string(l.first) + "," + integer2string(l.second) + " ";
    result += "\nIndex Adjustments: ";
    for (const auto &l : a.index_adjustments)
        result += integer2string(l) + " ";
    result += "\n";
    return result;
}

struct expr_array_index_locst
{
    mp_integer max_index_adjustment;
    std::vector<array_index_locst> array_indexes;
    std::vector<std::pair<int, int>> constant_locations;
    std::vector<constant_exprt> constant_values;
};

struct partial_solutiont
{
    exprt predicate;
    optionalt<std::size_t> lower_bound;
    optionalt<std::size_t> upper_bound;
};

inline bool operator==(const array_index_locst &a, const array_index_locst &b)
{
    if (a.name != b.name)
        return false;
    // if (a.locations != b.locations)
    //  return false;
    if (a.index_adjustments != b.index_adjustments)
        return false;
    else
        return true;
}

class array_syntht : public messaget
{
public:
    array_syntht(
        message_handlert &_message_handler) : messaget(_message_handler),
                                              max_array_index(2),

                                              single_local_var(true),
                                              local_var_counter(0),
                                              max_index_modifier(0)
    {
    }
    sygus_interfacet sygus_interface;
    solutiont solution;
    std::set<irep_idt> declared_variables;
    decision_proceduret::resultt array_synth_loop(sygus_parsert &parser, problemt &problem);

private:
    std::set<exprt> symbols_to_bound;
    std::set<exprt> symbols_to_bound_outside_constraint;
    void initialise_variable_set(const problemt &problem);
    void bound_arrays(problemt &problem, std::size_t bound);
    std::vector<partial_solutiont> solutions_so_far;
    solutiont build_solution(const solutiont &solution);

    mp_integer max_array_index;
    void unbound_arrays_in_solution(solutiont &solution);
    void add_quantifiers_back(exprt &expr);
    void normalise_quantifier_index_adjustments(expr_array_index_locst &loc);

    std::vector<expr_array_index_locst> array_index_locations;

    bool find_array_indices(const exprt &expr, const std::size_t &depth, const std::size_t &distance_from_left, bool top_expr, bool inside_idx);
    void replace_array_indices_with_local_vars(
        exprt &expr, const std::size_t vector_idx, const array_index_locst &locs,
        bool replace_constants, std::size_t &constant_vector_idx, const symbol_exprt &quantifier_binding,
        const std::vector<bool> &replace_these_constants);

    bool single_local_var;
    std::size_t local_var_counter;
    mp_integer max_index_modifier;
    void add_implication(exprt &expr, std::set<exprt> &symbols);
    bool compare_expr(const exprt &expr1, const exprt &expr2);
};

#endif /*CPROVER_FASTSYNTH_ARRAY_SYNTH_H_*/