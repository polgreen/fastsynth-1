#include "verify.h"
#include "array_synth.h"
#include <util/namespace.h>
#include <util/arith_tools.h>
#include <util/symbol_table.h>
#include <util/string2int.h>
#define MAX_ARRAY_SIZE 5
#include <iostream>
#include <cmath>
#include "bitvector2integer.h"
#include <algorithm>
//#define FUDGE

void array_syntht::initialise_variable_set(const problemt &problem)
{
  for (const auto &id : problem.id_map)
  {
    if (id.second.kind == smt2_parsert::idt::VARIABLE &&
        id.second.type.id() != ID_mathematical_function &&
        id.second.definition.is_nil())
    {
      declared_variables.insert(id.first);
    }
  }
}

void expand_let_expressions(problemt &problem)
{
  for (auto &expr : problem.constraints)
    expand_let_expressions(expr);
}

void array_syntht::process_counterexample(problemt &problem,
                                          const counterexamplet &cex)
{
  std::cout << "processing counterexamples" << std::endl;

  for (const auto &ass : cex.assignment)
  {
    if (ass.second.id() == ID_with)
    {
      debug() << "Array counterexample assignment was an ID with" << eom;
      debug() << "where " << to_with_expr(ass.second).where().pretty() << eom;
      exprt where = to_with_expr(ass.second).where();
      if (where.id() == ID_constant)
      {
        mp_integer cex_value;
        to_integer(to_constant_expr(where), cex_value);
        counterexamples.insert(to_constant_expr(where));

        // assume this must be new? if not, something has gone wrong
        bool is_new = true;

        for (const auto &i : indices)
          if (i == cex_value)
            is_new = false;

        if (is_new)
          indices.push_back(cex_value);
        else
        {
          mp_integer max = 0;
          for (const auto &i : indices)
            if (i > max)
              max = i;

          indices.push_back(max + 1);
        }
      }
    }
  }
}

solutiont array_syntht::build_solution(const solutiont &solution)
{

  INVARIANT(solution.functions.size() == 1,
            "only single solution synthesis is supported for array synth");
  partial_solutiont new_solution;
  new_solution.predicate = solution.functions.begin()->second;

  return solution;
}

decision_proceduret::resultt array_syntht::array_synth_loop(sygus_parsert &parser, problemt &problem)
{
  initialise_variable_set(problem);
  expand_let_expressions(problem);
  int no_grammar_timeout = 2;
  int grammar_timeout = 60;
  bool synthesis_phase_completed = false;

  std::size_t array_size = 1;
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  problemt local_problem = problem;

  verifyt verify(ns, local_problem, get_message_handler());
  verify.use_smt = true;

  array_size = 2;
  bool use_grammar = false;
  bool use_integers = true;
  bool solution_has_quants = false;
  while (indices.size() < MAX_ARRAY_SIZE)
  {
    sygus_interface.clear();
    problem = local_problem;
    bound_arrays(problem, array_size);
    debug() << "Array size bounded to width " << array_size << eom;
    decision_proceduret::resultt result;

    // alternates betrween "with grammar" and "without grammar". The timeout for "without grammar" is shorter
    result = sygus_interface.doit(
        problem, use_integers, use_grammar, array_size, use_grammar ? grammar_timeout : no_grammar_timeout);

    switch (result)
    {
    case decision_proceduret::resultt::D_ERROR:
      if (!use_grammar)
        use_grammar = true;
      else
      {
        use_grammar = false;
        if (synthesis_phase_completed)
          array_size++;
        else
        {
          no_grammar_timeout = 60;
          grammar_timeout = 120;
        }
      }
      break;
    case decision_proceduret::resultt::D_UNSATISFIABLE:
      debug() << " no solution with array bound " << array_size << eom;
      if (!use_grammar)
        use_grammar = true;
      else
      {
        use_grammar = false;
        array_size++;
      }
      break;
    case decision_proceduret::resultt::D_SATISFIABLE:
      debug() << "Verifying solution from CVC4\n"
              << eom;
      synthesis_phase_completed = true;
      // unbound the solution and put quantifiers back
      solution_has_quants = unbound_arrays_in_solution(sygus_interface.solution);
      // add solution to the rest of the solution we have obtained so far

      // verify
      switch (verify(build_solution(sygus_interface.solution)))
      {
      case decision_proceduret::resultt::D_SATISFIABLE:
      {
        status() << "verifying candidate failed, got counterexample."
                 << eom;
        counterexamplet cex = verify.get_counterexample();
        // update set of indices for synthesis, based on counterexample
        if (!use_grammar)
          use_grammar = true;
        else
        {
          use_grammar = false;
          // process_counterexample(problem, cex);
          if (synthesis_phase_completed)
            array_size++;
        }

        debug() << "Trying full scale synthesis with soln."
                << eom;
        solution = sygus_interface.solution;
        sygus_interface.clear();
        sygus_interface.add_prev_solution_to_grammar(solution);
        result = sygus_interface.doit(
            local_problem, use_integers, true, array_size, 120);
        if (result == decision_proceduret::resultt::D_SATISFIABLE)
        {
          status() << "Got solution from synthesis-based generalisation with array size "
                   << array_size << "\n"
                   << eom;
          solution = sygus_interface.solution;
          return decision_proceduret::resultt::D_SATISFIABLE;
        }

        sygus_interface.solution.functions.clear();
      }
      break;
      case decision_proceduret::resultt::D_UNSATISFIABLE:
        status() << "Got solution from semantic generalisation with array size "
                 << array_size << " \n " << eom;
        solution = sygus_interface.solution;
        return decision_proceduret::resultt::D_SATISFIABLE;
      case decision_proceduret::resultt::D_ERROR:
        status() << "ERROR " << eom;
        assert(0);
        break;
      }
    }
  }
  status() << "Reached max array size " << array_size << eom;
  return decision_proceduret::resultt::D_ERROR;
}