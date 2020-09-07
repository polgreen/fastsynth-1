#include "verify.h"
#include "array_synth.h"
#include <util/namespace.h>
#include <util/arith_tools.h>
#include <util/symbol_table.h>
#include <util/string2int.h>
#define MAX_ARRAY_SIZE 11
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
      status() << " Declared variable " << id2string(id.first) << eom;
    }
  }
}

void expand_let_expressions(problemt &problem)
{
  for (auto &expr : problem.constraints)
    expand_let_expressions(expr);
}

solutiont array_syntht::build_solution(const solutiont &solution)
{
  // INVARIANT(solution.functions.size() == 1,
  //           "only single solution synthesis is supported for array synth");

  // result exprt;
  // for (const auto &partial_sol : solutions_so_far)
  // {
  //   if (partial_sol.lower_bound && partial_sol.upper_bound)
  //     exprt =
  // }
  return solution;
}

decision_proceduret::resultt array_syntht::array_synth_loop(sygus_parsert &parser, problemt &problem)
{
  initialise_variable_set(problem);
  expand_let_expressions(problem);

  std::size_t array_size = 1;
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  problemt local_problem = problem;

  verifyt verify(ns, local_problem, get_message_handler());
  verify.use_smt = true;

  array_size = 2;
  while (array_size < MAX_ARRAY_SIZE)
  {
    problem = local_problem;
    bound_arrays(problem, array_size);
    sygus_interface.clear();
    status() << "Array size bounded to width " << array_size << eom;

    decision_proceduret::resultt result;
#ifdef FUDGE
    result = sygus_interface.fudge();
#else
    // try without grammar and with timeout
    result = sygus_interface.doit(problem, true, false, array_size, 10);
    // if failed without grammar, try with grammar
    if (result == decision_proceduret::resultt::D_ERROR)
    {
      sygus_interface.clear();
      result = sygus_interface.doit(problem, true, true, array_size);
    }

#endif

    switch (result)
    {
    case decision_proceduret::resultt::D_ERROR:
      status() << "Warning, error from sygus interface \n";
    case decision_proceduret::resultt::D_UNSATISFIABLE:
      status() << " no solution with array bound " << array_size << eom;
      array_size++;
      break;
    case decision_proceduret::resultt::D_SATISFIABLE:
      status() << "Verifying solution from CVC4\n"
               << eom;
      for (const auto &f : sygus_interface.solution.functions)
      {
        status() << "SOLUTION" << expr2sygus(f.second, false) << eom;
      }

      // unbound the solution and put quantifiers back
      unbound_arrays_in_solution(sygus_interface.solution);
      // add solution to the rest of the solution we have obtained so far

      // verify
      switch (verify(build_solution(sygus_interface.solution)))
      {
      case decision_proceduret::resultt::D_SATISFIABLE:
      {
        status() << "SAT, got counterexample.\n"
                 << eom;
        counterexamplet cex = verify.get_counterexample();
        // update set of indices for synthesis, based on counterexample

        // clear last sygus solution
        sygus_interface.solution.functions.clear();
      }
      break;
      case decision_proceduret::resultt::D_UNSATISFIABLE:
        status() << "UNSAT, got solution with array size " + std::to_string(array_size) + " \n " << eom;
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