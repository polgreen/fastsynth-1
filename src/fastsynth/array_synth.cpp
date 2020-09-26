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

void array_syntht::process_counterexample(problemt &problem,
                                          const counterexamplet &cex)
{
  std::cout << "processing counterexamples" << std::endl;

  for (const auto &ass : cex.assignment)
  {
    if (ass.second.id() == ID_with)
    {
      status() << "Array counterexample assignment was an ID with" << eom;
      status() << "where " << to_with_expr(ass.second).where().pretty() << eom;
      exprt where = to_with_expr(ass.second).where();
      if (where.id() == ID_constant)
      {
        mp_integer cex_value;
        to_integer(to_constant_expr(where), cex_value);
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

  std::size_t array_size = 1;
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  problemt local_problem = problem;

  verifyt verify(ns, local_problem, get_message_handler());
  verify.use_smt = true;

  array_size = 2;
  problem = local_problem;
  bound_arrays(problem, array_size);
  sygus_interface.clear();
  status() << "Array size bounded to width " << array_size << eom;

  while (indices.size() < MAX_ARRAY_SIZE)
  {
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
        process_counterexample(problem, cex);
        // array_size++;

        // clear last sygus solution
        sygus_interface.solution.functions.clear();
      }
      break;
      case decision_proceduret::resultt::D_UNSATISFIABLE:
        status() << "UNSAT, got solution with array size " << indices.size() << " \n " << eom;
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