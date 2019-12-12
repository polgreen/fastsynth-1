#include "verify.h"
#include "array_synth.h"
#include <util/namespace.h>
#include <util/symbol_table.h>
#include <util/string2int.h>
#define MAX_ARRAY_SIZE 10
#include <iostream>

void array_syntht::update_biggest_array_access(const exprt &expr)
{
  if (expr.id() == ID_index)
  {
    if (to_index_expr(expr).index().id() != ID_constant)
    {
      int index_num = safe_string2unsigned(id2string(to_constant_expr(expr).get_value()), 16u);
      if (index_num > biggest_array_access)
        biggest_array_access = index_num;
    }
  }
}

// replace array index type with next biggest bitvector type
void bound_array_types(typet &type, std::size_t &bound)
{
  if (type.id() == ID_array)
  {
    array_typet array = to_array_type(type);
    exprt new_size;
    if (array.size().id() == ID_constant)
    {
      std::cout << "were we expecting this??\n"
                << type.pretty() << std::endl;
    }
    else
    {
      if (array.size().type().id() == ID_unsignedbv)
      {
        // std::size_t width = to_unsignedbv_type(array.size().type()).get_width();
        new_size = infinity_exprt(unsignedbv_typet(bound));
      }
      // assume array size is an infinity exprt of a given type
    }
    type = array_typet(to_array_type(type).subtype(), new_size);
  }
  else if (type.id() == ID_mathematical_function)
  {
    mathematical_function_typet math_fun = to_mathematical_function_type(type);
    bound_array_types(math_fun.codomain(), bound);
    for (auto &arg : math_fun.domain())
      bound_array_types(arg, bound);
    type = math_fun;
  }
  else
  {
    std::cout << "Not bounding " << type.pretty() << std::endl;
  }
}

void bound_array_exprs(exprt &expr, std::size_t bound)
{
  for (auto &op : expr.operands())
    bound_array_exprs(op, bound);

  if (expr.id() == ID_array)
  {
    array_typet array_type = to_array_expr(expr).type();
    bound_array_types(array_type, bound);
    expr = array_exprt(to_array_expr(expr).operands(), array_type);
  }
  else if (expr.id() == ID_symbol)
  {
    if (expr.type().id() == ID_array)
    {
      array_typet array_type = to_array_type(expr.type());
      bound_array_types(array_type, bound);
      expr = symbol_exprt(to_symbol_expr(expr).get_identifier(), array_type);
    }
  }
  else if (expr.id() == ID_nondet_symbol)
  {
    if (expr.type().id() == ID_array)
    {
      array_typet array_type = to_array_type(expr.type());
      bound_array_types(array_type, bound);
      expr = nondet_symbol_exprt(to_nondet_symbol_expr(expr).get_identifier(), array_type);
    }
  }
  else if (expr.id() == ID_index)
  {
    // bound array
    bound_array_exprs(to_index_expr(expr).array(), bound);
    // bound index
    exprt index = to_index_expr(expr).index();
    if (index.id() == ID_constant && index.type().id() == ID_unsignedbv)
    {
      index = constant_exprt(to_constant_expr(index).get_value(), unsignedbv_typet(bound));
    }
    else
    {
      std::cout << "Unsupported array index type " << index.pretty() << std::endl;
    }
    expr = index_exprt(to_index_expr(expr).array(), index);
  }
  else if (expr.id() == ID_with)
  {
    std::cout << "Unsupported expr: ID_with " << expr.pretty() << std::endl;
  }
}

void array_syntht::unbound_arrays_in_solution(solutiont &solution)
{
  for (auto &e : solution.functions)
    bound_array_exprs(e.second, original_word_length);
}

void array_syntht::bound_arrays(problemt &problem, std::size_t bound)
{
  for (auto &c : problem.constraints)
    bound_array_exprs(c, bound);

  for (auto &id : problem.id_map)
  {
    bound_array_types(id.second.type, bound);
    bound_array_exprs(id.second.definition, bound);
  }
}

decision_proceduret::resultt array_syntht::array_synth_loop(sygus_parsert &parser, problemt &problem)
{
  std::size_t array_size = 2;
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  problemt local_problem = problem;

  verifyt verify(ns, local_problem, get_message_handler());
  solutiont local_solution;
  // try full length first:
  if (sygus_interface.doit(problem) == decision_proceduret::resultt::D_SATISFIABLE)
  {
    local_solution = sygus_interface.solution;
    //  return decision_proceduret::resultt::D_SATISFIABLE;
  }

  while (array_size < MAX_ARRAY_SIZE)
  {
    bound_arrays(problem, array_size);
    sygus_interface.clear();
    status() << "Array size bounded to width " << array_size << eom;
    switch (sygus_interface.doit(problem))
    {
    case decision_proceduret::resultt::D_ERROR:
      status() << "Warning, error from sygus interface \n";
    case decision_proceduret::resultt::D_UNSATISFIABLE:
      status() << " no solution with array bound " << array_size << eom;
      array_size++;
      break;
    case decision_proceduret::resultt::D_SATISFIABLE:
      status() << "Verifying solution from CVC4\n";
      unbound_arrays_in_solution(solution);
      switch (verify(sygus_interface.solution))
      {
      case decision_proceduret::resultt::D_SATISFIABLE:
      {
        status() << "SAT, got counterexample.\n";
        counterexamplet cex = verify.get_counterexample();
        for (const auto &ass : cex.assignment)
        {
          status() << "ASSIGNMENT" << ass.first.pretty() << "::\n";
          status() << ass.second.pretty() << "\n";
        }
        array_size++;
      }
      break;
      case decision_proceduret::resultt::D_UNSATISFIABLE:
        status() << "UNSAT, got solution \n ";
        return decision_proceduret::resultt::D_SATISFIABLE;
      case decision_proceduret::resultt::D_ERROR:
        status() << "ERROR ";
        break;
      }
    }
  }
  return decision_proceduret::resultt::D_ERROR;
}