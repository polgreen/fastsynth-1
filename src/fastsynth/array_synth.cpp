#include "verify.h"
#include "array_synth.h"
#include "bound_arrays.h"
#include <util/namespace.h>
#include <util/arith_tools.h>
#include <util/symbol_table.h>
#include <util/string2int.h>
#define MAX_ARRAY_SIZE 4
#include <iostream>
#include <cmath>
#include "bitvector2integer.h"
#include <algorithm>

void replace_variable_with_constant(exprt &expr, irep_idt var_name, const exprt &replacement)
{
  for (auto &op : expr.operands())
    replace_variable_with_constant(op, var_name, replacement);

  if (expr.id() == ID_symbol)
    if (to_symbol_expr(expr).get_identifier() == var_name)
      expr = replacement;
}

// if a forall expression has only one variable, and that variable
// is a small bitvector, attempts to replace the forall expr with
// a conjunction
void replace_quantifier_with_conjunction(exprt &expr, const std::size_t &bound)
{
  for (auto &op : expr.operands())
    replace_quantifier_with_conjunction(op, bound);

  if (expr.id() == ID_forall)
  {
    // std::cout << "Trying to replace ID forall\n";
    if (to_forall_expr(expr).variables().size() == 1)
    {
      //  std::cout << "variables size is 1\n";
      auto &var = to_symbol_expr(to_forall_expr(expr).variables()[0]);
      if (var.type().id() == ID_unsignedbv)
      {
        //   std::cout << "var is a bitvector\n";
        const auto &bv = to_unsignedbv_type(var.type());
        if (bv.get_width() < 4 || bound < 4)
        {
          // std::cout << "and the width is less than 4\n";
          const forall_exprt &forall = to_forall_expr(expr);
          irep_idt var_id = var.get_identifier();
          exprt conjunction(ID_and, forall.type());
          exprt local_where = forall.where();

          int number_of_options = std::pow(2, std::min(bv.get_width(), bound));
          for (int i = 0; i < number_of_options; i++)
          {
            replace_variable_with_constant(local_where, var_id, from_integer(i, var.type()));
            conjunction.operands().push_back(local_where);
            local_where = forall.where();
          }
          expr = conjunction;
          //     std::cout << "expr should now be\n"
          //             << conjunction.pretty() << std::endl;
          ;
        }
      }
    }
  }
}

// this changes the synthesis problem and shouldn't
// really be done
void remove_forall_quantifiers(exprt &expr)
{
  for (auto &op : expr.operands())
    remove_forall_quantifiers(op);

  if (expr.id() == ID_forall)
  {
    expr = to_forall_expr(expr).where();
  }
}

void array_syntht::clear_array_index_search()
{
  arrays_that_are_indexed.clear();
  location_of_array_indices.clear();
  quantifier_bindings.clear();
}

void array_syntht::find_array_indices(const exprt &expr,
                                      const std::size_t &depth,
                                      const std::size_t &distance_from_left)
{
  if (expr.id() == ID_index)
  {
    if (to_index_expr(expr).index().id() == ID_constant)
    {
      arrays_that_are_indexed.push_back(to_symbol_expr(to_index_expr(expr).array()).get_identifier());
      location_of_array_indices.push_back(std::pair<int, int>(depth, distance_from_left));
      std::string id = "local_var0"; //+ std::to_string(arrays_that_are_indexed.size());
      quantifier_bindings.push_back(symbol_exprt(id, to_index_expr(expr).index().type()));
    }
  }

  int distance = 0;
  for (const auto &op : expr.operands())
  {
    find_array_indices(op, depth + 1, distance);
    distance++;
  }
}

bool array_syntht::check_array_indices(const exprt &expr,
                                       const std::size_t &depth,
                                       const std::size_t &distance_from_left,
                                       std::size_t &vector_idx)
{
  if (expr.id() == ID_index)
  {
    if (to_index_expr(expr).index().id() == ID_constant)
    {
      if (vector_idx > location_of_array_indices.size())
      {
        status() << "Found an extra array index " << expr.pretty() << eom;
        return false;
      }

      if (to_symbol_expr(to_index_expr(expr).array()).get_identifier() != arrays_that_are_indexed[vector_idx] ||
          location_of_array_indices[vector_idx].first != depth || location_of_array_indices[vector_idx].second != distance_from_left)
      {
        status() << "Did not match array indices:\n"
                 << expr.pretty() << eom;
        return false;
      }
      else
      {
        vector_idx++;
      }
    }
  }
  int distance = 0;
  for (const auto &op : expr.operands())
  {
    if (!check_array_indices(op, depth + 1, distance, vector_idx))
      return false;
    distance++;
  }
  return true;
}

void array_syntht::replace_array_indices_with_local_vars(exprt &expr, std::size_t &vector_idx)
{
  if (expr.id() == ID_index)
  {
    assert(vector_idx < arrays_that_are_indexed.size());
    index_exprt new_expr(to_index_expr(expr).array(), quantifier_bindings[vector_idx]);
    expr = new_expr;
    vector_idx++;
  }

  for (auto &op : expr.operands())
  {
    replace_array_indices_with_local_vars(op, vector_idx);
  }
}

// return true if expressions are the same except with different
// array indices
bool compare_expr(const exprt &expr1, const exprt &expr2)
{
  const auto &operands1 = expr1.operands();
  const auto &operands2 = expr1.operands();
  if (expr1 == expr2)
    return true;
  if (expr1.id() != expr2.id())
    return false;
  if (operands1.size() != operands2.size())
    return false;

  if (expr1.id() == ID_index)
  {
    const auto &array1 = to_index_expr(expr1);
    const auto &array2 = to_index_expr(expr2);
    // TODO handle this better
    if (array1.array() == array2.array())
      return true;
  }

  for (int i = 0; i < operands1.size(); i++)
  {
    if (!compare_expr(operands1[i], operands2[i]))
      return false;
  }
  return true;
}

// this does some kind of reverse quantifier instantiation
void array_syntht::add_quantifiers_back(exprt &expr)
{
  for (auto &o : expr.operands())
    add_quantifiers_back(o);
  /*
    we can replace conjunctions with quantifiers if the following hold:
    - is a conjunction of predicates
    - each predicate is the same
    - each predicate takes an array index expr as an argument
    - the array that is indexed is the same
    - the index is a constant and all possible indices of that array must be covered
  */
  // if this is not a conjunction it can't be replaced with a forall.
  if (expr.id() == ID_and)
  {
    //int i = 0;
    std::vector<int> indices;
    auto &operands = to_and_expr(expr).operands();
    assert(operands.size() != 0);
    find_array_indices(operands[0], 0, 0);

    std::size_t vector_idx = 0;
    std::size_t depth = 0;
    // find matching sets of exprs
    std::vector<std::size_t> unmatching_exprs;
    for (std::size_t i = 1; i < operands.size(); i++)
    {
      // reset vector indx before calling check_array_indices
      vector_idx = 0;
      if (!check_array_indices(operands[i], depth, i - 1, vector_idx))
        unmatching_exprs.push_back(i);
      else
      {
        if (!compare_expr(operands[i], operands[0]))
          unmatching_exprs.push_back(i);
      }
    }

    if (unmatching_exprs.size() == 0)
    {
      status() << "Replaced full conjunction" << eom;
    }

    // we know the length of the array so we could check that there's an expression for each array element
    if (unmatching_exprs.size() < operands.size() - 1)
    {
      std::cout << "We matched some exprs, but not all. Size of operands " << operands.size() << " and unmatched exprs " << unmatching_exprs.size() << std::endl;

      exprt result_expr;
      std::size_t vector_idx = 0;
      replace_array_indices_with_local_vars(operands[0], vector_idx);
      quantifier_exprt new_expr(ID_forall, quantifier_bindings[0], operands[0]);
      result_expr = new_expr;

      if (unmatching_exprs.size() > 0)
      {
        for (const auto &i : unmatching_exprs)
        {
          result_expr = and_exprt(result_expr, operands[i]);
        }
      }
      expr = result_expr;
    }
  }
}

void array_syntht::unbound_arrays_in_solution(solutiont &solution)
{
  status() << "Original solution ";
  for (const auto &e : solution.functions)
    status() << expr2sygus(e.second, false) << eom;

  status() << "And in pretty print \n";
  for (const auto &e : solution.functions)
    status() << e.second.pretty() << eom;

  for (auto &e : solution.functions)
    bound_array_exprs(e.second, original_word_length);

  status() << "Unbounded solutions:";
  for (auto &e : solution.functions)
  {
    status() << "Convert this: " << expr2sygus(e.second, false);
    add_quantifiers_back(e.second);
    status() << " to " << expr2sygus(e.second, false) << eom;
  }
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

  for (auto &c : problem.constraints)
    replace_quantifier_with_conjunction(c, bound);
}

void fix_function_types(exprt &body, const std::vector<typet> &domain)
{
  for (auto &op : body.operands())
    fix_function_types(op, domain);

  if (body.id() == ID_symbol)
  {
    const irep_idt id = to_symbol_expr(body).get_identifier();
    if (id == "synth::parameter0")
      body = symbol_exprt(id, domain[0]);
    else if (id == "synth::parameter1")
      body = symbol_exprt(id, domain[1]);
    else if (id == "synth::parameter2")
      body = symbol_exprt(id, domain[2]);
    else if (id == "synth::parameter3")
      body = symbol_exprt(id, domain[3]);
    else if (id == "synth::parameter4")
      body = symbol_exprt(id, domain[4]);
    else
      std::cout << "Unsupported parameter " << id << std::endl;
  }
  else if (body.id() == ID_constant)
  {
    if (body.type().id() == ID_integer)
    {
      body = constant_exprt(to_constant_expr(body).get_value(), unsignedbv_typet(32));
    }
  }
  else if (body.id() == ID_infinity)
  {
    body = infinity_exprt(unsignedbv_typet(32));
  }
  else if (body.id() == ID_index)
  {
    // fix types in array
    fix_function_types(to_index_expr(body).array(), domain);
    // fix types in index
    exprt index = to_index_expr(body).index();
    if (index.id() == ID_constant && index.type().id() == ID_unsignedbv)
    {
      index = constant_exprt(to_constant_expr(index).get_value(), unsignedbv_typet(32));
    }
    else if (index.id() == ID_symbol)
    {
      index = symbol_exprt(to_symbol_expr(index).get_identifier(), unsignedbv_typet(32));
    }
    body = index_exprt(to_index_expr(body).array(), index);
    // if (body.type().id() == ID_integer)
    // std::cout << "integer " << body.pretty() << std::endl;
  }
}

solutiont array_syntht::fix_types(const problemt &problem, solutiont &solution)
{
  // fix types of a solution to match the problem
  solutiont new_solution;
  for (auto &f : solution.functions)
  {
    irep_idt id = clean_id(to_symbol_expr(f.first).get_identifier());
    std::cout << "Tring to convert function " << id2string(id) << std::endl;
    symbol_exprt intended_signature = symbol_exprt(id, problem.id_map.at(id).type);
    std::vector<typet>
        intended_domain = to_mathematical_function_type(intended_signature.type()).domain();
    fix_function_types(f.second, intended_domain);
    new_solution.functions[intended_signature] = f.second;
  }
  return new_solution;
}

decision_proceduret::resultt array_syntht::array_synth_with_ints_loop(sygus_parsert &parser, problemt &problem)
{
  status() << "Array synth with integers" << eom;
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  problemt original_problem = problem;

  verifyt verify(ns, original_problem, get_message_handler());

  // convert to integers
  status() << "Converting to integers " << eom;
  bitvec2integert bvconv;

  for (auto &c : problem.constraints)
    bvconv.convert(c);

  for (auto &id : problem.id_map)
  {
    bvconv.convert(id.second.type);
    bvconv.convert(id.second.definition);
    std::cout << "ID map " << id2string(id.first) << " " << id.second.type.pretty() << " " << id.second.definition.pretty() << std::endl;
  }

  if (sygus_interface.doit(problem, true) == decision_proceduret::resultt::D_SATISFIABLE)
  {
    status() << "Got integer solution :";
    for (const auto &f : sygus_interface.solution.functions)
      status() << expr2sygus(f.second) << eom;
    // convert back to bitvectors
    status() << "Converting back to bitvectors " << eom;
    solutiont fixedsolution = fix_types(original_problem, sygus_interface.solution);
    status() << "Verification" << eom;
    switch (verify(fixedsolution))
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
    }
    break;
    case decision_proceduret::resultt::D_UNSATISFIABLE:
      status() << "UNSAT, got solution \n ";
      solution = sygus_interface.solution;
      return decision_proceduret::resultt::D_SATISFIABLE;
    case decision_proceduret::resultt::D_ERROR:
      status() << "ERROR ";
      break;
    }
  }
  return decision_proceduret::resultt::D_ERROR;
}

decision_proceduret::resultt array_syntht::array_synth_loop(sygus_parsert &parser, problemt &problem)
{
  // return array_synth_with_ints_loop(parser, problem);

  std::size_t array_size = 2;
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  problemt local_problem = problem;

  verifyt verify(ns, local_problem, get_message_handler());
  verify.use_smt = true;

  // try removing quantifiers and nothing else;
  //for (auto &c : problem.constraints)
  // remove_forall_quantifiers(c);
  sygus_interface.doit(problem);

  while (array_size < MAX_ARRAY_SIZE)
  {
    problem = local_problem;
    status()
        << "Starting to bound arrays to width " << array_size << eom;
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
      clear_array_index_search();
      status() << "Verifying solution from CVC4\n"
               << eom;
      unbound_arrays_in_solution(sygus_interface.solution);
      status() << "About to verify \n"
               << eom;
      switch (verify(sygus_interface.solution))
      {
      case decision_proceduret::resultt::D_SATISFIABLE:
      {
        status() << "SAT, got counterexample.\n"
                 << eom;
        counterexamplet cex = verify.get_counterexample();
        for (const auto &ass : cex.assignment)
        {
          status() << "ASSIGNMENT" << ass.first.pretty() << "::\n"
                   << eom;
          status() << ass.second.pretty() << "\n"
                   << eom;
        }
        sygus_interface.solution.functions.clear();
        array_size++;
      }
      break;
      case decision_proceduret::resultt::D_UNSATISFIABLE:
        status() << "UNSAT, got solution \n " << eom;
        solution = sygus_interface.solution;
        return decision_proceduret::resultt::D_SATISFIABLE;
      case decision_proceduret::resultt::D_ERROR:
        status() << "ERROR " << eom;
        break;
      }
    }
  }
  status() << "Reached max array size " << array_size << eom;
  return decision_proceduret::resultt::D_ERROR;
}