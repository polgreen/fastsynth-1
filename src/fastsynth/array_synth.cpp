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

  if (expr.id() == ID_forall || expr.id() == ID_exists)
  {
    const quantifier_exprt &quant = to_quantifier_expr(expr);
    if (quant.variables().size() == 1)
    {
      auto &var = to_symbol_expr(quant.variables()[0]);
      if (var.type().id() == ID_unsignedbv)
      {
        const auto &bv = to_unsignedbv_type(var.type());
        if (bv.get_width() < 4 || bound < 4)
        {
          irep_idt var_id = var.get_identifier();
          exprt result = (expr.id() == ID_forall) ? exprt(ID_and, quant.type()) : exprt(ID_or, quant.type());
          exprt local_where = quant.where();

          int number_of_options = std::pow(2, std::min(bv.get_width(), bound));
          for (int i = 0; i < number_of_options; i++)
          {
            replace_variable_with_constant(local_where, var_id, from_integer(i, var.type()));
            result.operands().push_back(local_where);
            local_where = quant.where();
          }
          expr = result;
        }
      }
    }
  }
}

void array_syntht::clear_array_index_search()
{
  arrays_that_are_indexed.clear();
  location_of_array_indices.clear();
  quantifier_bindings.clear();
  quantifier_index_adjustment.clear();
  max_quantifier_adjustment = 0;
}

void array_syntht::normalise_quantifier_index_adjustments(array_index_locst &loc)
{
  if (loc.index_adjustments.size() == 0)
    return;
  mp_integer minimum = loc.index_adjustments[0];
  for (const auto &i : loc.index_adjustments)
    if (i < minimum)
      minimum = i;

  for (auto &i : loc.index_adjustments)
  {
    i = i - minimum;
    if (i > loc.max_index_adjustment)
      loc.max_index_adjustment = i;
  }
}

void array_syntht::find_array_indices(const exprt &expr,
                                      const std::size_t &depth,
                                      const std::size_t &distance_from_left,
                                      bool top_index = false)
{
  if (top_index)
  {
    // TODO: fix this initialisation
    // array_index_locst new_expr_locs;
    // std::vector<irep_idt> names;
    // std::vector<std::pair<int, int>> locations;
    // std::vector<mp_integer> index_adjustments;
    // std::vector<symbol_exprt> quantifier_bindings;
    // new_expr_locs.index_adjustments = index_adjustments;
    // new_expr_locs.max_index_adjustment = 0;
    // new_expr_locs.locations = locations;
    // new_expr_locs.names = names;
    array_index_locations.push_back(array_index_locst());
  }

  INVARIANT(array_index_locations.size() > 0, "vector must be bigger than 0");
  auto &this_expr = array_index_locations.back();
  if (expr.id() == ID_index)
  {
    if (to_index_expr(expr).index().id() == ID_constant)
    {
      // find linear relation between indices
      mp_integer value = 0;
      INVARIANT(!to_integer(to_constant_expr(to_index_expr(expr).index()), value), "unable to get index value");
      this_expr.index_adjustments.push_back(value);

      if (to_index_expr(expr).array().id() == ID_symbol)
        this_expr.names.push_back(to_symbol_expr(to_index_expr(expr).array()).get_identifier());
      else
        this_expr.names.push_back("no-symbol");

      this_expr.locations.push_back(std::pair<int, int>(depth, distance_from_left));
      std::string id = "local_var" + (single_local_var ? "0" : std::to_string(this_expr.names.size()));
      this_expr.quantifier_bindings.push_back(symbol_exprt(id, to_index_expr(expr).index().type()));
    }
  }

  std::size_t distance = 0;
  for (const auto &op : expr.operands())
  {
    find_array_indices(op, depth + 1, distance);
    distance++;
  }
}

void array_syntht::replace_array_indices_with_local_vars(exprt &expr, std::size_t &vector_idx, const array_index_locst &locs)
{
  if (expr.id() == ID_index)
  {
    assert(vector_idx < locs.names.size());
    if (locs.index_adjustments[vector_idx] == 0)
    {
      index_exprt new_expr(to_index_expr(expr).array(), locs.quantifier_bindings[vector_idx]);
      expr = new_expr;
    }
    else
    {
      exprt adjusted_index = binary_exprt(locs.quantifier_bindings[vector_idx], ID_plus,
                                          from_integer(locs.index_adjustments[vector_idx],
                                                       locs.quantifier_bindings[vector_idx].type()));
      index_exprt new_expr(to_index_expr(expr).array(), adjusted_index);
      expr = new_expr;
    }
    vector_idx++;
  }

  for (auto &op : expr.operands())
    replace_array_indices_with_local_vars(op, vector_idx, locs);
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

  // clear quantifier search here?
  clear_array_index_search();
  /*
    we can replace conjunctions with quantifiers if the following hold:
    - is a conjunction of predicates
    - each predicate is the same
    - each predicate takes an array index expr as an argument
    - the array that is indexed is the same
    - the index is a constant and all possible indices of that array must be covered
  */
  // if this is not a conjunction or disjunction it can't be replaced with a forall.
  if (expr.id() == ID_and || expr.id() == ID_or)
  {
    //int i = 0;
    std::vector<int> indices;

    std::vector<std::vector<int>> sets_of_matching_indices;

    auto &operands = expr.operands();
    assert(operands.size() != 0);

    for (int i = 0; i < operands.size(); i++)
    {
      find_array_indices(operands[i], 0, 0, true);
      normalise_quantifier_index_adjustments(array_index_locations[i]);
    }

    // hunt for sets of matching expressions in the conjunction
    std::vector<int> matching_indices;
    matching_indices.push_back(0);
    for (int i = 0; i < operands.size() - 1; i++)
    {
      if (array_index_locations[i] == array_index_locations[i + 1] && compare_expr(operands[i], operands[i + 1]))
      {
        std::cout << "Expression " << i << " and expression " << i + 1 << " matched " << std::endl;
        matching_indices.push_back(i + 1);
      }
      else
      {
        std::cout << "The following do not match: " << expr2sygus(operands[i], false) << " and " << expr2sygus(operands[i + 1]) << std::endl;
        std::cout << "The array index locations for the first expr are:" << std::endl;
        for (const auto &indx : array_index_locations[i].locations)
        {
          std::cout << indx.first << ", " << indx.second << std::endl;
        }
        std::cout << "The array index locations for the second expr are:" << std::endl;
        for (const auto &indx : array_index_locations[i + 1].locations)
        {
          std::cout << indx.first << ", " << indx.second << std::endl;
        }

        sets_of_matching_indices.push_back(matching_indices);
        matching_indices.clear();
        matching_indices.push_back(i + 1);
      }
    }
    sets_of_matching_indices.push_back(matching_indices);

    std::cout << "We found " << sets_of_matching_indices.size() << " sets of matching indices" << std::endl;
    exprt result;
    for (int i = 0; i < sets_of_matching_indices.size(); i++)
    {
      exprt result_expr;
      auto &indices = sets_of_matching_indices[i];

      if (indices.size() == 1)
        result_expr = operands[indices[0]];
      else
      {
        std::size_t vector_idx = 0;
        exprt &where = operands[indices[0]];
        replace_array_indices_with_local_vars(where, vector_idx, array_index_locations[indices[0]]);
        auto &first_expr_locs = array_index_locations[indices[0]];
        if (first_expr_locs.max_index_adjustment > 0)
        {
          INVARIANT(single_local_var, "Not yet implemented: multiple local vars with adjustements");
          // build implication which says that the property holds only if the local variables are within array bounds
          exprt adjusted_index = binary_exprt(first_expr_locs.quantifier_bindings[0], ID_plus,
                                              from_integer(first_expr_locs.max_index_adjustment,
                                                           first_expr_locs.quantifier_bindings[0].type()));

          exprt is_less_than_bound = binary_predicate_exprt(adjusted_index, ID_lt, from_integer(max_array_index, quantifier_bindings[0].type()));
          implies_exprt
              implication(is_less_than_bound, operands[0]);
          where = implication;
        }
        if (single_local_var)
        {
          quantifier_exprt new_expr =
              (expr.id() == ID_and) ? quantifier_exprt(
                                          ID_forall, first_expr_locs.quantifier_bindings[0], where)
                                    : quantifier_exprt(ID_exists, first_expr_locs.quantifier_bindings[0], where);
          result_expr = new_expr;
        }
        else
        {
          quantifier_exprt new_expr =
              (expr.id() == ID_and) ? quantifier_exprt(
                                          ID_forall, first_expr_locs.quantifier_bindings, where)
                                    : quantifier_exprt(ID_exists, first_expr_locs.quantifier_bindings, where);
          result_expr = new_expr;
        }
        if (i > 0)
        {
          if (expr.id() == ID_and)
            result_expr = and_exprt(result_expr, result);
          else
            result_expr = or_exprt(result_expr, result);
        }
        else
          result = result_expr;
      }
    }
    if (sets_of_matching_indices.size() > 0)
      expr = result;
  }
}

void array_syntht::unbound_arrays_in_solution(solutiont &solution)
{
  for (auto &e : solution.functions)
    bound_array_exprs(e.second, original_word_length);

  for (auto &e : solution.functions)
  {
    status() << "Convert this: " << expr2sygus(e.second, false) << eom;
    expand_let_expressions(e.second);
    status() << "To this " << expr2sygus(e.second, false) << eom;
  }

  status() << "Unbounded solutions:";
  for (auto &e : solution.functions)
  {
    status() << "Convert this: " << expr2sygus(e.second, false) << eom;
    add_quantifiers_back(e.second);
    status() << " to " << expr2sygus(e.second, false) << eom;
  }
}

void array_syntht::bound_arrays(problemt &problem, std::size_t bound)
{
  max_array_index = power(2, bound);

  for (auto &c : problem.constraints)
    replace_quantifier_with_conjunction(c, bound);

  for (auto &c : problem.constraints)
    bound_array_exprs(c, bound);

  // for each constraint, we add an implication that the constraints only need to hold if
  // the array indices are within bounds

  for (auto &id : problem.id_map)
  {
    bound_array_types(id.second.type, bound);
    bound_array_exprs(id.second.definition, bound);
  }
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
      std::cout << "Unsupported parameters " << id << std::endl;
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

  std::size_t array_size = 1;
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  problemt local_problem = problem;

  verifyt verify(ns, local_problem, get_message_handler());
  verify.use_smt = true;

  // try removing quantifiers and nothing else;
  //for (auto &c : problem.constraints)
  // remove_forall_quantifiers(c);
  sygus_interface.doit(problem);
  verify(sygus_interface.solution);

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
      status() << "Verifying solution from CVC4\n"
               << eom;
      unbound_arrays_in_solution(sygus_interface.solution);
      status() << "About to verify: \n"
               << eom;
      for (const auto &f : sygus_interface.solution.functions)
        status() << "SOLUTION" << expr2sygus(f.second, false) << eom;

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
        assert(0);
        break;
      }
    }
  }
  status() << "Reached max array size " << array_size << eom;
  return decision_proceduret::resultt::D_ERROR;
}