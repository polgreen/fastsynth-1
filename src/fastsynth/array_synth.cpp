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


bool compare_exprs_no_symbols(const exprt &expr1, const exprt &expr2)
{
  std::cout<<"Comparing "<< expr2sygus(expr1, true) <<" and "<< expr2sygus(expr2, true)<<std::endl;
  bool result=true;
  if (expr1.id() != expr2.id())
    result = false;
  else if (expr1.operands().size() != expr2.operands().size())
    result = false;
  else if (expr1.id() == ID_symbol)
  {
    if (expr1.type() != expr2.type())
      result = false;
  }
  else
  {
    for (int i = 0; i < expr1.operands().size(); i++)
    {
      if (!compare_exprs_no_symbols(expr1.operands()[i], expr2.operands()[i]))
        result = false;
    }
  }
  std::cout<<" Result: "<< result<<std::endl;
  return result;
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
    std::size_t conjunction_size = bound;
    if (quant.variables().size() == 1)
    {
      auto &var = to_symbol_expr(quant.variables()[0]);
      if (var.type().id() == ID_unsignedbv)
      {
        const auto bv_options =
            std::pow(2, to_unsignedbv_type(var.type()).get_width());
        if (bv_options < bound)
          conjunction_size = bv_options;
      }

      irep_idt var_id = var.get_identifier();
      exprt result = (expr.id() == ID_forall) ? exprt(ID_and, quant.type()) : exprt(ID_or, quant.type());
      exprt local_where = quant.where();

      for (int i = 0; i < conjunction_size; i++)
      {
        replace_variable_with_constant(local_where, var_id, from_integer(i, var.type()));
        result.operands().push_back(local_where);
        local_where = quant.where();
      }
      expr = result;
    }
  }
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

bool array_syntht::find_array_indices(const exprt &expr,
                                      const std::size_t &depth,
                                      const std::size_t &distance_from_left,
                                      bool top_index = false)
{
  bool result = false;
  if (top_index)
    array_index_locations.push_back(array_index_locst());

  INVARIANT(array_index_locations.size() > 0, "vector must be bigger than 0");
  auto &this_expr = array_index_locations.back();
  if (expr.id() == ID_index)
  {
    result = true;
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
    if (find_array_indices(op, depth + 1, distance))
      result = true;
    distance++;
  }
  return result;
}

void array_syntht::replace_array_indices_with_local_vars(exprt &expr, std::size_t &vector_idx, const array_index_locst &locs)
{
  if (expr.id() == ID_index && locs.names.size() > 0)
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
bool array_syntht::compare_expr(const exprt &expr1, const exprt &expr2)
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
  if(expr1.id()==ID_symbol)
  {
    if(declared_variables.find(
      clean_id(to_symbol_expr(expr1).get_identifier()))!=
      declared_variables.end())
      if(declared_variables.find(
        clean_id(to_symbol_expr(expr2).get_identifier()))!=
          declared_variables.end())
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
  array_index_locations.clear();
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
    bool found_array = false;
    for (int i = 0; i < operands.size(); i++)
    {
      if (find_array_indices(operands[i], 0, 0, true))
        found_array = true;
      normalise_quantifier_index_adjustments(array_index_locations[i]);
    }
    if (!found_array)
      return;

    // hunt for sets of matching expressions in the conjunction
    std::vector<int> matching_indices;
    matching_indices.push_back(0);
    for (int i = 0; i < operands.size() - 1; i++)
    {
      if (array_index_locations[i] == array_index_locations[i + 1] && compare_expr(operands[i], operands[i + 1]))
        matching_indices.push_back(i + 1);
      else
      {
        sets_of_matching_indices.push_back(matching_indices);
        matching_indices.clear();
        matching_indices.push_back(i + 1);
      }
    }
    sets_of_matching_indices.push_back(matching_indices);

    exprt result;
    for (int i = 0; i < sets_of_matching_indices.size(); i++)
    {
      exprt result_expr;
      auto &indices = sets_of_matching_indices[i];

      if (indices.size() == 1)
        result_expr = operands[indices[0]];
      else if (indices.size() != 0 && indices.size() != 1)
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

          exprt is_less_than_bound = binary_predicate_exprt(
              adjusted_index, ID_lt, from_integer(max_array_index, first_expr_locs.quantifier_bindings[0].type()));
          implies_exprt
              implication(is_less_than_bound, operands[0]);
          where = implication;
        }
        if (single_local_var)
        {
          if (first_expr_locs.quantifier_bindings.size() > 0)
          {
            quantifier_exprt new_expr =
                (expr.id() == ID_and) ? quantifier_exprt(
                                            ID_forall, first_expr_locs.quantifier_bindings[0], where)
                                      : quantifier_exprt(ID_exists, first_expr_locs.quantifier_bindings[0], where);
            result_expr = new_expr;
          }
        }
        else
        {
          if (first_expr_locs.quantifier_bindings.size() > 0)
          {
            quantifier_exprt new_expr =
                (expr.id() == ID_and) ? quantifier_exprt(
                                            ID_forall, first_expr_locs.quantifier_bindings, where)
                                      : quantifier_exprt(ID_exists, first_expr_locs.quantifier_bindings, where);
            result_expr = new_expr;
          }
        }
      }

      if (i > 0)
      {
        if (expr.id() == ID_and)
          result = and_exprt(result_expr, result);
        else
          result = or_exprt(result_expr, result);
      }
      else
        result = result_expr;
    }
    if (sets_of_matching_indices.size() > 0)
      expr = result;
  }
}

void find_and_remove_expr(exprt &original_expr, const exprt &find)
{
  if(original_expr.id()==ID_and)
  {
    //TODO make this more efficient
    std::vector<exprt> new_operands;
    for(auto &op: original_expr.operands())
      if(!compare_exprs_no_symbols(op, find))
        new_operands.push_back(op);

    if(new_operands.size()==1)
      original_expr = new_operands[0];
    else      
      original_expr.operands()=new_operands;  
  }
  if(original_expr.id()==ID_implies)
  {
    if(compare_exprs_no_symbols(original_expr.operands()[0], find))
      original_expr = original_expr.operands()[1];
  }

  for(auto &op: original_expr.operands())
    find_and_remove_expr(op, find);
}

void array_syntht::remove_added_implication(exprt &expr)
{
  status() << "List of "<< added_implications.size()<<" added implications ";
  for (const auto &e : added_implications)
    status() << expr2sygus(e, false) << " " << eom;
  status()<<"end of list \n"<<eom;  

  status() << "Expression to remove these from: " << expr2sygus(expr, false) << eom;
  std::vector<int> remove_operands;
  std::vector<int> keep_operands;

  for (const auto &comparison : added_implications)
  {
    find_and_remove_expr(expr, comparison);
  }
}



bool array_syntht::bound_arrays(problemt &problem, std::size_t bound)
{
  max_array_index = bound;

  for (auto &c : problem.constraints)
    if(!bound_arrays(c, bound))
      return false;

  for (auto &c : problem.constraints)
    replace_quantifier_with_conjunction(c, bound);    
  
  return true;    
}


void array_syntht::initialise_variable_set(const problemt &problem)
{
    for (const auto &id : problem.id_map)
  {
    if (id.second.kind == smt2_parsert::idt::VARIABLE &&
        id.second.type.id() != ID_mathematical_function &&
        id.second.definition.is_nil())
    {
      declared_variables.insert(id.first);
      status()<<" Declared variable "<< id2string(id.first)<<eom;
    }
  }
}


decision_proceduret::resultt array_syntht::array_synth_loop(sygus_parsert &parser, problemt &problem)
{
  // return array_synth_with_ints_loop(parser, problem);
  initialise_variable_set(problem);
  
  std::size_t array_size = 1;
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  problemt local_problem = problem;

  verifyt verify(ns, local_problem, get_message_handler());
  verify.use_smt = true;

  // try removing quantifiers and nothing else;
  //for (auto &c : problem.constraints)
  // remove_forall_quantifiers(c);
  //sygus_interface.doit(problem);
  //verify(sygus_interface.solution);
  array_size = 2;
  while (array_size < MAX_ARRAY_SIZE)
  {
    added_implications.clear();
    problem = local_problem;
    status()
        << "Starting to bound arrays to width " << array_size << eom;
    bound_arrays(problem, array_size);
    sygus_interface.clear();
    status() << "Array size bounded to width " << array_size << eom;
    switch (sygus_interface.doit(problem, true))
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
      {
        status() << "SOLUTION" << expr2sygus(f.second, false) << eom;
      }
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