#include "verify.h"
#include "array_synth.h"
#include "bound_arrays.h"
#include <util/namespace.h>
#include <util/arith_tools.h>
#include <util/symbol_table.h>
#include <util/string2int.h>
#include <iostream>
#include <cmath>
#include "bitvector2integer.h"
#include <algorithm>

void replace_local_var(exprt &expr, const irep_idt &target, exprt &replacement)
{
  if (expr.id() == ID_symbol)
  {
    if (to_symbol_expr(expr).get_identifier() == target)
      expr = replacement;
  }
  for (auto &op : expr.operands())
    replace_local_var(op, target, replacement);
}

std::vector<bool> constants_match(const array_index_locst &a, const array_index_locst &b)
{
  std::vector<bool> result;
  if (a.constant_adjustments.size() != b.constant_adjustments.size())
    return result;
  for (unsigned int i = 0; i < a.constant_adjustments.size(); i++)
  {
    // std::cout << "constant adjustments " << a.constant_adjustments[i] << " " << b.constant_adjustments[i] << std::endl;
    result.push_back(a.constant_adjustments[i] == b.constant_adjustments[i]);
  }

  return result;
}

void expand_let_expressions(exprt &expr)
{
  if (expr.id() == ID_let)
  {
    auto &let_expr = to_let_expr(expr);
    for (unsigned int i = 0; i < let_expr.variables().size(); i++)
    {
      INVARIANT(let_expr.variables()[i].id() == ID_symbol,
                "Let expression should have list of symbols, not " + let_expr.variables()[i].pretty());
      replace_local_var(let_expr.where(), to_symbol_expr(let_expr.variables()[i]).get_identifier(), let_expr.values()[i]);
    }
    expr = let_expr.where();
    expand_let_expressions(expr);
  }
  for (auto &op : expr.operands())
    expand_let_expressions(op);
}

void sort_operands(exprt &expr)
{
  for (auto &op : expr.operands())
    sort_operands(op);

  // sort operands of commutative operators
  if (expr.id() == ID_and || expr.id() == ID_or || expr.id() == ID_plus || expr.id() == ID_equal)
    std::sort(expr.operands().begin(), expr.operands().end());
}

// void array_syntht::remove_added_implication(exprt &expr)
// {
//   debug() << "List of " << added_implications.size() << " added implications ";
//   for (const auto &e : added_implications)
//     debug() << expr2sygus(e, false) << " " << eom;
//   debug() << "end of list \n"
//           << eom;

//   debug() << "Expression to remove these from: " << expr2sygus(expr, false) << eom;
//   std::vector<int> remove_operands;
//   std::vector<int> keep_operands;

//   for (const auto &comparison : added_implications)
//   {
//     find_and_remove_expr(expr, comparison);
//   }
// }

void array_syntht::normalise_quantifier_index_adjustments(expr_array_index_locst &expr_loc)
{

  if (expr_loc.array_indexes.size() == 0 && expr_loc.constant_locations.size() == 90)
    return;

  for (auto &loc : expr_loc.array_indexes)
  {
    mp_integer minimum_index = 100000; //arbitrarily large number
    debug() << "normalising the following:" << output_expr_locs(loc) << eom;
    if (loc.original_index_values.size() == 0)
      break;
    for (const auto &i : loc.original_index_values)
      if (i < minimum_index)
        minimum_index = i;

    debug() << "Minimum was " << minimum_index << eom;
    loc.index_adjustments.clear();

    for (auto &i : loc.original_index_values)
    {
      mp_integer adjustment = i - minimum_index;
      loc.index_adjustments.push_back(adjustment);
      if (adjustment > expr_loc.max_index_adjustment)
        expr_loc.max_index_adjustment = adjustment;
    }
    for (auto &const_val : expr_loc.constant_values)
    {
      mp_integer val;
      to_integer(const_val, val);
      loc.constant_adjustments.push_back(val - minimum_index);
    }
  }
}

bool array_syntht::find_array_indices(const exprt &expr,
                                      const std::size_t &depth,
                                      const std::size_t &distance_from_left,
                                      bool top_index = false,
                                      bool inside_index = false)
{
  bool result = false;
  if (top_index)
    array_index_locations.push_back(expr_array_index_locst());

  INVARIANT(array_index_locations.size() > 0, "vector must be bigger than 0");
  auto &this_expr = array_index_locations.back();

  debug() << "Looking for array index in " << expr2sygus(expr) << " " << id2string(expr.id()) << eom;
  if (expr.id() == ID_constant && !inside_index)
  {
    this_expr.constant_locations.push_back(std::pair<int, int>(depth, distance_from_left));
    this_expr.constant_values.push_back(to_constant_expr(expr));
    debug() << "Pushing back constant value " << expr.pretty() << eom;
  }
  bool found_idx = false;
  if (expr.id() == ID_index)
  {
    found_idx = true;
    //  std::cout << "FOUND ARRAY INDEX " << std::endl;
    result = true;
    if (to_index_expr(expr).index().id() == ID_constant)
    {
      irep_idt name;
      if (to_index_expr(expr).array().id() == ID_symbol)
        name = to_symbol_expr(to_index_expr(expr).array()).get_identifier();
      else
        name = "no-symbol";

      bool new_array = true;
      int this_array_idx = this_expr.array_indexes.size();
      for (unsigned int i = 0; i < this_expr.array_indexes.size(); i++)
      {
        if (name == this_expr.array_indexes[i].name)
        {
          debug() << "new array " << id2string(name) << eom;
          new_array = false;
          this_array_idx = i;
        }
      }
      if (new_array)
      {
        this_expr.array_indexes.push_back(array_index_locst());
        this_array_idx = this_expr.array_indexes.size() - 1;
      }
      auto &this_array = this_expr.array_indexes[this_array_idx];
      this_array.name = name;
      std::string id = "local_var";
      this_array.quantifier_binding = symbol_exprt(id, to_index_expr(expr).index().type());

      // find linear relation between indices
      mp_integer value = 0;
      INVARIANT(!to_integer(
                    to_constant_expr(to_index_expr(expr).index()), value),
                "unable to get index value");
      debug() << "index value: " << value << " at " << depth << ", " << distance_from_left << eom;
      this_array.original_index_values.push_back(value);

      this_array.locations.push_back(std::pair<int, int>(depth, distance_from_left));

      //if (new_array)
    }
  }

  std::size_t distance = 0;
  // no nested indices
  // if (!found_idx)
  {
    for (const auto &op : expr.operands())
    {
      if (find_array_indices(op, depth + 1, distance, false, found_idx))
        result = true;
      distance++;
    }
  }
  return result;
}

bool array_syntht::add_quantifiers_back(exprt &expr)
{
  for (auto &o : expr.operands())
    add_quantifiers_back(o);

  // clear quantifier search here
  array_index_locations.clear();

  // if this is not a conjunction or disjunction it can't be replaced with a forall/exists.
  if (expr.id() == ID_and || expr.id() == ID_or)
  {
    debug() << "Can we add a quantifier instead of: " << expr2sygus(expr, true) << eom;
    // sort_operands(expr);
    debug() << "sorted operands " << expr2sygus(expr, true) << eom;

    auto &operands = expr.operands();
    assert(operands.size() != 0);
    std::size_t found_array = 0;
    for (unsigned int i = 0; i < operands.size(); i++)
    {
      if (find_array_indices(operands[i], 0, 0, true))
        found_array++;
      normalise_quantifier_index_adjustments(array_index_locations[i]);
    }
    if (found_array <= 1)
      return false;

    // look for sets of operands which index the same number of arrays.
    // and are the same expression except for the index values
    // Add the indices for these sets to the vector
    std::vector<int> matching_indices;
    // and store the sets of indices in
    std::vector<std::vector<int>> sets_of_matching_indices;

    matching_indices.push_back(0);
    //    bool matching_constant = true;
    for (unsigned int i = 0; i < operands.size() - 1; i++)
    {
      if (array_index_locations[i].array_indexes == array_index_locations[i + 1].array_indexes &&
          compare_expr(operands[i], operands[i + 1]))
      {
        debug() << "\nMatching!" << eom;
        matching_indices.push_back(i + 1);
      }
      else
      {
        sets_of_matching_indices.push_back(matching_indices);
        matching_indices.clear();
        matching_indices.push_back(i + 1);
      }
    }
    sets_of_matching_indices.push_back(matching_indices);

    bool all_sets_size_one = true;
    for (const auto &s : sets_of_matching_indices)
    {
      if (s.size() > 1)
        all_sets_size_one = false;
      debug() << " set: ";
      for (const auto &i : s)
        debug() << i << " ";
      debug() << eom;
    }
    if (all_sets_size_one || sets_of_matching_indices.size() == 0)
    {
      debug() << "No sets of matching indices \n"
              << eom;
      return false;
    }

    // Now check which of the normalised array indices are the same for
    // each set. For each set, we first check which of the array indices in array_indexes
    // are the same, and store the indexes in the vector "which_arrays_match"

    exprt result;
    for (unsigned int i = 0; i < sets_of_matching_indices.size(); i++)
    {

      exprt result_expr;
      auto &this_matching_set = sets_of_matching_indices[i];
      debug() << "Set " << i << " size " << this_matching_set.size() << eom;
      if (this_matching_set.size() == 1)
      {
        result_expr = operands[this_matching_set[0]];
      }
      else if (this_matching_set.size() == 0)
        break;
      else
      {
        // TODO FIX THIS
        const auto &comparison_locs = array_index_locations[this_matching_set[0]];
        debug() << "comparison locs " << comparison_locs.array_indexes.size() << eom;

        std::vector<int> which_arrays_match;
        std::vector<std::vector<bool>> which_index_do_constants_match;

        // for each locs, check that all indices in this_matching_set match
        for (unsigned int j = 0; j < comparison_locs.array_indexes.size(); j++)
        {

          std::vector<bool> compare_constants_for_this_index(comparison_locs.constant_locations.size(), true);
          //     bool found_some_matching_constants = false;
          const auto &comparison_array_index = comparison_locs.array_indexes[j];
          debug() << "Checking array index " << id2string(comparison_array_index.name) << eom;
          debug() << " array adjustment" << (comparison_array_index.index_adjustments[0]) << eom;

          bool all_match = true;
          // check that, for each things in the matching set, this array index is the same
          for (unsigned int k = 1; k < this_matching_set.size(); k++)
          {
            const auto &comp_array_index2 =
                array_index_locations[this_matching_set[k]].array_indexes[j];
            debug() << "comparing with array index " << id2string(comp_array_index2.name) << eom;
            debug() << " array adjustment" << (comp_array_index2.index_adjustments[0]) << eom;

            if (!(comparison_array_index == comp_array_index2))
              all_match = false;
            else
            { // no use if the expressions are actually identical
              if (comparison_array_index.original_index_values == comp_array_index2.original_index_values)
                all_match = false;
            }
            if (all_match)
            {
              std::vector<bool> constant_comparison = constants_match(comparison_array_index, comp_array_index2);

              assert(constant_comparison.size() == compare_constants_for_this_index.size());
              for (unsigned int i = 0; i < constant_comparison.size(); i++)
              {
                debug() << "Comp: " << constant_comparison[i] << " and " << compare_constants_for_this_index[i];
                bool and_result = compare_constants_for_this_index[i] & constant_comparison[i];
                compare_constants_for_this_index[i] = and_result;
                debug() << " = " << and_result << eom;
              }
            }
            else
              break;
          }
          if (all_match)
          {
            which_arrays_match.push_back(j);
            which_index_do_constants_match.push_back(compare_constants_for_this_index);
          }
        }

        // uniformise quantifier bindings
        std::string id = "local_var" + integer2string(local_var_counter);
        auto binding = symbol_exprt(id, integer_typet());
        // array_index_locations[this_matching_set[0]].array_indexes[0].quantifier_binding.type());
        local_var_counter++;
        // now replace with quantifier
        exprt &where = operands[this_matching_set[0]];

        auto &first_expr_locs = array_index_locations[this_matching_set[0]];
        // replace array indices with local vars in the "where"
        for (unsigned int i = 0; i < which_arrays_match.size(); i++)
        {
          debug() << "CALLING replace array indices on expr " << expr2sygus(where) << eom;
          std::size_t const_index = 0;
          replace_array_indices_with_local_vars(
              where, 0, first_expr_locs.array_indexes[which_arrays_match[i]],
              true, const_index, binding, which_index_do_constants_match[i]);
        }
        if (which_arrays_match.size() > 0)
        {
          quantifier_exprt new_expr =
              (expr.id() == ID_and) ? quantifier_exprt(
                                          ID_forall, binding, where)
                                    : quantifier_exprt(ID_exists, binding, where);
          result_expr = new_expr;
        }
        else
        {
          result_expr = expr;
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
    { //TODO check is this why nested doesn't work?
      expr = result;
      debug() << "RESULT:: " << expr2sygus(expr, true) << eom;
    }
  }
  return true;
}

// return true if expressions are the same except with different
// array indices
bool array_syntht::compare_expr(const exprt &expr1, const exprt &expr2)
{
  debug() << "Comparing expr " << expr2sygus(expr1) << " and " << expr2sygus(expr2) << eom;
  const auto &operands1 = expr1.operands();
  const auto &operands2 = expr2.operands();
  if (expr1 == expr2)
  {
    debug() << "Definitely matching \n";
    return true;
  }
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
  if (expr1.id() == ID_symbol)
  {
    if (declared_variables.find(
            clean_id(to_symbol_expr(expr1).get_identifier())) !=
        declared_variables.end())
      if (declared_variables.find(
              clean_id(to_symbol_expr(expr2).get_identifier())) !=
          declared_variables.end())
        return true;
  }

  for (unsigned int i = 0; i < operands1.size(); i++)
  {
    if (!compare_expr(operands1[i], operands2[i]))
      return false;
  }
  return true;
}

void array_syntht::replace_array_indices_with_local_vars(
    exprt &expr, const std::size_t vector_idx, const array_index_locst &locs,
    bool replace_constants, std::size_t &constant_vector_idx, const symbol_exprt &quantifier_binding,
    const std::vector<bool> &replace_these_constants)
{
  std::size_t next_vector_idx = vector_idx;
  debug() << "replace array indices in " << expr2sygus(expr, true) << " with "
          << expr2sygus(quantifier_binding, true) << ", vector idx " << vector_idx << "and constant idx " << constant_vector_idx << eom;
  debug() << "Using locs" << output_expr_locs(locs) << eom;

  bool replace = false;
  if (expr.id() == ID_index && locs.name != "")
  {
    if (to_index_expr(expr).array().id() == ID_symbol)
    {
      if (to_symbol_expr(to_index_expr(expr).array()).get_identifier() == locs.name)
        replace = true;
    }
    else if (locs.name == "no-name")
      replace = true;

    if (replace)
    {
      assert(vector_idx < locs.locations.size());
      if (locs.index_adjustments[vector_idx] == 0)
      {
        index_exprt new_expr(to_index_expr(expr).array(), quantifier_binding);
        expr = new_expr;
      }
      else
      {
        exprt adjusted_index = binary_exprt(quantifier_binding, ID_plus,
                                            from_integer(locs.index_adjustments[vector_idx],
                                                         quantifier_binding.type()));
        index_exprt new_expr(to_index_expr(expr).array(), adjusted_index);
        expr = new_expr;
      }
      debug() << "Result: " << expr2sygus(expr, true) << eom;
      next_vector_idx++;
    }
  }
  if (expr.id() == ID_constant &&
      replace_constants && constant_vector_idx < locs.constant_adjustments.size())
  {
    if (replace_these_constants[constant_vector_idx])
    {
      debug() << "Attempting to replace constant in expression " << expr2sygus(expr)
              << ", constant index adjustment = "
              << locs.constant_adjustments[constant_vector_idx] << eom;
      exprt new_expr = binary_exprt(quantifier_binding, ID_plus,
                                    from_integer(locs.constant_adjustments[constant_vector_idx],
                                                 quantifier_binding.type()));
      expr = new_expr;
      debug() << "Result " << expr2sygus(expr) << eom;
    }
    constant_vector_idx++;
  }

  for (auto &op : expr.operands())
  {
    replace_array_indices_with_local_vars(
        op, next_vector_idx, locs, replace_constants, constant_vector_idx, quantifier_binding, replace_these_constants);
  }
}

bool array_syntht::unbound_arrays_in_solution(solutiont &solution)
{
  for (auto &e : solution.functions)
  {
    expand_let_expressions(e.second);
    sort_operands(e.second);
    debug() << "after expanding let:\n"
            << expr2sygus(e.second, true) << eom;
  }

  bool added_quantifiers = false;
  for (auto &e : solution.functions)
    if (add_quantifiers_back(e.second))
      added_quantifiers = true;

  for (auto &e : solution.functions)
    debug() << "after adding quant back; " << expr2sygus(e.second, true) << eom;

  return added_quantifiers;
}