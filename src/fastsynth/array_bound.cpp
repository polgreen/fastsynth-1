#include "verify.h"
#include "array_synth.h"
#include <util/namespace.h>
#include <util/arith_tools.h>
#include <util/symbol_table.h>
#include <util/string2int.h>
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
// a conjunction over the indices in the vector
void replace_quantifier_with_conjunction(exprt &expr, const std::vector<mp_integer> &indices)
{
  for (auto &op : expr.operands())
    replace_quantifier_with_conjunction(op, indices);

  if (expr.id() == ID_forall || expr.id() == ID_exists)
  {
    const quantifier_exprt &quant = to_quantifier_expr(expr);
    std::size_t conjunction_size = indices.size();
    if (quant.variables().size() == 1)
    {
      auto &var = to_symbol_expr(quant.variables()[0]);

      if (var.type().id() == ID_unsignedbv)
      {
        const auto bv_options =
            std::pow(2, to_unsignedbv_type(var.type()).get_width());
        if (bv_options < conjunction_size)
          conjunction_size = bv_options;
      }

      irep_idt var_id = var.get_identifier();
      exprt result = (expr.id() == ID_forall) ? exprt(ID_and, quant.type()) : exprt(ID_or, quant.type());
      exprt local_where = quant.where();

      for (unsigned int i = 0; i < conjunction_size; i++)
      {
        replace_variable_with_constant(local_where, var_id, from_integer(indices[i], var.type()));
        result.operands().push_back(local_where);
        local_where = quant.where();
      }
      expr = result;
    }
  }
}

void array_syntht::find_array_index_symbols(const exprt &expr, std::set<exprt> &result)
{

  for (auto &op : expr.operands())
    find_array_index_symbols(op, result);

  if (expr.id() == ID_index || expr.id() == ID_with)
  {
    exprt index = (expr.id() == ID_index) ? to_index_expr(expr).index() : to_with_expr(expr).where();
    if (index.id() == ID_symbol || index.id() == ID_nondet_symbol)
    {
      result.insert(index);
    }
  }
  // debug() << "Array index symbols: ";
  // for (const auto &r : result)
  //   debug() << expr2sygus(r) << " ";
  // debug() << eom;
}

// find variables that are compared to array indices and bound them (unless they are primed)
void array_syntht::find_vars_to_bound(const exprt &expr, std::set<exprt> &result)
{
  for (const auto &op : expr.operands())
    find_vars_to_bound(op, result);

  if (expr.id() == ID_lt || expr.id() == ID_le ||
      expr.id() == ID_gt || expr.id() == ID_equal || expr.id() == ID_ge)
  {
    if (result.find(expr.op0()) != result.end() && expr.op1().id() == ID_symbol)
    {
      if (clean_id(to_symbol_expr(expr.op1()).get_identifier()).find("!") == std::string::npos)
      {
        debug() << "bounding symbol " << expr.op1().pretty() << eom;
        symbols_to_bound.insert(expr.op1());
      }
    }
    else if (result.find(expr.op1()) != result.end() && expr.op0().id() == ID_symbol)
    {
      if (clean_id(to_symbol_expr(expr.op0()).get_identifier()).find("!") == std::string::npos)
      {
        debug() << "bounding symbol " << expr.op0().pretty() << eom;
        symbols_to_bound.insert(expr.op0());
      }
    }
  }
  for (const auto &r : result)
    if (declared_variables.find(to_symbol_expr(r).get_identifier()) != declared_variables.end())
      symbols_to_bound.insert(r);
}

void array_syntht::bound_array_indices(exprt &expr, std::size_t bound)
{
  if (symbols_to_bound.size() == 0)
    return;
  std::set<exprt>::iterator symbol_it = symbols_to_bound.begin();
  exprt result;
  bool first = true;
  bool added_symbols = false;
  while (symbol_it != symbols_to_bound.end())
  {
    if (declared_variables.find(
            clean_id(to_symbol_expr(*symbol_it).get_identifier())) != declared_variables.end())
    {
      added_symbols = true;
      exprt less_than_bound = binary_predicate_exprt(
          *symbol_it, ID_lt, from_integer(bound, integer_typet()));
      exprt greater_than_zero = binary_predicate_exprt(
          *symbol_it, ID_ge, from_integer(0, integer_typet()));
      if (first)
      {
        result = and_exprt(less_than_bound, greater_than_zero);
        first = false;
      }
      else
      {
        result = and_exprt(less_than_bound, greater_than_zero, result);
      }
    }
    symbol_it++;
  }
  if (added_symbols)
  {
    debug() << "constraint expression " << expr2sygus(result) << eom;
    implies_exprt implication(result, expr);
    expr = implication;
  }
}

void array_syntht::bound_arrays(problemt &problem)
{
  INVARIANT(indices.size() > 0, "size of array is 0");

  std::set<exprt> result;
  for (auto &c : problem.constraints)
    find_array_index_symbols(c, result);

  for (const auto &c : problem.constraints)
    find_vars_to_bound(c, result);

  for (auto &c : problem.constraints)
  {
    replace_quantifier_with_conjunction(c, indices);
    bound_array_indices(c, indices.size());
  }
}

void array_syntht::bound_arrays(problemt &problem, std::size_t bound)
{
  indices.clear();

  for (std::size_t i = 0; i < bound; i++)
    indices.push_back(i);

  bound_arrays(problem);
}