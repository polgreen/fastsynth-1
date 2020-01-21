#include "array_synth.h"
#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/mathematical_types.h>
#include <util/arith_tools.h>

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

void array_syntht::expand_let_expressions(exprt &expr)
{
  if (expr.id() == ID_let)
  {
    auto &let_expr = to_let_expr(expr);
    for (int i = 0; i < let_expr.variables().size(); i++)
    {
      INVARIANT(let_expr.variables()[i].id() == ID_symbol, "Let expression should have list of symbols");
      replace_local_var(let_expr.where(), to_symbol_expr(let_expr.variables()[i]).get_identifier(), let_expr.values()[i]);
    }
    expr = let_expr.where();
    expand_let_expressions(expr);
  }
  for (auto &op : expr.operands())
    expand_let_expressions(op);
}

bool array_syntht::bound_bitvectors(exprt &expr, const std::size_t &bound)
{
  if (expr.type().id() != ID_unsignedbv)
    return false;
  if (expr.id() == ID_symbol)
  {
    std::size_t width = to_unsignedbv_type(expr.type()).get_width();
    if (width > bound)
    {
      auto upper_e = from_integer(bound - 1, integer_typet());
      auto lower_e = from_integer(0, integer_typet());
      extractbits_exprt extract = extractbits_exprt(expr, upper_e, lower_e, unsignedbv_typet(bound));
      expr = extract;
    }
    else if (width < bound)
    {
      concatenation_exprt concat = concatenation_exprt(constant_exprt("0", unsignedbv_typet(bound - width)), expr, unsignedbv_typet(bound));
      expr = concat;
    }
    expr.type() = unsignedbv_typet(bound);
  }
  else if (expr.id() == ID_concatenation)
  {
    expr = to_concatenation_expr(expr).op1();
    bound_bitvectors(expr, bound);
  }
  else if (expr.id() == ID_extractbits)
  {
    expr = to_extractbits_expr(expr).src();
    bound_bitvectors(expr, bound);
  }
  else if (expr.id() == ID_constant)
  {
    mp_integer value;
    to_integer(to_constant_expr(expr), value);
    if (value <= max_array_index)
      expr = from_integer(value, unsignedbv_typet(bound));
    else
      return false;
  }
  else
  {
    if (expr.type().id() == ID_unsignedbv)
      expr.type() = unsignedbv_typet(bound);

    for (auto &op : expr.operands())
      bound_bitvectors(op, bound);
  }

  return true;
}

// replace array index type with an index type of bitvector width bound
void array_syntht::bound_array_types(typet &type, std::size_t &bound)
{
  if (type.id() == ID_array)
  {
    array_typet array = to_array_type(type);
    exprt new_size;
    if (array.size().id() == ID_constant)
    {
      std::cout << "were we expecting this??\n"
                << type.pretty() << std::endl;
      assert(0);
    }
    else
    {
      if (array.size().type().id() == ID_unsignedbv)
      {
        // const auto &bv = to_unsignedbv_type(array.size().type());

        // if (bv.get_width() > bound)
        {
          new_size = infinity_exprt(unsignedbv_typet(bound));
          bound_array_types(to_array_type(type).subtype(), bound);
          type = array_typet(to_array_type(type).subtype(), new_size);
        }
      }
      else if (array.size().type().id() == ID_infinity)
      {
        new_size = infinity_exprt(unsignedbv_typet(bound));
        bound_array_types(to_array_type(type).subtype(), bound);
        type = array_typet(to_array_type(type).subtype(), new_size);
      }
    }
  }
  else if (type.id() == ID_mathematical_function)
  {
    mathematical_function_typet math_fun = to_mathematical_function_type(type);
    bound_array_types(math_fun.codomain(), bound);
    for (auto &arg : math_fun.domain())
      bound_array_types(arg, bound);
    type = math_fun;
  }
}

// returns list of variables that index arrays
void array_syntht::bound_array_exprs(exprt &expr, std::size_t bound)
{

  for (auto &op : expr.operands())
    bound_array_exprs(op, bound);

  if (expr.id() == ID_array)
  {
    array_typet &array_type = to_array_expr(expr).type();
    bound_array_types(array_type, bound);
    expr = array_exprt(to_array_expr(expr).operands(), array_type);
  }
  else if (expr.id() == ID_symbol)
  {
    if (expr.type().id() == ID_array)
    {
      array_typet &array_type = to_array_type(expr.type());
      bound_array_types(array_type, bound);
      expr = symbol_exprt(to_symbol_expr(expr).get_identifier(), array_type);
    }
  }
  else if (expr.id() == ID_nondet_symbol)
  {
    if (expr.type().id() == ID_array)
    {
      array_typet &array_type = to_array_type(expr.type());
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
    bound_array_exprs(index, bound);

    if (index.id() == ID_concatenation)
    {
      //bound_array_exprs(to_concatenation_expr(index).op1(), bound);
      index = to_concatenation_expr(index).op1();
      if (index.id() == ID_symbol)
        symbols_to_bound.insert(to_symbol_expr(index));

      bound_array_exprs(index, bound);
    }
    else if (index.id() == ID_extractbits)
    {
      index = to_extractbits_expr(index).src();
      if (index.id() == ID_symbol)
        symbols_to_bound.insert(to_symbol_expr(index));

      bound_array_exprs(index, bound);
    }
    else if (index.type().id() == ID_unsignedbv)
    {
      if (index.id() == ID_symbol)
        symbols_to_bound.insert(to_symbol_expr(index));
      bound_bitvectors(index, bound);
    }
    else
    {
      std::cout << "Unsupported array index type " << index.pretty() << std::endl;
      assert(0);
    }
    bound_array_exprs(to_index_expr(expr).array(), bound);
    expr = index_exprt(to_index_expr(expr).array(), index);
  }
  else if (expr.id() == ID_with)
  {
    exprt index = to_with_expr(expr).where();

    if (index.id() == ID_constant && index.type().id() == ID_unsignedbv)
    {
      index = constant_exprt(to_constant_expr(index).get_value(), unsignedbv_typet(bound));
    }
    else if (index.id() == ID_symbol)
    {
      symbols_to_bound.insert(to_symbol_expr(index));
      bound_bitvectors(index, bound);
    }
    else if (index.id() == ID_concatenation)
    {
      index = to_concatenation_expr(index).op1();
      if (index.id() == ID_symbol)
        symbols_to_bound.insert(to_symbol_expr(index));

      bound_array_exprs(index, bound);
    }
    else if (index.id() == ID_extractbits)
    {
      index = to_extractbits_expr(index).src();
      if (index.id() == ID_symbol)
        symbols_to_bound.insert(to_symbol_expr(index));

      bound_array_exprs(index, bound);
    }
    else
    {
      std::cout << "Unsupported array index type " << id2string(index.id()) << std::endl;
      bound_array_exprs(index, bound);
      if (index.type().id() == ID_unsignedbv)
      {
        bound_bitvectors(index, bound);
      }
      //assert(0);
    }
    expr = with_exprt(to_with_expr(expr).old(), index, to_with_expr(expr).new_value());
  }
}
