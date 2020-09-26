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

void array_syntht::bound_arrays(problemt &problem)
{
  INVARIANT(indices.size() > 0, "size of array is 0");
  for (auto &c : problem.constraints)
    replace_quantifier_with_conjunction(c, indices);
}

void array_syntht::bound_arrays(problemt &problem, std::size_t bound)
{
  indices.clear();
  for (std::size_t i = 0; i < bound; i++)
    indices.push_back(i);

  for (auto &c : problem.constraints)
    replace_quantifier_with_conjunction(c, indices);
}