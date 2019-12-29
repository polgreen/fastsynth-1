
#include "bitvector2integer.h"
#include <util/arith_tools.h>

// TODO: check how we get value from constant or symbol bitvector
void bitvec2integert::convert(exprt &expr)
{
  for (auto &op : expr.operands())
    convert(op);

  if (expr.id() == ID_constant)
  {
    if (expr.type().id() == ID_unsignedbv)
    {
      mp_integer mpint;
      to_integer(to_constant_expr(expr), mpint);
      expr = constant_exprt(integer2string(mpint), integer_typet());
    }
  }
  else if (expr.id() == ID_symbol)
  {
    if (expr.type().id() == ID_unsignedbv)
    {
      expr = symbol_exprt(to_symbol_expr(expr).get_identifier(), integer_typet());
    }
  }
  else if (expr.id() == ID_infinity)
  {
    if (expr.type().id() == ID_unsignedbv)
      expr = infinity_exprt(integer_typet());
  }
}

void bitvec2integert::convert(typet &type)
{
  for (auto &t : type.get_sub())
  {
    const typet st = static_cast<const typet &>(t);
    if (st == get_nil_irep())
      break;
    else
      convert(type.subtype());
  }
  if (type.id() == ID_unsignedbv)
    type = integer_typet();
  else if (type.id() == ID_array)
  {
    exprt new_size = to_array_type(type).size();
    convert(new_size);
    // std::cout << "ARRAY SIZE " << new_size.pretty() << std::endl;
    type = array_typet(to_array_type(type).subtype(), new_size);
  }
  else if (type.id() == ID_mathematical_function)
  {
    for (auto &d : to_mathematical_function_type(type).domain())
      convert(d);
    convert(to_mathematical_function_type(type).codomain());
  }
}

// void bitvec2integert::convert_back(exprt &expr, std::size_t bv_size)
// {
// }

// void bitvec2integert::convert_back(typet &type, std::size_t bv_size)
// {
// }