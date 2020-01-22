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



bool array_syntht::bound_arrays(exprt &expr, std::size_t bound)
{
  symbols_to_bound.clear();
   status() << "clear symbols "<< symbols_to_bound.size()<<eom;

  if(!bound_array_exprs(expr, bound))
    return false;

  // status() << "number of symbols to bound: "<< symbols_to_bound.size()<<eom;
  // if (symbols_to_bound.size() > 0)
  // { 
  //   status()<<"Bounding symbols \n"<<eom;    
  //   std::set<exprt>::iterator symbol_it = symbols_to_bound.begin();

  //   // add a constraint that the property only holds if these variables have values less than the array size
  //   // build implication which says that the property holds only if the local variables are within array bounds
  //   exprt var_is_less_than_bound = binary_predicate_exprt(
  //         *symbol_it, ID_lt, from_integer(max_array_index, symbol_it->type()));
  //   added_implications.push_back(var_is_less_than_bound);

  //   symbol_it++;
  //   while (symbol_it != symbols_to_bound.end())
  //   {
  //     exprt next_var_is_less_than_bound = binary_predicate_exprt(
  //           *symbol_it, ID_lt, from_integer(max_array_index, symbol_it->type()));
  //     added_implications.push_back(next_var_is_less_than_bound);
  //     var_is_less_than_bound = and_exprt(var_is_less_than_bound, next_var_is_less_than_bound);
  //     symbol_it++;
  //   }

  //   implies_exprt implication(var_is_less_than_bound, expr);
  //   expr = implication;
  // }

  // status() <<"Added implications: \n";
  // for (const auto &e : added_implications)
  //   status() << expr2sygus(e, false) << " " << eom;

return true;
}

void array_syntht::unbound_arrays_in_solution(solutiont &solution)
{
  for (auto &e : solution.functions)
    expand_let_expressions(e.second);

  for (auto &e : solution.functions)
    add_quantifiers_back(e.second);

  for (auto &e : solution.functions)
    remove_added_implication(e.second);
}


void array_syntht::contains_variable(const exprt &expr, bool &contains_var, bool &contains_local_var)
{
  if(contains_var && contains_local_var)
    return;
  //TODO: handle nondet symbol
  for(const auto &op: expr.operands())
    contains_variable(op, contains_var, contains_local_var);

  if(expr.id()==ID_symbol)
  {
    if(declared_variables.find(
        clean_id(to_symbol_expr(expr).get_identifier()))!=declared_variables.end())
      contains_var=true;
    else
      contains_local_var=true;
  }
}


void array_syntht::bound_expression(const exprt & index_expr)
{
  bool contains_var=false;
  bool contains_local_var=false;
  contains_variable(index_expr,contains_var,contains_local_var);

  status()<<expr2sygus(index_expr, false)<<" var: "<< contains_var <<" local var: "<< contains_local_var <<eom;

  if(contains_var && !contains_local_var)
    symbols_to_bound.insert(index_expr);

}


void array_syntht::add_implication(exprt &expr)
{
  if (symbols_to_bound.size() > 0)
  {    
    std::set<exprt>::iterator symbol_it = symbols_to_bound.begin();

    // add a constraint that the property only holds if these variables have values less than the array size
    // build implication which says that the property holds only if the local variables are within array bounds
    exprt var_is_less_than_bound = binary_predicate_exprt(
          *symbol_it, ID_lt, from_integer(max_array_index, symbol_it->type()));
    added_implications.insert(var_is_less_than_bound);

    symbol_it++;
    while (symbol_it != symbols_to_bound.end())
    {
      exprt next_var_is_less_than_bound = binary_predicate_exprt(
            *symbol_it, ID_lt, from_integer(max_array_index, symbol_it->type()));
      added_implications.insert(next_var_is_less_than_bound);
      var_is_less_than_bound = and_exprt(var_is_less_than_bound, next_var_is_less_than_bound);
      symbol_it++;
    }
    implies_exprt implication(var_is_less_than_bound, expr);
    expr = implication;
  }
}

// returns list of variables that index arrays
bool array_syntht::bound_array_exprs(exprt &expr, std::size_t bound)
{
  if(expr.id()==ID_forall || expr.id()==ID_exists)
    symbols_to_bound.clear();

  for (auto &op : expr.operands())
    if(!bound_array_exprs(op, bound))
      return false;

   if((expr.id()==ID_forall || expr.id()==ID_exists) 
   && symbols_to_bound.size()>0)
      add_implication(to_quantifier_expr(expr).where());

  if (expr.id() == ID_index || expr.id() == ID_with)
  {
    // bound index
    exprt index = (expr.id() == ID_index) ? to_index_expr(expr).index() : to_with_expr(expr).where();
    if (index.id() == ID_symbol || index.id() == ID_nondet_symbol)
    {
      if(declared_variables.find(
        clean_id(to_symbol_expr(index).get_identifier()))!=declared_variables.end())
      {
        symbols_to_bound.insert(index);
      }
    }
    else if (index.id() == ID_constant)
    {
      mp_integer value;
      to_integer(to_constant_expr(index), value);
      if (value > max_array_index)
      {
        status() <<"constant expr takes value greater than max array index\n"
        << index.pretty()<<eom;
        return false;
      }
    }
    else
    {
      status()<<"Inserting an expr into the symbol to bound set:" << expr2sygus(index, false) <<"\n";
      symbols_to_bound.insert(index);
      // maybe handle these differently?
      //bound_expression(index);
    }
  }
  return true;
}
