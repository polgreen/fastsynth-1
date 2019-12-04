/*
 * array_cegis.cpp
 *
 *  Created on: 2 Dec 2019
 *      Author: elipol
 */
#include "array_cegis.h"
#include "verify.h"
#include <util/namespace.h>

#include <string>

#include <util/std_types.h>
#include <util/std_expr.h>
#include <langapi/language_util.h>
#include <goto-programs/show_symbol_table.h>

#include <iostream>

#define ARRAY_SIZE_MAX 20u


void bound_array_symbols(exprt &expr, std::size_t length)
{
  PRECONDITION(expr.id()==ID_symbol || expr.id()==ID_nondet_symbol);
  for(exprt &op : expr.operands())
    bound_array_symbols(op, length);

  typet type=expr.type();

  if(type.id()==ID_array)
  {
    array_typet array=to_array_type(type);

    irep_idt id=(expr.id()==ID_symbol)? to_symbol_expr(expr).get_identifier()
        : to_nondet_symbol_expr(expr).get_identifier();

    array_typet new_array(
        array.subtype(), constant_exprt(
            std::to_string(length), array.size().type()));

    if(expr.id()==ID_symbol)
    {
      symbol_exprt replacement_array_symbol(id, new_array);
      expr=replacement_array_symbol;
    }
    else
    {
      nondet_symbol_exprt replacement_array_symbol(id, new_array);
      expr=replacement_array_symbol;
    }
  }
}


void bound_array_exprs(exprt &expr, std::size_t length)
{
  for(exprt &op : expr.operands())
    bound_array_exprs(op, length);

  if(expr.id()==ID_index)
  {
    array_typet array=to_array_type(to_index_expr(expr).array().type());

    irep_idt id=to_symbol_expr(to_index_expr(expr).array()).get_identifier();
    array_typet new_array(
        array.subtype(), constant_exprt(
            std::to_string(length), array.size().type()));
    symbol_exprt replacement_array_symbol(id, new_array);

    // change size of expr

    expr=index_exprt(replacement_array_symbol, to_index_expr(expr).index());
  }
  else if(expr.id()==ID_array)
  {
    array_typet array_type=to_array_expr(expr).type();
    array_typet new_array(
            array_type.subtype(), constant_exprt(
                std::to_string(length), array_type.size().type()));

    expr=array_exprt(to_array_expr(expr).operands(), new_array);
  }
  else if(expr.id()==ID_symbol)
  {
    bound_array_symbols(expr, length);
  }
}



void unbound_array_symbols(exprt &expr)
{
  PRECONDITION(expr.id()==ID_symbol || expr.id()==ID_nondet_symbol);
  for(exprt &op : expr.operands())
    unbound_array_symbols(op);

  typet type=expr.type();

  if(type.id()==ID_array)
  {
    array_typet array=to_array_type(type);

    irep_idt id=(expr.id()==ID_symbol)? to_symbol_expr(expr).get_identifier()
        : to_nondet_symbol_expr(expr).get_identifier();

    array_typet new_array(
        array.subtype(), infinity_exprt(array.size().type()));

    if(expr.id()==ID_symbol)
    {
      symbol_exprt replacement_array_symbol(id, new_array);
      expr=replacement_array_symbol;
    }
    else
    {
      nondet_symbol_exprt replacement_array_symbol(id, new_array);
      expr=replacement_array_symbol;
    }
  }
}



void unbound_array_exprs(exprt &expr)
{
  for(exprt &op : expr.operands())
    unbound_array_exprs(op);

  if(expr.id()==ID_index)
  {
    array_typet array=to_array_type(to_index_expr(expr).array().type());

    irep_idt id=to_symbol_expr(to_index_expr(expr).array()).get_identifier();
    array_typet new_array(
        array.subtype(), infinity_exprt(array.size().type()));
    symbol_exprt replacement_array_symbol(id, new_array);
    // change size of expr

    expr=index_exprt(replacement_array_symbol, to_index_expr(expr).index());
  }
  else if(expr.id()==ID_array)
  {
    array_typet array_type=to_array_expr(expr).type();
    array_typet new_array(
            array_type.subtype(),
            infinity_exprt(to_array_expr(expr).type().size().type()));

    expr=array_exprt(to_array_expr(expr).operands(), new_array);
  }
  else if(expr.id()==ID_symbol)
  {
    unbound_array_symbols(expr);
  }
}

void clear_cegis(cegist &cegis)
{
  cegis.solution.functions.clear();
  cegis.solution.s_functions.clear();
}


int run_array_cegis(problemt &problem, cegist &cegis)
{
 /* symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  cegist bounded_cegis(ns);*/
  // create verification instance from original problem:
  verifyt full_array_verify(
      cegis.ns,
      problem,
      cegis.get_message_handler());
  full_array_verify.use_smt=true;

  std::size_t array_size=4;

  while(array_size < ARRAY_SIZE_MAX)
  {
    cegis.array_size=array_size;

  // bound array length
  for(auto &c : problem.constraints)
    bound_array_exprs(c, array_size);
  for(auto &s : problem.side_conditions)
    bound_array_exprs(s, array_size);

  // bound free variables
  for(auto it=problem.free_variables.begin();
      it!= problem.free_variables.end();)
  {
    exprt copy=*it;
    bound_array_exprs(copy, array_size);
    if(copy!=*it)
    {
      problem.free_variables.erase(it++);
      problem.free_variables.insert(copy);
    }
    else
      it++;
  }

  clear_cegis(cegis);

  // synthesise candidate for fixed array length
  switch(cegis(problem))
    {
    case decision_proceduret::resultt::D_UNSATISFIABLE:
    case decision_proceduret::resultt::D_ERROR:
      std::cout<<"no solution at this array length \n ";
      array_size++;
      break;

      // verify for full length
    case decision_proceduret::resultt::D_SATISFIABLE:
      // convert expression to full length:
      for(auto &soln : cegis.solution.functions)
        unbound_array_exprs(soln.second);

      // verify for full length
      std::cout<<"Full array verify \n";
      switch(full_array_verify(cegis.solution))
      {
        case decision_proceduret::resultt::D_SATISFIABLE: // counterexample
          array_size++;
          std::cout<<"increasing array size \n";
          break;
        case decision_proceduret::resultt::D_UNSATISFIABLE:  // done, got
                                                             // solution
          std::cout << "Result obtained with array length " << array_size
                    << "\n";
          return 0;
        case decision_proceduret::resultt::D_ERROR:
          return 1;
      }
    }
  }
 return 1;
}







