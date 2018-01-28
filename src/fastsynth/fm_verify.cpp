#include "fm_verify.h"

#include "fourier_motzkin.h"

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>

#include <langapi/language_util.h>

#include <util/replace_symbol.h>
#include <util/simplify_expr.h>

void get_symbols(const exprt &src, std::set<symbol_exprt> &dest)
{
  if(src.id()==ID_symbol)
    dest.insert(to_symbol_expr(src));
  else
    for(const auto &op : src.operands())
      get_symbols(op, dest);
}

std::set<symbol_exprt> get_symbols(const exprt &src)
{
  std::set<symbol_exprt> result;
  get_symbols(src, result);
  return result;
}

decision_proceduret::resultt fm_verifyt::operator()(
  solutiont &solution)
{
  output(solution.functions, debug());
  debug() << eom;

  satcheckt verify_satcheck;
  verify_satcheck.set_message_handler(get_message_handler());

  bv_pointerst verify_solver(ns, verify_satcheck);
  verify_solver.set_message_handler(get_message_handler());

  verify_encodingt verify_encoding;
  verify_encoding.functions=solution.functions;
  verify_encoding.free_variables=problem.free_variables;

  add_problem(verify_encoding, verify_solver);

  auto result=verify_solver();

  if(result==decision_proceduret::resultt::D_SATISFIABLE)
  {
    counterexample=
      verify_encoding.get_counterexample(verify_solver);

    // we might be able to generalize
    for(auto &f_it : solution.s_functions)
      f_it.second=simplify_expr(f_it.second, ns);

    satcheck_no_simplifiert fm_satcheck;
    fourier_motzkint fm_solver(ns, fm_satcheck);
    fm_solver.set_message_handler(get_message_handler());
    fm_solver.existential_variables=problem.free_variables;

    verify_encodingt fm_encoding;
    fm_encoding.functions=solution.s_functions;
    fm_encoding.free_variables=problem.free_variables;

    add_problem(fm_encoding, fm_solver);

    fm_solver();

    exprt r=fm_solver.get_result();
    status() << "FM RESULT: " << from_expr(ns, "", r) << eom;
    
    // solve this a bit further
    satcheckt r_satcheck;
    bv_pointerst r_solver(ns, r_satcheck);
    r_solver.set_message_handler(get_message_handler());
    r_solver.set_to_false(r);

    if(r_solver()==decision_proceduret::resultt::D_UNSATISFIABLE)
      return decision_proceduret::resultt::D_SATISFIABLE; // nope, give up

    // build new solution, try again
    std::set<symbol_exprt> symbols=get_symbols(r);

    replace_symbolt replace_symbol;

    for(const auto &s : symbols)
      replace_symbol.insert(s, r_solver.get(s));

    for(const auto &f_it : solution.s_functions)
    {
      exprt tmp=f_it.second;
      replace_symbol(tmp);
      tmp=simplify_expr(tmp, ns);
      solution.functions[f_it.first]=tmp;
    }

    satcheckt verify_satcheck2;
    verify_satcheck2.set_message_handler(get_message_handler());

    bv_pointerst verify_solver2(ns, verify_satcheck2);
    verify_solver2.set_message_handler(get_message_handler());

    verify_encodingt verify_encoding2;
    verify_encoding2.functions=solution.functions;
    verify_encoding2.free_variables=problem.free_variables;

    add_problem(verify_encoding2, verify_solver2);

    auto result=verify_solver2();

    return result;
  }
  else
  {
    counterexample.clear();
    return result;
  }
}