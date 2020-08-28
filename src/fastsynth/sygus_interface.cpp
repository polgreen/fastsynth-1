#include "sygus_interface.h"
#include <util/expr.h>
#include <iostream>
#include <util/tempfile.h>
#include <util/run.h>
#include <fstream>

// TODO: add operators for non-bitvectors
std::string type2sygus(const typet &type)
{
  std::string result;
  if (type.id() == ID_unsignedbv)
  {
    result += "(_ BitVec " + integer2string(to_unsignedbv_type(type).get_width()) + ")";
  }
  else if (type.id() == ID_integer)
  {
    result += "Int";
  }
  else if (type.id() == ID_bool)
  {
    result += "Bool";
  }
  else if (type.id() == ID_array)
  {
    array_typet array = to_array_type(type);
    result += "(Array " + type2sygus(array.size().type()) + " " + type2sygus(array.subtype()) + ")";
  }
  else
  {
    std::cout << "Unhandled type " << type.pretty() << std::endl;
    assert(0);
  }
  return result;
}

std::string clean_id(const irep_idt &id)
{
  std::string dest = id2string(id);
  std::string::size_type c_pos = dest.find("#");
  if (c_pos != std::string::npos &&
      dest.rfind("#") == c_pos)
    dest.erase(c_pos, std::string::npos);

  std::string::size_type c_pos2 = dest.find("synth_fun::");
  if (c_pos2 != std::string::npos &&
      dest.rfind("synth_fun::") == c_pos2)
    dest.erase(0, c_pos2 + 11);

  return dest;
}

void clean_symbols(exprt &expr)
{
  for (auto &op : expr.operands())
    clean_symbols(op);

  if (expr.id() == ID_symbol)
  {
    std::string new_id = clean_id(to_symbol_expr(expr).get_identifier());
    std::string::size_type c_pos = new_id.find("parameter");

    if (c_pos != std::string::npos &&
        new_id.rfind("parameter") == c_pos)
      new_id = "synth::" + new_id;
    {
      to_symbol_expr(expr).set_identifier(new_id);
      return;
    }
  }
}

std::string expr2sygus(const exprt &expr)
{
  return expr2sygus(expr, false);
}

std::string expr2sygus(const exprt &expr, bool use_integers)
{
  std::string result = /*id2string(expr.id()) + */ "(";

  if (expr.id() == ID_equal)
    result += "= " + expr2sygus(expr.op0(), use_integers) + " " +
              expr2sygus(expr.op1(), use_integers);
  else if (expr.id() == ID_le)
  {
    if (to_binary_relation_expr(expr).op0().id() == ID_typecast)
      result += (use_integers ? "<= " : "bvsle ") + expr2sygus(expr.op0(), use_integers) + " " +
                expr2sygus(expr.op1(), use_integers);
    else
      result += (use_integers ? "<= " : "bvule ") + expr2sygus(expr.op0(), use_integers) + " " +
                expr2sygus(expr.op1(), use_integers);
  }
  else if (expr.id() == ID_ge)
  {
    if (to_binary_relation_expr(expr).op0().id() == ID_typecast)
      result += (use_integers ? ">= " : "bvsge ") + expr2sygus(expr.op0(), use_integers) + " " +
                expr2sygus(expr.op1(), use_integers);
    else
      result += (use_integers ? ">= " : "bvuge ") + expr2sygus(expr.op0(), use_integers) + " " +
                expr2sygus(expr.op1(), use_integers);
  }
  else if (expr.id() == ID_lt)
  {
    if (to_binary_relation_expr(expr).op0().id() == ID_typecast)
      result += (use_integers ? "< " : "bvslt ") + expr2sygus(expr.op0(), use_integers) + " " +
                expr2sygus(expr.op1(), use_integers);
    else
      result += (use_integers ? "< " : "bvult ") + expr2sygus(expr.op0(), use_integers) + " " +
                expr2sygus(expr.op1(), use_integers);
  }
  else if (expr.id() == ID_gt)
  {
    if (to_binary_relation_expr(expr).op0().id() == ID_typecast)
      result += (use_integers ? "> " : "bvsgt ") + expr2sygus(expr.op0(), use_integers) + " " +
                expr2sygus(expr.op1(), use_integers);
    else
      result += (use_integers ? "> " : "bvugt ") + expr2sygus(expr.op0(), use_integers) + " " +
                expr2sygus(expr.op1(), use_integers);
  }
  else if (expr.id() == ID_and)
  {
    result += "and ";
    for (const auto &op : expr.operands())
      result += expr2sygus(op, use_integers) + " ";
  }
  else if (expr.id() == ID_or)
  {
    result += "or ";
    for (const auto &op : expr.operands())
      result += expr2sygus(op, use_integers) + " ";
  }
  else if (expr.id() == ID_xor)
    result += "xor " + expr2sygus(expr.op0(), use_integers) + " " +
              expr2sygus(expr.op1(), use_integers);
  else if (expr.id() == ID_not)
    result += "not " + expr2sygus(expr.op0(), use_integers);

  else if (expr.id() == ID_bitand)
    result += "bvand " + expr2sygus(expr.op0(), use_integers) + " " +
              expr2sygus(expr.op1(), use_integers);
  else if (expr.id() == ID_bitor)
    result += "bvor " + expr2sygus(expr.op0(), use_integers) + " " +
              expr2sygus(expr.op1(), use_integers);
  else if (expr.id() == ID_bitxor)
    result += "bvxor " + expr2sygus(expr.op0(), use_integers) + " " +
              expr2sygus(expr.op1(), use_integers);
  else if (expr.id() == ID_bitxnor)
    result += "bvxnor " + expr2sygus(expr.op0(), use_integers) + " " +
              expr2sygus(expr.op1(), use_integers);
  else if (expr.id() == ID_bitnot)
    result += "bvnot " + expr2sygus(expr.op0(), use_integers);
  else if (expr.id() == ID_lshr)
    result += "bvlshr " + expr2sygus(expr.op0(), use_integers) + " " +
              expr2sygus(expr.op1(), use_integers);
  else if (expr.id() == ID_shl)
    result += "bvlshl " + expr2sygus(expr.op0(), use_integers) + " " +
              expr2sygus(expr.op1(), use_integers);
  else if (expr.id() == ID_unary_minus)
  {
    if (use_integers)
      return result = "(- " + expr2sygus(expr.op0(), use_integers) + ")";
    else
      result += "bvneg " + expr2sygus(expr.op0(), use_integers);
  }
  else if (expr.id() == ID_plus)
  {
    result += (use_integers ? "+ " : "bvadd ");
    for (const auto &op : expr.operands())
      result += expr2sygus(op, use_integers) + " ";
  }
  else if (expr.id() == ID_minus)
    result += (use_integers ? "- "
                            : "bvsub ") +
              expr2sygus(expr.op0(), use_integers) + " " +
              expr2sygus(expr.op1(), use_integers);
  else if (expr.id() == ID_mult)
    result += (use_integers ? "* " : "bvmul ") + expr2sygus(expr.op0(), use_integers) + " " +
              expr2sygus(expr.op1(), use_integers);
  else if (expr.id() == ID_implies)
  {
    result += "=> " + expr2sygus(expr.op0(), use_integers) + expr2sygus(expr.op1(), use_integers);
  }
  else if (expr.id() == ID_function_application)
  {
    function_application_exprt fapp = to_function_application_expr(expr);
    if (fapp.function().id() != ID_symbol)
    {
      std::cout << "Unsupported function application " << expr.pretty() << std::endl;
      assert(0);
    }
    result += clean_id(to_symbol_expr(fapp.function()).get_identifier()) + " ";
    for (const auto &arg : fapp.arguments())
      result += expr2sygus(arg, use_integers) + " ";
  }
  else if (expr.id() == ID_symbol)
  {
    return result = clean_id(to_symbol_expr(expr).get_identifier());
  }
  else if (expr.id() == ID_index)
  {
    index_exprt indx = to_index_expr(expr);
    std::string array_string;
    if (indx.array().id() != ID_symbol)
      array_string = expr2sygus(indx.array(), use_integers);
    else
      array_string = id2string(to_symbol_expr(indx.array()).get_identifier());

    if (indx.index().id() != ID_infinity)
    {
      result += "select " +
                clean_id(array_string) + " ";
      if (indx.index().id() == ID_symbol || indx.index().id() == ID_constant)
        result += expr2sygus(indx.index(), use_integers);
      else
      {
        result += expr2sygus(indx.index(), use_integers);
      }
    }
    else
      return clean_id(array_string);
  }
  else if (expr.id() == ID_constant)
  {
    if (to_constant_expr(expr).type().id() == ID_unsignedbv)
    {
      result += "_ bv" + integer2string(string2integer(id2string(to_constant_expr(expr).get_value()), 16u), 10u) +
                " " + integer2string(to_unsignedbv_type(to_constant_expr(expr).type()).get_width()) + "";
    }
    else if (to_constant_expr(expr).type().id() == ID_integer)
    {
      result = clean_id(to_constant_expr(expr).get_value());
      if (result.front() == '-')
        return "(- " + result + ")";
      else
        return result;
    }
    else if (to_constant_expr(expr).type().id() == ID_bool)
      return result = clean_id(to_constant_expr(expr).get_value());
    else
    {
      std::cout << "Unsupported constant type" << expr.pretty() << std::endl;
      assert(0);
    }
  }
  else if (expr.id() == ID_with)
  {
    result += "store " +
              expr2sygus(to_with_expr(expr).old(), use_integers) + " " +
              expr2sygus(to_with_expr(expr).where(), use_integers) + " " +
              expr2sygus(to_with_expr(expr).new_value(), use_integers);
  }
  else if (expr.id() == ID_forall)
  {
    result += "forall (";
    for (const auto &e : to_forall_expr(expr).variables())
      result += "(" + expr2sygus(e, use_integers) + " " + type2sygus(e.type()) + ")";
    result += ") " + expr2sygus(to_forall_expr(expr).where(), use_integers);
  }
  else if (expr.id() == ID_exists)
  {
    result += "exists (";
    for (const auto &e : to_exists_expr(expr).variables())
      result += "(" + expr2sygus(e, use_integers) + " " + type2sygus(e.type()) + ")";
    result += ") " + expr2sygus(to_exists_expr(expr).where(), use_integers);
  }
  else if (expr.id() == ID_let)
  {
    result += "let (";
    const auto &var = to_let_expr(expr).variables();
    const auto &val = to_let_expr(expr).values();
    for (unsigned int i = 0; i < var.size(); i++)
    {
      result += "(" + expr2sygus(var[i], use_integers) + " " + expr2sygus(val[i], use_integers) + ")";
    }

    result += ") " + expr2sygus(to_let_expr(expr).where(), use_integers);
  }
  else if (expr.id() == ID_typecast)
  {
    // ignore typecast, they only occur when we use signed operators
    // risky behaviour..
    return expr2sygus(to_typecast_expr(expr).op(), use_integers);
  }
  else if (expr.id() == ID_extractbits)
  {
    const extractbits_exprt &extract = to_extractbits_expr(expr);
    result += "(_ extract " + expr2sygus(extract.upper(), use_integers) + " " + expr2sygus(extract.lower(), use_integers) + ") " + expr2sygus(extract.src(), use_integers);
  }
  else if (expr.id() == ID_concatenation)
  {
    const concatenation_exprt &c = to_concatenation_expr(expr);
    result += "concat " + expr2sygus(c.op0(), use_integers) + " " + expr2sygus(c.op1(), use_integers);
  }
  else if (expr.id() == ID_if)
  {
    result += "ite " + expr2sygus(to_if_expr(expr).cond(), use_integers) + " " + expr2sygus(to_if_expr(expr).true_case(), use_integers) + " " + expr2sygus(to_if_expr(expr).false_case(), use_integers);
  }
  else if (id2string(expr.id()) == "distinct")
  {
    result += "distinct ";
    for (const auto &op : expr.operands())
      result += expr2sygus(op) + " ";
  }
  else
  {
    std::cout << "WARNING: unsupported expression type" << expr.pretty() << std::endl;
    result += id2string(expr.id());
    // assert(0);
  }
  result += ")"; // + id2string(expr.id());
  return result;
}

std::string remove_synth_prefix(std::string in)
{
  std::string::size_type c_pos2 = in.find("synth_fun::");
  if (c_pos2 != std::string::npos &&
      in.rfind("synth_fun::") == c_pos2)
  {
    in.erase(0, c_pos2);
  }
  return in;
}

std::string sygus_interfacet::build_grammar(
    const symbol_exprt &function_symbol, const int &bound, const std::string &literal)
{
  std::string bools;
  std::string integers;
  if (!use_integers || !use_grammar)
  {
    std::cout << "do not use grammar " << std::endl;
    return bools;
  }

  bools += "(B Bool ((and B B) (or B B) (not B)\n";
  bools += "(= I I) (<= I I) (>= I I))\n";

  integers += "(I Int (0 1 " + literal + "\n";
  integers += "(+ I I)\n";
  integers += "(- I I)\n";
  integers += "(* I I)\n";

  int count = 0;
  for (const auto &d : to_mathematical_function_type(function_symbol.type()).domain())
  {
    if (d.id() == ID_integer)
      integers += "parameter" + integer2string(count) + " \n";
    else if (d.id() == ID_bool)
      bools += "parameter" + integer2string(count) + " \n";
    else if (d.id() == ID_array)
    {
      for (int i = 0; i < bound; i++)
        integers += "(select parameter" + integer2string(count) + " " + integer2string(i) + ")\n";
    }
    count++;
  }
  bools += ")\n";
  integers += ")\n";
  if (to_mathematical_function_type(function_symbol.type()).codomain().id() == ID_bool)
    return "((B Bool) (I Int))\n(" + bools + integers + "))";
  else
    return "((I Int) (B Bool))\n(" + integers + bools + "))";
}

void sygus_interfacet::build_query(problemt &problem, int bound)
{
  logic = "(set-logic ALL)\n";
  for (const auto &id : problem.id_map)
  {
    if (id.second.kind == smt2_parsert::idt::VARIABLE &&
        id.second.type.id() != ID_mathematical_function &&
        id.second.definition.is_nil())
    {
      exprt var = symbol_exprt(id.first, id.second.type);
      declare_vars += "(declare-var " + expr2sygus(var, use_integers) + " " + type2sygus(var.type()) + ")\n";
    }
  }
  for (const auto &f : problem.literals)
  {
    if (f.get_value() != "0" && f.get_value() != "1")
      literal_string += id2string(f.get_value()) + " ";
  }

  for (const auto &f : problem.synth_fun_set)
  {
    if (problem.id_map.find(f) == problem.id_map.end())
    {
      std::cout << "ERROR: did not find synth fun" << id2string(f) << std::endl;
      assert(0);
    }
    else
    {
      symbol_exprt var = symbol_exprt(f, problem.id_map.at(f).type);
      std::string grammar = build_grammar(var, bound, literal_string);

      synth_fun += "(synth-fun " + remove_synth_prefix(expr2sygus(var, use_integers)) + "(";
      std::size_t count = 0;
      for (const auto &d : to_mathematical_function_type(var.type()).domain())
      {
        synth_fun += "(parameter" + integer2string(count) + " " + type2sygus(d) + ")";
        count++;
      }

      synth_fun += ")";
      synth_fun += type2sygus(to_mathematical_function_type(var.type()).codomain());
      synth_fun += grammar + ") \n";
    }
  }

  for (const auto &f : problem.constraints)
  {
    constraints += "(constraint " + expr2sygus(f, use_integers) + ")\n";
  }
}

decision_proceduret::resultt sygus_interfacet::doit(problemt &problem)
{
  return doit(problem, false, false, 2);
}

decision_proceduret::resultt sygus_interfacet::fudge()
{
  std::istringstream is(
      "unsat\n(define-fun inv-fn ((parameter0 (Array Int Int)) (parameter1 (Array Int Int))) Bool (and (or (= (select parameter0 0) (select parameter1 0)) (= (select parameter0 0) (select parameter1 1)) ) (or (= (select parameter1 0) (select parameter0 1)) (= (select parameter1 1) (select parameter0 1)) ) ))");
  return read_result(is);
  //return decision_proceduret::resultt::D_SAT;
}

decision_proceduret::resultt sygus_interfacet::doit(
    problemt &problem, bool use_ints, bool use_gramm, const int bound, const int timeout)
{
  std::cout << "Use integers " << use_ints << std::endl;
  use_integers = use_ints;
  use_grammar = use_gramm;
  build_query(problem, bound);
  //use_integers = false;
  return solve(timeout);
}

decision_proceduret::resultt sygus_interfacet::solve(const int timeout)
{
  std::string query = logic + declare_vars + synth_fun + constraints + "(check-synth)\n";
  std::cout
      << "Solving query:\n"
      << query << std::endl;

  temporary_filet
      temp_file_problem("sygus_problem_", ""),
      temp_file_stdout("sygus_stdout_", ""),
      temp_file_stderr("sygus_stderr_", "");
  {
    // we write the problem into a file
    std::ofstream problem_out(
        temp_file_problem(), std::ios_base::out | std::ios_base::trunc);
    problem_out << query;
  }

  std::vector<std::string> argv;
  std::string stdin_filename;

  if (timeout == 0)
    argv = {"cvc4", "--lang", "sygus2", temp_file_problem()};
  else
    argv = {"timeout", integer2string(timeout), "cvc4", "--lang", "sygus2", temp_file_problem()};

  int res =
      run(argv[0], argv, stdin_filename, temp_file_stdout(), temp_file_stderr());
  if (res < 0)
  {
    return decision_proceduret::resultt::D_ERROR;
  }
  else
  {
    std::ifstream in(temp_file_stdout());
    return read_result(in);
  }
}

void sygus_interfacet::clear()
{
  constraints.clear();
  declare_vars.clear();
  synth_fun.clear();
  literal_string.clear();
}
decision_proceduret::resultt sygus_interfacet::read_result(std::istream &in)
{
  if (!in)
  {
    std::cout << "Failed to open input file";
    return decision_proceduret::resultt::D_ERROR;
  }
  std::string firstline;
  std::getline(in, firstline);
  if (firstline == "unknown")
  {
    std::cout << "SyGuS solver says unknown \n"
              << std::endl;
    return decision_proceduret::resultt::D_ERROR;
  }
  sygus_parsert result_parser(in);
  try
  {
    result_parser.parse();
  }
  catch (const sygus_parsert::smt2_errort &e)
  {
    std::cout << e.get_line_no() << ": "
              << e.what() << std::endl;
    return decision_proceduret::resultt::D_ERROR;
  }
  if (result_parser.id_map.size() == 0)
  {
    std::cout << "error: id_map is 0\n";
    return decision_proceduret::resultt::D_ERROR;
  }

  for (auto &id : result_parser.id_map)
  {
    if (id.second.type.id() == ID_mathematical_function)
    {
      //  solution.functions[symbol_exprt(id.first, id.second.type))]
      result[id.first] = id.second.definition;
      symbol_exprt symbol = symbol_exprt(to_mathematical_function_type(id.second.type));
      symbol.set_identifier("synth_fun::" + clean_id(id.first));
      clean_symbols(id.second.definition);
      solution.functions[symbol] = id.second.definition;
    }
  }
  return decision_proceduret::resultt::D_SATISFIABLE;
}
