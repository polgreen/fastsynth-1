#include "cvc4_interface.h"
#include <util/expr.h>
#include <iostream>
#include <util/expr.h>
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

static std::string clean_id(const irep_idt &id)
{
  std::string dest = id2string(id);
  std::string::size_type c_pos = dest.find("#");
  if (c_pos != std::string::npos &&
      dest.rfind("#") == c_pos)
    dest.erase(c_pos, std::string::npos);
  return dest;
}

std::string expr2sygus(const exprt &expr)
{
  std::string result = "(";

  if (expr.id() == ID_equal)
    result += "= " + expr2sygus(expr.op0()) + " " +
              expr2sygus(expr.op1());
  else if (expr.id() == ID_le)
    result += "bvule " + expr2sygus(expr.op0()) + " " +
              expr2sygus(expr.op1());
  else if (expr.id() == ID_ge)
    result += "bvuge" + expr2sygus(expr.op0()) + " " +
              expr2sygus(expr.op1());
  else if (expr.id() == ID_lt)
    result += "bvult " + expr2sygus(expr.op0()) + " " +
              expr2sygus(expr.op1());
  else if (expr.id() == ID_gt)
    result += "bvugt" + expr2sygus(expr.op0()) + " " +
              expr2sygus(expr.op1());
  else if (expr.id() == ID_and)
    result += "and " + expr2sygus(expr.op0()) + " " +
              expr2sygus(expr.op1());
  else if (expr.id() == ID_or)
    result += "or " + expr2sygus(expr.op0()) + " " +
              expr2sygus(expr.op1());
  else if (expr.id() == ID_xor)
    result += "xor " + expr2sygus(expr.op0()) + " " +
              expr2sygus(expr.op1());
  else if (expr.id() == ID_not)
    result += "not " + expr2sygus(expr.op0());

  else if (expr.id() == ID_bitand)
    result += "bvand " + expr2sygus(expr.op0()) + " " +
              expr2sygus(expr.op1());
  else if (expr.id() == ID_bitor)
    result += "bvor " + expr2sygus(expr.op0()) + " " +
              expr2sygus(expr.op1());
  else if (expr.id() == ID_bitxor)
    result += "bvxor " + expr2sygus(expr.op0()) + " " +
              expr2sygus(expr.op1());
  else if (expr.id() == ID_bitxnor)
    result += "bvxnor " + expr2sygus(expr.op0()) + " " +
              expr2sygus(expr.op1());
  else if (expr.id() == ID_bitnot)
    result += "bvnot " + expr2sygus(expr.op0());
  else if (expr.id() == ID_lshr)
    result += "bvlshr " + expr2sygus(expr.op0()) + " " +
              expr2sygus(expr.op1());
  else if (expr.id() == ID_shl)
    result += "bvlshl " + expr2sygus(expr.op0()) + " " +
              expr2sygus(expr.op1());
  else if (expr.id() == ID_unary_minus)
    result += "bvneg " + expr2sygus(expr.op0());
  else if (expr.id() == ID_plus)
    result += "bvadd " + expr2sygus(expr.op0()) + " " +
              expr2sygus(expr.op1());
  else if (expr.id() == ID_minus)
    result += "bvsub " + expr2sygus(expr.op0()) + " " +
              expr2sygus(expr.op1());
  else if (expr.id() == ID_mult)
    result += "bvmul " + expr2sygus(expr.op0()) + " " +
              expr2sygus(expr.op1());
  else if (expr.id() == ID_implies)
  {
    result += "=> " + expr2sygus(expr.op0()) + expr2sygus(expr.op1());
  }
  else if (expr.id() == ID_function_application)
  {
    function_application_exprt fapp = to_function_application_expr(expr);
    result += id2string(to_symbol_expr(fapp.function()).get_identifier()) + " ";
    for (const auto &arg : fapp.arguments())
      result += expr2sygus(arg) + " ";
  }
  else if (expr.id() == ID_symbol)
  {
    return result = clean_id(to_symbol_expr(expr).get_identifier());
  }
  else if (expr.id() == ID_index)
  {
    index_exprt indx = to_index_expr(expr);
    if (indx.index().id() != ID_infinity)
    {
      result += "select " +
                clean_id(to_symbol_expr(indx.array()).get_identifier()) + " " + expr2sygus(indx.index());
    }
    else
    {
      return result = clean_id(to_symbol_expr(indx.array()).get_identifier());
    }
  }
  else if (expr.id() == ID_constant)
  {
    if (to_constant_expr(expr).type().id() == ID_unsignedbv)
    {
      result += "_ bv" + id2string(to_constant_expr(expr).get_value()) +
                " " + integer2string(to_unsignedbv_type(to_constant_expr(expr).type()).get_width()) + "";
    }
    else if (to_constant_expr(expr).type().id() == ID_integer)
    {
      return result = id2string(to_constant_expr(expr).get_value());
    }
    else
    {
      std::cout << "Unsupported" << expr.pretty() << std::endl;
      assert(0);
    }
  }
  else
  {
    std::cout << "Unsupported" << expr.pretty() << std::endl;
    assert(0);
  }
  result += ")";
  return result;
}

void sygus_interfacet::build_query(sygus_parsert &sygus_parser)
{
  logic = "(set-logic ALL)\n";
  for (const auto &id : sygus_parser.id_map)
  {
    if (id.second.kind == smt2_parsert::idt::VARIABLE &&
        id.second.type.id() != ID_mathematical_function &&
        id.second.definition.is_nil())
    {
      exprt var = symbol_exprt(id.first, id.second.type);
      declare_vars += "(declare-var " + expr2sygus(var) + " " + type2sygus(var.type()) + ")\n";
    }
  }

  for (const auto &f : sygus_parser.synth_fun_set)
  {
    if (sygus_parser.id_map.find(f) == sygus_parser.id_map.end())
    {
      std::cout << "ERROR: did not find synth fun" << id2string(f) << std::endl;
      assert(0);
    }
    else
    {
      symbol_exprt var = symbol_exprt(f, sygus_parser.id_map.at(f).type);
      synth_fun += "(synth-fun " + expr2sygus(var) + "(";
      std::size_t count = 0;
      for (const auto &d : to_mathematical_function_type(var.type()).domain())
      {
        synth_fun += "(parameter" + integer2string(count) + " " + type2sygus(d) + ")";
      }
      synth_fun += ")";
      synth_fun += type2sygus(to_mathematical_function_type(var.type()).codomain()) + ") \n";
    }
  }

  for (const auto &f : sygus_parser.constraints)
  {
    constraints += "(constraint " + expr2sygus(f) + ")\n";
  }
}

void sygus_interfacet::doit(sygus_parsert &sygus_parser)
{
  build_query(sygus_parser);
  solve();
}

void sygus_interfacet::solve()
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

  // configurable
  argv = {"cvc4", "--lang", "sygus", temp_file_problem()};

  int res =
      run(argv[0], argv, stdin_filename, temp_file_stdout(), temp_file_stderr());
  if (res < 0)
  {
    std::cerr << "error running sygus solver\n";
  }
  else
  {
    std::ifstream in(temp_file_stdout());
    read_result(in);
  }
}

void sygus_interfacet::read_result(std::istream &in)
{
  if (!in)
  {
    std::cout << "Failed to open input file";
    return;
  }
  std::string firstline;
  std::getline(in, firstline);
  if (firstline == "unknown")
  {
    std::cout << "Error: no solution\n";
    assert(0);
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
    assert(0);
  }
  assert(result_parser.id_map.size() != 0);
  for (const auto &id : result_parser.id_map)
  {
    if (id.second.type.id() == ID_mathematical_function)
      result[id.first] = id.second.definition;
  }
}
