#include <set>

#include <solvers/smt2/smt2_parser.h>

#include <util/mathematical_expr.h>
#include <util/mathematical_types.h>

class sygus_parsert : public smt2_parsert
{
public:
  explicit sygus_parsert(std::istream &_in):
    smt2_parsert(_in)
  {
    append_to_commands();
  }

  using smt2_errort = smt2_tokenizert::smt2_errort;

  enum invariant_variablet { PRIMED, UNPRIMED };
  enum invariant_constraint_functiont { PRE, INV, TRANS, POST };

  exprt::operandst inv_arguments;
  exprt::operandst inv_primed_arguments;
  exprt::operandst constraints;
  std::string logic, action;

  std::vector<exprt> free_variables;

  std::set<irep_idt> synth_fun_set;

  smt2_parsert::signature_with_parameter_idst inv_function_signature();
  void expand_function_applications(exprt &);
  void generate_invariant_constraints();

  function_application_exprt apply_function_to_variables(
    invariant_constraint_functiont id,
    invariant_variablet variable_use);

  struct functiont : public idt
  {
    functiont(): idt(nil_exprt())
    {
    }
  };

protected:
  // commands
  void append_to_commands();


  void fix_binary_operation_operand_types(exprt &expr);
  void fix_ite_operation_result_type(if_exprt &expr);
  exprt cast_bv_to_signed(exprt &expr);
  exprt cast_bv_to_unsigned(exprt &expr);
  void check_bitvector_operands(exprt &expr);

  // grammars
  void NTDef_seq();
  void GTerm_seq();
  void NTDef();
  void GTerm();
};

