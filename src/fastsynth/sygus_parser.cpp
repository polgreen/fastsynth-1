#include "sygus_parser.h"

#include <solvers/smt2/smt2_format.h>
#include <util/bv_arithmetic.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/replace_symbol.h>
#include <util/arith_tools.h>

#include <cctype>
#include <cassert>
#include <fstream>
#include <iostream>


void sygus_parsert::append_to_commands()
{
  // declare-fun is not supported in SyGuS
  commands.erase("declare-fun");
  commands["declare-fun"] = [this]() {
    throw error("declare-fun not supported in SyGuS-IF");
  };

  // set-options is not supported in SyGuS
  commands.erase("set-options");
  commands["set-options"] = [this] {
    ignore_command();
  };

  commands.erase("declare-fun");

  commands["declare-fun"] = [this]() {
    if(next_token() != smt2_tokenizert::SYMBOL)
      throw error("expected a symbol after declare-fun");

    irep_idt id = smt2_tokenizer.get_buffer();
    auto type = function_signature_declaration();
    free_variables.push_back(symbol_exprt(id, type));
    add_unique_id(id, exprt(ID_nil, type));
  };

  commands["declare-primed-var"] = [this] {

    // we can ignore declare-primed-var,
    // it doesn't add any additional information
    // as the invariants are only applied to variables
    // local to the constraints

    ignore_command();
  };

// for some reason set-logic isn't supported in the smt2 parser
  commands["set-logic"] = [this] {
    if(smt2_tokenizer.next_token()!=smt2_tokenizert::SYMBOL)
      throw error("expected a symbol after set-logic");

    logic=smt2_tokenizer.get_buffer();
  };

  commands["synth-fun"] = [this] {
    if(smt2_tokenizer.next_token() != smt2_tokenizert::SYMBOL)
      throw error("expected a symbol after synth-fun");

    irep_idt id = smt2_tokenizer.get_buffer();

    auto signature = function_signature_definition();

    NTDef_seq();

    add_unique_id(id, exprt(ID_nil, signature.type));

    synth_fun_set.insert(id);

  };

  commands["synth-inv"] = [this] {

    if(smt2_tokenizer.next_token() != smt2_tokenizert::SYMBOL)
      throw error("expected a symbol after synth-fun");

    INVARIANT(inv_arguments.size()==0,
        "Inv argument list should be empty");
    irep_idt id = smt2_tokenizer.get_buffer();

    auto signature = inv_function_signature();

    NTDef_seq();

    add_unique_id(id, exprt(ID_nil, signature.type));

    id_map.at(id).type = signature.type;
    id_map.at(id).parameters = signature.parameters;

    synth_fun_set.insert(id);
  };

  commands["constraint"] = [this] {
    constraints.push_back(expression());
  };

  commands["inv-constraint"] = [this] {
    ignore_command();
    generate_invariant_constraints();
  };

  commands["check-synth"] = [this] {
    action="check-synth";
  };
}

smt2_parsert::signature_with_parameter_idst
sygus_parsert::inv_function_signature()
{
  if(smt2_tokenizer.next_token()!=smt2_tokenizert::OPEN)
    throw error("expected '(' at beginning of signature");

  if(smt2_tokenizer.peek() == smt2_tokenizert::CLOSE)
    throw error("An invariant must have arguments");

  mathematical_function_typet::domaint domain;
  std::vector<irep_idt> parameters;

  while(smt2_tokenizer.peek()!=smt2_tokenizert::CLOSE)
  {

    if(smt2_tokenizer.next_token()!=smt2_tokenizert::OPEN)
      throw error("expected '(' at beginning of parameter");

    if(smt2_tokenizer.next_token()!=smt2_tokenizert::SYMBOL)
      throw error("expected symbol in parameter");

    const irep_idt id=smt2_tokenizer.get_buffer();
    domain.push_back(sort());
    typet param_type=domain.back();

   // parameters.push_back(id);
    parameters.push_back(add_fresh_id(id, exprt(ID_nil, domain.back())));

    inv_arguments.push_back(symbol_exprt(id, param_type));
    inv_primed_arguments.push_back(symbol_exprt(id2string(id)+"!",param_type));

    if(smt2_tokenizer.next_token()!=smt2_tokenizert::CLOSE)
      throw error("expected ')' at end of parameter");
  }

  smt2_tokenizer.next_token(); // eat the ')'

  // invariants implicitly return Bool

  return smt2_parsert::signature_with_parameter_idst(
      mathematical_function_typet(domain, bool_typet()), parameters);
}

function_application_exprt sygus_parsert::apply_function_to_variables(
  invariant_constraint_functiont function_type,
  invariant_variablet var_use)
{

  std::string id;
  exprt::operandst arguments;

  switch(function_type)
  {
  case PRE:
    id = "pre-f";
    break;
  case INV:
    id = "inv-f";
    break;
  case TRANS:
    id = "trans-f";
    arguments.resize(2*inv_arguments.size());
    std::copy(inv_arguments.begin(), inv_arguments.end(), arguments.begin());
    std::copy(inv_primed_arguments.begin(), inv_primed_arguments.end(),
        arguments.begin()+inv_arguments.size());
    break;
  case POST:
    id = "post-f";
    break;
  }

  if(id_map.find(id) == id_map.end())
    throw error() << "undeclared function `" << id << '\'';

  auto f_it=id_map.find(id);
  const auto &f=f_it->second;

  DATA_INVARIANT(f.type.id() == ID_mathematical_function,
    "functions must have function type");
  const auto &f_type = to_mathematical_function_type(f.type);

  return function_application_exprt(
    symbol_exprt(id, f.type),
    (function_type==TRANS? arguments:
        (var_use==PRIMED? inv_primed_arguments: inv_arguments)),
    f_type.codomain());
}

void sygus_parsert::generate_invariant_constraints()
{
  // pre-condition application
  function_application_exprt pre_f =
    apply_function_to_variables(PRE, UNPRIMED);

  // invariant application
  function_application_exprt inv =
    apply_function_to_variables(INV, UNPRIMED);

  function_application_exprt primed_inv =
    apply_function_to_variables(INV, PRIMED);

  // transition function application
  function_application_exprt trans_f =
    apply_function_to_variables(TRANS, UNPRIMED);

  // post-condition function application
  function_application_exprt post_f =
    apply_function_to_variables(POST, UNPRIMED);

  // create constraints
  implies_exprt pre_condition(pre_f, inv);
  constraints.push_back(pre_condition);

  and_exprt inv_and_transition(inv, trans_f);
  implies_exprt transition_condition(inv_and_transition, primed_inv);
  constraints.push_back(transition_condition);

  implies_exprt post_condition(inv, post_f);
  constraints.push_back(post_condition);
}

void sygus_parsert::NTDef_seq()
{
  // it is not necessary to give a syntactic template
  if(smt2_tokenizer.peek()!=smt2_tokenizert::OPEN)
    return;

  while(smt2_tokenizer.peek()!=smt2_tokenizert::CLOSE)
  {
    NTDef();
  }

  smt2_tokenizer.next_token(); // eat the ')'
}

void sygus_parsert::GTerm_seq()
{
  while(smt2_tokenizer.peek()!=smt2_tokenizert::CLOSE)
  {
    GTerm();
  }
}

void sygus_parsert::NTDef()
{
  // (Symbol Sort GTerm+)
  if(smt2_tokenizer.next_token()!=smt2_tokenizert::OPEN)
    throw error("NTDef must begin with '('");

  if(smt2_tokenizer.peek()==smt2_tokenizert::OPEN)
    smt2_tokenizer.next_token(); // symbol might be in another set of parenthesis

  if(smt2_tokenizer.next_token()!=smt2_tokenizert::SYMBOL)
    throw error("NTDef must have a symbol");

  sort();

  GTerm_seq();

  if(smt2_tokenizer.next_token()!=smt2_tokenizert::CLOSE)
    throw error("NTDef must end with ')'");
}

void sygus_parsert::GTerm()
{
  // production rule

  switch(smt2_tokenizer.next_token())
  {
  case smt2_tokenizert::SYMBOL:
  case smt2_tokenizert::NUMERAL:
  case smt2_tokenizert::STRING_LITERAL:
    break;

  case smt2_tokenizert::OPEN:
    while(smt2_tokenizer.peek()!=smt2_tokenizert::CLOSE)
    {
      GTerm();
    }

    smt2_tokenizer.next_token(); // eat ')'
    break;

  case smt2_tokenizert::NONE:
  case smt2_tokenizert::END_OF_FILE:
  case smt2_tokenizert::KEYWORD:
  case smt2_tokenizert::CLOSE:
    throw error("Unexpected GTerm");
  }
}

void sygus_parsert::expand_function_applications(exprt &expr)
{
  for(exprt &op : expr.operands())
    expand_function_applications(op);

  if(expr.id() == ID_symbol)
  {
    auto &app=to_symbol_expr(expr);
    irep_idt identifier=app.get_identifier();
    if(synth_fun_set.find(identifier) != synth_fun_set.end())
    {
      app.set_identifier("synth_fun::" + id2string(identifier));
      return; // do not expand
    }
  }

  if(expr.id()==ID_function_application)
  {
    auto &app=to_function_application_expr(expr);

    // look it up
    DATA_INVARIANT(app.function().id()==ID_symbol, "function must be symbol");
    irep_idt identifier=to_symbol_expr(app.function()).get_identifier();
    std::cout<<"expanding function "<< id2string(identifier)<<std::endl;
    auto f_it=id_map.find(identifier);

    if(f_it!=id_map.end())
    {
      const auto &f=f_it->second;

      if(synth_fun_set.find(identifier)!=synth_fun_set.end())
      {
        to_symbol_expr(app.function()).set_identifier(
            "synth_fun::"+id2string(identifier));
        return; // do not expand
      }

      DATA_INVARIANT(f.type.id() == ID_mathematical_function,
        "functions must have function type");
      const auto &f_type = to_mathematical_function_type(f.type);

      INVARIANT(f_type.domain().size()==
             app.arguments().size(), "Invalid number of arguments to function");

      replace_symbolt replace_symbol;

      std::map<irep_idt, exprt> parameter_map;
      for(std::size_t i=0; i<f_type.domain().size(); i++)
      {
        const auto &parameter_type = f_type.domain()[i];
        const auto &parameter_id = f.parameters[i];

        replace_symbol.insert(
          symbol_exprt(parameter_id, parameter_type),
          app.arguments()[i]);
      }

      exprt body=f.definition;
      replace_symbol(body);
      expand_function_applications(body);
      expr=body;
    }
  }
}
