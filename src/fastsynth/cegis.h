#include <util/std_expr.h>
#include <util/decision_procedure.h>

class synth_encodingt;
class verify_encodingt;
class symex_target_equationt;
class prop_convt;

class cegist:public messaget
{
public:
  explicit cegist(const namespacet &_ns):
    max_program_size(0), ns(_ns)
  {
  }

  decision_proceduret::resultt operator()(
    symex_target_equationt &);
  
  std::map<symbol_exprt, exprt> expressions;

  std::size_t max_program_size;

protected:
  const namespacet &ns;

  decision_proceduret::resultt incremental_loop(
    symex_target_equationt &);

  decision_proceduret::resultt non_incremental_loop(
    symex_target_equationt &);

  // map symbols to values
  using counterexamplet=std::map<exprt, exprt>;

  using counterexamplest=std::vector<counterexamplet>;

  counterexamplest counterexamples;

  void convert(
    symex_target_equationt &,
    verify_encodingt &,
    prop_convt &);

  void convert_negation(
    symex_target_equationt &,
    synth_encodingt &,
    prop_convt &);

  void add_counterexample(
    const counterexamplet &,
    synth_encodingt &,
    prop_convt &);
};

void output_expressions(
  const std::map<symbol_exprt, exprt> &,
  const namespacet &,
  std::ostream &);
