#ifndef CPROVER_FASTSYNTH_CVC4_LEARN_H_
#define CPROVER_FASTSYNTH_CVC4_LEARN_H_

#include "learn.h"
#include "cvc4_interface.h"

class cvc4_learnt : public learnt
{
protected:
    /// Namespace passed on to decision procedure.
    const namespacet &ns;
    /// Synthesis problem to solve.
    const problemt &problem;

    void add_problem();

    sygus_interfacet sygus_interface;
};

#endif /* CPROVER_FASTSYNTH_CVC4_LEARN_H_ */
