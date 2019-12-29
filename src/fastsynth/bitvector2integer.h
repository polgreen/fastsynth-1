
#include <util/message.h>
#include <util/expr.h>
#include "cegis_types.h"
class bitvec2integert : public messaget
{
public:
    void convert(exprt &expr);
    void convert(typet &type);
};