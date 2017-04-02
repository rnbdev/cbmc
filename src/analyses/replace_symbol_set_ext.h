/*******************************************************************\

Module: Modified expression replacement for constant propagator

Author: Peter Schrammel, Ranadeep

\*******************************************************************/

#ifndef CPROVER_ANALYSES_REPLACE_SYMBOL_SET_EXT_H
#define CPROVER_ANALYSES_REPLACE_SYMBOL_SET_EXT_H

#include <util/replace_symbol_set.h>

class replace_symbol_set_extt:public replace_symbol_sett
{
public:
  virtual bool replace(exprt &dest) const;
};

#endif // CPROVER_ANALYSES_REPLACE_SYMBOL_SET_EXT_H
