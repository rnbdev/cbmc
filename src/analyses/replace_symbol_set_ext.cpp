/*******************************************************************\

Module: Modified expression replacement for constant propagator

Author: Peter Schrammel, Ranadeep

\*******************************************************************/

#include <util/std_types.h>
#include <util/std_expr.h>

#include "replace_symbol_set_ext.h"

// note: ranadeep
// todo - multi constant replace

/*******************************************************************\

Function: replace_symbol_set_extt::replace

  Inputs:

 Outputs:

 Purpose: does not replace object in address_of expressions

\*******************************************************************/

bool replace_symbol_set_extt::replace(exprt &dest) const
{
  bool result=true;

  // first look at type

  if(have_to_replace(dest.type()))
    if(!replace_symbol_sett::replace(dest.type()))
      result=false;

  // now do expression itself

  if(!have_to_replace(dest))
    return result;

  // do not replace object in address_of expressions
  if(dest.id()==ID_address_of)
  {
    const exprt &object = to_address_of_expr(dest).object();
    if(object.id()==ID_symbol)
    {
      expr_mapt::const_iterator it=
        expr_map.find(object.get(ID_identifier));

      if(it!=expr_map.end())
        return false;
    }
  }
  else if(dest.id()==ID_symbol)
  {
    expr_mapt::const_iterator it=
      expr_map.find(dest.get(ID_identifier));

    if(it!=expr_map.end() && it->second.size() < 2) // ranadeep -- not correct - but just for testing purpose
    {
      dest=*(it->second.begin());
      return false;
    }
  }

  Forall_operands(it, dest)
    if(!replace(*it))
      result=false;

  const irept &c_sizeof_type=dest.find(ID_C_c_sizeof_type);

  if(c_sizeof_type.is_not_nil() &&
     !replace_symbol_sett::replace(
       static_cast<typet&>(dest.add(ID_C_c_sizeof_type))))
    result=false;

  const irept &va_arg_type=dest.find(ID_C_va_arg_type);

  if(va_arg_type.is_not_nil() &&
     !replace_symbol_sett::replace(static_cast<typet&>(dest.add(ID_C_va_arg_type))))
    result=false;

  return result;
}
