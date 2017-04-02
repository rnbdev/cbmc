/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com, Ranadeep

\*******************************************************************/

#ifndef CPROVER_UTIL_REPLACE_SYMBOL_SET_H
#define CPROVER_UTIL_REPLACE_SYMBOL_SET_H

//
// true: did nothing
// false: replaced something
//

// note - ranadeep
// done!

#include "expr.h"
#include <set>

class replace_symbol_sett
{
public:
  typedef std::unordered_map<irep_idt, std::set<exprt>, irep_id_hash> expr_mapt;
  typedef std::unordered_map<irep_idt, typet, irep_id_hash> type_mapt;

  void insert(const irep_idt &identifier,
                     const exprt &expr)
  {
    // expr_map.insert(std::pair<irep_idt, exprt>(identifier, expr)); // ranadeep
    expr_map[identifier].insert(expr);
  }

  void insert(const class symbol_exprt &old_expr,
              const exprt &new_expr);

  void insert(const irep_idt &identifier,
                     const typet &type)
  {
    type_map.insert(std::pair<irep_idt, typet>(identifier, type));
  }

  virtual bool replace(exprt &dest) const;
  virtual bool replace(typet &dest) const;

  void operator()(exprt &dest) const
  {
    replace(dest);
  }

  void operator()(typet &dest) const
  {
    replace(dest);
  }

  void clear()
  {
    expr_map.clear();
    type_map.clear();
  }

  replace_symbol_sett();
  virtual ~replace_symbol_sett();

  expr_mapt expr_map;
  type_mapt type_map;

protected:
  bool have_to_replace(const exprt &dest) const;
  bool have_to_replace(const typet &type) const;
};

#endif // CPROVER_UTIL_REPLACE_SYMBOL_SET_H
