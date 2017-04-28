/*******************************************************************\

Module: Constant Propagation

Author: Peter Schrammel, Ranadeep

\*******************************************************************/

#define DEBUG
#define LOOPWIDE
#define INTERPROC

#ifdef DEBUG
#include <iostream>
#endif

#include <vector>
#include <set>
#include <algorithm>
#include <iterator>

#include <util/find_symbols.h>
#include <util/arith_tools.h>
#include <util/simplify_expr.h>

#include <goto-instrument/function.h>

#include "constant_set_propagator.h"

/*******************************************************************\

Function: constant_set_propagator_domaint::assign_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void constant_set_propagator_domaint::assign_rec(
  valuest &values,
  const exprt &lhs, const exprt &rhs,
  const namespacet &ns)
{
  const typet &rhs_type = ns.follow(rhs.type());

#ifdef DEBUG
  std::cout << "assign: " << from_expr(ns, "", lhs)
            << " := " << from_type(ns, "", rhs_type) << std::endl;
#endif

  if(lhs.id()==ID_symbol && rhs_type.id()!=ID_array
                         && rhs_type.id()!=ID_struct
                         && rhs_type.id()!=ID_union)
  {
    if(values.is_constant(rhs))
      assign(values, to_symbol_expr(lhs), rhs, ns);
    else
      values.set_to_top(to_symbol_expr(lhs));
  }
#if 0
  else // TODO: could make field or array element-sensitive
  {
  }
#endif
}

bool constant_set_propagator_domaint::is_in_loop(locationt from, ai_baset &ai)
{
  for(auto e: static_cast<const constant_set_propagator_ait &>(ai).loophead_list) {
    if(e->location_number <= from->location_number && from->location_number <= e->get_target()->location_number)
      return true;
  }
  return false;
}

/*******************************************************************\

Function: constant_set_propagator_domaint::transform

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void constant_set_propagator_domaint::transform(
  locationt from,
  locationt to,
  ai_baset &ai,
  const namespacet &ns)
{
  #ifdef DEBUG
  std::cout << from->location_number << " --> "
            << to->location_number << '\n';
  std::cout << "\"from\" expr " << from_expr(ns, "", from->code) << "\n";
  #endif

#ifdef DEBUG
  std::cout << "before:\n";
  output(std::cout, ai, ns);
#endif

  if(from->is_decl())
  {
    const code_declt &code_decl=to_code_decl(from->code);
    const symbol_exprt &symbol=to_symbol_expr(code_decl.symbol());
    values.set_to_top(symbol);
  }
  else if(from->is_assign())
  {
    const code_assignt &assignment=to_code_assign(from->code);
    const exprt &lhs = assignment.lhs();
    const exprt &rhs = assignment.rhs();
    #ifdef DEBUG
      std::cout << "assign statement\n" << from_expr(ns, "", lhs) << " = " << from_expr(ns, "", rhs) << "\n";
    #endif
    if(is_in_loop(from, ai)){
      std::set<irep_idt> dep_symbols;
      exprt rhs_ = rhs;
      get_dep_exprs(rhs_, dep_symbols);
      #ifdef DEBUG
        std::cout << "inside loop assignment\n";
      #endif
      if(dep_symbols.size() > 0){
        #ifdef DEBUG
          std::cout << "not constant -- setting to top\n";
        #endif
        values.set_to_top(to_symbol_expr(lhs).get_identifier());
      }
      else{
        #ifdef DEBUG
          std::cout << "constant -- not setting to top\n";
        #endif
        assign_rec(values, lhs, rhs, ns);
      }
    }
    else {
      assign_rec(values, lhs, rhs, ns);
    }
  }
  else if(from->is_assume())
  {
    two_way_propagate_rec(from->guard, ns);
  }
  else if(from->is_goto())
  {
    exprt g;
    if(from->get_target()==to)
      g = simplify_expr(from->guard, ns);
    else
      g = simplify_expr(not_exprt(from->guard), ns);

    #ifdef DEBUG
      std::cout << "goto condition -- " << from_expr(ns, "", g) << "\n";
      std::cout << "goto from -- " << from->location_number << "\n";
      std::cout << "goto backward --" << from->is_backwards_goto() << "\n";
      std::cout << "goto body till -- " << std::prev(from->get_target())->location_number << "\n";
    #endif
    locationt goto_body_end = std::prev(from->get_target());
    if(!from->is_backwards_goto() && goto_body_end->is_backwards_goto() && goto_body_end->get_target() == from)
    {
      #ifdef DEBUG
      std::cout << "found loop -- " << from->location_number << "\n";
      #endif
      #ifdef LOOPWIDE
      static_cast<constant_set_propagator_ait &>(ai).loophead_list.insert(from);
      #endif
    }

    two_way_propagate_rec(g, ns);
  }
  else if(from->is_dead())
  {
    const code_deadt &code_dead=to_code_dead(from->code);
    values.set_to_top(to_symbol_expr(code_dead.symbol()));
  }
  else if(from->is_function_call()) // todo: if no function body
  {
    const code_function_callt &code_function_call = to_code_function_call(from->code);
    const exprt &function=code_function_call.function();

    #ifdef INTERPROC
    if(function.id()==ID_symbol)
    #else
    if(0)
    #endif
    {
      const irep_idt &identifier=to_symbol_expr(function).get_identifier();

      if(identifier=="__CPROVER_set_must" ||
         identifier=="__CPROVER_get_must" ||
         identifier=="__CPROVER_set_may" ||
         identifier=="__CPROVER_get_may" ||
         identifier=="__CPROVER_cleanup" ||
         identifier=="__CPROVER_clear_may" ||
         identifier=="__CPROVER_clear_must")
      {
      }
      else
      {
        // values.set_to_top();
        #ifdef DEBUG
          if(code_function_call.lhs().is_not_nil()) std::cout << "lhs " << from_expr(ns, "", code_function_call.lhs())<< "\n";
          std::cout << "function call -- " << from_expr(ns, "", from->code) << "\n";
          std::cout << "function name-- " << from_expr(ns, "", function) << "\n";
          for(const exprt e: code_function_call.arguments()){
            std::cout << "arg : " << from_expr(ns, "", e) << "\n";
          }
          if(to->is_decl()) {
            std::cout << "rnb -- declaration\n";
              const code_declt &code_decl=to_code_decl(to->code);
              std::cout << "statement " << from_expr(ns, "", code_decl.symbol())<< "\n";
          } else {
            std::cout << "rnb -- not decl\n";
          }
        #endif

        if(!values.is_bottom)
        {
          if(ai.body_available)
          {
          const symbol_exprt &fn_symbol_expr=to_symbol_expr(function);
          const code_typet &code_type=to_code_type(ns.lookup(fn_symbol_expr.get_identifier()).type);
          auto parameters = code_type.parameter_identifiers();
          auto arguments = code_function_call.arguments();
          // valuest copy_values = values;
          // values.set_to_top(); // TODO: have to leave out global vars
          for(unsigned int i = 0; i < arguments.size(); ++i)
          {
            #ifdef DEBUG
            std::cout << "adding param for -- " << from_expr(ns, "", ns.lookup(parameters[i]).symbol_expr()) << "\n";
            #endif
            assign_rec(values, ns.lookup(parameters[i]).symbol_expr(), arguments[i], ns);
          }
          }
          else
          {
            #ifdef DEBUG
              std::cout << "no function body so just setting to top\n";
            #endif
            if(code_function_call.lhs().is_not_nil())
              values.set_to_top(to_symbol_expr(code_function_call.lhs()).get_identifier());
          }
        }
      }
    }
    else
      values.set_to_top();
  }
  else if(from->is_return()){
    const code_returnt &code_return = to_code_return(from->code);
    const exprt &return_value = code_return.return_value();
    #ifdef DEBUG
      std::cout << "Found a return : " << from_expr(ns, "", return_value) << "\n";
    #endif
    locationt last_call_site = ai.get_top_function_call_location_from_stack();
    assert(last_call_site->is_function_call());
    const code_function_callt &code_function_call = to_code_function_call(last_call_site->code);
    const exprt &lhs = code_function_call.lhs();
    if(lhs.is_not_nil()){
      #ifdef DEBUG
        std::cout << "adding return value\n";
      #endif
      if(is_in_loop(last_call_site, ai)){
        #ifdef DEBUG
          std::cout << "function call -- in the loop -- setting to top\n";
        #endif
        values.set_to_top(to_symbol_expr(lhs).get_identifier());
      } else {
        #ifdef DEBUG
          std::cout << "function call -- out of loop -- not setting to top\n";
        #endif
        assign_rec(values, lhs, return_value, ns);
      }
    }
  }
  else if(from->is_end_function()){
    #ifdef DEBUG
      std::cout << "Found a end_function\n";
      std::cout << "to location -- " << from_expr(ns, "", to->code) << "\n";
    #endif
    locationt last_call_site = ai.get_top_function_call_location_from_stack();
    const code_function_callt &code_function_call = to_code_function_call(last_call_site->code);
    const symbol_exprt &fn_symbol_expr=to_symbol_expr(code_function_call.function());
    const code_typet &code_type=to_code_type(ns.lookup(fn_symbol_expr.get_identifier()).type);
    auto parameters = code_type.parameter_identifiers();
    for(irep_idt e_param: parameters) {
      values.set_to_top(e_param);
    }
  }
#ifdef DEBUG
  std::cout << "after:\n";
  output(std::cout, ai, ns);
#endif
}


/*******************************************************************\

Function: constant_set_propagator_domaint::two_way_propagate_rec

  Inputs:

 Outputs:

 Purpose: handles equalities and conjunctions containing equalities

\*******************************************************************/

bool constant_set_propagator_domaint::two_way_propagate_rec( // ranadeep -- done
  const exprt &expr,
  const namespacet &ns)
{
#ifdef DEBUG
  std::cout << "two_way_propagate_rec - expr: " << from_expr(ns, "", expr) << '\n';
#endif
  bool change = false;

  if(expr.id()==ID_and)
  {
    // need a fixed point here to get the most out of it
    do
    {
      change = false;

      forall_operands(it, expr)
        if(two_way_propagate_rec(*it, ns))
          change = true;
    }
    while(change);
  }
  else if(expr.id()==ID_equal)
  {
    const exprt &lhs = expr.op0();
    const exprt &rhs = expr.op1();

    // two-way propagation
    valuest copy_values = values;
    assign_rec(copy_values, lhs, rhs, ns);
    if(!values.is_constant(rhs) || values.is_constant(lhs))
      assign_rec(values, rhs, lhs, ns);
    #ifdef DEBUG
      std::cout << "meet between:\n";
      values.output(std::cout, ns);
      copy_values.output(std::cout, ns);
    #endif
    change = values.meet(copy_values);
  }
  else if(expr.id()==ID_or) // ranadeep - added for OR
  {
    change = false;
    valuest old_values = values;
    valuest merge_values;
    merge_values.is_bottom = true;

    forall_operands(it, expr)
    {
      if(two_way_propagate_rec(*it, ns)){
        #ifdef DEBUG
          std::cout << "merge between:\n";
          values.output(std::cout, ns);
          merge_values.output(std::cout, ns);
        #endif
        change = values.merge(merge_values);
        #ifdef DEBUG
          std::cout << "merged maps:\n";
          values.output(std::cout, ns);
        #endif
      }
      merge_values = values;
      values = old_values;
    }
    #ifdef DEBUG
      std::cout << "all merge\n";
      merge_values.output(std::cout, ns);
      values.output(std::cout, ns);
    #endif
    valuest temp = merge_values;
    change = temp.merge(values); // if actually there is any change
    if(change)
      values = merge_values;
  }

#ifdef DEBUG
  std::cout << "two_way_propagate_rec - is_changed: " << change << '\n';
  std::cout << "final map:\n";
  values.output(std::cout, ns);
#endif
  return change;
}

/*******************************************************************\

Function: constant_set_propagator_domaint::assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void constant_set_propagator_domaint::assign( // done: cross product propagation
  valuest &dest,
  const symbol_exprt &lhs,
  exprt rhs,
  const namespacet &ns) const
{
  std::set<irep_idt> dep_symbols;
  get_dep_exprs(rhs, dep_symbols);
  for(auto it = dep_symbols.begin(); it != dep_symbols.end();) {
    if(values.replace_const.expr_map.find(*it) == values.replace_const.expr_map.end())
      it = dep_symbols.erase(it);
    else
      ++it;
  }
  valuest single_values;
  single_values.set_to_bottom();
  std::vector<irep_idt> dep_symbols_list;
  std::vector<std::set<exprt>::const_iterator> iterator_list;
  std::vector<std::set<exprt>::const_iterator> begin_iterator_list;
  std::vector<std::set<exprt>::const_iterator> end_iterator_list;
  std::set<exprt> rhs_set;
  for(const irep_idt &e: dep_symbols) {
    dep_symbols_list.push_back(e);
    replace_symbol_sett::expr_mapt::const_iterator e1 = values.replace_const.expr_map.find(e);
    iterator_list.push_back(e1->second.begin());
    begin_iterator_list.push_back(e1->second.begin());
    end_iterator_list.push_back(e1->second.end());
    assert(begin_iterator_list.back() != end_iterator_list.back());
  }
  while(true) {
    for(unsigned int i = 0; i < iterator_list.size(); ++i) { // single valuation from crossed product
      single_values.set_to(dep_symbols_list[i], *(iterator_list[i]));
    }
    exprt rhs_copy = rhs;
    single_values.replace_const(rhs_copy);
    rhs_copy = simplify_expr(rhs_copy, ns);
    rhs_set.insert(rhs_copy);

    bool complete = true;
    for(unsigned int i = 0; i < iterator_list.size(); ++i) {
      ++iterator_list[i];
      if(iterator_list[i] == end_iterator_list[i]) {
        iterator_list[i] = begin_iterator_list[i];
      } else {
        complete = false;
        break;
      }
    }
    if(complete) break;
  }
  for(const irep_idt &e: dep_symbols) {
    replace_symbol_sett::expr_mapt::const_iterator e1 = dest.replace_const.expr_map.find(e);
    if(e1 != dest.replace_const.expr_map.end() && e1->second.size() > 1) dest.set_to_top(e);
  }
  dest.set_to(lhs, rhs_set);
}

/*******************************************************************\

Function: constant_set_propagator_domaint::valuest::is_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool constant_set_propagator_domaint::valuest::is_constant(const exprt &expr) const
{
  if(expr.id()==ID_side_effect &&
     to_side_effect_expr(expr).get_statement()==ID_nondet)
    return false;

  if(expr.id()==ID_side_effect &&
     to_side_effect_expr(expr).get_statement()==ID_malloc)
    return false;

  if(expr.id()==ID_symbol){
    replace_symbol_sett::expr_mapt::const_iterator f = replace_const.expr_map.find(to_symbol_expr(expr).get_identifier());
    if(f == replace_const.expr_map.end())
      return false;
  }

  if(expr.id()==ID_address_of)
    return is_constant_address_of(to_address_of_expr(expr).object());

  forall_operands(it, expr)
    if(!is_constant(*it))
      return false;

  return true;
}

/*******************************************************************\

Function: constant_set_propagator_domaint::valuest::is_constant_address_of

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool constant_set_propagator_domaint::valuest::is_constant_address_of(
  const exprt &expr) const
{
  if(expr.id()==ID_index)
    return is_constant_address_of(to_index_expr(expr).array()) &&
           is_constant(to_index_expr(expr).index());

  if(expr.id()==ID_member)
    return is_constant_address_of(to_member_expr(expr).struct_op());

  if(expr.id()==ID_dereference)
    return is_constant(to_dereference_expr(expr).pointer());

  if(expr.id()==ID_string_constant)
    return true;

  return true;
}

/*******************************************************************\

Function: constant_set_propagator_domaint::valuest::set_to_top

  Inputs:

 Outputs:

 Purpose: Do not call this when iterating over replace_const.expr_map!

\*******************************************************************/

bool constant_set_propagator_domaint::valuest::set_to_top(const irep_idt &id)
{
  bool result = false;

  replace_symbol_sett::expr_mapt::iterator r_it =
    replace_const.expr_map.find(id);

  if(r_it != replace_const.expr_map.end())
  {
    assert(!is_bottom);
    replace_const.expr_map.erase(r_it);
    result = true;
  }

  return result;
}

/*******************************************************************\

Function: constant_set_propagator_domaint::valuest::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void constant_set_propagator_domaint::valuest::output( // ranadeep
  std::ostream &out,
  const namespacet &ns) const
{
  out << "const map:\n";

  if(is_bottom)
    out << "  bottom\n";

  for(replace_symbol_sett::expr_mapt::const_iterator
      it=replace_const.expr_map.begin();
      it!=replace_const.expr_map.end();
      ++it){
    out << ' ' << it->first << "= { ";

    for(auto e: it->second) // ranadeep - todo: clean up code!
      out << from_expr(ns, "", e) << ' ';
    out << "}\n";
  }
}

/*******************************************************************\

Function: constant_set_propagator_domaint::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void constant_set_propagator_domaint::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  values.output(out, ns);
}

/*******************************************************************\

Function: constant_set_propagator_domaint::valuest::merge

  Inputs:

 Outputs: Return true if "this" has changed.

 Purpose: join

\*******************************************************************/

bool constant_set_propagator_domaint::valuest::merge(const valuest &src)
{
  // nothing to do
  if(src.is_bottom)
    return false;

  // just copy
  if(is_bottom)
  {
    replace_const = src.replace_const;
    is_bottom = src.is_bottom;
    return true;
  }

  bool changed = false;


  // set everything to top that is not in src
  for(replace_symbol_sett::expr_mapt::const_iterator
        it=replace_const.expr_map.begin();
      it!=replace_const.expr_map.end();
      ) // no it++
  {
    if(src.replace_const.expr_map.find(it->first) ==
       src.replace_const.expr_map.end())
    {
      //cannot use set_to_top here
      replace_const.expr_map.erase(it++);
      changed = true;
    }
    else ++it;
  }

  std::vector<replace_symbol_sett::expr_mapt::iterator> subset, superset, incomparable, to_top;

  for(replace_symbol_sett::expr_mapt::const_iterator
      it=src.replace_const.expr_map.begin();
      it!=src.replace_const.expr_map.end();
      ++it)
  {
    replace_symbol_sett::expr_mapt::iterator
      c_it = replace_const.expr_map.find(it->first);

    if(c_it != replace_const.expr_map.end())
    {
      std::set<exprt> new_set;
      std::set_union(it->second.begin(), it->second.end(),
                     c_it->second.begin(), c_it->second.end(),
                     std::inserter(new_set, new_set.begin()));

      unsigned int new_elems, new_elems_c;
      new_elems = new_set.size() - it->second.size();
      new_elems_c = new_set.size() - c_it->second.size();
      if(new_elems == 0 && new_elems_c == 0) // equal
      {
      }
      else if(new_elems_c == 0 && new_elems > 0) // superset
      {
        superset.push_back(c_it);
      }
      else if(new_elems == 0 && new_elems_c > 0) // subset
      {
        subset.push_back(c_it);
        c_it->second = it->second;
      }
      else // incomparable
      {
        if(new_set.size() > limit)
        {
          to_top.push_back(c_it);
        }
        else
        {
          incomparable.push_back(c_it);
        }
        c_it->second = new_set;
      }
    }
  }

  if(superset.size() > 0 && superset.size() >= subset.size())
  {
    if(subset.size() || incomparable.size()) changed = true; // changed if subset and incomparable is removed
    for(replace_symbol_sett::expr_mapt::iterator e: subset)
      replace_const.expr_map.erase(e);
    for(replace_symbol_sett::expr_mapt::iterator e: incomparable)
      replace_const.expr_map.erase(e);
  }
  else if(subset.size() > 0 && subset.size() >= superset.size())
  {
    changed = true; // has at least one subset-key which is changed
    for(replace_symbol_sett::expr_mapt::iterator e: superset)
      replace_const.expr_map.erase(e);
    for(replace_symbol_sett::expr_mapt::iterator e: incomparable)
      replace_const.expr_map.erase(e);
  }
  else if(incomparable.size() >= 1 && 1 >= subset.size() && 1 >= superset.size())
  {
    changed = true; // has at least one incomparable-key which is changed
    for(replace_symbol_sett::expr_mapt::iterator e: superset)
      replace_const.expr_map.erase(e);
    for(replace_symbol_sett::expr_mapt::iterator e: subset)
      replace_const.expr_map.erase(e);
    incomparable.pop_back();
    for(replace_symbol_sett::expr_mapt::iterator e: incomparable)
      replace_const.expr_map.erase(e);
  }

  if(to_top.size() > 0) changed = true;
  for(replace_symbol_sett::expr_mapt::iterator e: to_top) {
    replace_const.expr_map.erase(e);
  }



#ifdef DEBUG
  std::cout << "merged: " << changed << '\n';
#endif

  return changed;
}

/*******************************************************************\

Function: constant_set_propagator_domaint::valuest::meet

  Inputs:

 Outputs: Return true if "this" has changed.

 Purpose: meet

\*******************************************************************/

bool constant_set_propagator_domaint::valuest::meet(const valuest &src)  // ranadeep : done
{
  if(src.is_bottom || is_bottom)
    return false;

  bool changed = false;

  for(const auto &src_replace_pair : src.replace_const.expr_map)
  {
    replace_symbol_sett::expr_mapt::iterator c_it=
      replace_const.expr_map.find(src_replace_pair.first);

    if(c_it != replace_const.expr_map.end())
    {
      // if(c_it->second != it->second)
      // {
      //   set_to_bottom();
      //   changed = true;
      //   break;
      // }

      std::set<exprt> new_set;
      std::set_intersection(src_replace_pair.second.begin(), src_replace_pair.second.end(),
                            c_it->second.begin(), c_it->second.end(),
                            std::inserter(new_set, new_set.begin()));

      if(new_set.empty())
      {
        set_to_bottom();
        changed = true;
        break;
      }

      if(new_set.size() != c_it->second.size())
      {
        c_it->second = new_set;
        changed = true;
      }
    }
    else
    {
      // set_to(it->first, it->second);
      replace_const.expr_map[src_replace_pair.first] = src_replace_pair.second;
      changed = true;
    }
  }

  return changed;
}

/*******************************************************************\

Function: constant_set_propagator_domaint::valuest::is_equal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool constant_set_propagator_domaint::valuest::is_equal(const valuest &src)
{
  // return false;
  if(replace_const.expr_map.size() != src.replace_const.expr_map.size()) return false;
  for(const auto &src_replace_pair : src.replace_const.expr_map) {
    replace_symbol_sett::expr_mapt::iterator c_it=
      replace_const.expr_map.find(src_replace_pair.first);
    if(c_it == replace_const.expr_map.end()) return false;
    if(c_it->second != src_replace_pair.second) return false;
  }
  return true;
}

/*******************************************************************\

Function: constant_set_propagator_domaint::merge

  Inputs:

 Outputs: Return true if "this" has changed.

 Purpose:

\*******************************************************************/

bool constant_set_propagator_domaint::merge(
  const constant_set_propagator_domaint &other,
  locationt from,
  locationt to)
{
  return values.merge(other.values);
}

/*******************************************************************\

Function: constant_set_propagator_domaint::is_equal

  Inputs:

 Outputs: Return true if "this" has changed.

 Purpose:

\*******************************************************************/

bool constant_set_propagator_domaint::is_equal (
  locationt l,
  const ai_baset &ai)
{
  return is_equal(static_cast<const constant_set_propagator_ait &>(ai)[l]);
}

/*******************************************************************\

Function: constant_set_propagator_domaint::is_equal

  Inputs:

 Outputs: Return true if "this" has changed.

 Purpose:

\*******************************************************************/

bool constant_set_propagator_domaint::is_equal (
  const constant_set_propagator_domaint &other)
{
  return values.is_equal(other.values);
}

/*******************************************************************\

Function: constant_set_propagator_domaint::get_dep_exprs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void constant_set_propagator_domaint::get_dep_exprs(
  exprt &expr,
  std::set<irep_idt> &dep_exprs_set) const
{
  if(expr.id()==ID_symbol)
    dep_exprs_set.insert(expr.get(ID_identifier));
  else
    Forall_operands(it, expr)
      get_dep_exprs(*it, dep_exprs_set);
}

/*******************************************************************\

Function: constant_set_propagator_ait::replace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void constant_set_propagator_ait::replace(
  goto_functionst &goto_functions,
  const namespacet &ns)
{
  Forall_goto_functions(f_it, goto_functions)
    replace(f_it->second, ns);
}

/*******************************************************************\

Function: constant_set_propagator_ait::get_dep_exprs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void constant_set_propagator_ait::get_dep_exprs(
  exprt &expr,
  std::set<irep_idt> &dep_exprs_set)
{
  if(expr.id()==ID_symbol)
    dep_exprs_set.insert(expr.get(ID_identifier));
  else
    Forall_operands(it, expr)
      get_dep_exprs(*it, dep_exprs_set);
}


/*******************************************************************\

Function: constant_set_propagator_ait::replace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void constant_set_propagator_ait::replace(
  goto_functionst::goto_functiont &goto_function,
  const namespacet &ns)
{
  goto_programt &body = goto_function.body;
  Forall_goto_program_instructions(it, body)
  {
    state_mapt::iterator s_it = merged_state_map.find(it);

    if(s_it == merged_state_map.end())
      continue;

    replace_types_rec(s_it->second.values.replace_const, it->code);
    replace_types_rec(s_it->second.values.replace_const, it->guard);

    std::set<irep_idt> dep_exprs_set;

    if(it->is_goto() || it->is_assume() || it->is_assert())
    {
      s_it->second.values.replace_const(it->guard);
      it->guard = simplify_expr(it->guard, ns);
      get_dep_exprs(it->guard, dep_exprs_set);
    }
    else if(it->is_assign())
    {
      exprt &rhs = to_code_assign(it->code).rhs();
      s_it->second.values.replace_const(rhs);
      rhs = simplify_expr(rhs, ns);
      get_dep_exprs(rhs, dep_exprs_set);
    }
    else if(it->is_function_call())
    {
      s_it->second.values.replace_const(
        to_code_function_call(it->code).function());
      simplify_expr(to_code_function_call(it->code).function(), ns);

      exprt::operandst &args =
        to_code_function_call(it->code).arguments();

      for(exprt::operandst::iterator o_it = args.begin();
          o_it != args.end(); ++o_it)
      {
        s_it->second.values.replace_const(*o_it);
        *o_it = simplify_expr(*o_it, ns);
        get_dep_exprs(*o_it, dep_exprs_set);
      }
    }
    else if(it->is_return()) {
      exprt &return_value = to_code_return(it->code).return_value();
      s_it->second.values.replace_const(return_value);
      return_value = simplify_expr(return_value, ns);
      get_dep_exprs(return_value, dep_exprs_set);
    }
    else if(it->is_other())
    {
      if(it->code.get_statement()==ID_expression)
      {
        s_it->second.values.replace_const(it->code);
        // get_dep_exprs(it->code);
      }
    }
    else;

    if(dep_exprs_set.size() > 0 && s_it->second.values.replace_const.expr_map.size() > 0) {
      exprt assume_st;
      bool empty_and = true;
      for(auto e : s_it->second.values.replace_const.expr_map) {
        std::set<irep_idt>::iterator it = dep_exprs_set.find(e.first);
        if(it == dep_exprs_set.end()) continue;
        exprt symb = ns.lookup(e.first).symbol_expr();
        exprt or_st;
        bool empty_or = true;
        if(e.second.size() < 2) continue;
        for(auto e1 : e.second) {
          if(empty_or) {
            or_st = equal_exprt(symb, e1);
            empty_or = false;
          } else {
            or_st = or_exprt(or_st, equal_exprt(symb, e1));
          }
        }
        if(!empty_or){
          if(empty_and) {
            assume_st = or_st;
            empty_and = false;
          } else {
            assume_st = and_exprt(assume_st, or_st);
          }
        }
      }
      if(!empty_and){
        body.insert_before_swap(it);
        it->make_assumption(assume_st);
      }
    }
  }
}

/*******************************************************************\

Function: constant_set_propagator_ait::replace_types_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void constant_set_propagator_ait::replace_types_rec(
  const replace_symbol_sett &replace_const,
  exprt &expr)
{
  replace_const(expr.type());

  Forall_operands(it, expr)
    replace_types_rec(replace_const, *it);
}


bool constant_set_propagator_ait::is_cached(const goto_functionst::function_mapt::const_iterator f_it) {
  #ifdef DEBUG
    std::cout << "checking if cached\n";
  #endif
  if(state_cache.find(f_it->first) == state_cache.end()) return false;

  locationt l_begin = f_it->second.body.instructions.begin();
  for(auto e: state_cache[f_it->first]) {
  #ifdef DEBUG
    std::cout << "found some caches\n";
  #endif
    if(e.first.is_equal(l_begin, *this)) return true;
  }
  return false;
}


void constant_set_propagator_ait::summarize_from_cache(const goto_functionst::function_mapt::const_iterator f_it) {
  #ifdef DEBUG
    std::cout << "reusing cache\n";
  #endif
  assert(state_cache.find(f_it->first) != state_cache.end());
  locationt l_begin = f_it->second.body.instructions.begin();
  locationt l_end = --f_it->second.body.instructions.end();
  locationt last_call = get_top_function_call_location_from_stack();
  exprt lhs = to_code_function_call(last_call->code).lhs();
  if(!lhs.is_not_nil()) return;
  assert(l_end->is_end_function());
  std::pair<constant_set_propagator_domaint, std::set<exprt>> matched_context;
  for(auto e: state_cache[f_it->first]) {
    if(e.first.is_equal(l_begin, *this)) {
      matched_context = e;
      break;
    }
  }
  std::unique_ptr<statet> tmp_state(make_temporary_state(get_state(l_begin)));
  static_cast<constant_set_propagator_domaint &>(*tmp_state).set_to(to_symbol_expr(lhs), matched_context.second);

  merge(*tmp_state, l_begin, l_end);
    #ifdef DEBUG
    std::cout << "reusing cache till end\n";
  #endif
}


void constant_set_propagator_ait::put_new_in_cache(const goto_functionst::function_mapt::const_iterator f_it) {
  #ifdef DEBUG
    std::cout << "storing in cache\n";
  #endif
  locationt last_call = get_top_function_call_location_from_stack();
  exprt lhs = to_code_function_call(last_call->code).lhs();
  if(!lhs.is_not_nil()) return;
  locationt l_begin = f_it->second.body.instructions.begin();
  locationt l_end = --f_it->second.body.instructions.end();
  std::pair<constant_set_propagator_domaint, std::set<exprt>> p;
    state_mapt::iterator s_it = state_map.find(l_begin);
    if(s_it == state_map.end()) return;
  p.first = s_it->second;
  p.second = s_it->second.values.replace_const.expr_map[to_symbol_expr(lhs).get_identifier()];
  state_cache[f_it->first].push_back(p);
}