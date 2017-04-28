/*******************************************************************\

Module: Constant propagation

Author: Peter Schrammel, Ranadeep

\*******************************************************************/

#ifndef CPROVER_ANALYSES_CONSTANT_SET_PROPAGATOR_H
#define CPROVER_ANALYSES_CONSTANT_SET_PROPAGATOR_H

#include "ai.h"

#include "replace_symbol_set_ext.h"

#include <iostream>
#include <chrono>

class constant_set_propagator_domaint:public ai_domain_baset
{
public:
  void transform(
    locationt,
    locationt,
    ai_baset &,
    const namespacet &) final;
  void transform_with_summary (
      locationt from,
      locationt to,
      ai_baset &ai,
      const namespacet &ns,
      bool use_merged_summary);
  void output(
    std::ostream &,
    const ai_baset &,
    const namespacet &) const final;
  void make_top() final { values.set_to_top(); }
  void make_bottom() final { values.set_to_bottom(); }
  void make_entry() final { values.set_to_top(); }
  bool merge(const constant_set_propagator_domaint &, locationt, locationt);
  bool is_equal(const constant_set_propagator_domaint &);
  bool is_equal (locationt, const ai_baset &);
  void get_dep_exprs(exprt &, std::set<irep_idt> &) const;
  void set_to(const symbol_exprt &lhs, const std::set<exprt> &rhs_vals)
  {
    values.set_to(lhs.get_identifier(), rhs_vals);
  }
  bool is_in_loop(locationt , ai_baset &);


  struct valuest
  {
  public:
    unsigned int limit = 10;
    valuest():is_bottom(true) { }

    // maps variables to constants
    replace_symbol_set_extt replace_const; // ranadeep
    bool is_bottom;

    void output(std::ostream &, const namespacet &) const;

    bool merge(const valuest &src);
    bool meet(const valuest &src);
    bool is_equal(const valuest &src);

    void set_to_bottom()
    {
      replace_const.clear();
      is_bottom = true;
    }

    void set_to(const irep_idt &lhs_id, const exprt &rhs_val)
    {
      replace_const.expr_map[lhs_id].clear();
      replace_const.expr_map[lhs_id].insert(rhs_val); // ranadeep
      is_bottom = false;
    }

    void set_to(const symbol_exprt &lhs, const exprt &rhs_val)
    {
      set_to(lhs.get_identifier(), rhs_val);
    }

    void set_to(const irep_idt &lhs_id, const std::set<exprt> &rhs_vals)
    {
      if(rhs_vals.size() > 0){
        replace_const.expr_map[lhs_id].clear();
        replace_const.expr_map[lhs_id].insert(rhs_vals.begin(), rhs_vals.end()); // ranadeep
        is_bottom = false;
      }
    }

    void set_to(const symbol_exprt &lhs, const std::set<exprt> &rhs_vals)
    {
      set_to(lhs.get_identifier(), rhs_vals);
    }

    bool is_constant(const exprt &expr) const;
    bool is_constant_address_of(const exprt &expr) const;
    bool set_to_top(const irep_idt &id);

    bool set_to_top(const symbol_exprt &expr)
    {
      return set_to_top(expr.get_identifier());
    }

    void set_to_top()
    {
      replace_const.clear();
      is_bottom = false;
    }
  };

  valuest values;

private:
  void assign(
    valuest &dest,
    const symbol_exprt &lhs,
    exprt rhs,
    const namespacet &ns) const;

  void assign_rec(
    valuest &values,
    const exprt &lhs,
    const exprt &rhs,
    const namespacet &ns);

  bool two_way_propagate_rec(
    const exprt &expr,
    const namespacet &ns);
};

class constant_set_propagator_ait:public ait<constant_set_propagator_domaint>
{
public:
  constant_set_propagator_ait(
    goto_functionst &goto_functions,
    const namespacet &ns)
  {
    std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();

    operator()(goto_functions, ns);
    replace(goto_functions, ns);

    std::chrono::steady_clock::time_point end= std::chrono::steady_clock::now();
    long elapsed_dur = std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count();
    double elapsed_ = elapsed_dur * 0.000001;
    std::cout << "constant set propagator took " << elapsed_ << "s\n";
  }

  constant_set_propagator_ait(
    goto_functionst::goto_functiont &goto_function,
    const namespacet &ns)
  {
    operator()(goto_function, ns);
    replace(goto_function, ns);
  }

  bool is_cached(const goto_functionst::function_mapt::const_iterator f_it) override;
  void summarize_from_cache(const goto_functionst::function_mapt::const_iterator f_it) override;
  void put_new_in_cache(const goto_functionst::function_mapt::const_iterator f_it) override;

  typedef std::unordered_map<irep_idt, std::vector<std::pair<constant_set_propagator_domaint, std::set<exprt>>>, irep_id_hash> state_cachet;
  state_cachet state_cache;

  typedef std::set<locationt> loophead_listt;
  loophead_listt loophead_list;

protected:
  void get_dep_exprs(
    exprt &,
    std::set<irep_idt> &);

  void replace(
    goto_functionst::goto_functiont &,
    const namespacet &);

  void replace(
    goto_functionst &,
    const namespacet &);

  void replace_types_rec(
    const replace_symbol_sett &replace_const,
    exprt &expr);
};

#endif // CPROVER_ANALYSES_CONSTANT_SET_PROPAGATOR_H
