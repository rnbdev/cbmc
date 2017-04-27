/*******************************************************************\

Module: Abstract Interpretation

Author: Daniel Kroening, kroening@kroening.com, Ranadeep

\*******************************************************************/

#include <cassert>
#include <memory>

#include <util/std_expr.h>
#include <util/std_code.h>

#include "is_threaded.h"

#include "ai.h"

// #define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: ai_baset::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_baset::output(
  const namespacet &ns,
  const goto_functionst &goto_functions,
  std::ostream &out) const
{
  forall_goto_functions(f_it, goto_functions)
  {
    if(f_it->second.body_available())
    {
      out << "////\n";
      out << "//// Function: " << f_it->first << "\n";
      out << "////\n";
      out << "\n";

      output(ns, f_it->second.body, f_it->first, out);
    }
  }
}

/*******************************************************************\

Function: ai_baset::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_baset::output(
  const namespacet &ns,
  const goto_programt &goto_program,
  const irep_idt &identifier,
  std::ostream &out) const
{
  forall_goto_program_instructions(i_it, goto_program)
  {
    out << "**** " << i_it->location_number << " "
        << i_it->source_location << "\n";

    // find_state(i_it).output(out, *this, ns);
    find_merged_state(i_it).output(out, *this, ns); // ranadeep
    out << "\n";
    #if 1
    goto_program.output_instruction(ns, identifier, out, i_it);
    out << "\n";
    #endif
  }
}

/*******************************************************************\

Function: ai_baset::entry_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_baset::entry_state(const goto_functionst &goto_functions)
{
  // find the 'entry function'

  goto_functionst::function_mapt::const_iterator
    f_it=goto_functions.function_map.find(goto_functions.entry_point());

  if(f_it!=goto_functions.function_map.end())
    entry_state(f_it->second.body);
}

/*******************************************************************\

Function: ai_baset::entry_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_baset::entry_state(const goto_programt &goto_program)
{
  // The first instruction of 'goto_program' is the entry point
  get_state(goto_program.instructions.begin()).make_entry();
  get_merged_state(goto_program.instructions.begin()).make_entry();
}

/*******************************************************************\

Function: ai_baset::initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_baset::initialize(const goto_functionst::goto_functiont &goto_function)
{
  initialize(goto_function.body);
}

/*******************************************************************\

Function: ai_baset::initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_baset::initialize(const goto_programt &goto_program)
{
  // we mark everything as unreachable as starting point

  forall_goto_program_instructions(i_it, goto_program)
    get_state(i_it).make_bottom();
}

/*******************************************************************\

Function: ai_baset::initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_baset::initialize(const goto_functionst &goto_functions)
{
  forall_goto_functions(it, goto_functions)
    initialize(it->second);
}

/*******************************************************************\

Function: ai_baset::get_next

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

ai_baset::locationt ai_baset::get_next(
  working_sett &working_set)
{
  assert(!working_set.empty());

  working_sett::iterator i=working_set.begin();
  locationt l=i->second;
  working_set.erase(i);

  return l;
}

/*******************************************************************\

Function: ai_baset::fixedpoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ai_baset::fixedpoint(
  const goto_programt &goto_program,
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  working_sett working_set;

  // Put the first location in the working set
  if(!goto_program.empty())
    put_in_working_set(
      working_set,
      goto_program.instructions.begin());

  bool new_data=false;

  while(!working_set.empty())
  {
    locationt l=get_next(working_set);

    if(visit(l, working_set, goto_program, goto_functions, ns))
      new_data=true;
  }

  return new_data;
}

/*******************************************************************\

Function: ai_baset::visit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ai_baset::visit(
  locationt l,
  working_sett &working_set,
  const goto_programt &goto_program,
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  bool new_data=false;

  statet &current=get_state(l);

  goto_programt::const_targetst successors;

  goto_program.get_successors(l, successors);

  #ifdef DEBUG
  for(const auto &to_l : successors) {
      std::cout << l->location_number << " --> " << to_l->location_number;
      std::cout << " : is backwards_goto -- " << to_l->is_backwards_goto() << "\n";
      std::cout << " : is goto -- " << to_l->is_goto() << "\n";
  }
  #endif

  for(const auto &to_l : successors)
  {
    if(to_l==goto_program.instructions.end())
      continue;

    std::unique_ptr<statet> tmp_state(
      make_temporary_state(current));

    statet &new_values=*tmp_state;

    bool have_new_values=false;

    if(l->is_function_call() &&
       !goto_functions.function_map.empty())
    {
      // this is a big special case
      const code_function_callt &code=
        to_code_function_call(l->code);

      if(do_function_call_rec(
          l, to_l,
          code.function(),
          code.arguments(),
          goto_functions, ns))
        have_new_values=true;
    }
    else
    {
      // initialize state, if necessary
      get_state(to_l);
      get_merged_state(to_l);

      new_values.transform(l, to_l, *this, ns);
      #ifdef DEBUG
      std::cout << "inside visit -- before merge\n";
      get_state(to_l).output(std::cout, *this, ns);
      new_values.output(std::cout, *this, ns);
      #endif
      if(merge(new_values, l, to_l))
        have_new_values=true;
      #ifdef DEBUG
      std::cout << "inside visit -- after merge " << have_new_values << "\n";
      get_state(to_l).output(std::cout, *this, ns);
      #endif
    }

    if(have_new_values)
    {
      new_data=true;
      put_in_working_set(working_set, to_l);
    }
  }

  return new_data;
}

/*******************************************************************\

Function: ai_baset::do_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ai_baset::do_function_call(
  locationt l_call, locationt l_return,
  const goto_functionst &goto_functions,
  const goto_functionst::function_mapt::const_iterator f_it,
  const exprt::operandst &arguments,
  const namespacet &ns)
{
  #ifdef DEBUG
    std::cout << "inside do_function_call\n";
  #endif
  // initialize state, if necessary
  get_state(l_return);
  get_merged_state(l_return);

  const goto_functionst::goto_functiont &goto_function=
    f_it->second;

  if(!goto_function.body_available())
  {
    body_available = false;
    // if we don't have a body, we just do an edige call -> return
    std::unique_ptr<statet> tmp_state(make_temporary_state(get_state(l_call)));
    tmp_state->transform(l_call, l_return, *this, ns);

    body_available = true;
    return merge(*tmp_state, l_call, l_return);
  }

  assert(!goto_function.body.instructions.empty());

  // This is the edge from call site to function head.

  bool cached = false;
  {
    // get the state at the beginning of the function
    locationt l_begin=goto_function.body.instructions.begin();
    // initialize state, if necessary
    get_state(l_begin);

    // do the edge from the call site to the beginning of the function
    std::unique_ptr<statet> tmp_state(make_temporary_state(get_state(l_call)));
    tmp_state->transform(l_call, l_begin, *this, ns);


    bool new_data=false;

    forall_goto_program_instructions(i_it, f_it->second.body)
        get_state(i_it).make_bottom();

    // merge the new stuff
    if(merge(*tmp_state, l_call, l_begin))
      new_data=true;

    #ifdef DEBUG
    std::cout << "checking for cache for this\n";
    get_state(l_begin).output(std::cout, *this, ns);
    #endif
    // check if stored before
    cached = is_cached(f_it);

    // if not end skip to end
    if(!cached)
    {

    #ifdef DEBUG
      statet &func_begin = get_state(l_begin);
      std::cout << "new calling context\n";
      func_begin.output(std::cout, *this, ns);
    #endif

    // do we need to do/re-do the fixedpoint of the body?
    if(new_data)
      fixedpoint(goto_function.body, goto_functions, ns);
    }
    else
    {
    #ifdef DEBUG
      std::cout << "found cached context\n";
    #endif
    }
  }

  // This is the edge from function end to return site.

  {
    // get location at end of the procedure we have called
    locationt l_end=--goto_function.body.instructions.end();
    assert(l_end->is_end_function());

    // if cached before
    if(cached) {
      // transform l_end using old
      summarize_from_cache(f_it);
    }

    // do edge from end of function to instruction after call
    std::unique_ptr<statet> tmp_state(make_temporary_state(get_state(l_end)));
    tmp_state->transform(l_end, l_return, *this, ns);

    if(!cached) {
      // store it
      put_new_in_cache(f_it);
    }

    // Propagate those
    return merge(*tmp_state, l_end, l_return);
  }
}

/*******************************************************************\

Function: ai_baset::do_function_call_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ai_baset::do_function_call_rec(
  locationt l_call, locationt l_return,
  const exprt &function,
  const exprt::operandst &arguments,
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  assert(!goto_functions.function_map.empty());

  bool new_data=false;

  if(function.id()==ID_symbol)
  {
    const irep_idt &identifier=function.get(ID_identifier);

    if(recursion_set.find(identifier)!=recursion_set.end())
    {
      // recursion detected!
      return new_data;
    }
    else
    {
      recursion_set.insert(identifier);
      push_function_call_location_to_stack(l_call);
    }

    goto_functionst::function_mapt::const_iterator it=
      goto_functions.function_map.find(identifier);

    if(it==goto_functions.function_map.end())
      throw "failed to find function "+id2string(identifier);

    new_data=do_function_call(
      l_call, l_return,
      goto_functions,
      it,
      arguments,
      ns);

    recursion_set.erase(identifier);
    pop_function_call_location_from_stack();
  }
  else if(function.id()==ID_if)
  {
    if(function.operands().size()!=3)
      throw "if has three operands";

    bool new_data1=
      do_function_call_rec(
        l_call, l_return,
        function.op1(),
        arguments,
        goto_functions,
        ns);

    bool new_data2=
      do_function_call_rec(
        l_call, l_return,
        function.op2(),
        arguments,
        goto_functions,
        ns);

    if(new_data1 || new_data2)
      new_data=true;
  }
  else if(function.id()==ID_dereference)
  {
    // We can't really do this here -- we rely on
    // these being removed by some previous analysis.
  }
  else if(function.id()=="NULL-object")
  {
    // ignore, can't be a function
  }
  else if(function.id()==ID_member || function.id()==ID_index)
  {
    // ignore, can't be a function
  }
  else
  {
    throw "unexpected function_call argument: "+
      function.id_string();
  }

  return new_data;
}

/*******************************************************************\

Function: ai_baset::sequential_fixedpoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_baset::sequential_fixedpoint(
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  goto_functionst::function_mapt::const_iterator
    f_it=goto_functions.function_map.find(goto_functions.entry_point());

  if(f_it!=goto_functions.function_map.end())
    fixedpoint(f_it->second.body, goto_functions, ns);
}

/*******************************************************************\

Function: ai_baset::concurrent_fixedpoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_baset::concurrent_fixedpoint(
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  sequential_fixedpoint(goto_functions, ns);

  is_threadedt is_threaded(goto_functions);

  // construct an initial shared state collecting the results of all
  // functions
  goto_programt tmp;
  tmp.add_instruction();
  goto_programt::const_targett sh_target=tmp.instructions.begin();
  statet &shared_state=get_state(sh_target);

  typedef std::list<std::pair<goto_programt const*,
                              goto_programt::const_targett> > thread_wlt;
  thread_wlt thread_wl;

  forall_goto_functions(it, goto_functions)
    forall_goto_program_instructions(t_it, it->second.body)
    {
      if(is_threaded(t_it))
      {
        thread_wl.push_back(std::make_pair(&(it->second.body), t_it));

        goto_programt::const_targett l_end=
          it->second.body.instructions.end();
        --l_end;

        merge_shared(shared_state, l_end, sh_target, ns);
      }
    }

  // now feed in the shared state into all concurrently executing
  // functions, and iterate until the shared state stabilizes
  bool new_shared=true;
  while(new_shared)
  {
    new_shared=false;

    for(const auto &wl_pair : thread_wl)
    {
      working_sett working_set;
      put_in_working_set(working_set, wl_pair.second);

      statet &begin_state=get_state(wl_pair.second);
      merge(begin_state, sh_target, wl_pair.second);

      while(!working_set.empty())
      {
        goto_programt::const_targett l=get_next(working_set);

        visit(l, working_set, *(wl_pair.first), goto_functions, ns);

        // the underlying domain must make sure that the final state
        // carries all possible values; otherwise we would need to
        // merge over each and every state
        if(l->is_end_function())
          new_shared|=merge_shared(shared_state, l, sh_target, ns);
      }
    }
  }
}
