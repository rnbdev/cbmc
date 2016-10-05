/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

 \*******************************************************************/

#ifndef CEGIS_REFACTOR_INSTRUCTIONSET_CREATE_CEGIS_PROCESSOR_H_
#define CEGIS_REFACTOR_INSTRUCTIONSET_CREATE_CEGIS_PROCESSOR_H_

#include <set>

#include <util/type.h>
#include <goto-programs/goto_program.h>

/**
 * @brief
 *
 * @details
 *
 * @param first
 * @param last
 *
 * @return
 */
std::set<typet> collect_context_types(
    goto_programt::const_targett first,
    const goto_programt::const_targett &last);

/**
 * @brief
 *
 * @details
 *
 * @param state_types
 * @param var_slots_per_state_type
 * @param context_types
 */
void create_cegis_processor(
    const std::set<typet> &state_types,
    size_t var_slots_per_state_type,
    const std::set<typet> &context_types);

#endif /* CEGIS_REFACTOR_INSTRUCTIONSET_CREATE_CEGIS_PROCESSOR_H_ */