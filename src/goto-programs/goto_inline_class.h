/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_INLINE_CLASS_H
#define CPROVER_GOTO_PROGRAMS_GOTO_INLINE_CLASS_H

#include <util/message.h>

#include "goto_functions.h"

class goto_inlinet:public messaget
{
public:
  goto_inlinet(
    goto_functionst &_goto_functions,
    const namespacet &_ns,
    message_handlert &_message_handler):
    messaget(_message_handler),
    smallfunc_limit(0),
    goto_functions(_goto_functions),
    ns(_ns),
    is_recursion_detected(false)
  {
  }
  
  void operator()();
  void goto_inline(goto_programt &dest);

  void goto_inline_rec(
    goto_functionst::function_mapt::iterator,
    bool full);

  void goto_inline_rec(goto_programt &dest, bool full);
  
  // inline single instruction at 'target'
  // returns true in case a change was done
  // set 'full' to perform this recursively
  bool inline_instruction(
    goto_programt &dest,
    bool full,
    goto_programt::targett &target);

  bool recursion_detected() { return is_recursion_detected; }

  unsigned smallfunc_limit; 

protected:
  goto_functionst &goto_functions;
  const namespacet &ns;
  bool is_recursion_detected;
  
  void expand_function_call(
    goto_programt &dest,
    goto_programt::targett &target,
    const exprt &lhs,
    const symbol_exprt &function,
    const exprt::operandst &arguments,
    const exprt &constrain,
    bool recursive);
    
  void replace_return(
    goto_programt &body,
    const exprt &lhs,
    const exprt &constrain);
    
  void parameter_assignments(
    const source_locationt &source_location,
    const irep_idt &function_name,
    const code_typet &code_type,
    const exprt::operandst &arguments,
    goto_programt &dest);

  void parameter_destruction(
    const source_locationt &source_location,
    const irep_idt &function_name,
    const code_typet &code_type,
    goto_programt &dest);

  typedef hash_set_cont<irep_idt, irep_id_hash> recursion_sett;
  recursion_sett recursion_set;
  
  typedef hash_set_cont<irep_idt, irep_id_hash> no_body_sett;
  no_body_sett no_body_set;

  typedef hash_set_cont<irep_idt, irep_id_hash> finished_inlining_sett;
  finished_inlining_sett finished_inlining_set;
};

#endif // CPROVER_GOTO_PROGRAMS_GOTO_INLINE_CLASS_H
