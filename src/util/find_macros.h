/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_FIND_MACROS_H
#define CPROVER_UTIL_FIND_MACROS_H

#include "hash_cont.h"
#include "irep.h"

class exprt;
class namespacet;

typedef hash_set_cont<irep_idt, irep_id_hash> find_macros_sett;

void find_macros(
  const exprt &src,
  const namespacet &ns,
  find_macros_sett &dest);

#endif // CPROVER_UTIL_FIND_MACROS_H
