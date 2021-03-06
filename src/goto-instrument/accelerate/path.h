#ifndef CPROVER_GOTO_INSTRUMENT_ACCELERATE_PATH_H
#define CPROVER_GOTO_INSTRUMENT_ACCELERATE_PATH_H

#include <iosfwd>
#include <list>

#include <util/std_expr.h>
#include <util/namespace.h>

#include <goto-programs/goto_program.h>

class path_nodet
{
public:
  path_nodet(goto_programt::targett &_loc) :
      loc(_loc),
      guard(nil_exprt())
  {
  }

  path_nodet(goto_programt::targett &_loc,
             const exprt &_guard) :
      loc(_loc),
      guard(_guard)
  {
  }

  void output(goto_programt &program, std::ostream &str);

  goto_programt::targett loc;
  const exprt guard;
};

typedef std::list<path_nodet> patht;
typedef std::list<patht> pathst;

void output_path(patht &path, goto_programt &program, namespacet &ns, std::ostream &str);

#endif // CPROVER_GOTO_INSTRUMENT_ACCELERATE_PATH_H
