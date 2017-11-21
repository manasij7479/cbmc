/*******************************************************************\

Module: Z3 C++ API Backend

Author: Manasij Mukherjee, manasij7479@gmail.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SMT2_Z3_CONV_H
#define CPROVER_SOLVERS_SMT2_Z3_CONV_H

#include <fstream>
#include <set>

#include <util/hash_cont.h>
#include <util/std_expr.h>
#include <util/byte_operators.h>

#include <solvers/prop/prop_conv.h>
#include <solvers/flattening/boolbv_width.h>
#include <solvers/flattening/pointer_logic.h>
#include <z3++.h>

class typecast_exprt;
class constant_exprt;
class index_exprt;
class member_exprt;

class z3_convt:public prop_convt
{
public:
  z3_convt(
    const namespacet &_ns):
    prop_convt(_ns),
    solver(context),
    store(context),
    out("/tmp/test"),
    ns(_ns) {}

  virtual ~z3_convt() { }
  resultt dec_solve() {
    // out << "CHECK-SAT" << std::endl;;
    auto result = solver.check();
    // out << "MODEL : " << solver.get_model() << std::endl;
    switch(result) {
    case z3::unsat:   return D_UNSATISFIABLE;
    case z3::sat:     return D_SATISFIABLE;
    default: return D_ERROR;
    }
  }

  // overloading interfaces
  virtual literalt convert(const exprt &expr) {
    // out << "convert : " <<from_expr(ns, " ", expr) << "\n";
    throw 1;
  }
  virtual void set_frozen(literalt a) { /* not needed */ }
  virtual void set_to(const exprt &expr, bool value) {
    // out << "set to : " <<from_expr(ns, " ", expr) << " : " << value << "\n";
    z3::expr result = convert_expr(expr);
    if (value) {
      solver.add(result);
      out << "(assert " << result << " )\n`";
    } else {
      solver.add(!result);
    }
  }
  virtual exprt get(const exprt &expr) const;
  virtual std::string decision_procedure_text() const { return "Z3/CPP-API"; }
  virtual void print_assignment(std::ostream &out) const {}
  virtual tvt l_get(literalt l) const {
    throw 2;
  }
  virtual void set_assumptions(const bvt &bv) { assumptions=bv; throw 3;}

  // new stuff
  z3::expr convert_expr(const exprt &) const ;
  // z3::expr convert_literal(const literalt);

  void new_context() {
    solver.push();
  }
  void pop_context() {
    solver.pop(1);
  }

protected:
  mutable z3::context context;
  z3::solver solver;

  bool exists(const irep_idt &id) const {
    return map.find(id) != map.end();
  }
  z3::expr fetch(const irep_idt &id) const {
    return store[map[id]];
  }
  mutable std::unordered_map<irep_idt, int, irep_id_hash> map;
  mutable z3::expr_vector store;

  bvt assumptions;
  mutable std::ofstream out;
  const namespacet &ns;
};

#endif // CPROVER_SOLVERS_SMT2_SMT2_CONV_H
