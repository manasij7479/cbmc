/*******************************************************************\

Module: Z3 C++ API Backend

Author: Manasij Mukherjee, manasij7479@gmail.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SMT2_Z3_CONV_H
#define CPROVER_SOLVERS_SMT2_Z3_CONV_H

#include <fstream>
#include <set>

#include <util/hash_cont.h>
#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/byte_operators.h>
#include <ansi-c/string_constant.h>

#include <langapi/language_util.h>

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
    // model(context),
    store(context),
    lit_store(context),
    out("/tmp/test"),
    ns(_ns),
    no_boolean_variables(0) {}

  virtual ~z3_convt() {}
  resultt dec_solve() {
    // out << "CHECK-SAT" << std::endl;;
    // std::cout << solver.to_smt2() << std::endl;
    auto result = solver.check();
    // auto model = solver.get_model();
    // std::cout << "MODEL : " << solver.get_model() << std::endl;
    switch(result) {
    case z3::unsat:   return D_UNSATISFIABLE;
    case z3::sat:     return D_SATISFIABLE;
    default: return D_ERROR;
    }
  }

  // overloading interfaces
  virtual literalt convert(const exprt &expr);

  virtual void set_frozen(literalt a) { /* not needed */ }
  virtual void set_to(const exprt &expr, bool value) override
  {
    // std::cout << "set to : " << from_expr(expr) << " : " << value << "\n";
    if (value)
      solver.add(convert_expr(expr));
    else
      solver.add(!convert_expr(expr));
  }

  exprt get(const exprt &expr) const;
  std::string decision_procedure_text() const { return "Z3/CPP-API"; }
  virtual void print_assignment(std::ostream &out) const {}
  virtual tvt l_get(literalt l) const;
  virtual void set_assumptions(const bvt &bv) { assumptions=bv; throw 3;}

  // new stuff
  z3::expr convert_expr(const exprt &) const ;
  z3::expr convert_literal(const literalt) const;

  void new_context() {
    solver.push();
  }
  void pop_context() {
    solver.pop(1);
  }

protected:
  mutable z3::context context;
  z3::solver solver;
  // z3::model model;

  bool exists(const irep_idt &id) const {
    return map.find(id) != map.end();
  }
  z3::expr fetch(const irep_idt &id) const {
    return store[map[id]];
  }
  mutable std::unordered_map<irep_idt, int, irep_id_hash> map;
  mutable z3::expr_vector store;
  mutable std::unordered_map<std::string, int> lit_map;
  mutable z3::expr_vector lit_store;

  bvt assumptions;
  mutable std::ofstream out;
  const namespacet &ns;
  
  unsigned no_boolean_variables;
  // std::vector<bool> boolean_assignment;

  z3::sort convert_type(const typet &type) const;

  // specific expressions go here
  // void convert_byte_update(const byte_update_exprt &expr);
  // void convert_byte_extract(const byte_extract_exprt &expr);
  z3::expr convert_typecast(const typecast_exprt &expr) const;
  z3::expr convert_array(const array_exprt &expr) const;
  z3::expr convert_array_of(const array_of_exprt &expr) const;
  // void convert_floatbv_typecast(const floatbv_typecast_exprt &expr);
  // void convert_struct(const struct_exprt &expr);
  // void convert_union(const union_exprt &expr);
  // void convert_constant(const constant_exprt &expr);
  // void convert_relation(const exprt &expr);
  // void convert_is_dynamic_object(const exprt &expr);
  // void convert_plus(const plus_exprt &expr);
  // void convert_minus(const minus_exprt &expr);
  // void convert_div(const div_exprt &expr);
  // void convert_mult(const mult_exprt &expr);
  // void convert_rounding_mode_FPA(const exprt &expr);
  // void convert_floatbv_plus(const ieee_float_op_exprt &expr);
  // void convert_floatbv_minus(const ieee_float_op_exprt &expr);
  // void convert_floatbv_div(const ieee_float_op_exprt &expr);
  // void convert_floatbv_mult(const ieee_float_op_exprt &expr);
  // void convert_mod(const mod_exprt &expr);
  // void convert_member(const member_exprt &expr);
  // void convert_overflow(const exprt &expr);
  // void convert_update(const exprt &expr);
  z3::expr convert_with(const with_exprt &expr) const;
  z3::expr convert_index(const index_exprt &expr) const;

  exprt convert_z3_array(const z3::expr &expr, const array_typet &array_type) const;
  exprt convert_z3_expr(const z3::expr &expr, const typet &type) const;
};

#endif // CPROVER_SOLVERS_SMT2_SMT2_CONV_H
