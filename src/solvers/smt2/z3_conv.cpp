/*******************************************************************\

Module: Z3 C++ API Backend

Author: Manasij Mukherjee, manasij7479@gmail.com

\*******************************************************************/

#include <cassert>

#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/i2string.h>
#include <util/fixedbv.h>
#include <util/pointer_offset_size.h>
#include <util/ieee_float.h>
#include <util/base_type.h>
#include <util/string2int.h>

#include <ansi-c/string_constant.h>

#include <langapi/language_util.h>

#include <solvers/flattening/boolbv_width.h>
#include <solvers/flattening/flatten_byte_operators.h>
#include <solvers/flattening/c_bit_field_replacement_type.h>
#include <solvers/floatbv/float_bv.h>

#include "z3_conv.h"

#include <sstream>
// using namespace z3;
// Mark different kinds of error condition
// General
#define UNREACHABLE throw "Supposidly unreachable location reached"
#define PARSERERROR(S) throw S

// Error checking the expression type
#define INVALIDEXPR(S) throw "Invalid expression: " S

// Unexpected types and other combination not implemented and not expected to be needed
#define UNEXPECTEDCASE(S) throw "Unexpected case: " S

// General todos
#define TODO(S) throw "TODO: " S

// /*******************************************************************

z3::expr z3_convt::convert_expr(const exprt &expr) const
{
  boolbv_widtht boolbv_width(ns);
  if (expr.id() == ID_constant)
  {
    const constant_exprt &ce = to_constant_expr(expr);

    if (ce.type().id() == ID_bool /*|| ce.type().id() == ID_c_bool*/)
    {
      if (from_expr(ns, " ", ce) == "TRUE")
      {
        return context.bool_val(true);
      }
      else
      {
        return context.bool_val(false);
      }
    }
    const typet &expr_type=ce.type();

    if(expr_type.id()==ID_unsignedbv ||
       expr_type.id()==ID_signedbv ||
       expr_type.id()==ID_bv ||
       expr_type.id()==ID_c_enum ||
       expr_type.id()==ID_c_enum_tag ||
       expr_type.id()==ID_c_bool ||
       expr_type.id()==ID_incomplete_c_enum ||
       expr_type.id()==ID_c_bit_field)
    {

      std::size_t width=boolbv_width(expr_type);

      // out << "(_ bv" << value
      //     << " " << width << ")";
      return context.bv_val(id2string(ce.get_value()).c_str(), width);
    }
    else
    {
      UNEXPECTEDCASE("NON-BOOL Constant : " + std::string(ce.type().id().c_str()) + " " + from_expr(ns, " ", expr));

    }
  }
  else if(expr.id()==ID_symbol)
  {
    irep_idt id=to_symbol_expr(expr).get_identifier();
    assert(id!=irep_idt());
    if (!exists(id)) {
      z3::expr new_expr(context);
      const auto& expr_type = expr.type();

      if (expr_type.id() == ID_bool)
      {
        new_expr = context.bool_const(id.c_str());
      }
      if(expr_type.id()==ID_unsignedbv ||
        expr_type.id()==ID_signedbv ||
        expr_type.id()==ID_bv ||
        expr_type.id()==ID_c_enum ||
        expr_type.id()==ID_c_enum_tag ||
        expr_type.id()==ID_c_bool ||
        expr_type.id()==ID_incomplete_c_enum ||
        expr_type.id()==ID_c_bit_field)
      {
        std::size_t width=boolbv_width(expr_type);
        new_expr = context.bv_const(id.c_str(), width);
      }

      store.push_back(new_expr);
      map[id] = store.size() - 1;
    }
    return fetch(id);
  }
  else if(expr.id()==ID_if)
  {
    assert(expr.operands().size()==3);
    return ite(
    convert_expr(expr.op0()),
    convert_expr(expr.op1()),
    convert_expr(expr.op2()));
  }
  else if(expr.id()==ID_and)
  {
    assert(expr.type().id()==ID_bool);
    assert(expr.operands().size()>=2);
    z3::expr result = convert_expr(expr.op0());
    for (int i = 1; i < expr.operands().size(); ++i)
    {
      result = result && convert_expr(expr.operands()[i]);
    }
    return result;
  }
  else if(expr.id()==ID_or)
  {
    assert(expr.type().id()==ID_bool);
    assert(expr.operands().size()>=2);
    z3::expr result = convert_expr(expr.op0());
    for (int i = 1; i < expr.operands().size(); ++i)
    {
      result = result || convert_expr(expr.operands()[i]);
    }
    return result;
  }
  else if(expr.id()==ID_xor)
  {
    assert(expr.type().id()==ID_bool);
    assert(expr.operands().size()>=2);
    z3::expr result = convert_expr(expr.op0());
    for (int i = 1; i < expr.operands().size(); ++i)
    {
      result = result ^ convert_expr(expr.operands()[i]);
    }
    return result;
  }
  else if(expr.id()==ID_implies)
  {
    assert(expr.type().id()==ID_bool);
    assert(expr.operands().size()==2);

    return implies
    (convert_expr(expr.op0()),
     convert_expr(expr.op1()));
  }
  else if(expr.id()==ID_not)
  {
    assert(expr.type().id()==ID_bool);
    assert(expr.operands().size()==1);
    return !convert_expr(expr.op0());;
  }
  else if(expr.id()==ID_equal)
  {
    assert(expr.operands().size()==2);
    assert(base_type_eq(expr.op0().type(), expr.op1().type(), ns));

    return convert_expr(expr.op0())
           == convert_expr(expr.op1());
  }
  else if(expr.id()==ID_notequal)
  {
    assert(expr.operands().size()==2);
    assert(base_type_eq(expr.op0().type(), expr.op1().type(), ns));
    return convert_expr(expr.op0())
           != convert_expr(expr.op1());
  }
  else if (expr.id()==ID_plus)
  {
    assert(expr.operands().size()==2);
    assert(base_type_eq(expr.op0().type(), expr.op1().type(), ns));
    return convert_expr(expr.op0())
           + convert_expr(expr.op1());
  }
  else
  { 
    UNEXPECTEDCASE("Not yet implemented: " + std::string(expr.id().c_str()) + "\n"+ from_expr(ns, " ", expr));
  }
}

exprt z3_convt::get(const exprt &expr) const {
  z3::model m=solver.get_model();
  z3::expr e = m.eval(convert_expr(expr));

  // out << from_expr(ns, " ", expr) << '\t' <<  e << std::endl;

  if (Z3_get_ast_kind(context, e) == Z3_NUMERAL_AST)
  {
    std::string str = Z3_get_numeral_string(context , e);
    auto value = string2integer(str.c_str());
    auto type = expr.type();
    if(type.id()==ID_signedbv ||
     type.id()==ID_unsignedbv ||
     type.id()==ID_bv ||
     type.id()==ID_c_enum ||
     type.id()==ID_c_bool)
    {
      return from_integer(value, type);
    }
    else
    {
      PARSERERROR("Unsupported number type" + from_expr(ns, " ", expr));
    }
  }

  std::ostringstream estr;
  estr << e;

  if (estr.str() == "true") {
    return true_exprt();
  } else if (estr.str() == "false") {
    return false_exprt();
  } else {
    UNEXPECTEDCASE("Can not parse model : " + estr.str());
  }
}