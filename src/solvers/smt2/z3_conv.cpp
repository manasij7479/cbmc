/*******************************************************************\

Module: Z3 C++ API Backend

Author(s): Manasij Mukherjee, manasij7479@gmail.com
           Johanan Wahlang, johananwahlang@gmail.com

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

#include <stdlib.h>
#include <sstream>

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
z3::sort z3_convt::convert_type(const typet &type) const {
  if(type.id()==ID_signedbv ||
     type.id()==ID_unsignedbv ||
     type.id()==ID_fixedbv ||
     type.id()==ID_floatbv ||
     type.id()==ID_verilog_signedbv ||
     type.id()==ID_verilog_unsignedbv ||
     type.id()==ID_bv ||
     type.id()==ID_pointer ||
     type.id()==ID_c_bit_field ||
     type.id()==ID_c_bool) {
    size_t width = to_bitvector_type(type).get_width();
    return context.bv_sort(width);
  }
  else if (type.id()==ID_array) {
    const array_typet &array_type = to_array_type(type);
    const typet &array_index_type = array_type.size().type();    
    const typet &array_value_type = array_type.subtype();
    return context.array_sort(convert_type(array_index_type), convert_type(array_value_type));
  }
}

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
      //TODO: fix conversion error here
      return context.bv_val(std::strtoll(ce.get_value().c_str(),NULL,2), width);
    }
    else
    {
      out << expr_type.id() << std::endl;
      UNEXPECTEDCASE("NON-BOOL Constant : " + std::string(ce.type().id().c_str()) + " " + from_expr(ns, " ", expr));

    }
  }
  else if(expr.id()==ID_symbol)
  {
    irep_idt id=to_symbol_expr(expr).get_identifier();
    assert(id!=irep_idt());
    // out << "Symbol id: " << id.c_str() << std::endl;
    if (!exists(id)) {
      z3::expr new_expr(context);
      const typet &expr_type=ns.follow(expr.type());

      if (expr_type.id() == ID_bool)
      {
        new_expr = context.bool_const(id.c_str());
      }
      else if(expr_type.id()==ID_unsignedbv ||
        expr_type.id()==ID_signedbv ||
        expr_type.id()==ID_bv ||
        expr_type.id()==ID_c_enum ||
        expr_type.id()==ID_c_enum_tag ||
        expr_type.id()==ID_c_bool ||
        expr_type.id()==ID_incomplete_c_enum ||
        expr_type.id()==ID_c_bit_field)
      {
        new_expr = context.constant(id.c_str(), convert_type(expr_type));
      }
      else if(expr_type.id()==ID_array)
      {
        new_expr = context.constant(id.c_str(), convert_type(expr_type));
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

    if (expr.op1().id() != ID_nondet_symbol)
    {
      return convert_expr(expr.op0())
             == convert_expr(expr.op1());
    }
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
  else if (expr.id()==ID_mult)
  {
    assert(expr.operands().size()==2);
    assert(base_type_eq(expr.op0().type(), expr.op1().type(), ns));
    return convert_expr(expr.op0())
           * convert_expr(expr.op1());
  }
  else if (expr.id()==ID_minus)
  {
    assert(expr.operands().size()==2);
    assert(base_type_eq(expr.op0().type(), expr.op1().type(), ns));
    return convert_expr(expr.op0())
           - convert_expr(expr.op1());
  }
  else if (expr.id()==ID_div)
  {
    assert(expr.operands().size()==2);
    assert(base_type_eq(expr.op0().type(), expr.op1().type(), ns));
    return convert_expr(expr.op0())
           / convert_expr(expr.op1());
  }
  else if (expr.id()==ID_le)
  {
    assert(expr.operands().size()==2);
    assert(base_type_eq(expr.op0().type(), expr.op1().type(), ns));
    return convert_expr(expr.op0())
           <= convert_expr(expr.op1());
  }
  else if (expr.id()==ID_lt)
  {
    assert(expr.operands().size()==2);
    assert(base_type_eq(expr.op0().type(), expr.op1().type(), ns));
    return convert_expr(expr.op0())
           < convert_expr(expr.op1());
  }
  else if (expr.id()==ID_ge)
  {
    assert(expr.operands().size()==2);
    assert(base_type_eq(expr.op0().type(), expr.op1().type(), ns));
    return convert_expr(expr.op0())
           >= convert_expr(expr.op1());
  }
  else if (expr.id()==ID_gt)
  {
    assert(expr.operands().size()==2);
    assert(base_type_eq(expr.op0().type(), expr.op1().type(), ns));
    return convert_expr(expr.op0())
           > convert_expr(expr.op1());
  }
  else if (expr.id()==ID_forall)
  {
    //return z3::forall(convert_expr(expr.op0), convert_expr(expr.op1));
  }
  else if (expr.id()==ID_exists)
  {
    //  return z3::exists(convert_expr(expr.op0), convert_expr(expr.op1));
  }
  else if (expr.id()==ID_array)
  {
    // out << from_expr(expr) << std::endl;
  }
  else if (expr.id()==ID_array_of)
  {
    // out << from_expr(expr) << std::endl;
  }
  else if (expr.id()==ID_array_copy)
  {
  }
  else if (expr.id()==ID_array_equal)
  {
  }
  else if (expr.id()==ID_array_set)
  {
  }
  else if (expr.id()==ID_with)
  {
    return convert_with(to_with_expr(expr));
  }
  else if (expr.id()==ID_index)
  {
    return convert_index(to_index_expr(expr));
  }
  else if (expr.id() == ID_typecast)
  {
    return convert_typecast(to_typecast_expr(expr));

  }
  else
  { 
    UNEXPECTEDCASE("Not yet implemented: " + std::string(expr.id().c_str()) + "\n"+ from_expr(ns, " ", expr));
  }
}

z3::expr z3_convt::convert_with(const with_exprt &expr) const {
  // get rid of "with" that has more than three operands

  assert(expr.operands().size()>=3);

  if(expr.operands().size()>3)
  {
    std::size_t s=expr.operands().size();

    // strip of the trailing two operands
    exprt tmp=expr;
    tmp.operands().resize(s-2);

    with_exprt new_with_expr;
    assert(new_with_expr.operands().size()==3);
    new_with_expr.type()=expr.type();
    new_with_expr.old()=tmp;
    new_with_expr.where()=expr.operands()[s-2];
    new_with_expr.new_value()=expr.operands()[s-1];

    // recursive call
    return convert_with(new_with_expr);
  }
  const typet &expr_type=ns.follow(expr.type());

  if(expr_type.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(expr_type);
    const z3::expr &array = convert_expr(expr.old());
    const z3::expr &index = convert_expr(expr.where());
    const z3::expr &value = convert_expr(expr.new_value());
    return z3::store(array, index, value);
  }
}

z3::expr z3_convt::convert_index(const index_exprt &expr) const {
  assert(expr.operands().size()==2);

  const typet &array_op_type=ns.follow(expr.array().type());

  if(array_op_type.id()==ID_array)
  {
    // const array_typet &array_type=to_array_type(array_op_type);
    const z3::expr &array = convert_expr(expr.array());
    const z3::expr &index = convert_expr(expr.index());
    return z3::select(array, index);
  }
  else
    UNEXPECTEDCASE("index with unsupported array type: "+array_op_type.id_string());
}

exprt z3_convt::get(const exprt &expr) const {
  z3::model m = solver.get_model();
  const z3::expr & e = m.eval(convert_expr(expr));
  return z3_convt::convert_z3_expr(e, expr.type());
}

exprt z3_convt::convert_z3_expr(const z3::expr &expr, const typet &type) const {
  if (expr.is_app()) {
    switch (expr.decl().decl_kind()) {
      case Z3_OP_TRUE:
        return from_integer(1, type);
      case Z3_OP_FALSE:
        return from_integer(0, type);
      case Z3_OP_BNUM:
        return from_integer(expr.get_numeral_int64(), type);
      case Z3_OP_STORE:
      case Z3_OP_CONST_ARRAY:
      {
        const array_typet &array_type = to_array_type(type);
        return convert_z3_array(expr, array_type);
      }
      default:
        out << "Conversion from z3 expression type " << expr.decl().decl_kind() << " not yet added" << std::endl;
        return nil_exprt();
    }
  }
  else {
    out << "Conversion from z3 expression type " << expr.decl().decl_kind() << " not yet added" << std::endl;
    return nil_exprt();
  }
}

exprt z3_convt::convert_z3_array(const z3::expr &expr, const array_typet &array_type) const {
  switch (expr.decl().decl_kind()) {
    case Z3_OP_CONST_ARRAY:
    {
      const exprt &what = from_integer(expr.arg(0).get_numeral_int(),array_type.subtype());
      return array_of_exprt(what, array_type);
    }
    case Z3_OP_STORE:
    {
      const exprt &array = convert_z3_array(expr.arg(0), array_type);
      const exprt &index = convert_z3_expr(expr.arg(1), array_type.size().type());
      const exprt &value = convert_z3_expr(expr.arg(2), array_type.subtype());
      return with_exprt(array, index, value);
    }
    default:
      UNEXPECTEDCASE("Not an array\n");
  }
}

z3::expr z3_convt::convert_typecast(const typecast_exprt &expr) const
{
  assert(expr.operands().size()==1);
  const exprt &src=expr.op0();
  boolbv_widtht boolbv_width(ns);

  typet dest_type=ns.follow(expr.type());
  if(dest_type.id()==ID_c_enum_tag)
    dest_type=ns.follow_tag(to_c_enum_tag_type(dest_type));

  typet src_type=ns.follow(src.type());
  if(src_type.id()==ID_c_enum_tag)
    src_type=ns.follow_tag(to_c_enum_tag_type(src_type));

  auto&& src_expr = convert_expr(src);

  // return convert_expr(src);
  if(dest_type.id()==ID_bool)
  {
    // this is comparison with zero
    if(src_type.id()==ID_signedbv ||
       src_type.id()==ID_unsignedbv ||
       src_type.id()==ID_c_bool ||
       src_type.id()==ID_fixedbv ||
       src_type.id()==ID_pointer)
    {
      return src_expr != convert_expr(gen_zero(src_type));

    }
    // else if(src_type.id()==ID_floatbv)
    // {
    //   if(use_FPA_theory)
    //   {
    //     out << "(not (fp.isZero ";
    //     convert_expr(src);
    //     out << "))";
    //   }
    //   else
    //     convert_floatbv(expr);
    // }
    else
    {
      UNEXPECTEDCASE("TODO typecast1 "+src_type.id_string()+" -> bool");
    }
  }
  else if(dest_type.id()==ID_c_bool)
  {
    std::size_t to_width=boolbv_width(dest_type);
    return z3::ite(src_expr != convert_expr(gen_zero(src_type)),
      context.bv_val(1, to_width), context.bv_val(0, to_width));
  }
  else if(dest_type.id()==ID_signedbv ||
          dest_type.id()==ID_unsignedbv ||
          dest_type.id()==ID_c_enum ||
          dest_type.id()==ID_bv)
  {
    std::size_t to_width=boolbv_width(dest_type);

    if(src_type.id()==ID_signedbv || // from signedbv
       src_type.id()==ID_unsignedbv || // from unsigedbv
       src_type.id()==ID_c_bool ||
       src_type.id()==ID_c_enum ||
       src_type.id()==ID_bv)
    {
      std::size_t from_width=boolbv_width(src_type);

      if(from_width==to_width)
        return src_expr; // ignore
      else if(from_width<to_width) // extend
      {
        if(src_type.id()==ID_signedbv)
          return z3::sext(src_expr, to_width-from_width);
        else
          z3::sext(src_expr, to_width-from_width);
      }
      else // chop off extra bits
      {
        return src_expr.extract(0, to_width);
      }
    }
    else if(src_type.id()==ID_bool) // from boolean to int
    {
      out << "(ite ";
      convert_expr(src);

      out << " (_ bv1 " << to_width << ")";
      out << " (_ bv0 " << to_width << ")";

      out << ")";
      return z3::ite(src_expr, context.bv_val(1, to_width), context.bv_val(0, to_width));
    }
    else
    {
      UNEXPECTEDCASE("TODO typecast2 "+src_type.id_string()+" -> "+dest_type.id_string() + " src == " + from_expr(ns, "", src));
    }
  }
}