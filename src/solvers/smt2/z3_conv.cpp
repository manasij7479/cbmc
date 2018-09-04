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

/*******************************************************************\

Function: z3_convt::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt z3_convt::l_get(literalt l) const
{
  if(l.is_true()) return tvt(true);
  if(l.is_false()) return tvt(false);
  // assert(l.var_no()<boolean_assignment.size());
  // return tvt(boolean_assignment[l.var_no()]^l.sign());
  z3::model model=solver.get_model();
  // std::cout << model.eval(convert_literal(l)) << std::endl;
  z3::expr res=model.eval(convert_literal(l));
  if (res.is_true())
    return tvt(true);
  else if (res.is_false())
    return tvt(false);
  else
    return tvt(tvt::unknown());
}

/*******************************************************************\

Function: z3_convt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt z3_convt::convert(const exprt &expr)
{
  assert(expr.type().id()==ID_bool);

  // Three cases where no new handle is needed.

  if(expr.is_true())
    return const_literal(true);
  else if(expr.is_false())
    return const_literal(false);
  else if(expr.id()==ID_literal)
    return to_literal_expr(expr).get_literal();

  // Need a new handle

  // find_symbols(expr);

  literalt l(no_boolean_variables, false);
  no_boolean_variables++;

  // std::cout << "(define-fun ";
  // std::cout << convert_literal(l);
  // std::cout << " () Bool ";
  // std::cout << convert_expr(expr);
  // std::cout << ")" << "\n";

  // std::cout << (convert_literal(l) == convert_expr(expr)) << std::endl;
  solver.add(convert_literal(l) == convert_expr(expr));
  return l;
}

/*******************************************************************\

Function: z3_convt::convert_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

z3::expr z3_convt::convert_literal(const literalt l) const
{
  if(l==const_literal(false))
    return context.bool_val(false);
  else if(l==const_literal(true))
    return context.bool_val(true);
  else
  {
    std::string lit_name="B"+i2string(l.var_no());
    z3::expr lit(context);
    if (lit_map.find(lit_name)==lit_map.end())
    {
      // std::cout << "lit not found, creating one" << std::endl;
      lit=context.bool_const(lit_name.c_str());
      lit_store.push_back(lit);
      lit_map[lit_name]=lit_store.size() - 1;
    }
    lit=lit_store[lit_map[lit_name]];
    if(l.sign())
      return !lit;
    else
      return lit;
  }
}

z3::sort z3_convt::convert_type(const typet &type) const {
  if (type.id()==ID_bool)
  {
    return context.bool_sort();
  }
  else if (type.id()==ID_signedbv ||
     type.id()==ID_unsignedbv ||
     type.id()==ID_fixedbv ||
     type.id()==ID_floatbv ||
     type.id()==ID_verilog_signedbv ||
     type.id()==ID_verilog_unsignedbv ||
     type.id()==ID_bv ||
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
  else if (type.id()==ID_pointer)
  {
    size_t width=to_bitvector_type(type).get_width();
    if (width==0)
      return context.bv_sort(64);
    else
      return context.bv_sort(width);
  }
  else
  {
    std::cout << type.id_string() << std::endl;
    UNEXPECTEDCASE("Unknown type!\n");
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
      if (expr.is_true())
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
       expr_type.id()==ID_c_enum ||
       expr_type.id()==ID_c_enum_tag ||
       expr_type.id()==ID_c_bool ||
       expr_type.id()==ID_incomplete_c_enum ||
       expr_type.id()==ID_c_bit_field)
    {

      std::size_t width=boolbv_width(expr_type);
      uint64_t value=binary2integer(id2string(ce.get_value()), false).to_ulong();
      return context.bv_val(value, width);
    }
    else if (expr_type.id()==ID_signedbv ||
             expr_type.id()==ID_bv)
    {
      std::size_t width=boolbv_width(expr_type);
      int64_t value=binary2integer(id2string(ce.get_value()), false).to_long();
      return context.bv_val(value, width);
    }
    else if (expr_type.id()==ID_integer)
    {
      // std::cout << context.int_val(ce.get_value().c_str()) << std::endl;
      return context.int_val(ce.get_value().c_str());
    }
    else if (expr_type.id()==ID_pointer)
    {
      const irep_idt &value=expr.get(ID_value);
      if (value==ID_NULL)
      {
        // std::cout << context.bv_val(0, boolbv_width(expr_type)) << std::endl;
        return context.bv_val(0, boolbv_width(expr_type));
      }
      else
      {
        std::cout << value << std::endl;
        UNEXPECTEDCASE("unknown pointer constant: "+id2string(value));
      }
    }
    else
    {
      std::cout << expr.type().id_string() << std::endl;
      UNEXPECTEDCASE("NON-BOOL Constant : " + std::string(ce.type().id().c_str()) + " " + from_expr(ns, " ", expr));
    }
  }
  else if(expr.id()==ID_symbol)
  {
    irep_idt id=to_symbol_expr(expr).get_identifier();
    assert(id!=irep_idt());
    if (!exists(id)) {
      z3::expr new_expr(context);
      const typet &expr_type=ns.follow(expr.type());

      new_expr = context.constant(id.c_str(), convert_type(expr_type));

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
  else if (expr.id()==ID_typecast)
  {
    return convert_typecast(to_typecast_expr(expr));
  }
  else if (expr.id()==ID_literal)
  {
    return convert_literal(to_literal_expr(expr).get_literal());
  }
  else if (expr.id()==ID_forall)
  {
    // std::cout << z3::forall(convert_expr(expr.op0()), convert_expr(expr.op1())) << std::endl;
    return z3::forall(convert_expr(expr.op0()), convert_expr(expr.op1()));
  }
  else if (expr.id()==ID_exists)
  {
    int i=0;
    for (auto it=expr.operands().begin(); it!=expr.operands().end(); it++, i++)
    {
      // std::cout << i << from_expr(*it) << std::endl;
    }
    // return z3::exists(convert_expr(expr.op0()), convert_expr(expr.op1()));
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
  else if (expr.id() == ID_array)
  {
    return convert_array(to_array_expr(expr));
  }
  else if (expr.id()==ID_array_of)
  {
    return convert_array_of(to_array_of_expr(expr));
  }
  else if (expr.id()==ID_unary_minus)
  {
    assert(expr.operands().size()==1);
    if (expr.type().id()==ID_signedbv)
      return z3::to_expr(context, Z3_mk_bvneg(context,convert_expr(expr.op0())));
  }
  else if (expr.id()==ID_unary_plus)
  {
    return convert_expr(expr.op0());
  }
  else
  { 
    UNEXPECTEDCASE("Not yet implemented: " + std::string(expr.id().c_str()) + "\n"+ from_expr(ns, " ", expr));
  }
}

z3::expr z3_convt::convert_array(const array_exprt &expr) const
{
  array_typet array_type = to_array_type(expr.type());
  exprt zero=from_integer(mp_integer(0),array_type.subtype());
  z3::expr z3_array=convert_array_of(array_of_exprt(zero, array_type));
  
  int i=0;
  for (auto it=expr.operands().begin(); it!=expr.operands().end(); it++, i++)
  {
    z3_array = z3::store(z3_array, i, convert_expr(*it));
  }
  return z3_array;
}

z3::expr z3_convt::convert_array_of(const array_of_exprt &expr) const
{
  array_typet array_type=to_array_type(expr.type());
  return z3::const_array(convert_type(array_type.size().type()),convert_expr(expr.what()));
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

exprt z3_convt::get(const exprt &expr) const
{
  z3::model model=solver.get_model();
  const z3::expr &e = model.eval(convert_expr(expr));
  out << from_expr(ns, "", expr) << ": ";
  out << e << std::endl;
  return z3_convt::convert_z3_expr(e, expr.type());
}

exprt z3_convt::convert_z3_expr(const z3::expr &expr, const typet &type) const
{
  if (expr.get_sort().is_array())
  {
    return convert_z3_array(expr, to_array_type(type));
  }
  switch(expr.kind())
  {
    case Z3_NUMERAL_AST:
    case Z3_APP_AST:
    {
      switch(expr.decl().decl_kind())
      {
        case Z3_OP_TRUE:
        {
          return true_exprt();
        }
        case Z3_OP_FALSE:
        {
          return false_exprt();
        }
        case Z3_OP_BNUM:
        {
          unsigned int bv_size=expr.get_sort().bv_size();
          return from_integer(mp_integer(expr.get_decimal_string(bv_size).c_str()), type);          
        }
        default:
          UNEXPECTEDCASE("Not implemented yet\n");
      }
    }
    case Z3_VAR_AST:
      UNEXPECTEDCASE("Z3_VAR_AST");
    case Z3_QUANTIFIER_AST:
      // std::cout << "Z3_QUANTIFIER_AST" << std::endl;
      std::cout << expr << std::endl;
      if (expr.is_exists())
      {
      }
      else if (expr.is_forall())
      {
        // std::cout << Z3_get_quantifier_bound_name(context, expr, 0) << std::endl;
      }
      else if (expr.is_lambda())
      {
      }
      else
      {
        UNEXPECTEDCASE("Not a quantifier!");
      }
    case Z3_SORT_AST:
      UNEXPECTEDCASE("Z3_SORT_AST");
    case Z3_FUNC_DECL_AST:
      UNEXPECTEDCASE("Z3_FUNC_DECL_AST");
    default:
      UNEXPECTEDCASE("Z3_UNKNOWN_AST");
  }
}

exprt z3_convt::convert_z3_array(const z3::expr &expr, const array_typet &array_type) const 
{
  switch(expr.kind())
  {
    case Z3_QUANTIFIER_AST:
      if (expr.is_lambda())
      {
        z3::expr body=expr.body();

        // "Evaluate" the value at each index, and copy to a new array's operands

        // size_t size=binary2integer(id2string(to_constant_expr(array_type.size()).get_value()), false).to_ulong();
        // exprt array=array_exprt(array_type);
        // for (size_t i=0; i<size; i++)
        // {
        //   z3::expr_vector dst(context);
        //   dst.push_back(context.bv_val(i,expr.get_sort().array_domain().bv_size()));
        //   array.copy_to_operands(convert_z3_expr(body.substitute(dst).simplify(), array_type.subtype()));
        // }

        return convert_z3_array(body, array_type);
      }
      else
      {
        UNEXPECTEDCASE("Unexpected quantifier\n");
      }
    case Z3_NUMERAL_AST:
    case Z3_APP_AST:
      switch (expr.decl().decl_kind())
      {
        case Z3_OP_BNUM:
        {
          const exprt &what=convert_z3_expr(expr,array_type.subtype());
          return array_of_exprt(what, array_type);           
        }
        case Z3_OP_CONST_ARRAY:
        {
          const exprt &what = convert_z3_expr(expr.arg(0),array_type.subtype());
          return array_of_exprt(what, array_type);
        }
        case Z3_OP_STORE:
        {
          const exprt &array = convert_z3_array(expr.arg(0), array_type);
          const exprt &index = convert_z3_expr(expr.arg(1), array_type.size().type());
          const exprt &value = convert_z3_expr(expr.arg(2), array_type.subtype());
          return with_exprt(array, index, value);
        }
        case Z3_OP_ITE:
        {
          const exprt &index = convert_z3_expr(expr.arg(0).arg(1), array_type.size().type());
          const exprt &value = convert_z3_expr(expr.arg(1), array_type.subtype());
          const exprt &array = convert_z3_array(expr.arg(2), array_type);
          return with_exprt(array, index, value);
        }
        default:
          UNEXPECTEDCASE("Not implemented yet\n");
      }
    default:
      UNEXPECTEDCASE("Not implemented yet\n");
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
        {
          return z3::zext(src_expr, to_width-from_width);
        }
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
