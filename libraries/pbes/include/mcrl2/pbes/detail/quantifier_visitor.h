// Author(s): Wieger Wesselink
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file quantifier_visitor.h
/// \brief Add your file description here.

#ifndef MCRL2_PBES_DETAIL_QUANTIFIER_VISITOR_H
#define MCRL2_PBES_DETAIL_QUANTIFIER_VISITOR_H

#include "mcrl2/data/detail/data_functional.h"
#include "mcrl2/pbes/pbes_expression_visitor.h"

namespace lps {

namespace detail {

using namespace mcrl2::data;

/// Visitor for collecting the quantifier variables that occur in a pbes expression.
struct quantifier_visitor: public pbes_expression_visitor
{
  std::set<data_variable> variables;

  bool visit_forall(const pbes_expression& e, const data_variable_list& v, const pbes_expression&)
  {
    variables.insert(v.begin(), v.end());
    return stop_recursion;
  }

  bool visit_exists(const pbes_expression& e, const data_variable_list& v, const pbes_expression&)
  {
    variables.insert(v.begin(), v.end());
    return stop_recursion;
  }
};  

/// Visitor for determining if within the scope of a quantifier there are quantifier
/// variables of free variables with the same name.
struct quantifier_name_clash_visitor: public pbes_expression_visitor
{
  std::vector<data_variable_list> quantifier_stack;
  bool result;
  data_variable name_clash; // if result is true, then this attribute contains the conflicting variable

  quantifier_name_clash_visitor()
    : result(false)
  {}

  /// returns true if the quantifier_stack contains a data variable with the given name
  bool is_in_quantifier_stack(identifier_string name) const
  {
    for (std::vector<data_variable_list>::const_iterator i = quantifier_stack.begin(); i != quantifier_stack.end(); ++i)
    {
      if (std::find(boost::make_transform_iterator(i->begin(), mcrl2::data::detail::data_variable_name()),
                    boost::make_transform_iterator(i->end()  , mcrl2::data::detail::data_variable_name()),
                    name
                   ) != boost::make_transform_iterator(i->end()  , mcrl2::data::detail::data_variable_name())
         )
      {
        return true;
      }
    }
    return false;
  }

  // Add variables to the quantifier stack, and add replacements for the name clashes to replacements.
  // Returns the number of replacements that were added.
  void push(const data_variable_list& variables)
  {
    if (result)
    {
      return;
    }
    for (data_variable_list::iterator i = variables.begin(); i != variables.end(); ++i)
    {
      if (is_in_quantifier_stack(i->name()))
      {
        result = true;
        name_clash = *i;
        return;
      }
    }
    quantifier_stack.push_back(variables);
  }

  void pop()
  {
    if (result)
    {
      return;
    }
    quantifier_stack.pop_back();
  }

  bool visit_forall(const pbes_expression& e, const data_variable_list& v, const pbes_expression&)
  {
    push(v);
    return continue_recursion;
  }

  void leave_forall()
  {
    pop();
  }

  bool visit_exists(const pbes_expression& e, const data_variable_list& v, const pbes_expression&)
  {
    push(v);
    return continue_recursion;
  }

  void leave_exists()
  {
    pop();
  }
};  

} // namespace detail

} // namespace lps

#endif // MCRL2_PBES_DETAIL_QUANTIFIER_VISITOR_H
