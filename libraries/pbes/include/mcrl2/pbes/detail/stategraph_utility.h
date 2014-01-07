// Author(s): Wieger Wesselink
// Copyright: see the accompanying file COPYING or copy at
// https://svn.win.tue.nl/trac/MCRL2/browser/trunk/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/pbes/detail/stategraph_utility.h
/// \brief add your file description here.

#ifndef MCRL2_PBES_DETAIL_STATEGRAPH_UTILITY_H
#define MCRL2_PBES_DETAIL_STATEGRAPH_UTILITY_H

#include <sstream>
#include "mcrl2/data/detail/simplify_rewrite_builder.h"
#include "mcrl2/pbes/pbes_equation.h"
#include "mcrl2/pbes/detail/simplify_quantifier_builder.h"

namespace mcrl2 {

namespace pbes_system {

namespace detail {

inline
std::string print_equation(const pbes_equation& eq)
{
  return (eq.symbol().is_mu() ? "mu " : "nu ")  + pbes_system::pp(eq.variable()) + " = " + pbes_system::pp(eq.formula());
}

inline
std::string print_set(const std::set<std::size_t>& v)
{
  std::ostringstream out;
  out << "{";
  for (std::set<std::size_t>::const_iterator i = v.begin(); i != v.end(); ++i)
  {
    if (i != v.begin())
    {
      out << ", ";
    }
    out << *i;
  }
  out << "}";
  return out.str();
}

inline
const data::data_expression& nth_element(const data::data_expression_list& e, std::size_t n)
{
  assert(n < e.size());
  data::data_expression_list::const_iterator i = e.begin();
  for (std::size_t j = 0; j < n; ++j)
  {
    ++i;
  }
  return *i;
}

inline
bool is_constant(const data::data_expression& x)
{
  typedef core::term_traits<data::data_expression> tr;
  return tr::is_constant(x);
}

inline
std::string print_pbes_expressions(const std::set<pbes_expression>& v)
{
  std::ostringstream out;
  out << "{";
  for (std::set<pbes_expression>::const_iterator j = v.begin(); j != v.end(); ++j)
  {
    if (j != v.begin())
    {
      out << ", ";
    }
    out << pbes_system::pp(*j);
  }
  out << "}";
  return out.str();
}

// Adds some simplifications to simplify_rewrite_builder.
template <typename Term, typename DataRewriter, typename SubstitutionFunction = no_substitution>
struct stategraph_simplify_quantifier_builder: public pbes_system::detail::simplify_quantifier_builder<Term, DataRewriter, SubstitutionFunction>
{
  typedef pbes_system::detail::simplify_quantifier_builder<Term, DataRewriter, SubstitutionFunction> super;
  typedef SubstitutionFunction                                                                       argument_type;
  typedef typename super::term_type                                                                  term_type;
  typedef typename core::term_traits<term_type>::data_term_type                                      data_term_type;
  typedef typename core::term_traits<term_type>::data_term_sequence_type                             data_term_sequence_type;
  typedef typename core::term_traits<term_type>::variable_sequence_type                              variable_sequence_type;
  typedef typename core::term_traits<term_type>::propositional_variable_type                         propositional_variable_type;
  typedef core::term_traits<Term> tr;

  /// \brief Constructor.
  /// \param rewr A data rewriter
  stategraph_simplify_quantifier_builder(const DataRewriter& rewr)
    : simplify_quantifier_builder<Term, DataRewriter, SubstitutionFunction>(rewr)
  { }

  bool is_data_not(const pbes_expression& x) const
  {
    return data::is_data_expression(x) && data::sort_bool::is_not_application(x);
  }

  bool is_data_and(const pbes_expression& x) const
  {
    return data::is_data_expression(x) && data::sort_bool::is_and_application(x);
  }

  bool is_data_or(const pbes_expression& x) const
  {
    return data::is_data_expression(x) && data::sort_bool::is_or_application(x);
  }

  // returns the argument of a data not
  data::data_expression not_arg(const data::data_expression& x)
  {
    return *data::application(x).begin();
  }

  // replace !(y || z) by !y && !z
  // replace !(y && z) by !y || !z
  // replace !(y => z) by y || !z
  // replace y => z by !y || z
  term_type post_process(const term_type& x)
  {
    term_type result = x;
    if (tr::is_not(x))
    {
      const term_type& t = tr::not_arg(x);
      if (tr::is_or(t)) // x = !(y && z)
      {
        term_type y = utilities::optimized_not(tr::left(t));
        term_type z = utilities::optimized_not(tr::right(t));
        result = utilities::optimized_and(y, z);
      }
      else if (tr::is_and(t)) // x = !(y || z)
      {
        term_type y = utilities::optimized_not(tr::left(t));
        term_type z = utilities::optimized_not(tr::right(t));
        result = utilities::optimized_or(y, z);
      }
      else if (tr::is_imp(t)) // x = !(y => z)
      {
        term_type y = tr::left(t);
        term_type z = utilities::optimized_not(tr::right(t));
        result = utilities::optimized_or(y, z);
      }
      else if (is_data_not(t)) // x = !val(!y)
      {
        const data::data_expression& z = atermpp::aterm_cast<const data::data_expression>(t);
        data::data_expression y = not_arg(z);
        result = y;
      }
    }
    else if (tr::is_imp(x)) // x = y => z
    {
      term_type y = utilities::optimized_not(tr::left(x));
      term_type z = tr::right(x);
      result = utilities::optimized_or(y, z);
    }
    return result;
  }

  // replaces data operators !, ||, && by their pbes equivalent
  term_type preprocess(const term_type& x)
  {
    typedef core::term_traits<data::data_expression> tt;
    if (is_data_not(x))
    {
      const data::data_expression& y = atermpp::aterm_cast<const data::data_expression>(x);
      return tr::not_(not_arg(y));
    }
    else if (is_data_and(x))
    {
      const data::data_expression& y = atermpp::aterm_cast<const data::data_expression>(x);
      return tr::and_(tt::left(y), tt::right(y));
    }
    else if (is_data_or(x))
    {
      const data::data_expression& y = atermpp::aterm_cast<const data::data_expression>(x);
      return tr::or_(tt::left(y), tt::right(y));
    }
    return x;
  }

  // replace the data expression y != z by !(y == z)
  term_type visit_data_expression(const term_type& x, const data_term_type& d, SubstitutionFunction& sigma)
  {
    // if x has one of the operators !, ||, && at the top level, handle it by the PBES simplification
    term_type y = preprocess(x);
    if (y != x)
    {
      return super::visit(y, sigma);
    }
    typedef core::term_traits<data::data_expression> tt;
    term_type result = super::visit_data_expression(x, d, sigma);
    const data::data_expression& t = atermpp::aterm_cast<const data::data_expression>(result);
    if (data::is_not_equal_to_application(t)) // result = y != z
    {
      data::data_expression y = tt::left(t);
      data::data_expression z = tt::right(t);
      result = tr::not_(data::equal_to(y, z));
    }
    return post_process(result);
  }

  term_type visit_true(const term_type& x, SubstitutionFunction& sigma)
  {
    return post_process(super::visit_true(x, sigma));
  }

  term_type visit_false(const term_type& x, SubstitutionFunction& sigma)
  {
    return post_process(super::visit_false(x, sigma));
  }

  term_type visit_not(const term_type& x, const term_type& n, SubstitutionFunction& sigma)
  {
    return post_process(super::visit_not(x, n, sigma));
  }

  term_type visit_and(const term_type& x, const term_type& left, const term_type& right, SubstitutionFunction& sigma)
  {
    return post_process(super::visit_and(x, left, right, sigma));
  }

  term_type visit_or(const term_type& x, const term_type& left, const term_type& right, SubstitutionFunction& sigma)
  {
    return post_process(super::visit_or(x, left, right, sigma));
  }

  term_type visit_imp(const term_type& x, const term_type& left, const term_type& right, SubstitutionFunction& sigma)
  {
    return post_process(super::visit_imp(x, left, right, sigma));
  }

  term_type visit_forall(const term_type& x, const variable_sequence_type&  variables, const term_type&  expression, SubstitutionFunction& sigma)
  {
    return post_process(super::visit_forall(x, variables, expression, sigma));
  }

  term_type visit_exists(const term_type& x, const variable_sequence_type&  variables, const term_type&  expression, SubstitutionFunction& sigma)
  {
    return post_process(super::visit_exists(x, variables, expression, sigma));
  }

  term_type visit_propositional_variable(const term_type& x, const propositional_variable_type&  v, SubstitutionFunction& sigma)
  {
    return post_process(super::visit_propositional_variable(x, v, sigma));
  }
};

template <typename Term, typename DataRewriter>
class stategraph_simplifying_rewriter
{
  protected:
    DataRewriter m_rewriter;

  public:
    typedef typename core::term_traits<Term>::term_type term_type;
    typedef typename core::term_traits<Term>::variable_type variable_type;

    stategraph_simplifying_rewriter(const DataRewriter& rewriter)
      : m_rewriter(rewriter)
    {}

    term_type operator()(const term_type& x) const
    {
      stategraph_simplify_quantifier_builder<Term, DataRewriter> r(m_rewriter);
      return r(x);
    }

    template <typename SubstitutionFunction>
    term_type operator()(const term_type& x, SubstitutionFunction sigma) const
    {
      stategraph_simplify_quantifier_builder<Term, DataRewriter, SubstitutionFunction> r(m_rewriter);
      return r(x, sigma);
    }
};

} // namespace detail

} // namespace pbes_system

} // namespace mcrl2

#endif // MCRL2_PBES_DETAIL_STATEGRAPH_UTILITY_H
