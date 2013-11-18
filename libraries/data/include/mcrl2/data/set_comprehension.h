// Author(s): Wieger Wesselink
// Copyright: see the accompanying file COPYING or copy at
// https://svn.win.tue.nl/trac/MCRL2/browser/trunk/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/data/set_comprehension.h
/// \brief add your file description here.

#ifndef MCRL2_DATA_SET_COMPREHENSION_H
#define MCRL2_DATA_SET_COMPREHENSION_H

#include "mcrl2/data/abstraction.h"
#include "mcrl2/data/variable.h"

namespace mcrl2 {

namespace data {

/// \brief universal quantification.
///
class set_comprehension: public abstraction
{
  public:

    /// Constructor.
    ///
    /// \param[in] d A data expression.
    /// \pre d has the interal structure of an abstraction.
    /// \pre d is a universal quantification.
    set_comprehension(const data_expression& d)
      : abstraction(d)
    {
      assert(is_abstraction(d));
      assert(static_cast<abstraction>(d).binding_operator() == set_comprehension_binder());
    }

    /// Constructor.
    ///
    /// \param[in] variables A nonempty list of binding variables (objects of type variable).
    /// \param[in] body The body of the set_comprehension abstraction.
    /// \pre variables is not empty.
    template < typename Container >
    set_comprehension(const Container& variables,
           const data_expression& body,
           typename atermpp::detail::enable_if_container< Container, variable >::type* = 0)
      : abstraction(set_comprehension_binder(), variables, body)
    {
      assert(!variables.empty());
    }

}; // class set_comprehension

//--- start generated class set_comprehension ---//
// prototype declaration
std::string pp(const set_comprehension& x);

/// \brief Outputs the object to a stream
/// \param out An output stream
/// \return The output stream
inline
std::ostream& operator<<(std::ostream& out, const set_comprehension& x)
{
  return out << data::pp(x);
}

/// \brief swap overload
inline void swap(set_comprehension& t1, set_comprehension& t2)
{
  t1.swap(t2);
}
//--- end generated class set_comprehension ---//

} // namespace data

} // namespace mcrl2

#endif // MCRL2_DATA_SET_COMPREHENSION_H
