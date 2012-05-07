// Author(s): Wieger Wesselink
// Copyright: see the accompanying file COPYING or copy at
// https://svn.win.tue.nl/trac/MCRL2/browser/trunk/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/atermpp/aterm_appl.h
/// \brief The term_appl class represents function application.

#ifndef MCRL2_ATERMPP_ATERM_APPL_H
#define MCRL2_ATERMPP_ATERM_APPL_H

#include <cassert>
#include <iterator>
#include <vector>
#include "mcrl2/utilities/detail/memory_utility.h"
#include "mcrl2/atermpp/aterm.h"
#include "mcrl2/atermpp/aterm_list.h"
#include "mcrl2/atermpp/function_symbol.h"
#include "mcrl2/atermpp/aterm_appl_iterator.h"
#include "mcrl2/atermpp/aterm_traits.h"

namespace atermpp
{

namespace detail
{

// Function object for conversion to ATerm
struct aterm_converter
{
  template <typename T>
  ATerm operator()(const T& x)
  {
    return aterm_traits<T>::term(x);
  }
};

// Note: ATmakeAppl requires a forward iterator, so we have to make a special case for input iterators.
template <class InputIterator>
inline ATermAppl at_make_appl(const function_symbol& sym, InputIterator first, InputIterator last, std::input_iterator_tag)
{
  MCRL2_SYSTEM_SPECIFIC_ALLOCA(arguments,_ATerm*,sym.arity());
  size_t c=0;
  for (InputIterator i = first; i != last; ++i, ++c)
  {
    arguments[c]=&*aterm_traits<typename std::iterator_traits<InputIterator>::value_type>::term(*i);
  }
  assert(c==sym.arity());
  return ATmakeApplArray(sym, reinterpret_cast<ATerm*>(arguments));
}

template <class ForwardIterator>
inline ATermAppl at_make_appl(const function_symbol& sym, ForwardIterator first, ForwardIterator last, std::forward_iterator_tag)
{
  return ATmakeAppl(sym, first, last, aterm_converter());
}

template <class Iterator>
inline ATermAppl at_make_appl(const function_symbol& sym, Iterator first, Iterator last)
{
  return at_make_appl(sym, first, last, typename std::iterator_traits<Iterator>::iterator_category());
}

} // namespace detail

/// \brief A term that represents a function application.
template <typename Term>
class term_appl: public ::aterm::term_appl<Term> 
{

  public:
    explicit term_appl(const ATerm &t)
    {
      assert(t.type()==AT_APPL);
      this->copy_term(&*t);
    }

    term_appl(const ATermAppl &t)
    {
      assert(t.type()==AT_APPL);
      this->copy_term(&*t);
    }

    term_appl(const AFun &sym, const Term &t1)
    {
      this->copy_term(&* ::aterm::term_appl<Term>(sym,t1));
    }

    term_appl(const AFun &sym, const Term &t1, const Term &t2)
    {
      this->copy_term(&* ::aterm::term_appl<Term>(sym,t1,t2));
    }

    term_appl(const AFun &sym, const Term &t1, const Term &t2, const Term &t3)
    {
      this->copy_term(&* ::aterm::term_appl<Term>(sym,t1,t2,t3));
    }

    term_appl(const AFun &sym, const Term &t1, const Term &t2, const Term &t3, const Term &t4)
    {
      this->copy_term(&* ::aterm::term_appl<Term>(sym,t1,t2,t3,t4));
    }

    term_appl(const AFun &sym, const Term &t1, const Term &t2, const Term &t3, const Term &t4, const Term &t5)
    {
      this->copy_term(&* ::aterm::term_appl<Term>(sym,t1,t2,t3,t4,t5));
    }

    term_appl()
    {}

    template <class Iter>
    term_appl(const AFun &sym, Iter first, Iter last)
    {
      this->copy_term(&*::aterm::term_appl<Term>(sym,first,last));
    }


/*   friend class aterm_string;

  private:
    /// \brief Prevent accidental usage of operator[], since this maps to the
    /// built-in C++ operator[](ATermAppl, int)
    /// \param i A positive integer
    /// \return The default constructed term
    Term operator[](size_t ) const
    {
      return Term();
    }

  protected:
    /// \brief Conversion operator.
    /// \return The wrapped ATerm.
    ATermAppl appl() const
    {
      return (ATermAppl)m_term;
    }

  public:
    /// The type of object, T stored in the term_appl.
    typedef Term value_type;

    /// Pointer to T.
    typedef Term* pointer;

    /// Reference to T.
    typedef Term& reference;

    /// Const reference to T.
    typedef const Term const_reference;

    /// An unsigned integral type.
    typedef size_t size_type;

    /// A signed integral type.
    typedef ptrdiff_t difference_type;

    /// Iterator used to iterate through an term_appl.
    typedef term_appl_iterator<Term> iterator;

    /// Const iterator used to iterate through an term_appl.
    typedef term_appl_iterator<Term> const_iterator;

    /// Default constructor.
    term_appl()
    {}

    /// \brief Constructor.
    /// \param term A term
    term_appl(ATerm term)
      : aterm_base(term)
    {
      assert(type() == AT_APPL);
    }

    /// \brief Constructor.
    /// \param term A term
    term_appl(ATermAppl term)
      : aterm_base(term)
    {}

    /// \brief Constructor.
    /// \param sym A function symbol.
    /// \param args A list of arguments.
    term_appl(function_symbol sym, term_list<Term> args)
      : aterm_base(ATmakeApplList(sym, args))
    {}

    /// \brief Constructor.
    /// \param sym A function symbol.
    /// \param first The start of a range of elements.
    /// \param last The end of a range of elements.
    template <typename Iter>
    term_appl(function_symbol sym, Iter first, Iter last)
    {
      m_term = static_cast<ATerm>(detail::at_make_appl(sym, first, last));
    }

    /// \brief Constructor.
    /// \param sym A function symbol.
    term_appl(function_symbol sym)
      : aterm_base(ATmakeAppl0(sym))
    {
    }

#include "mcrl2/atermpp/aterm_appl_constructor.h" // additional constructors generated by preprocessor

    /// \brief Conversion operator.
    /// \return The wrapped ATermAppl pointer
    operator ATermAppl() const
    {
      return (ATermAppl)m_term;
    }

    /// Assignment operator.
    /// \param t A term.
    /// \return The result of the assignment.
    term_appl<Term>& operator=(ATermAppl t)
    {
      assert(t==ATermAppl() || t->reference_count>0);
      m_term = t;
      return *this;
    }

    /// \brief Returns the size of the list.
    /// \return The size of the list.
    size_type size() const
    {
      return ATgetArity(ATgetAFun(appl()));
    }

    /// \brief Returns an iterator pointing to the beginning of the list.
    /// \return An iterator pointing to the beginning of the list.
    const_iterator begin() const
    {
      return const_iterator(((ATerm*)(&*m_term) + ARG_OFFSET));
    }

    /// \brief Returns a const_iterator pointing to the beginning of the list.
    /// \return A const_iterator pointing to the beginning of the list.
    const_iterator end() const
    {
      return const_iterator(((ATerm*)(&*m_term) + ARG_OFFSET + size()));
    }

    /// \brief Returns the largest possible size of the list.
    /// \return The largest possible size of the list.
    size_type max_size() const
    {
      return (std::numeric_limits<unsigned long>::max)();
    }

    /// \brief Returns true if the list's size is 0.
    /// \return True if the function application has no arguments.
    bool empty() const
    {
      return size() == 0;
    }

    /// \brief Get the function symbol (function_symbol) of the application.
    /// \return The function symbol of the function application.
    function_symbol function() const
    {
      return function_symbol(ATgetAFun(appl()));
    }

    /// \brief Returns true if the term is quoted.
    /// \return True if the term is quoted.
    bool is_quoted() const
    {
      return function().is_quoted();
    }

    /// \brief Returns the i-th argument.
    /// \param i A positive integer
    /// \return The argument with the given index.
    Term operator()(size_type i) const
    {
      return Term(ATgetArgument(appl(), i));
    }

    /// \brief Returns a copy of the term with the i-th child replaced by t.
    /// \deprecated
    /// \param t A term
    /// \param i A positive integer
    /// \return The term with one of its arguments replaced.
    term_appl<Term> set_argument(Term t, size_type i)
    {
      return ATsetArgument(appl(), t, i);
    }

    /// \brief Get the i-th argument of the application.
    /// \deprecated
    /// \param i A positive integer
    /// \return The argument with the given index.
    aterm argument(size_type i) const
    {
      return aterm(ATgetArgument(appl(), i));
    }

    /// \brief Get the list of arguments of the application.
    /// \deprecated
    /// \return A list containing the function arguments.
    term_list<Term> argument_list() const
    {
      return term_list<Term>(ATgetArguments(appl()));
    } */
}; 

/// \brief A term_appl with children of type aterm.
typedef term_appl<aterm> aterm_appl;

/// \cond INTERNAL_DOCS
template <typename Term>
struct aterm_traits<term_appl<Term> >
{
  // static void protect(const term_appl<Term>& t)
  // {
  //   t.protect();
  // }
  // static void unprotect(const term_appl<Term>& t)
  // {
    // t.unprotect();
  //  }
  //static void mark(const term_appl<Term>& t)
  //{
  //  t.mark();
  //}
  static ATerm term(const term_appl<Term>& t)
  {
    return t;
  }
};

template <typename T>
struct aterm_appl_traits
{
  /// \brief Protects the term t from garbage collection.
  /// \param t A term
  // static void protect(const aterm_appl& t)
  // {
  //   t.protect();
  // }

  /// \brief Unprotects the term t from garbage collection.
  /// \param t A term
  // static void unprotect(const aterm_appl& t)
  // {
  //   t.unprotect();
  // }

  /// \brief Marks t for garbage collection.
  /// \param t A term
  // static void mark(const aterm_appl& t)
  // {
  //   t.mark();
  // }

  /// \brief Returns the ATerm that corresponds to the term t.
  /// \param t A term
  /// \return The ATerm that corresponds to the term t.
  // static ATerm term(const aterm_appl& t)
  // {
  //  return t.term();
  //}
};

template < typename T >
struct select_traits_base< T, typename boost::enable_if<typename boost::is_base_of<term_appl<aterm>, T>::type>::type >
{
  typedef aterm_appl_traits< T > base_type;
};
/// \endcond

/// \brief Equality operator.
/// \param x A term.
/// \param y A term.
/// \return True if the terms are equal.
/* template <typename Term>
bool operator==(const term_appl<Term>& x, const term_appl<Term>& y)
{
  return ATisEqual(aterm_traits<term_appl<Term> >::term(x), aterm_traits<term_appl<Term> >::term(y)) == true;
}

/// \brief Equality operator.
/// \param x A term.
/// \param y A term.
/// \return True if the terms are equal.
template <typename Term>
bool operator==(const term_appl<Term>& x, ATermAppl y)
{
  // return ATisEqual((ATermAppl)aterm_traits<term_appl<Term> >::term(x), y) == true;
  return (ATermAppl)aterm_traits<term_appl<Term> >::term(x)==y;
} 

/// \brief Equality operator.
/// \param x A term.
/// \param y A term.
/// \return True if the terms are equal.
template <typename Term>
bool operator==(ATermAppl x, const term_appl<Term>& y)
{
  return x==(ATermAppl)aterm_traits<term_appl<Term> >::term(y);
}

/// \brief Inequality operator.
/// \param x A term.
/// \param y A term.
/// \return True if the terms are not equal.
template <typename Term>
bool operator!=(const term_appl<Term>& x, const term_appl<Term>& y)
{
  return aterm_traits<term_appl<Term> >::term(x)!=aterm_traits<term_appl<Term> >::term(y);
}

/// \brief Inequality operator.
/// \param x A term.
/// \param y A term.
/// \return True if the terms are not equal.
template <typename Term>
bool operator!=(const term_appl<Term>& x, ATermAppl y)
{
  return ATisEqual(aterm_traits<term_appl<Term> >::term(x), y) == false;
}

/// \brief Inequality operator.
/// \param x A term.
/// \param y A term.
/// \return True if the terms are not equal.
template <typename Term>
bool operator!=(ATermAppl x, const term_appl<Term>& y)
{
  return ATisEqual(x, aterm_traits<term_appl<Term> >::term(y)) == false;
} */

} // namespace atermpp

#endif // MCRL2_ATERMPP_ATERM_APPL_H
