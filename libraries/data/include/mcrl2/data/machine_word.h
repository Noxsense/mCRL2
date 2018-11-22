// Author(s): Jeroen Keiren
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/data/machine_word.h
/// \brief The standard sort machine_word.
///
/// This file was generated from the data sort specification
/// mcrl2/data/build/machine_word.spec.

#ifndef MCRL2_DATA_MACHINE_WORD_H
#define MCRL2_DATA_MACHINE_WORD_H

#include "mcrl2/utilities/exception.h"
#include "mcrl2/data/basic_sort.h"
#include "mcrl2/data/function_sort.h"
#include "mcrl2/data/function_symbol.h"
#include "mcrl2/data/application.h"
#include "mcrl2/data/data_equation.h"
#include "mcrl2/data/standard.h"

namespace mcrl2 {

  namespace data {

    /// \brief Namespace for system defined sort machine_word
    namespace sort_machine_word {

      inline
      core::identifier_string const& machine_word_name()
      {
        static core::identifier_string machine_word_name = core::identifier_string("@word");
        return machine_word_name;
      }

      /// \brief Constructor for sort expression \@word
      /// \return Sort expression \@word
      inline
      basic_sort const& machine_word()
      {
        static basic_sort machine_word = basic_sort(machine_word_name());
        return machine_word;
      }

      /// \brief Recogniser for sort expression \@word
      /// \param e A sort expression
      /// \return true iff e == machine_word()
      inline
      bool is_machine_word(const sort_expression& e)
      {
        if (is_basic_sort(e))
        {
          return basic_sort(e) == machine_word();
        }
        return false;
      }


      /// \brief Generate identifier zero_word
      /// \return Identifier zero_word
      inline
      core::identifier_string const& zero64_name()
      {
        static core::identifier_string zero64_name = core::identifier_string("zero_word");
        return zero64_name;
      }

      /// \brief Constructor for function symbol zero_word
      
      /// \return Function symbol zero64
      inline
      function_symbol const& zero64()
      {
        static function_symbol zero64(zero64_name(), machine_word());
        return zero64;
      }

      /// \brief Recogniser for function zero_word
      /// \param e A data expression
      /// \return true iff e is the function symbol matching zero_word
      inline
      bool is_zero64_function_symbol(const atermpp::aterm& e)
      {
        if (is_function_symbol(e))
        {
          return function_symbol(e) == zero64();
        }
        return false;
      }

      /// \brief Generate identifier succ_word
      /// \return Identifier succ_word
      inline
      core::identifier_string const& succ64_name()
      {
        static core::identifier_string succ64_name = core::identifier_string("succ_word");
        return succ64_name;
      }

      /// \brief Constructor for function symbol succ_word
      
      /// \return Function symbol succ64
      inline
      function_symbol const& succ64()
      {
        static function_symbol succ64(succ64_name(), make_function_sort(machine_word(), machine_word()));
        return succ64;
      }

      /// \brief Recogniser for function succ_word
      /// \param e A data expression
      /// \return true iff e is the function symbol matching succ_word
      inline
      bool is_succ64_function_symbol(const atermpp::aterm& e)
      {
        if (is_function_symbol(e))
        {
          return function_symbol(e) == succ64();
        }
        return false;
      }

      /// \brief Application of function symbol succ_word
      
      /// \param arg0 A data expression
      /// \return Application of succ_word to a number of arguments
      inline
      application succ64(const data_expression& arg0)
      {
        return sort_machine_word::succ64()(arg0);
      }

      /// \brief Recogniser for application of succ_word
      /// \param e A data expression
      /// \return true iff e is an application of function symbol succ64 to a
      ///     number of arguments
      inline
      bool is_succ64_application(const atermpp::aterm& e)
      {
        if (is_application(e))
        {
          return is_succ64_function_symbol(atermpp::down_cast<application>(e).head());
        }
        return false;
      }
      /// \brief Give all system defined constructors for machine_word
      /// \return All system defined constructors for machine_word
      inline
      function_symbol_vector machine_word_generate_constructors_code()
      {
        function_symbol_vector result;
        result.push_back(sort_machine_word::zero64());
        result.push_back(sort_machine_word::succ64());

        return result;
      }

      /// \brief Generate identifier \@one_word
      /// \return Identifier \@one_word
      inline
      core::identifier_string const& one_word_name()
      {
        static core::identifier_string one_word_name = core::identifier_string("@one_word");
        return one_word_name;
      }

      /// \brief Constructor for function symbol \@one_word
      
      /// \return Function symbol one_word
      inline
      function_symbol const& one_word()
      {
        static function_symbol one_word(one_word_name(), machine_word());
        return one_word;
      }

      /// \brief Recogniser for function \@one_word
      /// \param e A data expression
      /// \return true iff e is the function symbol matching \@one_word
      inline
      bool is_one_word_function_symbol(const atermpp::aterm& e)
      {
        if (is_function_symbol(e))
        {
          return function_symbol(e) == one_word();
        }
        return false;
      }

      /// \brief Generate identifier \@max_word
      /// \return Identifier \@max_word
      inline
      core::identifier_string const& max_word_name()
      {
        static core::identifier_string max_word_name = core::identifier_string("@max_word");
        return max_word_name;
      }

      /// \brief Constructor for function symbol \@max_word
      
      /// \return Function symbol max_word
      inline
      function_symbol const& max_word()
      {
        static function_symbol max_word(max_word_name(), machine_word());
        return max_word;
      }

      /// \brief Recogniser for function \@max_word
      /// \param e A data expression
      /// \return true iff e is the function symbol matching \@max_word
      inline
      bool is_max_word_function_symbol(const atermpp::aterm& e)
      {
        if (is_function_symbol(e))
        {
          return function_symbol(e) == max_word();
        }
        return false;
      }

      /// \brief Generate identifier \@add_word
      /// \return Identifier \@add_word
      inline
      core::identifier_string const& add_word_name()
      {
        static core::identifier_string add_word_name = core::identifier_string("@add_word");
        return add_word_name;
      }

      /// \brief Constructor for function symbol \@add_word
      
      /// \return Function symbol add_word
      inline
      function_symbol const& add_word()
      {
        static function_symbol add_word(add_word_name(), make_function_sort(machine_word(), machine_word(), machine_word()));
        return add_word;
      }

      /// \brief Recogniser for function \@add_word
      /// \param e A data expression
      /// \return true iff e is the function symbol matching \@add_word
      inline
      bool is_add_word_function_symbol(const atermpp::aterm& e)
      {
        if (is_function_symbol(e))
        {
          return function_symbol(e) == add_word();
        }
        return false;
      }

      /// \brief Application of function symbol \@add_word
      
      /// \param arg0 A data expression
      /// \param arg1 A data expression
      /// \return Application of \@add_word to a number of arguments
      inline
      application add_word(const data_expression& arg0, const data_expression& arg1)
      {
        return sort_machine_word::add_word()(arg0, arg1);
      }

      /// \brief Recogniser for application of \@add_word
      /// \param e A data expression
      /// \return true iff e is an application of function symbol add_word to a
      ///     number of arguments
      inline
      bool is_add_word_application(const atermpp::aterm& e)
      {
        if (is_application(e))
        {
          return is_add_word_function_symbol(atermpp::down_cast<application>(e).head());
        }
        return false;
      }

      /// \brief Generate identifier \@add_overflow_word
      /// \return Identifier \@add_overflow_word
      inline
      core::identifier_string const& add_overflow_name()
      {
        static core::identifier_string add_overflow_name = core::identifier_string("@add_overflow_word");
        return add_overflow_name;
      }

      /// \brief Constructor for function symbol \@add_overflow_word
      
      /// \return Function symbol add_overflow
      inline
      function_symbol const& add_overflow()
      {
        static function_symbol add_overflow(add_overflow_name(), make_function_sort(machine_word(), machine_word(), machine_word()));
        return add_overflow;
      }

      /// \brief Recogniser for function \@add_overflow_word
      /// \param e A data expression
      /// \return true iff e is the function symbol matching \@add_overflow_word
      inline
      bool is_add_overflow_function_symbol(const atermpp::aterm& e)
      {
        if (is_function_symbol(e))
        {
          return function_symbol(e) == add_overflow();
        }
        return false;
      }

      /// \brief Application of function symbol \@add_overflow_word
      
      /// \param arg0 A data expression
      /// \param arg1 A data expression
      /// \return Application of \@add_overflow_word to a number of arguments
      inline
      application add_overflow(const data_expression& arg0, const data_expression& arg1)
      {
        return sort_machine_word::add_overflow()(arg0, arg1);
      }

      /// \brief Recogniser for application of \@add_overflow_word
      /// \param e A data expression
      /// \return true iff e is an application of function symbol add_overflow to a
      ///     number of arguments
      inline
      bool is_add_overflow_application(const atermpp::aterm& e)
      {
        if (is_application(e))
        {
          return is_add_overflow_function_symbol(atermpp::down_cast<application>(e).head());
        }
        return false;
      }

      /// \brief Generate identifier \@times_word
      /// \return Identifier \@times_word
      inline
      core::identifier_string const& times_word_name()
      {
        static core::identifier_string times_word_name = core::identifier_string("@times_word");
        return times_word_name;
      }

      /// \brief Constructor for function symbol \@times_word
      
      /// \return Function symbol times_word
      inline
      function_symbol const& times_word()
      {
        static function_symbol times_word(times_word_name(), make_function_sort(machine_word(), machine_word(), machine_word()));
        return times_word;
      }

      /// \brief Recogniser for function \@times_word
      /// \param e A data expression
      /// \return true iff e is the function symbol matching \@times_word
      inline
      bool is_times_word_function_symbol(const atermpp::aterm& e)
      {
        if (is_function_symbol(e))
        {
          return function_symbol(e) == times_word();
        }
        return false;
      }

      /// \brief Application of function symbol \@times_word
      
      /// \param arg0 A data expression
      /// \param arg1 A data expression
      /// \return Application of \@times_word to a number of arguments
      inline
      application times_word(const data_expression& arg0, const data_expression& arg1)
      {
        return sort_machine_word::times_word()(arg0, arg1);
      }

      /// \brief Recogniser for application of \@times_word
      /// \param e A data expression
      /// \return true iff e is an application of function symbol times_word to a
      ///     number of arguments
      inline
      bool is_times_word_application(const atermpp::aterm& e)
      {
        if (is_application(e))
        {
          return is_times_word_function_symbol(atermpp::down_cast<application>(e).head());
        }
        return false;
      }

      /// \brief Generate identifier \@times_overflow_word
      /// \return Identifier \@times_overflow_word
      inline
      core::identifier_string const& timew_overflow_word_name()
      {
        static core::identifier_string timew_overflow_word_name = core::identifier_string("@times_overflow_word");
        return timew_overflow_word_name;
      }

      /// \brief Constructor for function symbol \@times_overflow_word
      
      /// \return Function symbol timew_overflow_word
      inline
      function_symbol const& timew_overflow_word()
      {
        static function_symbol timew_overflow_word(timew_overflow_word_name(), make_function_sort(machine_word(), machine_word(), machine_word()));
        return timew_overflow_word;
      }

      /// \brief Recogniser for function \@times_overflow_word
      /// \param e A data expression
      /// \return true iff e is the function symbol matching \@times_overflow_word
      inline
      bool is_timew_overflow_word_function_symbol(const atermpp::aterm& e)
      {
        if (is_function_symbol(e))
        {
          return function_symbol(e) == timew_overflow_word();
        }
        return false;
      }

      /// \brief Application of function symbol \@times_overflow_word
      
      /// \param arg0 A data expression
      /// \param arg1 A data expression
      /// \return Application of \@times_overflow_word to a number of arguments
      inline
      application timew_overflow_word(const data_expression& arg0, const data_expression& arg1)
      {
        return sort_machine_word::timew_overflow_word()(arg0, arg1);
      }

      /// \brief Recogniser for application of \@times_overflow_word
      /// \param e A data expression
      /// \return true iff e is an application of function symbol timew_overflow_word to a
      ///     number of arguments
      inline
      bool is_timew_overflow_word_application(const atermpp::aterm& e)
      {
        if (is_application(e))
        {
          return is_timew_overflow_word_function_symbol(atermpp::down_cast<application>(e).head());
        }
        return false;
      }

      /// \brief Generate identifier \@minus_word
      /// \return Identifier \@minus_word
      inline
      core::identifier_string const& minus_word_name()
      {
        static core::identifier_string minus_word_name = core::identifier_string("@minus_word");
        return minus_word_name;
      }

      /// \brief Constructor for function symbol \@minus_word
      
      /// \return Function symbol minus_word
      inline
      function_symbol const& minus_word()
      {
        static function_symbol minus_word(minus_word_name(), make_function_sort(machine_word(), machine_word(), machine_word()));
        return minus_word;
      }

      /// \brief Recogniser for function \@minus_word
      /// \param e A data expression
      /// \return true iff e is the function symbol matching \@minus_word
      inline
      bool is_minus_word_function_symbol(const atermpp::aterm& e)
      {
        if (is_function_symbol(e))
        {
          return function_symbol(e) == minus_word();
        }
        return false;
      }

      /// \brief Application of function symbol \@minus_word
      
      /// \param arg0 A data expression
      /// \param arg1 A data expression
      /// \return Application of \@minus_word to a number of arguments
      inline
      application minus_word(const data_expression& arg0, const data_expression& arg1)
      {
        return sort_machine_word::minus_word()(arg0, arg1);
      }

      /// \brief Recogniser for application of \@minus_word
      /// \param e A data expression
      /// \return true iff e is an application of function symbol minus_word to a
      ///     number of arguments
      inline
      bool is_minus_word_application(const atermpp::aterm& e)
      {
        if (is_application(e))
        {
          return is_minus_word_function_symbol(atermpp::down_cast<application>(e).head());
        }
        return false;
      }

      /// \brief Generate identifier \@div_word
      /// \return Identifier \@div_word
      inline
      core::identifier_string const& div_word_name()
      {
        static core::identifier_string div_word_name = core::identifier_string("@div_word");
        return div_word_name;
      }

      /// \brief Constructor for function symbol \@div_word
      
      /// \return Function symbol div_word
      inline
      function_symbol const& div_word()
      {
        static function_symbol div_word(div_word_name(), make_function_sort(machine_word(), machine_word(), machine_word()));
        return div_word;
      }

      /// \brief Recogniser for function \@div_word
      /// \param e A data expression
      /// \return true iff e is the function symbol matching \@div_word
      inline
      bool is_div_word_function_symbol(const atermpp::aterm& e)
      {
        if (is_function_symbol(e))
        {
          return function_symbol(e) == div_word();
        }
        return false;
      }

      /// \brief Application of function symbol \@div_word
      
      /// \param arg0 A data expression
      /// \param arg1 A data expression
      /// \return Application of \@div_word to a number of arguments
      inline
      application div_word(const data_expression& arg0, const data_expression& arg1)
      {
        return sort_machine_word::div_word()(arg0, arg1);
      }

      /// \brief Recogniser for application of \@div_word
      /// \param e A data expression
      /// \return true iff e is an application of function symbol div_word to a
      ///     number of arguments
      inline
      bool is_div_word_application(const atermpp::aterm& e)
      {
        if (is_application(e))
        {
          return is_div_word_function_symbol(atermpp::down_cast<application>(e).head());
        }
        return false;
      }

      /// \brief Generate identifier \@mod_word
      /// \return Identifier \@mod_word
      inline
      core::identifier_string const& mod_word_name()
      {
        static core::identifier_string mod_word_name = core::identifier_string("@mod_word");
        return mod_word_name;
      }

      /// \brief Constructor for function symbol \@mod_word
      
      /// \return Function symbol mod_word
      inline
      function_symbol const& mod_word()
      {
        static function_symbol mod_word(mod_word_name(), make_function_sort(machine_word(), machine_word(), machine_word()));
        return mod_word;
      }

      /// \brief Recogniser for function \@mod_word
      /// \param e A data expression
      /// \return true iff e is the function symbol matching \@mod_word
      inline
      bool is_mod_word_function_symbol(const atermpp::aterm& e)
      {
        if (is_function_symbol(e))
        {
          return function_symbol(e) == mod_word();
        }
        return false;
      }

      /// \brief Application of function symbol \@mod_word
      
      /// \param arg0 A data expression
      /// \param arg1 A data expression
      /// \return Application of \@mod_word to a number of arguments
      inline
      application mod_word(const data_expression& arg0, const data_expression& arg1)
      {
        return sort_machine_word::mod_word()(arg0, arg1);
      }

      /// \brief Recogniser for application of \@mod_word
      /// \param e A data expression
      /// \return true iff e is an application of function symbol mod_word to a
      ///     number of arguments
      inline
      bool is_mod_word_application(const atermpp::aterm& e)
      {
        if (is_application(e))
        {
          return is_mod_word_function_symbol(atermpp::down_cast<application>(e).head());
        }
        return false;
      }

      /// \brief Generate identifier \@sqrt_word
      /// \return Identifier \@sqrt_word
      inline
      core::identifier_string const& sqrt_word_name()
      {
        static core::identifier_string sqrt_word_name = core::identifier_string("@sqrt_word");
        return sqrt_word_name;
      }

      /// \brief Constructor for function symbol \@sqrt_word
      
      /// \return Function symbol sqrt_word
      inline
      function_symbol const& sqrt_word()
      {
        static function_symbol sqrt_word(sqrt_word_name(), make_function_sort(machine_word(), machine_word()));
        return sqrt_word;
      }

      /// \brief Recogniser for function \@sqrt_word
      /// \param e A data expression
      /// \return true iff e is the function symbol matching \@sqrt_word
      inline
      bool is_sqrt_word_function_symbol(const atermpp::aterm& e)
      {
        if (is_function_symbol(e))
        {
          return function_symbol(e) == sqrt_word();
        }
        return false;
      }

      /// \brief Application of function symbol \@sqrt_word
      
      /// \param arg0 A data expression
      /// \return Application of \@sqrt_word to a number of arguments
      inline
      application sqrt_word(const data_expression& arg0)
      {
        return sort_machine_word::sqrt_word()(arg0);
      }

      /// \brief Recogniser for application of \@sqrt_word
      /// \param e A data expression
      /// \return true iff e is an application of function symbol sqrt_word to a
      ///     number of arguments
      inline
      bool is_sqrt_word_application(const atermpp::aterm& e)
      {
        if (is_application(e))
        {
          return is_sqrt_word_function_symbol(atermpp::down_cast<application>(e).head());
        }
        return false;
      }

      /// \brief Generate identifier \@div_doubleword
      /// \return Identifier \@div_doubleword
      inline
      core::identifier_string const& div_doubleword_name()
      {
        static core::identifier_string div_doubleword_name = core::identifier_string("@div_doubleword");
        return div_doubleword_name;
      }

      /// \brief Constructor for function symbol \@div_doubleword
      
      /// \return Function symbol div_doubleword
      inline
      function_symbol const& div_doubleword()
      {
        static function_symbol div_doubleword(div_doubleword_name(), make_function_sort(machine_word(), machine_word(), machine_word(), machine_word()));
        return div_doubleword;
      }

      /// \brief Recogniser for function \@div_doubleword
      /// \param e A data expression
      /// \return true iff e is the function symbol matching \@div_doubleword
      inline
      bool is_div_doubleword_function_symbol(const atermpp::aterm& e)
      {
        if (is_function_symbol(e))
        {
          return function_symbol(e) == div_doubleword();
        }
        return false;
      }

      /// \brief Application of function symbol \@div_doubleword
      
      /// \param arg0 A data expression
      /// \param arg1 A data expression
      /// \param arg2 A data expression
      /// \return Application of \@div_doubleword to a number of arguments
      inline
      application div_doubleword(const data_expression& arg0, const data_expression& arg1, const data_expression& arg2)
      {
        return sort_machine_word::div_doubleword()(arg0, arg1, arg2);
      }

      /// \brief Recogniser for application of \@div_doubleword
      /// \param e A data expression
      /// \return true iff e is an application of function symbol div_doubleword to a
      ///     number of arguments
      inline
      bool is_div_doubleword_application(const atermpp::aterm& e)
      {
        if (is_application(e))
        {
          return is_div_doubleword_function_symbol(atermpp::down_cast<application>(e).head());
        }
        return false;
      }

      /// \brief Generate identifier \@div_double_doubleword
      /// \return Identifier \@div_double_doubleword
      inline
      core::identifier_string const& div_double_doubleword_name()
      {
        static core::identifier_string div_double_doubleword_name = core::identifier_string("@div_double_doubleword");
        return div_double_doubleword_name;
      }

      /// \brief Constructor for function symbol \@div_double_doubleword
      
      /// \return Function symbol div_double_doubleword
      inline
      function_symbol const& div_double_doubleword()
      {
        static function_symbol div_double_doubleword(div_double_doubleword_name(), make_function_sort(machine_word(), machine_word(), machine_word(), machine_word(), machine_word()));
        return div_double_doubleword;
      }

      /// \brief Recogniser for function \@div_double_doubleword
      /// \param e A data expression
      /// \return true iff e is the function symbol matching \@div_double_doubleword
      inline
      bool is_div_double_doubleword_function_symbol(const atermpp::aterm& e)
      {
        if (is_function_symbol(e))
        {
          return function_symbol(e) == div_double_doubleword();
        }
        return false;
      }

      /// \brief Application of function symbol \@div_double_doubleword
      
      /// \param arg0 A data expression
      /// \param arg1 A data expression
      /// \param arg2 A data expression
      /// \param arg3 A data expression
      /// \return Application of \@div_double_doubleword to a number of arguments
      inline
      application div_double_doubleword(const data_expression& arg0, const data_expression& arg1, const data_expression& arg2, const data_expression& arg3)
      {
        return sort_machine_word::div_double_doubleword()(arg0, arg1, arg2, arg3);
      }

      /// \brief Recogniser for application of \@div_double_doubleword
      /// \param e A data expression
      /// \return true iff e is an application of function symbol div_double_doubleword to a
      ///     number of arguments
      inline
      bool is_div_double_doubleword_application(const atermpp::aterm& e)
      {
        if (is_application(e))
        {
          return is_div_double_doubleword_function_symbol(atermpp::down_cast<application>(e).head());
        }
        return false;
      }

      /// \brief Generate identifier \@div_triple_doubleword
      /// \return Identifier \@div_triple_doubleword
      inline
      core::identifier_string const& div_triple_doubleword_name()
      {
        static core::identifier_string div_triple_doubleword_name = core::identifier_string("@div_triple_doubleword");
        return div_triple_doubleword_name;
      }

      /// \brief Constructor for function symbol \@div_triple_doubleword
      
      /// \return Function symbol div_triple_doubleword
      inline
      function_symbol const& div_triple_doubleword()
      {
        static function_symbol div_triple_doubleword(div_triple_doubleword_name(), make_function_sort(machine_word(), machine_word(), machine_word(), machine_word(), machine_word(), machine_word()));
        return div_triple_doubleword;
      }

      /// \brief Recogniser for function \@div_triple_doubleword
      /// \param e A data expression
      /// \return true iff e is the function symbol matching \@div_triple_doubleword
      inline
      bool is_div_triple_doubleword_function_symbol(const atermpp::aterm& e)
      {
        if (is_function_symbol(e))
        {
          return function_symbol(e) == div_triple_doubleword();
        }
        return false;
      }

      /// \brief Application of function symbol \@div_triple_doubleword
      
      /// \param arg0 A data expression
      /// \param arg1 A data expression
      /// \param arg2 A data expression
      /// \param arg3 A data expression
      /// \param arg4 A data expression
      /// \return Application of \@div_triple_doubleword to a number of arguments
      inline
      application div_triple_doubleword(const data_expression& arg0, const data_expression& arg1, const data_expression& arg2, const data_expression& arg3, const data_expression& arg4)
      {
        return sort_machine_word::div_triple_doubleword()(arg0, arg1, arg2, arg3, arg4);
      }

      /// \brief Recogniser for application of \@div_triple_doubleword
      /// \param e A data expression
      /// \return true iff e is an application of function symbol div_triple_doubleword to a
      ///     number of arguments
      inline
      bool is_div_triple_doubleword_application(const atermpp::aterm& e)
      {
        if (is_application(e))
        {
          return is_div_triple_doubleword_function_symbol(atermpp::down_cast<application>(e).head());
        }
        return false;
      }

      /// \brief Generate identifier \@mod_doubleword
      /// \return Identifier \@mod_doubleword
      inline
      core::identifier_string const& mod_doubleword_name()
      {
        static core::identifier_string mod_doubleword_name = core::identifier_string("@mod_doubleword");
        return mod_doubleword_name;
      }

      /// \brief Constructor for function symbol \@mod_doubleword
      
      /// \return Function symbol mod_doubleword
      inline
      function_symbol const& mod_doubleword()
      {
        static function_symbol mod_doubleword(mod_doubleword_name(), make_function_sort(machine_word(), machine_word(), machine_word(), machine_word()));
        return mod_doubleword;
      }

      /// \brief Recogniser for function \@mod_doubleword
      /// \param e A data expression
      /// \return true iff e is the function symbol matching \@mod_doubleword
      inline
      bool is_mod_doubleword_function_symbol(const atermpp::aterm& e)
      {
        if (is_function_symbol(e))
        {
          return function_symbol(e) == mod_doubleword();
        }
        return false;
      }

      /// \brief Application of function symbol \@mod_doubleword
      
      /// \param arg0 A data expression
      /// \param arg1 A data expression
      /// \param arg2 A data expression
      /// \return Application of \@mod_doubleword to a number of arguments
      inline
      application mod_doubleword(const data_expression& arg0, const data_expression& arg1, const data_expression& arg2)
      {
        return sort_machine_word::mod_doubleword()(arg0, arg1, arg2);
      }

      /// \brief Recogniser for application of \@mod_doubleword
      /// \param e A data expression
      /// \return true iff e is an application of function symbol mod_doubleword to a
      ///     number of arguments
      inline
      bool is_mod_doubleword_application(const atermpp::aterm& e)
      {
        if (is_application(e))
        {
          return is_mod_doubleword_function_symbol(atermpp::down_cast<application>(e).head());
        }
        return false;
      }

      /// \brief Generate identifier \@sqrt_doubleword
      /// \return Identifier \@sqrt_doubleword
      inline
      core::identifier_string const& sqrt_doubleword_name()
      {
        static core::identifier_string sqrt_doubleword_name = core::identifier_string("@sqrt_doubleword");
        return sqrt_doubleword_name;
      }

      /// \brief Constructor for function symbol \@sqrt_doubleword
      
      /// \return Function symbol sqrt_doubleword
      inline
      function_symbol const& sqrt_doubleword()
      {
        static function_symbol sqrt_doubleword(sqrt_doubleword_name(), make_function_sort(machine_word(), machine_word(), machine_word()));
        return sqrt_doubleword;
      }

      /// \brief Recogniser for function \@sqrt_doubleword
      /// \param e A data expression
      /// \return true iff e is the function symbol matching \@sqrt_doubleword
      inline
      bool is_sqrt_doubleword_function_symbol(const atermpp::aterm& e)
      {
        if (is_function_symbol(e))
        {
          return function_symbol(e) == sqrt_doubleword();
        }
        return false;
      }

      /// \brief Application of function symbol \@sqrt_doubleword
      
      /// \param arg0 A data expression
      /// \param arg1 A data expression
      /// \return Application of \@sqrt_doubleword to a number of arguments
      inline
      application sqrt_doubleword(const data_expression& arg0, const data_expression& arg1)
      {
        return sort_machine_word::sqrt_doubleword()(arg0, arg1);
      }

      /// \brief Recogniser for application of \@sqrt_doubleword
      /// \param e A data expression
      /// \return true iff e is an application of function symbol sqrt_doubleword to a
      ///     number of arguments
      inline
      bool is_sqrt_doubleword_application(const atermpp::aterm& e)
      {
        if (is_application(e))
        {
          return is_sqrt_doubleword_function_symbol(atermpp::down_cast<application>(e).head());
        }
        return false;
      }

      /// \brief Generate identifier \@sqrt_tripleword
      /// \return Identifier \@sqrt_tripleword
      inline
      core::identifier_string const& sqrt_tripleword_name()
      {
        static core::identifier_string sqrt_tripleword_name = core::identifier_string("@sqrt_tripleword");
        return sqrt_tripleword_name;
      }

      /// \brief Constructor for function symbol \@sqrt_tripleword
      
      /// \return Function symbol sqrt_tripleword
      inline
      function_symbol const& sqrt_tripleword()
      {
        static function_symbol sqrt_tripleword(sqrt_tripleword_name(), make_function_sort(machine_word(), machine_word(), machine_word(), machine_word()));
        return sqrt_tripleword;
      }

      /// \brief Recogniser for function \@sqrt_tripleword
      /// \param e A data expression
      /// \return true iff e is the function symbol matching \@sqrt_tripleword
      inline
      bool is_sqrt_tripleword_function_symbol(const atermpp::aterm& e)
      {
        if (is_function_symbol(e))
        {
          return function_symbol(e) == sqrt_tripleword();
        }
        return false;
      }

      /// \brief Application of function symbol \@sqrt_tripleword
      
      /// \param arg0 A data expression
      /// \param arg1 A data expression
      /// \param arg2 A data expression
      /// \return Application of \@sqrt_tripleword to a number of arguments
      inline
      application sqrt_tripleword(const data_expression& arg0, const data_expression& arg1, const data_expression& arg2)
      {
        return sort_machine_word::sqrt_tripleword()(arg0, arg1, arg2);
      }

      /// \brief Recogniser for application of \@sqrt_tripleword
      /// \param e A data expression
      /// \return true iff e is an application of function symbol sqrt_tripleword to a
      ///     number of arguments
      inline
      bool is_sqrt_tripleword_application(const atermpp::aterm& e)
      {
        if (is_application(e))
        {
          return is_sqrt_tripleword_function_symbol(atermpp::down_cast<application>(e).head());
        }
        return false;
      }

      /// \brief Generate identifier \@sqrt_tripleword_overflow
      /// \return Identifier \@sqrt_tripleword_overflow
      inline
      core::identifier_string const& sqrt_tripleword_overflow_name()
      {
        static core::identifier_string sqrt_tripleword_overflow_name = core::identifier_string("@sqrt_tripleword_overflow");
        return sqrt_tripleword_overflow_name;
      }

      /// \brief Constructor for function symbol \@sqrt_tripleword_overflow
      
      /// \return Function symbol sqrt_tripleword_overflow
      inline
      function_symbol const& sqrt_tripleword_overflow()
      {
        static function_symbol sqrt_tripleword_overflow(sqrt_tripleword_overflow_name(), make_function_sort(machine_word(), machine_word(), machine_word(), machine_word()));
        return sqrt_tripleword_overflow;
      }

      /// \brief Recogniser for function \@sqrt_tripleword_overflow
      /// \param e A data expression
      /// \return true iff e is the function symbol matching \@sqrt_tripleword_overflow
      inline
      bool is_sqrt_tripleword_overflow_function_symbol(const atermpp::aterm& e)
      {
        if (is_function_symbol(e))
        {
          return function_symbol(e) == sqrt_tripleword_overflow();
        }
        return false;
      }

      /// \brief Application of function symbol \@sqrt_tripleword_overflow
      
      /// \param arg0 A data expression
      /// \param arg1 A data expression
      /// \param arg2 A data expression
      /// \return Application of \@sqrt_tripleword_overflow to a number of arguments
      inline
      application sqrt_tripleword_overflow(const data_expression& arg0, const data_expression& arg1, const data_expression& arg2)
      {
        return sort_machine_word::sqrt_tripleword_overflow()(arg0, arg1, arg2);
      }

      /// \brief Recogniser for application of \@sqrt_tripleword_overflow
      /// \param e A data expression
      /// \return true iff e is an application of function symbol sqrt_tripleword_overflow to a
      ///     number of arguments
      inline
      bool is_sqrt_tripleword_overflow_application(const atermpp::aterm& e)
      {
        if (is_application(e))
        {
          return is_sqrt_tripleword_overflow_function_symbol(atermpp::down_cast<application>(e).head());
        }
        return false;
      }

      /// \brief Generate identifier \@sqrt_quadrupleword
      /// \return Identifier \@sqrt_quadrupleword
      inline
      core::identifier_string const& sqrt_quadrupleword_name()
      {
        static core::identifier_string sqrt_quadrupleword_name = core::identifier_string("@sqrt_quadrupleword");
        return sqrt_quadrupleword_name;
      }

      /// \brief Constructor for function symbol \@sqrt_quadrupleword
      
      /// \return Function symbol sqrt_quadrupleword
      inline
      function_symbol const& sqrt_quadrupleword()
      {
        static function_symbol sqrt_quadrupleword(sqrt_quadrupleword_name(), make_function_sort(machine_word(), machine_word(), machine_word(), machine_word(), machine_word()));
        return sqrt_quadrupleword;
      }

      /// \brief Recogniser for function \@sqrt_quadrupleword
      /// \param e A data expression
      /// \return true iff e is the function symbol matching \@sqrt_quadrupleword
      inline
      bool is_sqrt_quadrupleword_function_symbol(const atermpp::aterm& e)
      {
        if (is_function_symbol(e))
        {
          return function_symbol(e) == sqrt_quadrupleword();
        }
        return false;
      }

      /// \brief Application of function symbol \@sqrt_quadrupleword
      
      /// \param arg0 A data expression
      /// \param arg1 A data expression
      /// \param arg2 A data expression
      /// \param arg3 A data expression
      /// \return Application of \@sqrt_quadrupleword to a number of arguments
      inline
      application sqrt_quadrupleword(const data_expression& arg0, const data_expression& arg1, const data_expression& arg2, const data_expression& arg3)
      {
        return sort_machine_word::sqrt_quadrupleword()(arg0, arg1, arg2, arg3);
      }

      /// \brief Recogniser for application of \@sqrt_quadrupleword
      /// \param e A data expression
      /// \return true iff e is an application of function symbol sqrt_quadrupleword to a
      ///     number of arguments
      inline
      bool is_sqrt_quadrupleword_application(const atermpp::aterm& e)
      {
        if (is_application(e))
        {
          return is_sqrt_quadrupleword_function_symbol(atermpp::down_cast<application>(e).head());
        }
        return false;
      }

      /// \brief Generate identifier \@sqrt_quadrupleword_overflow
      /// \return Identifier \@sqrt_quadrupleword_overflow
      inline
      core::identifier_string const& sqrt_quadrupleword_overflow_name()
      {
        static core::identifier_string sqrt_quadrupleword_overflow_name = core::identifier_string("@sqrt_quadrupleword_overflow");
        return sqrt_quadrupleword_overflow_name;
      }

      /// \brief Constructor for function symbol \@sqrt_quadrupleword_overflow
      
      /// \return Function symbol sqrt_quadrupleword_overflow
      inline
      function_symbol const& sqrt_quadrupleword_overflow()
      {
        static function_symbol sqrt_quadrupleword_overflow(sqrt_quadrupleword_overflow_name(), make_function_sort(machine_word(), machine_word(), machine_word(), machine_word(), machine_word()));
        return sqrt_quadrupleword_overflow;
      }

      /// \brief Recogniser for function \@sqrt_quadrupleword_overflow
      /// \param e A data expression
      /// \return true iff e is the function symbol matching \@sqrt_quadrupleword_overflow
      inline
      bool is_sqrt_quadrupleword_overflow_function_symbol(const atermpp::aterm& e)
      {
        if (is_function_symbol(e))
        {
          return function_symbol(e) == sqrt_quadrupleword_overflow();
        }
        return false;
      }

      /// \brief Application of function symbol \@sqrt_quadrupleword_overflow
      
      /// \param arg0 A data expression
      /// \param arg1 A data expression
      /// \param arg2 A data expression
      /// \param arg3 A data expression
      /// \return Application of \@sqrt_quadrupleword_overflow to a number of arguments
      inline
      application sqrt_quadrupleword_overflow(const data_expression& arg0, const data_expression& arg1, const data_expression& arg2, const data_expression& arg3)
      {
        return sort_machine_word::sqrt_quadrupleword_overflow()(arg0, arg1, arg2, arg3);
      }

      /// \brief Recogniser for application of \@sqrt_quadrupleword_overflow
      /// \param e A data expression
      /// \return true iff e is an application of function symbol sqrt_quadrupleword_overflow to a
      ///     number of arguments
      inline
      bool is_sqrt_quadrupleword_overflow_application(const atermpp::aterm& e)
      {
        if (is_application(e))
        {
          return is_sqrt_quadrupleword_overflow_function_symbol(atermpp::down_cast<application>(e).head());
        }
        return false;
      }

      /// \brief Generate identifier \@pred_word
      /// \return Identifier \@pred_word
      inline
      core::identifier_string const& pred_word_name()
      {
        static core::identifier_string pred_word_name = core::identifier_string("@pred_word");
        return pred_word_name;
      }

      /// \brief Constructor for function symbol \@pred_word
      
      /// \return Function symbol pred_word
      inline
      function_symbol const& pred_word()
      {
        static function_symbol pred_word(pred_word_name(), make_function_sort(machine_word(), machine_word()));
        return pred_word;
      }

      /// \brief Recogniser for function \@pred_word
      /// \param e A data expression
      /// \return true iff e is the function symbol matching \@pred_word
      inline
      bool is_pred_word_function_symbol(const atermpp::aterm& e)
      {
        if (is_function_symbol(e))
        {
          return function_symbol(e) == pred_word();
        }
        return false;
      }

      /// \brief Application of function symbol \@pred_word
      
      /// \param arg0 A data expression
      /// \return Application of \@pred_word to a number of arguments
      inline
      application pred_word(const data_expression& arg0)
      {
        return sort_machine_word::pred_word()(arg0);
      }

      /// \brief Recogniser for application of \@pred_word
      /// \param e A data expression
      /// \return true iff e is an application of function symbol pred_word to a
      ///     number of arguments
      inline
      bool is_pred_word_application(const atermpp::aterm& e)
      {
        if (is_application(e))
        {
          return is_pred_word_function_symbol(atermpp::down_cast<application>(e).head());
        }
        return false;
      }
      /// \brief Give all system defined mappings for machine_word
      /// \return All system defined mappings for machine_word
      inline
      function_symbol_vector machine_word_generate_functions_code()
      {
        function_symbol_vector result;
        result.push_back(sort_machine_word::one_word());
        result.push_back(sort_machine_word::max_word());
        result.push_back(sort_machine_word::add_word());
        result.push_back(sort_machine_word::add_overflow());
        result.push_back(sort_machine_word::times_word());
        result.push_back(sort_machine_word::timew_overflow_word());
        result.push_back(sort_machine_word::minus_word());
        result.push_back(sort_machine_word::div_word());
        result.push_back(sort_machine_word::mod_word());
        result.push_back(sort_machine_word::sqrt_word());
        result.push_back(sort_machine_word::div_doubleword());
        result.push_back(sort_machine_word::div_double_doubleword());
        result.push_back(sort_machine_word::div_triple_doubleword());
        result.push_back(sort_machine_word::mod_doubleword());
        result.push_back(sort_machine_word::sqrt_doubleword());
        result.push_back(sort_machine_word::sqrt_tripleword());
        result.push_back(sort_machine_word::sqrt_tripleword_overflow());
        result.push_back(sort_machine_word::sqrt_quadrupleword());
        result.push_back(sort_machine_word::sqrt_quadrupleword_overflow());
        result.push_back(sort_machine_word::pred_word());
        return result;
      }
      ///\brief Function for projecting out argument
      ///        right from an application
      /// \param e A data expression
      /// \pre right is defined for e
      /// \return The argument of e that corresponds to right
      inline
      data_expression right(const data_expression& e)
      {
        assert(is_add_word_application(e) || is_add_overflow_application(e) || is_times_word_application(e) || is_timew_overflow_word_application(e) || is_minus_word_application(e) || is_div_word_application(e) || is_mod_word_application(e));
        return atermpp::down_cast<const application >(e)[1];
      }

      ///\brief Function for projecting out argument
      ///        arg1 from an application
      /// \param e A data expression
      /// \pre arg1 is defined for e
      /// \return The argument of e that corresponds to arg1
      inline
      data_expression arg1(const data_expression& e)
      {
        assert(is_div_doubleword_application(e) || is_div_double_doubleword_application(e) || is_div_triple_doubleword_application(e) || is_mod_doubleword_application(e) || is_sqrt_doubleword_application(e) || is_sqrt_tripleword_application(e) || is_sqrt_tripleword_overflow_application(e) || is_sqrt_quadrupleword_application(e) || is_sqrt_quadrupleword_overflow_application(e));
        return atermpp::down_cast<const application >(e)[0];
      }

      ///\brief Function for projecting out argument
      ///        arg2 from an application
      /// \param e A data expression
      /// \pre arg2 is defined for e
      /// \return The argument of e that corresponds to arg2
      inline
      data_expression arg2(const data_expression& e)
      {
        assert(is_div_doubleword_application(e) || is_div_double_doubleword_application(e) || is_div_triple_doubleword_application(e) || is_mod_doubleword_application(e) || is_sqrt_doubleword_application(e) || is_sqrt_tripleword_application(e) || is_sqrt_tripleword_overflow_application(e) || is_sqrt_quadrupleword_application(e) || is_sqrt_quadrupleword_overflow_application(e));
        return atermpp::down_cast<const application >(e)[1];
      }

      ///\brief Function for projecting out argument
      ///        arg3 from an application
      /// \param e A data expression
      /// \pre arg3 is defined for e
      /// \return The argument of e that corresponds to arg3
      inline
      data_expression arg3(const data_expression& e)
      {
        assert(is_div_doubleword_application(e) || is_div_double_doubleword_application(e) || is_div_triple_doubleword_application(e) || is_mod_doubleword_application(e) || is_sqrt_tripleword_application(e) || is_sqrt_tripleword_overflow_application(e) || is_sqrt_quadrupleword_application(e) || is_sqrt_quadrupleword_overflow_application(e));
        return atermpp::down_cast<const application >(e)[2];
      }

      ///\brief Function for projecting out argument
      ///        arg4 from an application
      /// \param e A data expression
      /// \pre arg4 is defined for e
      /// \return The argument of e that corresponds to arg4
      inline
      data_expression arg4(const data_expression& e)
      {
        assert(is_div_double_doubleword_application(e) || is_div_triple_doubleword_application(e) || is_sqrt_quadrupleword_application(e) || is_sqrt_quadrupleword_overflow_application(e));
        return atermpp::down_cast<const application >(e)[3];
      }

      ///\brief Function for projecting out argument
      ///        arg5 from an application
      /// \param e A data expression
      /// \pre arg5 is defined for e
      /// \return The argument of e that corresponds to arg5
      inline
      data_expression arg5(const data_expression& e)
      {
        assert(is_div_triple_doubleword_application(e));
        return atermpp::down_cast<const application >(e)[4];
      }

      ///\brief Function for projecting out argument
      ///        arg from an application
      /// \param e A data expression
      /// \pre arg is defined for e
      /// \return The argument of e that corresponds to arg
      inline
      data_expression arg(const data_expression& e)
      {
        assert(is_succ64_application(e) || is_sqrt_word_application(e) || is_pred_word_application(e));
        return atermpp::down_cast<const application >(e)[0];
      }

      ///\brief Function for projecting out argument
      ///        left from an application
      /// \param e A data expression
      /// \pre left is defined for e
      /// \return The argument of e that corresponds to left
      inline
      data_expression left(const data_expression& e)
      {
        assert(is_add_word_application(e) || is_add_overflow_application(e) || is_times_word_application(e) || is_timew_overflow_word_application(e) || is_minus_word_application(e) || is_div_word_application(e) || is_mod_word_application(e));
        return atermpp::down_cast<const application >(e)[0];
      }

      /// \brief Give all system defined equations for machine_word
      /// \return All system defined equations for sort machine_word
      inline
      data_equation_vector machine_word_generate_equations_code()
      {
        variable vd("d",machine_word());

        data_equation_vector result;
        result.push_back(data_equation(variable_list({vd==d, vtrue}), vd==d, vtrue));
        return result;
      }

    } // namespace sort_machine_word

  } // namespace data

} // namespace mcrl2

#endif // MCRL2_DATA_MACHINE_WORD_H
