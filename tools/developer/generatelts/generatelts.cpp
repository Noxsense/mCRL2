// Author(s): Wieger Wesselink
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file transform.cpp

#include <csignal>
#include <iostream>
#include <fstream>
#include <memory>
#include <string>
#include <sstream>
#include <mcrl2/lps/generate_lts.h>

#include "mcrl2/data/rewriter.h"
#include "mcrl2/data/rewriter_tool.h"
#include "mcrl2/lps/generate_lts.h"
#include "mcrl2/lps/detail/lps_io.h"
#include "mcrl2/utilities/detail/io.h"
#include "mcrl2/utilities/detail/transform_tool.h"
#include "mcrl2/utilities/input_output_tool.h"

using namespace mcrl2;
using data::tools::rewriter_tool;
using utilities::detail::transform_tool;
using utilities::tools::input_output_tool;

class generatelts_tool: public rewriter_tool<input_output_tool>
{
  typedef rewriter_tool<input_output_tool> super;

  lps::generate_lts_options options;
  lps::lts_generator* current_generator = nullptr; // used for making the tool abortable

  public:
    generatelts_tool()
      : super("generatelts",
              "Wieger Wesselink",
              "generates an LTS from an LPS",
              "Transforms the LPS in INFILE and writes a corresponding LTS in .aut format "
              " to OUTFILE. If OUTFILE is not present, stdout is used. If INFILE is not "
              " present, stdin is used."
             )
    {}

    void add_options(utilities::interface_description& desc) override
    {
      super::add_options(desc);
      desc.add_option("cached", "cache enumerator solutions");
      desc.add_option("global-cache", "use a global cache");
      desc.add_option("confluence", "apply confluence reduction", 'c');
      desc.add_option("no-one-point-rule-rewrite", "do not apply the one point rule rewriter");
      desc.add_option("no-replace-constants-by-variables", "do not move constant expressions to a substitution");
      desc.add_option("no-resolve-summand-variable-name-clashes", "do not resolve summand variable name clashes");
      options.rewrite_strategy = rewrite_strategy();
    }

    void parse_options(const utilities::command_line_parser& parser) override
    {
      super::parse_options(parser);
      options.cached                                = parser.options.find("cached") != parser.options.end();
      options.global_cache                          = parser.options.find("global-cache") != parser.options.end();
      options.confluence                            = parser.options.find("confluence") != parser.options.end();
      options.one_point_rule_rewrite                = parser.options.find("no-one-point-rule-rewrite") == parser.options.end();
      options.replace_constants_by_variables        = parser.options.find("no-replace-constants-by-variables") == parser.options.end();
      options.resolve_summand_variable_name_clashes = parser.options.find("no-resolve-summand-variable-name-clashes") == parser.options.end();
    }

    bool run() override
    {
      mCRL2log(log::verbose) << options << std::endl;
      lps::labeled_transition_system lts;
      lps::specification lpsspec = lps::detail::load_lps(input_filename());
      lps::lts_generator generator(lpsspec, options);
      current_generator = &generator;
      generator.generate_labeled_transition_system(lts);
      std::ostringstream out;
      out << lts;
      utilities::detail::write_text(output_filename(), out.str());
      return true;
    }

    void abort()
    {
      current_generator->abort();
    }
};

std::unique_ptr<generatelts_tool> tool_instance;

static
void premature_termination_handler(int)
{
  // Reset signal handlers.
  signal(SIGABRT, nullptr);
  signal(SIGINT, nullptr);
  tool_instance->abort();
}

int main(int argc, char** argv)
{
  tool_instance = std::unique_ptr<generatelts_tool>(new generatelts_tool());
  signal(SIGABRT, premature_termination_handler);
  signal(SIGINT, premature_termination_handler); // At ^C invoke the termination handler.
  return tool_instance->execute(argc, argv);
}