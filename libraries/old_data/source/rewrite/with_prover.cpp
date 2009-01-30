// Author(s): Muck van Weerdenburg
// Copyright: see the accompanying file COPYING or copy at
// https://svn.win.tue.nl/trac/MCRL2/browser/trunk/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)

#define NAME "rewr_prover"

#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <memory.h>
#include <aterm2.h>
#include "mcrl2/core/detail/struct.h"
#include "mcrl2/core/messaging.h"
#include "mcrl2/old_data/data_specification.h"
#include "mcrl2/old_data/bdd_prover.h"
#include "mcrl2/old_data/rewrite.h"
#include "mcrl2/old_data/detail/rewrite/with_prover.h"

using namespace mcrl2::core;

RewriterProver::RewriterProver(mcrl2::old_data::data_specification DataSpec, RewriteStrategy strat)
{
  prover_obj = new BDD_Prover(DataSpec,strat);
  rewr_obj = prover_obj->get_rewriter();
}

RewriterProver::~RewriterProver()
{
  delete prover_obj;
}

bool RewriterProver::addRewriteRule(ATermAppl Rule)
{
  return rewr_obj->addRewriteRule(Rule);
}

bool RewriterProver::removeRewriteRule(ATermAppl Rule)
{
  return rewr_obj->removeRewriteRule(Rule);
}

ATerm RewriterProver::rewriteInternal(ATerm Term)
{
  return rewr_obj->toRewriteFormat(
                rewrite(
                  rewr_obj->fromRewriteFormat(Term)
                  )
                );
}

ATermAppl RewriterProver::rewrite(ATermAppl Term)
{
  if ( mcrl2::core::detail::gsGetSort(Term) == mcrl2::core::detail::gsMakeSortExprBool() )
  {
    prover_obj->set_formula(Term);
    return prover_obj->get_bdd();
  } else {
    return rewr_obj->rewrite(Term);
  }
}

ATerm RewriterProver::toRewriteFormat(ATermAppl Term)
{
  return rewr_obj->toRewriteFormat(Term);
}

ATermAppl RewriterProver::fromRewriteFormat(ATerm Term)
{
  return rewr_obj->fromRewriteFormat(Term);
}

void RewriterProver::setSubstitution(ATermAppl Var, ATerm Expr)
{
  return rewr_obj->setSubstitution(Var,Expr);
}

ATerm RewriterProver::getSubstitution(ATermAppl Var)
{
  return rewr_obj->getSubstitution(Var);
}

void RewriterProver::clearSubstitution(ATermAppl Var)
{
  return rewr_obj->clearSubstitution(Var);
}

void RewriterProver::clearSubstitutions()
{
  return rewr_obj->clearSubstitutions();
}

RewriteStrategy RewriterProver::getStrategy()
{
  switch ( rewr_obj->getStrategy() )
  {
    case GS_REWR_INNER:
      return GS_REWR_INNER_P;
    case GS_REWR_JITTY:
      return GS_REWR_JITTY_P;
    case GS_REWR_INNERC:
      return GS_REWR_INNERC_P;
    case GS_REWR_JITTYC:
      return GS_REWR_JITTYC_P;
    default:
      return GS_REWR_INVALID;
  }
}

