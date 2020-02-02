// Author(s): Muck van Weerdenburg, Jan Friso Groote
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//

/** \file
 *
 * \brief Algorithms for LTS, such as equivalence reductions, determinisation, etc.
 * \details This contains the main algorithms useful to manipulate with
 * labelled transition systems. Typically, it contains algorithms for bisimulation
 * reduction, removal of tau loops, making an lts deterministic etc.
 * \author Jan Friso Groote, Bas Ploeger, Muck van Weerdenburg
 */

#ifndef MCRL2_LTS_LTS_ALGORITHM_H
#define MCRL2_LTS_LTS_ALGORITHM_H

#include <algorithm>
#include <cstdio>
#include <cstdlib>
// #include <functional>
#include <iostream>
#include <map>
#include <stack>
#include <string>
#include <vector>
#include "mcrl2/utilities/logger.h"
#include "mcrl2/lts/lts.h"
#include "mcrl2/lts/detail/liblts_bisim.h"
#include "mcrl2/lts/detail/liblts_bisim_gjkw.h"
#include "mcrl2/lts/detail/liblts_weak_bisim.h"
#include "mcrl2/lts/detail/liblts_add_an_action_loop.h"
#include "mcrl2/lts/detail/liblts_ready_sim.h"
#include "mcrl2/lts/detail/liblts_failures_refinement.h"
#include "mcrl2/lts/detail/tree_set.h"
#include "mcrl2/lts/lts_equivalence.h"
#include "mcrl2/lts/lts_preorder.h"
#include "mcrl2/lts/sigref.h"
#include "mcrl2/lts/transition.h"

namespace mcrl2
{
namespace lts
{

/** \brief Applies a reduction algorithm to this LTS.
 * \param[in] l A labelled transition system that must be reduced.
 * \param[in] eq The equivalence with respect to which the LTS will be
 * reduced.
 **/
template <class LTS_TYPE>
void reduce(LTS_TYPE& l, lts_equivalence eq);


// TODO(nox): extrac this
// NOX BA ---------------------------------------------------------------------

const unsigned char NODE_ATK = 0;  // placeholder indicating node is an attacker node
const unsigned char NODE_DEF = 1;  // placeholder indicating a node, which is alwas reachable as coupling.
const unsigned char NODE_CPL = 2;  // placeholder indicating a node, which is alwas reachable as coupling.

// std::vector<ACTION_LABEL_T> m_action_labels; // At position 0 we always find the label that corresponds to tau.
// typedef ACTION_LABEL_T action_label_t;
typedef struct _game_node
{
  unsigned char flag;
  size_t act;
  size_t p; size_t q;
  bool swapped;  // false := p is from lts1
} cs_game_node;

typedef struct _game_move
{
  cs_game_node from, to;
  size_t act;
  // ? action_label;
  bool weak;
} move;

bool operator==(const cs_game_node &n0, const cs_game_node &n1)
{
  return n0.flag == n1.flag
    && n0.swapped == n1.swapped
    && n0.act == n1.act
    && n0.p == n1.p
    && n0.q == n1.q;
}
bool operator!=(const cs_game_node &n0, const cs_game_node &n1)
{
  return !(n0 == n1);
}

bool operator<(const cs_game_node &n0, const cs_game_node &n1)
{
  return n0.flag != n1.flag ? n0.flag < n1.flag
    : n0.act != n1.act ? n0.act < n1.act
    : n0.swapped != n1.swapped ? n0.swapped < n1.swapped
    : n0.p != n1.p ? n0.p < n1.p
    : n0.q < n1.q;
}

std::string to_string(const cs_game_node &n)
{
  std::string fst = !n.swapped ? "p" : "q";
  std::string snd = !n.swapped ? "q" : "p";

  switch (n.flag)
  {
    case NODE_ATK:
      return
        "(" + fst + std::to_string(n.p) +
        "," + snd + std::to_string(n.q) + ")a";

    case NODE_CPL:
      return "(Cpl,"
        + fst + std::to_string(n.p) + ","
        + snd + std::to_string(n.q) + ")d";

    case NODE_DEF:
      return
        "(" + std::to_string(n.act) +
        "," + fst + std::to_string(n.p) +
        "," + snd + std::to_string(n.q) + ")d";

    default: return "(<strange node>)?";
  }
}

std::string to_string(const move &m)
{
  std::string tag0 = m.from.flag == NODE_ATK ? "<a>" : "<d>";
  std::string tag1 = m.to.flag == NODE_ATK ? "<a>" : "<d>";

  std::string alabel
    = m.to.flag != NODE_DEF ? "" : " " + std::to_string(m.to.act);

  return
    "[" + tag0 + to_string(m.from) + "]"
    + (alabel + (m.weak ? " => " : " -> "))
    + "[" + tag1 + to_string(m.to) + "]";
}

bool equals(const move &m0, const move &m1, bool weak_transition = false)
{
  return m0.act == m1.act && (!weak_transition && !(m0.weak || m1.weak));
}

bool operator<(const move &m0, const move &m1)
{
  return m0.from != m1.from ? m0.from < m1.from : m0.to < m1.to;
}
// NOX BA ---------------------------------------------------------------------

/** \brief Checks whether this LTS is equivalent to another LTS.
 * \param[in] l1 The first LTS that will be compared.
 * \param[in] l2 The second LTS that will be compared.
 * \param[in] eq The equivalence with respect to which the LTSs will be
 * compared.
 * \param[in] generate_counter_examples
 * \retval true if the LTSs are found to be equivalent.
 * \retval false otherwise.
 * \warning This function alters the internal data structure of
 * both LTSs for efficiency reasons. After comparison, this LTS is
 * equivalent to the original LTS by equivalence \a eq, and
 * similarly for the LTS \a l.
 */
template <class LTS_TYPE>
bool destructive_compare(LTS_TYPE& l1,
                         LTS_TYPE& l2,
                         const lts_equivalence eq,
                         const bool generate_counter_examples = false)
{
  // Merge this LTS and l and store the result in this LTS.
  // In the resulting LTS, the initial state i of l will have the
  // state number i + N where N is the number of states in this
  // LTS (before the merge).

  switch (eq)
  {
    case lts_eq_none:
      return false;
    case lts_eq_bisim:
    {
      if (generate_counter_examples)
      {
        mCRL2log(mcrl2::log::warning) << "The default bisimulation comparison algorithm cannot generate counter examples. Therefore the slower gv algorithm is used instead.\n";
        return detail::destructive_bisimulation_compare(l1,l2, false,false,generate_counter_examples);
      }
      return detail::destructive_bisimulation_compare_dnj(l1,l2, false,false,generate_counter_examples);
    }
    case lts_eq_bisim_gv:
    {
      return detail::destructive_bisimulation_compare(l1,l2, false,false,generate_counter_examples);
    }
    case lts_eq_bisim_gjkw:
    {
      return detail::destructive_bisimulation_compare_gjkw(l1,l2, false,false,generate_counter_examples);
    }
    case lts_eq_branching_bisim:
    {
      if (generate_counter_examples)
      {
        mCRL2log(mcrl2::log::warning) << "The default branching bisimulation comparison algorithm cannot generate counter examples. Therefore the slower gv algorithm is used instead.\n";
        return detail::destructive_bisimulation_compare(l1,l2, true,false,generate_counter_examples);
      }
      return detail::destructive_bisimulation_compare_dnj(l1,l2, true,false,generate_counter_examples);
    }
    case lts_eq_branching_bisim_gv:
    {
      return detail::destructive_bisimulation_compare(l1,l2, true,false,generate_counter_examples);
    }
    case lts_eq_branching_bisim_gjkw:
    {
      return detail::destructive_bisimulation_compare_gjkw(l1,l2, true,false,generate_counter_examples);
    }
    case lts_eq_divergence_preserving_branching_bisim:
    {
      if (generate_counter_examples)
      {
        mCRL2log(mcrl2::log::warning) << "The default divergence-preserving branching bisimulation comparison algorithm cannot generate counter examples. Therefore the slower gv algorithm is used instead.\n";
        return detail::destructive_bisimulation_compare(l1,l2, true,true,generate_counter_examples);
      }
      return detail::destructive_bisimulation_compare_dnj(l1,l2, true,true,generate_counter_examples);
    }
    case lts_eq_divergence_preserving_branching_bisim_gv:
    {
      return detail::destructive_bisimulation_compare(l1,l2, true,true,generate_counter_examples);
    }
    case lts_eq_divergence_preserving_branching_bisim_gjkw:
    {
      return detail::destructive_bisimulation_compare_gjkw(l1,l2, true,true,generate_counter_examples);
    }
    case lts_eq_weak_bisim:
    {
      if (generate_counter_examples)
      {
        mCRL2log(log::warning) << "Cannot generate counter example traces for weak bisimulation\n";
      }
      return detail::destructive_weak_bisimulation_compare(l1,l2,false);
    }
    case lts_eq_divergence_preserving_weak_bisim:
    {
      if (generate_counter_examples)
      {
        mCRL2log(log::warning) << "Cannot generate counter example traces for for divergence-preserving weak bisimulation\n";
      }
      return detail::destructive_weak_bisimulation_compare(l1,l2, true);
    }
    case lts_eq_sim:
    {
      if (generate_counter_examples)
      {
        mCRL2log(log::warning) << "Cannot generate counter example traces for simulation equivalence\n";
      }
      // Run the partitioning algorithm on this merged LTS
      std::size_t init_l2 = l2.initial_state() + l1.num_states();
      detail::merge(l1,l2);
      l2.clear(); // l2 is not needed anymore.
      detail::sim_partitioner<LTS_TYPE> sp(l1);
      sp.partitioning_algorithm();

      return sp.in_same_class(l1.initial_state(),init_l2);
    }
    case lts_eq_ready_sim:
    {
      if (generate_counter_examples)
      {
        mCRL2log(log::warning) << "Cannot generate counter example traces for ready-simulation equivalence\n";
      }
      // Run the partitioning algorithm on this merged LTS
      std::size_t init_l2 = l2.initial_state() + l1.num_states();
      detail::merge(l1,l2);
      l2.clear(); // l2 is not needed anymore.
      detail::ready_sim_partitioner<LTS_TYPE> rsp(l1);
      rsp.partitioning_algorithm();

      return rsp.in_same_class(l1.initial_state(),init_l2);
    }
    case lts_eq_trace:
    {
      // Determinise first LTS
      detail::bisimulation_reduce(l1,false);
      determinise(l1);

      // Determinise second LTS
      detail::bisimulation_reduce(l2,false);
      determinise(l2);

      // Trace equivalence now corresponds to bisimilarity
      return detail::destructive_bisimulation_compare(l1,l2,false,false,generate_counter_examples);
    }
    case lts_eq_weak_trace:
    {
      // Eliminate silent steps and determinise first LTS
      detail::bisimulation_reduce(l1,true,false);
      detail::tau_star_reduce(l1);
      detail::bisimulation_reduce(l1,false);
      determinise(l1);

      // Eliminate silent steps and determinise second LTS
      detail::bisimulation_reduce(l2,true,false);
      detail::tau_star_reduce(l2);
      detail::bisimulation_reduce(l2,false);
      determinise(l2);

      // Weak trace equivalence now corresponds to bisimilarity
      return detail::destructive_bisimulation_compare(l1,l2,false,false,generate_counter_examples);
    }
    case lts_eq_coupled_sim:
    {
      // USE TAU REDUCTION. =>  Reduces too much.
      // TODO(nox) 2020-01-25 maybe bisimulation_reduce() instead?
      if (false)
      {
        std::cout << "# TEST: ========== \n# Weak Bisim reduction and so on.\n";
        // detail::tau_star_reduce(l1);
        bool preserve_divergences = false;

        detail::weak_bisimulation_reduce(l1,preserve_divergences);
        detail::weak_bisimulation_reduce(l2,preserve_divergences);
        // detail::tau_star_reduce(l2);
        // /home/nox/Projects/collaboration/mCRL2/libraries/lts/include/mcrl2/lts/detail/liblts_tau_star_reduce.h

        std::string DEBUG_NOTE = "'";
        {
          std::cout << "# TEST: l1.get_transitions():\n";
          for (transition t : l1.get_transitions())
          {
            std::cout
              << "[p" << DEBUG_NOTE << ": " << t.from() << "]"
              << " " << (t.label()) << "="
              // << (l1.is_tau(t.label()) ? "\u03c4" : std::to_string(l1.action_label(t.label())))
              << (l1.action_label(t.label()))
              << " ->"
              << " [p" << DEBUG_NOTE << ": " << t.to() << "]\n";
          }

          std::cout << "# TEST: l2.get_transitions():\n";
          for (const transition t : l2.get_transitions())
          {
            std::cout
              << "[q" << DEBUG_NOTE << ": " << t.from() << "]"
              << " " << (t.label()) << "="
              // << (l2.is_tau(t.label()) ? "\u03c4" : std::to_string(l2.action_label(t.label())))
              << (l2.action_label(t.label()))
              << " ->"
              << " [q" << DEBUG_NOTE << ": " << t.to() << "]\n";
          }
        }
      }

      std::cout << "# Attacker nodes (p,q)a in Ga ... as S1 x S2 aka all possible pairs between them\n";
      std::cout << "# Prepare defender nodes 1: all possible nodes, and how they are reached.\n";

      std::set<cs_game_node> attacker_nodes;  // (flag=NODE_ATK, placeholder, node::int, node::int)
      std::set<cs_game_node> defender_nodes;  // (flag, act::int, (node:int, node::int))

      // std::vector<move> moves;  // moves (node,node)
      std::set<move> moves;  // moves (node,node)

      /* Define game nodes here. */

      /* Get Weak transitions. */
      // NOP

      /* filter transitions of t2. */
      std::map<size_t,std::vector<transition>>
        t2_tran_from_node, t2_tran_into_node,
        t1_tran_from_node, t1_tran_into_node;

      for (const transition t2 : l2.get_transitions())
      {
        t2_tran_from_node[t2.from()].push_back(t2);  // outgoing
        t2_tran_into_node[t2.to()].push_back(t2);  // incoming

        /* If tau, then add to weak transitions. */
        if (l2.is_tau(t2.label()))
        {
          // NOP
        }

        // DEBUG
          std::cout << "[q" << t2.from() << "]"
            << " " << (l2.action_label(t2.label()))
            << " ->"
            << " [q" << t2.to() << "]\n";
      }

      /* Add weak transititions. */
      // NOP

      /* Create Attacker nodes (P,Q),
       * .. similarity game defender nodes (A1,P,Q) -> (P,Q)
       * .. and answering swapped similarity challanges (B,Q,P) => (Q,P)
       */
      for (transition t1 : l1.get_transitions())
      {
        size_t a, p0, p1;
        // ? act_label = t1.action_label(act);

        a = t1.label();
        p0 = t1.from();
        p1 = t1.to();

        // bool a_is_tau = l1.is_tau(a);

        // for reusing.
        t1_tran_from_node[p0].push_back(t1);  // outgoing
        t1_tran_into_node[p1].push_back(t1);  // incoming

        // DEBUG
          std::cout
            << "[p" << t1.from() << "]"
            << " " << (l1.action_label(t1.label()))
            << " ->"
            << " [p" << t1.to() << "]\n";

        /* Translate transition (p0) a -> (p1) to game nodes and moves:
         * (p0,q) a -> (a,p1,q) for all q in t2.num_states()
         * Create also (p0,q) -> (cpl, p0, q) */

        for (size_t q = 0; q < l2.num_states(); q++)
        {
          /* Challange: (Weak) Simulation Game. */
          cs_game_node node_atk = {NODE_ATK, 0, p0, q, false}; // (p0,q) f.a q in L2
          cs_game_node node_sim = {NODE_DEF, a, p1, q, false}; // (a,p1,q) f.a q in L2

          attacker_nodes.insert(node_atk);
          defender_nodes.insert(node_sim);

          /* p0 -> p1 */
          // moves.push_back({node_atk, node_sim, a, false});
          moves.insert({node_atk, node_sim, a, false});

          /* Answer to swapped challange.
           * (b,q,p0) -> (q,p1), if p0 b=> p1. */
          for (transition bqq1 : t2_tran_into_node[q])
          {
            size_t b = bqq1.label();
            bool b_is_tau = l2.is_tau(b);
            // if (b_is_tau || l2.action_label(b) == l1.action_label(a))
            if (l2.action_label(b) == l1.action_label(a))
            {
              // moves.push_back({
              moves.insert({
                  {NODE_DEF, b, q, p0, true},
                  {NODE_ATK, 0, q, p1, true},
                  a,
                  false});  // one weak step is no weak transition.
            }
          }
        }
      }

      /* Create (swapped) Attacker nodes (Q,P),
       * .. (swapped) similarity game defender nodes (B,Q,P) -> (Q,P)
       * .. and answering similarity challanges (A,P,Q) => (P,Q)
       */
      for (transition t2 : l2.get_transitions())
      {
        size_t b, q0, q1;
        // ? act_label = t1.action_label(act);

        b = t2.label();
        q0 = t2.from();
        q1 = t2.to();

        // bool b_is_tau = l2.is_tau(b);

        /* Translate transition (p0) a -> (p1) to game nodes and moves:
         * (p0,q) a -> (a,p1,q) for all q in t2.num_states()
         * Create also (p0,q) -> (cpl, p0, q) */

        for (size_t p = 0; p < l1.num_states(); p++)
        {
          /* Challange: Swapped (Weak) Simulation Game. */
          // XXX
          cs_game_node node_atk = {NODE_ATK, 0, q0, p, true};
          cs_game_node node_sim = {NODE_DEF, b, q1, p, true};

          attacker_nodes.insert(node_atk);
          defender_nodes.insert(node_sim);

          /* q0 -> q1 (swapped) .*/
          // moves.push_back({node_atk, node_sim, b, false});
          moves.insert({node_atk, node_sim, b, false});

          /* Answer to challenge.
           * (a,p,q0) -> (p,q1), if q0 a=> q1. */
          for (transition bpp1 : t1_tran_into_node[p])
          {
            size_t a = bpp1.label();
            bool a_is_tau = false && l2.is_tau(b);
            if (a_is_tau || l2.action_label(b) == l1.action_label(a))
            {
              // moves.push_back({
              moves.insert({
                  {NODE_DEF, a, p, q0, false},
                  {NODE_ATK, 0, p, q1, false},
                  b,
                  false});  // one weak step is no weak transition.
            }
          }
        }
      }

      /* Add all Coupling challanges and their answers. */
      for (size_t p = 0; p < l1.num_states(); p++)
      {
        for (size_t q = 0; q < l2.num_states(); q++)
        {
          /* Challange coupling */
          cs_game_node node_atk = {NODE_ATK, 0, p, q, false};
          // cs_game_node node_cpl = {NODE_CPL, 0, p, q, false};
          cs_game_node node_swp = {NODE_ATK, 0, q, p, true};

          attacker_nodes.insert(node_atk);
          attacker_nodes.insert(node_swp);

          // defender_nodes.insert(node_cpl);

          // moves.push_back({node_atk, node_cpl, 0, false});
          // moves.push_back({node_cpl, node_swp, 0, false});

          // bisim.
          moves.insert({node_atk, node_swp, 0, false});
          moves.insert({node_swp, node_atk, 0, false});
        }
      }

      // DEBUG
      std::cout << "# Now, a Game with "
        << attacker_nodes.size() << " Attacker nodes, "
        << defender_nodes.size() << " Defender nodes and "
        << moves.size() << " (unready) moves exists\n";

      std::cout << "# Get all the predecessors.\n";
      std::cout << "# Count their successors\n";
      std::cout << "# Mark everyone won by defender (d)\n";

      std::map<cs_game_node,std::set<cs_game_node>> predecessors;
      std::map<cs_game_node,int> successor_count;
      std::map<cs_game_node,int> nodes_won;
      const int WON_DEFENDER = 0, WON_ATTACKER = 1;

      std::cout // XXX REMOVE_ME
        << "\n#title: ltscompare_coupledsim_csgame"
        << "\n#fontSize: 10"
        << "\n#arrowSize: 0.2"
        << "\n#lineWidth: 1.0"
        << "\n#zoom: 1.0"
        << "\n#edges: rounded"
        << "\n#.a: fill=#f77"
        << "\n#.d: fill=#7f7 visual=roundrect"
        << "\n#.l: visual=none"
        << "\n#ranker: longest-path"
        << "\n";

      for (const auto &m : moves)
      {
        cs_game_node pred = m.from;
        cs_game_node succ = m.to;

        /* All nodes set won by defender. */
        nodes_won[pred] = WON_DEFENDER;
        nodes_won[succ] = WON_DEFENDER;

        /* Update predecessors for succ.
         * Predecessors[succ] += [pred] */
        predecessors[succ].insert(pred);  // append predecessors.

        /* Update succesors for the pred. */
        successor_count[pred] += 1;  // "append" successors.

        // DEBUG
        std::cout << to_string(m) << "\n";
      }

      std::cout << "\n# Run: Computing Winning Regions.\n";

      std::stack<cs_game_node> todo;
      for (cs_game_node d : defender_nodes) todo.push(d); // XXX make me better
      // todo.assign(defender_nodes.begin(), defender_nodes.end());

      while (!todo.empty())
      {
        /* Pop from queue. */
        cs_game_node n = todo.top();
        todo.pop();

        if (successor_count[n] <= 0)
        {
          std::cout << "// propagate_attacker_win(" << to_string(n) << ")\n";
          if (nodes_won[n] == WON_DEFENDER)
          {
            nodes_won[n] = WON_ATTACKER;

            /* now reduce it from all predecessors as successor.
             * and check if the predecessor is also about to be won by the
             * attacker. */
            for (cs_game_node pred : predecessors[n])
            {
              successor_count[pred] -= 1;
              if (successor_count[pred] < 1 || attacker_nodes.count(pred))
              {
                todo.push(pred);
                successor_count[pred] = 0; // to propagate next run.
              }
            }
          }
        }
      }

      std::cout << "> R = {";
      char seperator[3] = {'\0', ' ', '\0'};

      // Filter attacker nodes, which won the challange.
      std::set<cs_game_node> cs_relation;

      for (const auto &pq : attacker_nodes)
      {
        if (nodes_won[pq] == WON_DEFENDER)
        {
          cs_relation.insert(pq);
          std::cout << seperator << to_string(pq);
          seperator[0] = ',';
        }
      }
      std::cout << "}\n";

      /* Return true iff root nodes are in R / won by defender. */
      cs_game_node roots[]
        = {{NODE_ATK, 0, 0, 0, false}, {NODE_ATK, 0, 0, 0, true}};

      return
        nodes_won[roots[0]] == WON_DEFENDER &&
        nodes_won[roots[1]] == WON_DEFENDER;
    }
    default:
    throw mcrl2::runtime_error("Comparison for this equivalence is not available");
    return false;
  }
}

/** \brief Checks whether this LTS is equivalent to another LTS.
 * \details The input labelled transition systems are duplicated in memory to carry
 *          out the comparison. When space efficiency is a concern, one can consider
 *          to use destructive_compare.
 * \param[in] l1 The first LTS to compare.
 * \param[in] l2 The second LTS to compare.
 * \param[in] eq The equivalence with respect to which the LTSs will be
 * compared.
 * \param[in] generate_counter_examples If true counter examples are written to file.
 * \retval true if the LTSs are found to be equivalent.
 * \retval false otherwise.
 */
template <class LTS_TYPE>
bool compare(const LTS_TYPE& l1,
             const LTS_TYPE& l2,
             const lts_equivalence eq,
             const bool generate_counter_examples = false);

/** \brief Checks whether this LTS is smaller than another LTS according
 * to a preorder.
 * \param[in] l1 The first LTS to be compared.
 * \param[in] l2 The second LTS to be compared.
 * \param[in] pre The preorder with respect to which the LTSs will be
 * compared.
 * \param[in] generate_counter_example Indicates whether a file containing a counter example is
 *            generated when the comparison fails.
 * \param[in] strategy Choose breadth-first or depth-first for exploration strategy
 *            of the antichain algorithms.
 * \param[in] preprocess Whether to allow preprocessing of the given LTSs.
 * \retval true if LTS \a l1 is smaller than LTS \a l2 according to
 * preorder \a pre.
 * \retval false otherwise.
 * \warning This function alters the internal data structure of
 * both LTSs for efficiency reasons. After comparison, this LTS is
 * equivalent to the original LTS by equivalence \a eq, and
 * similarly for the LTS \a l, where \a eq is the equivalence
 * induced by the preorder \a pre (i.e. \f$eq = pre \cap
 * pre^{-1}\f$).
 */
template <class LTS_TYPE >
bool destructive_compare(LTS_TYPE& l1,
                         LTS_TYPE& l2,
                         const lts_preorder pre,
                         const bool generate_counter_example,
                         const lps::exploration_strategy strategy = lps::es_breadth,
                         const bool preprocess = true);

/** \brief Checks whether this LTS is smaller than another LTS according
 * to a preorder.
 * \param[in] l1 The first LTS to be compared.
 * \param[in] l2 The second LTS to be compared.
 * \param[in] pre The preorder with respect to which the LTSs will be compared.
 * \param[in] generate_counter_example Indicates whether a file containing a counter example is
 *            generated when the comparison fails.
 * \param[in] strategy Choose breadth-first or depth-first for exploration strategy
 *            of the antichain algorithms.
 * \param[in] preprocess Whether to allow preprocessing of the given LTSs.
 * \retval true if this LTS is smaller than LTS \a l according to
 * preorder \a pre.
 * \retval false otherwise.
 */
template <class  LTS_TYPE >
bool compare(const LTS_TYPE&  l1,
             const  LTS_TYPE& l2,
             const lts_preorder pre,
             const bool generate_counter_example,
             const lps::exploration_strategy strategy = lps::es_breadth,
             const bool preprocess = true);

/** \brief Determinises this LTS. */
template <class LTS_TYPE>
void determinise(LTS_TYPE& l);


/** \brief Checks whether all states in this LTS are reachable
 * from the initial state and remove unreachable states if required.
 * \details Runs in O(num_states * num_transitions) time.
 * \param[in] l The LTS on which reachability is checked.
 * \param[in] remove_unreachable Indicates whether all unreachable states
 *            should be removed from the LTS. This option does not
 *            influence the return value; the return value is with
 *            respect to the original LTS.
 * \retval true if all states are reachable from the initial state;
 * \retval false otherwise. */
template <class SL, class AL, class BASE>
bool reachability_check(lts < SL, AL, BASE>& l, bool remove_unreachable = false)
{
  // First calculate which states can be reached, and store this in the array visited.
  const outgoing_transitions_per_state_t out_trans(l.get_transitions(),l.num_states(),true);

  std::vector < bool > visited(l.num_states(),false);
  std::stack<std::size_t> todo;

  visited[l.initial_state()]=true;
  todo.push(l.initial_state());

  while (!todo.empty())
  {
    std::size_t state_to_consider=todo.top();
    todo.pop();
    // for (const outgoing_pair_t& p: out_trans[state_to_consider])
    for (detail::state_type i=out_trans.lowerbound(state_to_consider); i<out_trans.upperbound(state_to_consider); ++i)
    {
      const outgoing_pair_t& p=out_trans.get_transitions()[i];
      assert(visited[state_to_consider] && state_to_consider<l.num_states() && to(p)<l.num_states());
      if (!visited[to(p)])
      {
        visited[to(p)]=true;
        todo.push(to(p));
      }
    }
  }

  // Property: in_visited(s) == true: state s is reachable from the initial state

  // check to see if all states are reachable from the initial state, i.e.
  // whether all bits are set.
  bool all_reachable = find(visited.begin(),visited.end(),false)==visited.end();

  if (!all_reachable && remove_unreachable)
  {
    // Remove all unreachable states, transitions from such states and labels
    // that are only used in these transitions.

    std::vector < detail::state_type > state_map(l.num_states());
    std::vector < detail::state_type > label_map(l.num_action_labels());

    lts < SL, AL, BASE> new_lts=l; // In this way set data specification and action declarations in the new lts.
    new_lts.clear();

    std::size_t new_nstates = 0;
    for (std::size_t i=0; i<l.num_states(); i++)
    {
      if (visited[i])
      {
        state_map[i] = new_nstates;
        if (l.has_state_info())
        {
          new_lts.add_state(l.state_label(i));
        }
        else
        {
          new_lts.add_state();
        }
        new_nstates++;
      }
    }

    for (const transition& t: l.get_transitions())
    {
      if (visited[t.from()])
      {
        label_map[t.label()] = 1;
      }
    }

    label_map[0]=1; // Declare the tau action explicitly present.
    std::size_t new_nlabels = 0;
    for (std::size_t i=0; i<l.num_action_labels(); i++)
    {
      if (label_map[i]>0)   // Label i is used.
      {
        label_map[i] = new_nlabels;
        new_lts.add_action(l.action_label(i));
        new_nlabels++;
      }
    }

    for (const transition& t: l.get_transitions())
    {
      if (visited[t.from()])
      {
        new_lts.add_transition(transition(state_map[t.from()],label_map[t.label()],state_map[t.to()]));
      }
    }

    new_lts.set_initial_state(state_map.at(l.initial_state()));
    l.swap(new_lts);
  }

  return all_reachable;
}

/** \brief Checks whether all states in a probabilistic LTS are reachable
 * from the initial state and remove unreachable states if required.
 * \details Runs in O(num_states * num_transitions) time.
 * \param[in] l The LTS on which reachability is checked.
 * \param[in] remove_unreachable Indicates whether all unreachable states
 *            should be removed from the LTS. This option does not
 *            influence the return value; the return value is with
 *            respect to the original LTS.
 * \retval true if all states are reachable from the initial state;
 * \retval false otherwise. */
template <class SL, class AL, class PROBABILISTIC_STATE, class BASE>
bool reachability_check(probabilistic_lts < SL, AL, PROBABILISTIC_STATE, BASE>&  l, bool remove_unreachable = false)
{
  // First calculate which states can be reached, and store this in the array visited.
  const outgoing_transitions_per_state_t out_trans(l.get_transitions(),l.num_states(),true);

  std::vector < bool > visited(l.num_states(),false);
  std::stack<std::size_t> todo;

  for(const typename PROBABILISTIC_STATE::state_probability_pair& s: l.initial_probabilistic_state())
  {
    visited[s.state()]=true;
    todo.push(s.state());
  }

  while (!todo.empty())
  {
    std::size_t state_to_consider=todo.top();
    todo.pop();
    // for (const outgoing_pair_t& p: out_trans[state_to_consider])
    for (detail::state_type i=out_trans.lowerbound(state_to_consider); i<out_trans.upperbound(state_to_consider); ++i)
    {
      const outgoing_pair_t& p=out_trans.get_transitions()[i];
      assert(visited[state_to_consider] && state_to_consider<l.num_states() && to(p)<l.num_probabilistic_states());
      // Walk through the the states in this probabilistic state.
      for(const typename PROBABILISTIC_STATE::state_probability_pair& pr: l.probabilistic_state(to(p)))
      {
        if (!visited[pr.state()])
        {
          visited[pr.state()]=true;
          todo.push(pr.state());
        }
      }
    }
  }

  // Property: in_visited(s) == true: state s is reachable from the initial state

  // check to see if all states are reachable from the initial state, i.e.
  // whether all bits are set.
  bool all_reachable = find(visited.begin(),visited.end(),false)==visited.end();

  if (!all_reachable && remove_unreachable)
  {
    // Remove all unreachable states, transitions from such states and labels
    // that are only used in these transitions.

    std::vector < detail::state_type > state_map(l.num_states());
    std::vector < detail::state_type > label_map(l.num_action_labels());

    probabilistic_lts < SL, AL, PROBABILISTIC_STATE, BASE> new_lts=l; // In this way set data specification and action declarations in the new lts.
    new_lts.clear();

    std::size_t new_nstates = 0;
    for (std::size_t i=0; i<l.num_states(); i++)
    {
      if (visited[i])
      {
        state_map[i] = new_nstates;
        if (l.has_state_info())
        {
          new_lts.add_state(l.state_label(i));
        }
        else
        {
          new_lts.add_state();
        }
        new_nstates++;
      }
    }

    for (const transition& t: l.get_transitions())
    {
      if (visited[t.from()])
      {
        label_map[t.label()] = 1;
      }
    }

    label_map[0]=1; // Declare the tau action explicitly present.
    std::size_t new_nlabels = 0;
    for (std::size_t i=0; i<l.num_action_labels(); i++)
    {
      if (label_map[i]>0)   // Label i is used.
      {
        label_map[i] = new_nlabels;
        new_lts.add_action(l.action_label(i));
        new_nlabels++;
      }
    }

    for (const transition& t: l.get_transitions())
    {
      if (visited[t.from()])
      {
        new_lts.add_transition(transition(state_map[t.from()],label_map[t.label()],t.to()));
      }
    }

    PROBABILISTIC_STATE new_initial_state;
    for(const typename PROBABILISTIC_STATE::state_probability_pair& s: l.initial_probabilistic_state())
    {
      new_initial_state.add(state_map[s.state()], s.probability());
    }
    new_lts.set_initial_probabilistic_state(new_initial_state);
    l.swap(new_lts);
  }

  return all_reachable;
}

/** \brief Checks whether this LTS is deterministic.
 * \retval true if this LTS is deterministic;
 * \retval false otherwise. */
template <class LTS_TYPE>
bool is_deterministic(const LTS_TYPE& l);

/** \brief Merge the second lts into the first lts.
    \param[in,out] l1 The transition system in which l2 is merged.
    \param[in] l2 The second transition system, which remains unchanged
 */
template <class LTS_TYPE>
void merge(LTS_TYPE& l1, const LTS_TYPE& l2)
{
  detail::merge(l1,l2);
}


/* Here the implementations of the declared functions above are given.
   Originally these were in a .cpp file, before lts's were templated  */



template <class LTS_TYPE>
void reduce(LTS_TYPE& l,lts_equivalence eq)
{

  switch (eq)
  {
    case lts_eq_none:
      return;
    case lts_eq_bisim:
    {
      detail::bisimulation_reduce_dnj(l,false,false);
      return;
    }
    case lts_eq_bisim_gv:
    {
      detail::bisimulation_reduce(l,false,false);
      return;
    }
    case lts_eq_bisim_gjkw:
    {
      detail::bisimulation_reduce_gjkw(l,false,false);
      return;
    }
    case lts_eq_bisim_sigref:
    {
      sigref<LTS_TYPE, signature_bisim<LTS_TYPE> > s(l);
      s.run();
      return;
    }
    case lts_eq_branching_bisim:
    {
      detail::bisimulation_reduce_dnj(l,true,false);
      return;
    }
    case lts_eq_branching_bisim_gv:
    {
      detail::bisimulation_reduce(l,true,false);
      return;
    }
    case lts_eq_branching_bisim_gjkw:
    {
      detail::bisimulation_reduce_gjkw(l,true,false);
      return;
    }
    case lts_eq_branching_bisim_sigref:
    {
      sigref<LTS_TYPE, signature_branching_bisim<LTS_TYPE> > s(l);
      s.run();
      return;
    }
    case lts_eq_divergence_preserving_branching_bisim:
    {
      detail::bisimulation_reduce_dnj(l,true,true);
      return;
    }
    case lts_eq_divergence_preserving_branching_bisim_gv:
    {
      detail::bisimulation_reduce(l,true,true);
      return;
    }
    case lts_eq_divergence_preserving_branching_bisim_gjkw:
    {
      detail::bisimulation_reduce_gjkw(l,true,true);
      return;
    }
    case lts_eq_divergence_preserving_branching_bisim_sigref:
    {
      sigref<LTS_TYPE, signature_divergence_preserving_branching_bisim<LTS_TYPE> > s(l);
      s.run();
      return;
    }
    case lts_eq_weak_bisim:
    {
      detail::weak_bisimulation_reduce(l,false);
      return;
    }
    /*
    case lts_eq_weak_bisim_sigref:
    {
     {
      sigref<LTS_TYPE, signature_branching_bisim<LTS_TYPE> > s1(l);
      s1.run();
     }
      detail::reflexive_transitive_tau_closure(l);
     {
      sigref<LTS_TYPE, signature_bisim<LTS_TYPE> > s2(l);
      s2.run();
     }
      scc_reduce(l); // Remove tau loops
      return;
    }
    */
    case lts_eq_divergence_preserving_weak_bisim:
    {
      detail::weak_bisimulation_reduce(l,true);
      return;
    }
    /*
    case lts_eq_divergence_preserving_weak_bisim_sigref:
    {
     {
      sigref<LTS_TYPE, signature_divergence_preserving_branching_bisim<LTS_TYPE> > s1(l);
      s1.run();
     }
      std::size_t divergence_label=detail::mark_explicit_divergence_transitions(l);
      detail::reflexive_transitive_tau_closure(l);
     {
      sigref<LTS_TYPE, signature_bisim<LTS_TYPE> > s2(l);
      s2.run();
     }
      scc_reduce(l); // Remove tau loops
      detail::unmark_explicit_divergence_transitions(l,divergence_label);
      return;
    }
    */
    case lts_eq_sim:
    {
      // Run the partitioning algorithm on this LTS
      detail::sim_partitioner<LTS_TYPE> sp(l);
      sp.partitioning_algorithm();

      // Clear this LTS, but keep the labels
      // l.clear_type();
      l.clear_state_labels();
      l.clear_transitions();

      // Assign the reduced LTS
      l.set_num_states(sp.num_eq_classes());
      l.set_initial_state(sp.get_eq_class(l.initial_state()));

      const std::vector <transition> trans=sp.get_transitions();
      l.clear_transitions();
      for (std::vector <transition>::const_iterator i=trans.begin(); i!=trans.end(); ++i)
      {
        l.add_transition(*i);
      }
      // Remove unreachable parts

      reachability_check(l,true);

      return;
    }
    case lts_eq_ready_sim:
    {
      // Run the partitioning algorithm on this LTS
      detail::ready_sim_partitioner<LTS_TYPE> rsp(l);
      rsp.partitioning_algorithm();

      // Clear this LTS, but keep the labels
      // l.clear_type();
      l.clear_state_labels();
      l.clear_transitions();

      // Assign the reduced LTS
      l.set_num_states(rsp.num_eq_classes());
      l.set_initial_state(rsp.get_eq_class(l.initial_state()));

      const std::vector <transition> trans=rsp.get_transitions();
      l.clear_transitions();
      for (std::vector <transition>::const_iterator i=trans.begin(); i!=trans.end(); ++i)
      {
        l.add_transition(*i);
      }
      // Remove unreachable parts

      reachability_check(l,true);

      return;
    }
    case lts_eq_trace:
      detail::bisimulation_reduce(l,false);
      determinise(l);
      detail::bisimulation_reduce(l,false);
      return;
    case lts_eq_weak_trace:
    {
      detail::bisimulation_reduce(l,true,false);
      detail::tau_star_reduce(l);
      detail::bisimulation_reduce(l,false);
      determinise(l);
      detail::bisimulation_reduce(l,false);
      return;
    }
    case lts_red_tau_star:
    {
      detail::bisimulation_reduce(l,true,false);
      detail::tau_star_reduce(l);
      detail::bisimulation_reduce(l,false);
      return;
    }
    case lts_red_determinisation:
    {
      determinise(l);
      return;
    }
    default:
      throw mcrl2::runtime_error("Unknown reduction method.");
  }
}

template <class LTS_TYPE>
bool compare(const LTS_TYPE& l1, const LTS_TYPE& l2, const lts_equivalence eq, const bool generate_counter_examples)
{
  switch (eq)
  {
    case lts_eq_none:
      return false;
    default:
      LTS_TYPE l1_copy(l1);
      LTS_TYPE l2_copy(l2);
      return destructive_compare(l1_copy,l2_copy,eq,generate_counter_examples);
  }
  return false;
}

template <class LTS_TYPE>
bool compare(const LTS_TYPE& l1, const LTS_TYPE& l2, const lts_preorder pre, const bool generate_counter_example, const lps::exploration_strategy strategy, const bool preprocess)
{
  LTS_TYPE l1_copy(l1);
  LTS_TYPE l2_copy(l2);
  return destructive_compare(l1_copy, l2_copy, pre, generate_counter_example, strategy, preprocess);
}

template <class LTS_TYPE>
bool destructive_compare(LTS_TYPE& l1, LTS_TYPE& l2, const lts_preorder pre, const bool generate_counter_example, const lps::exploration_strategy strategy, const bool preprocess)
{
  switch (pre)
  {
    case lts_pre_sim:
    {
      // Merge this LTS and l and store the result in this LTS.
      // In the resulting LTS, the initial state i of l will have the
      // state number i + N where N is the number of states in this
      // LTS (before the merge).
      const std::size_t init_l2 = l2.initial_state() + l1.num_states();
      detail::merge(l1,l2);

      // We no longer need l, so clear it to save memory
      l2.clear();

      // Run the partitioning algorithm on this merged LTS
      detail::sim_partitioner<LTS_TYPE> sp(l1);
      sp.partitioning_algorithm();

      return sp.in_preorder(l1.initial_state(),init_l2);
    }
    case lts_pre_ready_sim:
    {
      // Merge this LTS and l and store the result in this LTS.
      // In the resulting LTS, the initial state i of l will have the
      // state number i + N where N is the number of states in this
      // LTS (before the merge).
      const std::size_t init_l2 = l2.initial_state() + l1.num_states();
      detail::merge(l1,l2);

      // We no longer need l, so clear it to save memory
      l2.clear();

      // Run the partitioning algorithm on this prepropcessed LTS
      detail::ready_sim_partitioner<LTS_TYPE> rsp(l1);
      rsp.partitioning_algorithm();

      return rsp.in_preorder(l1.initial_state(),init_l2);
    }
    case lts_pre_trace:
    {
      // Preprocessing: reduce modulo strong bisimulation equivalence.
      // This is not strictly necessary, but may reduce time/memory
      // needed for determinisation.
      detail::bisimulation_reduce(l1,false);
      detail::bisimulation_reduce(l2,false);

      // Determinise both LTSes. As postprocessing, reduce modulo
      // strong bisimulation equivalence. This is not strictly
      // necessary, but may reduce time/memory needed for simulation
      // preorder checking.
      determinise(l1);
      detail::bisimulation_reduce(l1,false);

      determinise(l2);
      detail::bisimulation_reduce(l2,false);

      // Trace preorder now corresponds to simulation preorder
      return destructive_compare(l1, l2, lts_pre_sim, generate_counter_example, strategy);
    }
    case lts_pre_weak_trace:
    {
      // Eliminate silent steps of first LTS
      detail::bisimulation_reduce(l1,true,false);
      detail::tau_star_reduce(l1);

      // Eliminate silent steps of second LTS
      detail::bisimulation_reduce(l2,true,false);
      detail::tau_star_reduce(l2);

      // Weak trace preorder now corresponds to strong trace preorder
      return destructive_compare(l1, l2, lts_pre_trace, generate_counter_example, strategy);
    }
    case lts_pre_trace_anti_chain:
    {
      if (generate_counter_example)
      {
        detail::counter_example_constructor cec("counter_example_trace_preorder.trc");
        return destructive_refinement_checker(l1, l2, trace, false, strategy, preprocess, cec);
      }
      return destructive_refinement_checker(l1, l2, trace, false, strategy, preprocess);
    }
    case lts_pre_weak_trace_anti_chain:
    {
      if (generate_counter_example)
      {
        detail::counter_example_constructor cec("counter_example_weak_trace_preorder.trc");
        return destructive_refinement_checker(l1, l2, trace, true, strategy, preprocess, cec);
      }
      return destructive_refinement_checker(l1, l2, trace, true, strategy, preprocess);
    }
    case lts_pre_failures_refinement:
    {
      if (generate_counter_example)
      {
        detail::counter_example_constructor cec("counter_example_failures_refinement.trc");
        return destructive_refinement_checker(l1, l2, failures, false, strategy, preprocess, cec);
      }
      return destructive_refinement_checker(l1, l2, failures, false, strategy, preprocess);
    }
    case lts_pre_weak_failures_refinement:
    {
      if (generate_counter_example)
      {
        detail::counter_example_constructor cec("counter_example_weak_failures_refinement.trc");
        return destructive_refinement_checker(l1, l2, failures, true, strategy, preprocess, cec);
      }
      return destructive_refinement_checker(l1, l2, failures, true, strategy, preprocess);
    }
    case lts_pre_failures_divergence_refinement:
    {
      if (generate_counter_example)
      {
        detail::counter_example_constructor cec("counter_example_failures_divergence_refinement.trc");
        return destructive_refinement_checker(l1, l2, failures_divergence, true, strategy, preprocess, cec);
      }
      return destructive_refinement_checker(l1, l2, failures_divergence, true, strategy, preprocess);
    }
    default:
      mCRL2log(log::error) << "Comparison for this preorder is not available\n";
      return false;
  }
}


template <class LTS_TYPE>
bool is_deterministic(const LTS_TYPE& l)
{
  if (l.num_transitions() == 0)
  {
    return true;
  }

  std::vector<transition> temporary_copy_of_transitions = l.get_transitions();
  sort_transitions(temporary_copy_of_transitions, l.hidden_label_map(), src_lbl_tgt);
  
  // Traverse the ordered transitions, and search for two consecutive pairs <s,l,t> and <s,l,t'> with t!=t'. 
  // Such a pair exists iff l is not deterministic.
  transition& previous_t=temporary_copy_of_transitions[0];
  bool previous_t_is_valid=false;
  for(const transition& t: temporary_copy_of_transitions) 
  {
    if (previous_t_is_valid)
    {
      if (previous_t.from()==t.from() && 
          previous_t.label()==t.label() &&
          previous_t.to()!=t.to())
      {
        return false;
      }
    }
    previous_t=t;
    previous_t_is_valid=true;
  }
  return true;
}


namespace detail
{

template <class LTS_TYPE>
void get_trans(const outgoing_transitions_per_state_t& begin,
               tree_set_store& tss,
               std::size_t d,
               std::vector<transition>& d_trans,
               LTS_TYPE& aut)
{
  if (!tss.is_set_empty(d))
  {
    if (tss.is_set_empty(tss.get_set_child_right(d)))
    {
      // for (outgoing_transitions_per_state_t:: const_iterator
      //     j=begin.lower_bound(tss.get_set_child_left(d)); j!=begin.upper_bound(tss.get_set_child_left(d)); ++j)
      const state_type from=tss.get_set_child_left(d);
      // for(const outgoing_pair_t& p: begin[from])
      for (detail::state_type i=begin.lowerbound(from); i<begin.upperbound(from); ++i)
      {
        const outgoing_pair_t& p=begin.get_transitions()[i];
        d_trans.push_back(transition(from, aut.apply_hidden_label_map(label(p)), to(p)));
      }
    }
    else
    {
      get_trans(begin,tss,tss.get_set_child_left(d),d_trans,aut);
      get_trans(begin,tss,tss.get_set_child_right(d),d_trans,aut);
    }
  }
}
} // namespace detail


template <class LTS_TYPE>
void determinise(LTS_TYPE& l)
{
  tree_set_store tss;

  std::vector<transition> d_transs;
  std::vector<std::ptrdiff_t> d_states;

  // create the initial state of the DLTS
  d_states.push_back(l.initial_state());
  std::ptrdiff_t d_id = tss.set_set_tag(tss.create_set(d_states));
  d_states.clear();

  // std::multimap < transition::size_type, std::pair < transition::size_type, transition::size_type > >
  // const outgoing_transitions_per_state_t begin(l.get_transitions(),l.hidden_label_map(),l.num_states(),true);
  const outgoing_transitions_per_state_t begin(l.get_transitions(),l.num_states(),true);

  l.clear_transitions();
  l.clear_state_labels();
  std::size_t d_ntransitions = 0;
  std::vector < transition > d_transitions;

  std::size_t s;
  std::size_t i,to,lbl,n_t;

  while (d_id < tss.get_next_tag())
  {
    // collect the outgoing transitions of every state of DLTS state d_id in
    // the vector d_transs
    detail::get_trans(begin,tss,tss.get_set(d_id),d_transs,l);

    // sort d_transs by label and (if labels are equal) by destination
    const detail::compare_transitions_lts compare(l.hidden_label_map());
    sort(d_transs.begin(),d_transs.end(),compare);

    n_t = d_transs.size();
    i = 0;
    for (lbl = 0; lbl < l.num_action_labels(); ++lbl)
    {
      // compute the destination of the transition with label lbl
      while (i < n_t && l.apply_hidden_label_map(d_transs[i].label()) < lbl)
      {
        ++i;
      }
      while (i < n_t && l.apply_hidden_label_map(d_transs[i].label()) == lbl)
      {
        to = d_transs[i].to();
        d_states.push_back(to);
        while (i < n_t && l.apply_hidden_label_map(d_transs[i].label()) == lbl &&
               d_transs[i].to() == to)
        {
          ++i;
        }
      }
      s = tss.create_set(d_states);

      // generate the transitions to each of the next states
      if (!tss.is_set_empty(s))
      {
        d_transitions.push_back(transition(d_id,lbl,tss.set_set_tag(s)));

        if (d_ntransitions%10000 == 0)
        {
          mCRL2log(log::debug) <<
            "generated " << tss.get_next_tag() << " states and " << d_ntransitions
                         << " transitions; explored " << d_id << " states" << std::endl;
        }
      }
      d_states.clear();
    }
    d_transs.clear();
    ++d_id;
  }


  l.set_num_states(d_id,false); // remove the state values, and reset the number of states.
  l.set_initial_state(0);

  for (const transition& t: d_transitions)
  {
    l.add_transition(t);
  }
  assert(is_deterministic(l));
}

} // namespace lts
} // namespace mcrl2

#endif // MCRL2_LTS_LTS_ALGORITHM_H



