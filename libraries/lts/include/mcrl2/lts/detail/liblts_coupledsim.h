// Author(s): Huong Ngoc Le
// Copyright: ?
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file lts/detail/liblts_coupledsim.h

// NOX BA ---------------------------------------------------------------------

#ifndef _LIBLTS_COUPLED_SIM_H
#define _LIBLTS_COUPLED_SIM_H

#include <iostream>
#include <cstdio>
#include <cstdlib>
#include <algorithm>
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

bool DEBUG_COUPLED_SIM_ENABLE = true;
bool use_old_approch_before_20200219 = false;

namespace mcrl2
{
namespace lts
{
namespace detail
{

// TODO(nox): extrac this
// NOX BA ---------------------------------------------------------------------

const unsigned char NODE_ATK = 0;  // placeholder indicating node is an attacker node
const unsigned char NODE_DEF = 1;  // placeholder indicating a node, which is alwas reachable as coupling.
const unsigned char NODE_CPL = 2;  // placeholder indicating a node, which is alwas reachable as coupling.

// std::vector<ACTION_LABEL_T> m_action_labels; // At position 0 we always find the label that corresponds to tau.
// typedef ACTION_LABEL_T action_label_t;

// coupled simulation game node
typedef struct _game_node
{
  unsigned char flag;
  size_t act;
  size_t p; size_t q;
  bool swapped;  // false := p is from lts1
} cs_game_node;

// connection between game nodes
typedef struct _game_move
{
  cs_game_node from, to;
  size_t act;
  std::string action_label;
  bool weak;
} cs_game_move;

// support
bool operator==(const cs_game_node &n0, const cs_game_node &n1)
{
  return n0.flag == n1.flag
    && n0.swapped == n1.swapped
    && n0.act == n1.act
    && n0.p == n1.p
    && n0.q == n1.q;
}

// support
bool operator!=(const cs_game_node &n0, const cs_game_node &n1)
{
  return !(n0 == n1);
}

// support
bool operator<(const cs_game_node &n0, const cs_game_node &n1)
{
  return n0.flag != n1.flag ? n0.flag < n1.flag
    : n0.act != n1.act ? n0.act < n1.act
    : n0.swapped != n1.swapped ? n0.swapped < n1.swapped
    : n0.p != n1.p ? n0.p < n1.p
    : n0.q < n1.q;
}

// support
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

// support
std::string to_string(const cs_game_move &m)
{
  std::string tag0 = m.from.flag == NODE_ATK ? "<a>" : "<d>";
  std::string tag1 = m.to.flag == NODE_ATK ? "<a>" : "<d>";

  std::string alabel
    = m.to.flag != NODE_DEF
    ? ""
    : " " + std::to_string(m.act) + "=" + m.action_label;

  return
    "[" + tag0 + to_string(m.from) + "] "
    + (m.weak ? " --> " : " -> ")
    + alabel
    + " [" + tag1 + to_string(m.to) + "]";
}

// support
bool equals(const cs_game_move &m0, const cs_game_move &m1, bool weak_transition = false)
{
  return m0.act == m1.act && (!weak_transition && !(m0.weak || m1.weak));
}

// support
bool operator<(const cs_game_move &m0, const cs_game_move &m1)
{
  return m0.from != m1.from ? m0.from < m1.from : m0.to < m1.to;
}

// --

template <class LTS_TYPE>
bool coupled_simulation_compare(LTS_TYPE& l1,
                         LTS_TYPE& l2)
{
  std::set<cs_game_node> attacker_nodes;  // (flag=NODE_ATK, placeholder, node::int, node::int)
  std::set<cs_game_node> defender_nodes;  // (flag, act::int, (node:int, node::int))

  std::set<transition> l1_weak_transitions, l2_weak_transitions;

  std::set<cs_game_move> moves;  // moves (node,node)
  std::string move_label; // label as string representation.
  std::ostringstream stream; // bypassing behavior (workaround for DEBUG)

  /* Define game nodes here. */

  /* Get Weak transitions. */
  std::stack<transition> todo_weak;
  // std::set<transition> l1_weak_transitions;
  // std::set<transition> l2_weak_transitions; // do I need to save them?

  /* filter transitions of t2. */
  std::map<size_t,std::map<transition,bool>>  // if strong transition on true
    l2_tran_from_node, l2_tran_into_node,
    l1_tran_from_node, l1_tran_into_node;

  std::cout
    << "// Restructure given LTS data structures, "
    << " get meta and chain weak-transitions\n"
    << "var show_lts = \""
    << "\\n# zoom: 1.0"
    //<< "\\n# edgeMargin: 1.0"
    << "\\n# gutter: 200.0"
    << "\\n# fontSize: 10"
    << "\\n# arrowSize: 0.5"
    << "\\n# lineWidth: 1.0"
    << "\\n# stroke: #000"
    << "\\n# .p: fill=#D9D64F circle"
    << "\\n# .q: fill=#ACA8F0 circle\\n\";\n\n";

  { // restructure l1 => get meta data and chain weak transitions.
    std::cout << "var show_lts1_strong = \"\";\n";
    for (const transition t1 : l1.get_transitions())
    {
      l1_tran_from_node[t1.from()][t1] = true;  // outgoing
      l1_tran_into_node[t1.to()][t1] = true;  // incoming

      /* Every transition is a weak transition, append to todo. */
      todo_weak.push(transition(t1.from(), t1.label(), t1.to()));

      l1_weak_transitions.insert(transition(t1.from(), t1.label(), t1.to()));

      // add tau loop for everyone.
      l1_weak_transitions.insert(transition(t1.from(), 0, t1.from()));
      l1_weak_transitions.insert(transition(t1.to(), 0, t1.to()));

      // DEBUG
      std::cout << "show_lts1_strong += \"\\n[<p>p" << t1.from() << "]"
        << " -> "
        << " " << (l1.action_label(t1.label()))
        << " [<p>p" << t1.to() << "]\";\n";
    }
    std::cout << "show_lts2_strong += \"\\n\";\n";

    /* Add weak transititions. */
    // on branching copy path and add all branches fins as fins.
    while (!todo_weak.empty())
    {
      // pop and keep just start and extension.
      // finish if next is second not tau.
      transition weak = todo_weak.top();
      todo_weak.pop();
      size_t f = weak.from();
      size_t l = weak.label();
      size_t t = weak.to();
      bool already_good = !l1.is_tau(l);  // path already has a good action

      std::map<transition,bool> next = l1_tran_from_node[t];
      size_t len = next.size();

      if (true)  // also just tau chains may be later used
      // if (already_good)  // (actually already) done
      {
        /* The current todo weak transition is already valid.*/
        // if it was strong before, it stays strong, else added as weak.
        l1_weak_transitions.insert(weak);
        l1_tran_into_node[t][weak] |= false;
        l1_tran_from_node[f][weak] |= false;
      }

      if (len < 1)  // no further steps.
      {
        continue;
      }
      else  // just extend simply.
      {
        for (const auto &ntrans : next)
        {
          size_t next_label = ntrans.first.label();
          bool next_tau = l1.is_tau(next_label);

          /* If tau: extend new todo with extension.
           * If all before only tau: extend new todo with extension.
           */
          if (next_tau || !already_good)
          {
            /* Maybe use new label: If now good.*/
            transition new_extended_weak
              = transition(f, !already_good ? next_label : l, ntrans.first.to());

            // re-add new branches.
            todo_weak.push(new_extended_weak);
          }

        }
      }
      // cuurent weak transition is done now.
    }  // done l1 tau forest (all tau pathes).
  }

  { // ANALOG for l2
    std::cout << "var show_lts2_strong = \"\";\n";
    for (const transition t2 : l2.get_transitions())
    {
      l2_tran_from_node[t2.from()][t2] = true;  // outgoing
      l2_tran_into_node[t2.to()][t2] = true;  // incoming

      /* Every transition is a weak transition, append to todo. */
      todo_weak.push(transition(t2.from(), t2.label(), t2.to()));
      l2_weak_transitions.insert(transition(t2.from(), t2.label(), t2.to()));

      // add tau loop for everyone.
      l2_weak_transitions.insert(transition(t2.from(), 0, t2.from()));
      l2_weak_transitions.insert(transition(t2.to(), 0, t2.to()));

      // DEBUG
      std::cout << "show_lts2_strong += \"\\n[<q>q" << t2.from() << "]"
        << " -> "
        << " " << (l2.action_label(t2.label()))
        << " [<q>q" << t2.to() << "]\";\n";
    }
    std::cout << "show_lts2_strong += \"\\n\";\n";

    /* Add weak transititions. */
    // on branching copy path and add all branches fins as fins.
    while (!todo_weak.empty())
    {
      // pop and keep just start and extension.
      // finish if next is second not tau.
      transition weak = todo_weak.top();
      todo_weak.pop();
      size_t f = weak.from();
      size_t l = weak.label();
      size_t t = weak.to();
      bool already_good = !l2.is_tau(l);  // path already has a good action

      std::map<transition,bool> next = l2_tran_from_node[t];
      size_t len = next.size();

      if (true)  // all, also just tau chains may be requeseted later
      // if (already_good)  // (actually already) done
      {
        /* The current todo weak transition is already valid.*/
        // if it was strong before, it stays strong, else added as weak.
        l2_weak_transitions.insert(weak);
        l2_tran_into_node[t][weak] |= false;
        l2_tran_from_node[f][weak] |= false;
      }

      if (len < 1)  // no further steps.
      {
        continue;
      }
      else  // just extend simply.
      {
        for (const auto &ntrans : next)
        {
          size_t next_label = ntrans.first.label();
          bool next_tau = l2.is_tau(next_label);

          /* If tau: extend new todo with extension.
           * If all before only tau: extend new todo with extension.
           */
          if (next_tau || !already_good)
          {
            /* Maybe use new label: If now good.*/
            transition new_extended_weak
              = transition(f, !already_good ? next_label : l, ntrans.first.to());

            // re-add new branches.
            todo_weak.push(new_extended_weak);
          }

        }
      }
      // cuurent weak transition is done now.
    }  // done l2 tau forest (all tau pathes).
  }

  std::cout << "\n// show all out, including weak;\nvar show_lts_weak = \"\";\n";
  for (size_t p = 0; p < l1.num_states(); p++)
  {
      for (const auto &out : l1_tran_from_node[p])
      {
        if (std::find(
              l1.get_transitions().begin(),
              l1.get_transitions().end(), out.first)
            != l1.get_transitions().end())
          continue; // strong, skip

        std::cout << "show_lts_weak += \"\\n"
          << "[<p>p" << out.first.from() << "]"
          << " --> "
          << " " << out.first.label()
          << ":" << l1.action_label(out.first.label()) << " "
          << "[<p>p" << out.first.to() << "]"
          << "\";\n";
      }
  }

  // DEBUG: Show all new inserted outgoing nodes (by weak transition
  // creation)
  for (size_t q = 0; q < l2.num_states(); q++)
  {
      for (const auto &out : l2_tran_from_node[q])
      {
        if (std::find(
              l2.get_transitions().begin(),
              l2.get_transitions().end(),
              out.first)
            != l2.get_transitions().end())
          continue; // strong, skip

        std::cout << " show_lts_weak += \"\\n"
          << "[<q>q" << out.first.from() << "]"
          << " --> "
          << " " << out.first.label()
          << ":" << l2.action_label(out.first.label()) << " "
          << "[<q>q" << out.first.to() << "]"
          << "\";\n";
      }
  }

  std::cout << "// Attacker nodes (p,q)a in Ga ... as S1 x S2 aka all possible pairs between them\n";
  std::cout << "// Prepare defender nodes 1: all possible nodes, and how they are reached.\n";

  // TODO(nox) 2020-02-08: How do I call them on the answering stuff?
  // They are not the same like the normal transition labels. :<

  for (size_t p0 = 0; p0 < l1.num_states(); p0++)
  {
    for (size_t q0 = 0; q0 < l2.num_states(); q0++)
    {
      cs_game_node p0q0 = {NODE_ATK, 0, p0, q0, false};  // atk (p0,q0)
      cs_game_node cplp0q0 = {NODE_CPL, 0, p0, q0, false}; // (cpl,p0,q0)

      /* swapped. */
      cs_game_node q0p0 = {NODE_ATK, 0, q0, p0, true};  // swapped (q0,p0)
      cs_game_node cplq0p0 = {NODE_CPL, 0, q0, p0, true};  // swapped (cpl,q0,p0)

      attacker_nodes.insert(p0q0);
      attacker_nodes.insert(q0p0);
      defender_nodes.insert(cplp0q0);
      defender_nodes.insert(cplq0p0);

      moves.insert({p0q0, cplp0q0, 0, "cpl"});  // (p0,q0) -> (Cpl,p0,q0)
      moves.insert({q0p0, cplq0p0, 0, "cpl"});  // (q0,p0) -> (Cpl,q0,p0)

      /* bisim: coupling answer q'=q, p'=p*/
      moves.insert({cplp0q0, q0p0, 0, "bisim"});
      moves.insert({cplq0p0, p0q0, 0, "bisim"});

      std::map<cs_game_move, bool> todo_if;

      // TODO this includes also weak, as challenge giver invalid, solve!
      /* CREATED:
       * challenge: p0 a -> p1
       * answers : p0 a => p1, if there's q0 a -> q1
       * coupling : p0 => p1
       */
      for (const auto t1 : l1_tran_from_node[p0])
      {
        size_t a = t1.first.label();
        size_t p1 = t1.first.to();
        bool atau = l1.is_tau(a);
        bool strong = t1.second;  // transition was strong

        stream << (l1.action_label(a));
        move_label = stream.str();
        stream.str("");
        stream.clear();

        // --

        // TODO only strong
        if (strong)
        {
          /* (p0,q0) -> (a,p1,q0),  if [p0] a -> [p1] */
          cs_game_node ap1q0 = {NODE_DEF, a, p1, q0, false};
          defender_nodes.insert(ap1q0);
          moves.insert({p0q0, ap1q0, a, move_label});

          if (atau)  // => answering q0 can also stay.
          {
            cs_game_node q0_stay = {NODE_ATK, 0, p1, q0, false};
            attacker_nodes.insert(q0_stay);
            moves.insert({ap1q0, q0_stay, 0, ""});
          }
        }

        /* ANSWER swapped, only if (q0,a,q1)
         * (a, q1,p0) -> (q1,q1),  if [p0] a => [p1]*/
        // if [*] a -> [2] exists, and then for all [2].
        // XXX reconsider, maybe TODO with delayed checks, bc l2_transitions are later reviewed
        for (const transition &bq1 : l2.get_transitions())
        {
          size_t b = bq1.label(), q1 = bq1.to();

          // strong q a-> q1 demonstrates, p0 a=> p1 simulates.
          if (l2.action_label(b) == l1.action_label(a))
          {
            /* (a, q1, p0) -> (q1, p1), ... if p0 a=> p1.*/
            cs_game_node bqp0 = {NODE_DEF, b, q1, p0, true};  // (b, q, p0)d
            cs_game_node qp1 = {NODE_ATK, 0, q1, p1, true};  /// (q,p1)a
            defender_nodes.insert(bqp0);
            attacker_nodes.insert(qp1);
            // todo_if.insert();  // waiting list for this move on condition.
            moves.insert({bqp0, qp1, a, move_label});
          }
        }

        /* Coupling, .. if p0 => p1 */
        if (atau)  // for cplq0p0, answer the swapped cpl-challenge
        {
          cs_game_node p0p1 = {NODE_ATK, 0, p1, q0, false};  // swapping
          attacker_nodes.insert(p0p1);
          moves.insert({cplq0p0, p0p1, 0, "p \21d2 p'"});
        }
      }

      // TODO this includes also weak, as challenge giver invalid, solve!
      /* CREATED:
       * challenge: q0 b -> q1
       * answers : q0 b => q1,  if there's p0 b -> p1
       * coupling : q0 => q1
       */
      for (const auto &t2 : l2_tran_from_node[q0])
      {
        size_t b = t2.first.label();
        size_t q1 = t2.first.to();
        bool btau = l2.is_tau(b);
        bool strong = t2.second; // transition was strong

        stream << (l2.action_label(b));
        move_label = stream.str();
        stream.str("");
        stream.clear();

        // --

        // TODO only strong
        if (strong)  // only strong
        {
          /* swapped.
           * (q0,p0) -> (a,q1,p0),  if [q0] a -> [q1] */
          cs_game_node bq1p0 = {NODE_DEF, b, q1, p0, true};
          defender_nodes.insert(bq1p0);
          moves.insert({q0p0, bq1p0, b, move_label});

          if (btau)  // => answering q0 can also stay.
          {
            cs_game_node p0_stay = {NODE_ATK, 0, q1, p0, true};
            attacker_nodes.insert(p0_stay);
            moves.insert({bq1p0, p0_stay, 0, ""});
          }
        }

        /* ANSWER, only if (p0,b,p1)
         * (b, p1,q0) -> (p1,q1),  if [q0] a => [p1]*/
        // if [*] a -> [2] exists, and then for all [2].
        // XXX reconsider, maybe TODO with delayed checks, bc l2_transitions are later reviewed
        for (const transition &ap1 : l1.get_transitions())
        {
          size_t a = ap1.label(), p1 = ap1.to();

          // strong q a-> q1 demonstrates, p0 a=> p1 simulates.
          if (l2.action_label(b) == l1.action_label(a))
          {
            /* (a, p1, q0) -> (p1, q1), ... if q0 a=> q1.*/
            cs_game_node apq0 = {NODE_DEF, a, p1, q0, false};  // (a,p?,q0)d
            cs_game_node pq1 = {NODE_ATK, 0, p1, q1, false};  // (p?,q1)a
            defender_nodes.insert(apq0);
            attacker_nodes.insert(pq1);
            // todo_if.insert();  // waiting list for this move on condition.
            moves.insert({apq0, pq1, b, move_label});
          }
        }

        /* Coupling, .. if q0 => q1 */
        if (btau)  // strong and weak, for cplp0q0
        {
          cs_game_node q0q1 = {NODE_ATK, 0, q1, p0, true};  // swapping
          attacker_nodes.insert(q0q1);
          moves.insert({cplp0q0, q0q1, 0, "q \21d2 q'"});
        }
      }
    }
  }

      // DEBUG
  std::cout << "// Now, a Game with "
    << attacker_nodes.size() << " Attacker nodes, "
    << defender_nodes.size() << " Defender nodes and "
    << moves.size() << " (unready) moves exists\n";

  std::cout << "// Get all the predecessors.\n";
  std::cout << "// Count their successors\n";
  std::cout << "// Mark everyone won by defender (d)\n";

  std::map<cs_game_node,std::set<cs_game_node>> predecessors;
  std::map<cs_game_node,int> successor_count;
  std::map<cs_game_node,int> nodes_won;
  const int WON_DEFENDER = 0, WON_ATTACKER = 1;

  std::cout // XXX REMOVE_ME
    << "var show_game "
    << "= \"\\n#title: ltscompare_coupledsim_csgame"
    << "\\n#fontSize: 10"
    << "\\n#arrowSize: 0.5"
    << "\\n#lineWidth: 1.0"
    << "\\n#zoom: 1.0"
    << "\\n#edges: rounded"
    << "\\n#.a: fill=#f77"
    << "\\n#.d: fill=#7f7 visual=roundrect"
    << "\\n#.l: visual=none"
    << "\\n#ranker: longest-path"
    << "\\n#gutter: 100"
    << "\\n#direction: right\\n\";\n";

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
    std::cout << "show_game += \"\\n" << to_string(m) << "\";\n";
  }
  std::cout << "show_game += \"\\n\";\n";

  std::cout << "\n// Run: Computing Winning Regions.\n";

  std::stack<cs_game_node> todo;
  for (cs_game_node d : defender_nodes) todo.push(d); // XXX make me better
  // todo.assign(defender_nodes.begin(), defender_nodes.end());

  std::cout << "// propagate_attacker_win for ...\n\n";
  std::cout << "var show_game_lost = \"\";\n";

  /* Calculate winning region. */
  while (!todo.empty())
  {
    /* Pop from queue. */
    cs_game_node n = todo.top();
    todo.pop();

    if (successor_count[n] <= 0)
    {
      std::cout << "show_game_lost += \"\\n[<l>" << to_string(n) << "]\";\n";
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
            std::cout << "// .. next : " << to_string(pred) << "\n";
            todo.push(pred);
            successor_count[pred] = 0; // to propagate next run.
          }
        }
      }
    }
  }
  std::cout << "show_game_lost += \"\\n\";\n";

  std::cout << "\n\nvar R = \"{";
  char seperator[3] = {'\0', ' ', '\0'};

  /* Filter R, where its elemens are coupled similar. */
  std::set<cs_game_node> cs_relation;
  for (const auto &pq : attacker_nodes)
  {
    if (nodes_won.find(pq) == nodes_won.end())
    {
      std::cout << "I am requested, but never listed. Set to default\n";
    }

    if (nodes_won[pq] == WON_DEFENDER)
    {
      cs_relation.insert(pq);
      std::cout << seperator << to_string(pq);
      seperator[0] = ',';
    }
  }
  std::cout << "}\";\n";

  std::string fst, snd;
  if (true)  // DEBUG
  {
    std::cout << "\n\n// Show linking.\n";
    std::cout << "var show_sim_related = \"\";\n";
    for (const auto &n : cs_relation)
    {
      fst = !n.swapped ? "<p>p" : "<q>q";
      snd = !n.swapped ? "<q>q" : "<p>p";
      std::cout << "show_sim_related += \"\\n[" << fst << n.p << "] --> [" << snd << n.q << "]\";\n";
    }
  }
  std::cout << "show_sim_related += \"\\n\";\n";

  // DEBUG
  std::cout << "\n"
    << "\nvar show_lts_strong = show_lts1_strong + show_lts2_strong;\n"
    << "\nnomnoml.draw(document.getElementById(\"show-lts-input\"),"
    << " show_lts + show_lts_strong);"
    << "\nnomnoml.draw(document.getElementById(\"show-lts-weak\"),"
    << " show_lts + show_lts_strong + show_lts_weak);"
    << "\nnomnoml.draw(document.getElementById(\"show-lts-simulation\"),"
    << " show_lts + show_lts_strong + show_sim_related);"
    << "\nnomnoml.draw(document.getElementById(\"show-game-moves\"),"
    << " show_game_lost + show_game);"
    << "\n";

  /* Return true iff root nodes are in R / won by defender. */
  cs_game_node roots[]
    = {{NODE_ATK, 0, 0, 0, false}, {NODE_ATK, 0, 0, 0, true}};

  bool similar  // root is in R
    = nodes_won[roots[0]] == WON_DEFENDER
    && nodes_won[roots[1]] == WON_DEFENDER;

  std::cout
  << "document.getElementById(\"lts-relation\").innerHTML "
  << "= \"R = \" + R + \"</br>"
  << "&rArr; <b>" << (similar ? "true" : "false") << "</b>\";";

  std::cout << "\n\n// ";

  return similar;
}
} // end namespace detail
} // end namespace lts
} // end namespace mclr
#endif // _LIBLTS_COUPLED_SIM_H
