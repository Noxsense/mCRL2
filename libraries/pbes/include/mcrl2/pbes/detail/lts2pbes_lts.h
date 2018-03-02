// Author(s): Wieger Wesselink
// Copyright: see the accompanying file COPYING or copy at
// https://svn.win.tue.nl/trac/MCRL2/browser/trunk/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/pbes/detail/lts2pbes_lts.h
/// \brief add your file description here.

#ifndef MCRL2_PBES_DETAIL_LTS2PBES_LTS_H
#define MCRL2_PBES_DETAIL_LTS2PBES_LTS_H

#include "mcrl2/lts/lts_lts.h"

namespace mcrl2 {

namespace pbes_system {

namespace detail {

// custom LTS type that maps states to a vector of outgoing edges
class lts2pbes_lts
{
  public:
    typedef std::size_t state_type;
    typedef std::size_t label_type;

    struct edge
    {
      edge(label_type label_, state_type state_, std::size_t index_)
        : label(label_),
          state(state_),
          index(index_)
      {}

      label_type label;
      state_type state;
      std::size_t index;
    };

    typedef std::vector<edge> edge_list;

  protected:
    std::map<state_type, edge_list> m_state_map;
    std::vector<lps::multi_action> m_action_labels;
    std::size_t m_state_count;
    edge_list m_empty_edge_list;

  public:
    lts2pbes_lts(const lts::lts_lts_t& lts0)
    {
      const auto& transitions = lts0.get_transitions();
      for (std::size_t i = 0; i < transitions.size(); i++)
      {
        const auto& transition = transitions[i];
        state_type s = transition.from();
        label_type a = transition.label();
        state_type t = transition.to();
        m_state_map[s].emplace_back(a, t, i);
      }

      for (lts::lts_lts_t::labels_size_type i = 0; i < lts0.num_action_labels(); i++)
      {
        lts::action_label_lts a = lts0.action_label(i);
        m_action_labels.emplace_back(a.actions(), a.time());
      }
      m_state_count = lts0.num_states();
    }

    // returns the outgoing edges of state s
    const edge_list& edges(state_type s) const
    {
      auto i = m_state_map.find(s);
      if (i == m_state_map.end())
      {
        return m_empty_edge_list;
      }
      else
      {
        return i->second;
      }
    }

    const std::vector<lps::multi_action>& action_labels() const
    {
      return m_action_labels;
    }

    std::size_t state_count() const
    {
      return m_state_count;
    }

    const std::map<state_type, edge_list>& state_map() const
    {
      return m_state_map;
    }
};

} // namespace detail

} // namespace pbes_system

} // namespace mcrl2

#endif // MCRL2_PBES_DETAIL_LTS2PBES_LTS_H
