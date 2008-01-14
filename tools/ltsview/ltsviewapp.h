// Author(s): Bas Ploeger and Carst Tankink
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file ltsviewapp.h
/// \brief Add your file description here.

#ifndef LTSVIEWAPP_H
#define LTSVIEWAPP_H
#include <wx/wx.h>
#include <string>
#include "mediator.h"
#include "mainframe.h"
#include "glcanvas.h"
#include "lts.h"
#include "visualizer.h"
#include "utils.h"

class LTSViewApp : public wxApp, public Mediator {
  private:
    LTS *lts;
    GLCanvas *glCanvas;
    MainFrame *mainFrame;
    Settings *settings;
    Visualizer *visualizer;
    Utils::RankStyle rankStyle;
    Utils::MarkStyle markStyle;
    bool fsmStyle;

  public:
    void	  activateMarkRule(const int index,const bool activate);
    void	  addMarkRule();
    void	  applyMarkStyle(Utils::MarkStyle ms);
    void	  editMarkRule(const int index);
    Utils::RGB_Color getNewRuleColour();
    std::string getVersionString();
    void	  markAction(std::string label);
    void	  notifyRenderingFinished();
    void	  notifyRenderingStarted();
    virtual int  OnExit();
    virtual bool OnInit();
    void	  openFile(std::string fileName);
    void	  removeMarkRule(const int index);
    void	  setMatchAnyMarkRule(int i);
    void	  setRankStyle(Utils::RankStyle rs);
    void	  setVisStyle(Utils::VisStyle vs);
    void	  setFSMStyle(bool b);
    void	  unmarkAction(std::string label);
    void          startSim();
    int           getNumberOfParams() const;
    std::string   getActionLabel(const int i) const;
    std::string   getParName(const int i) const;
    std::string   getParValue(const int i, const int j) const;
    void          selectStateByID(const int id);
    void          selectCluster(const int rank, const int pos);
    void          deselect();
    int           getNumberOfObjects();
    
    void          zoomInBelow();
    void          zoomInAbove();
    void          zoomOutTillTop();
    void          zoomOut();

    void          reportError(std::string const& error);

    void          loadTrace(std::string const& path);
    void          generateBackTrace();

    void printHelp();
    void printVersion();

    DECLARE_EVENT_TABLE()
};


DECLARE_APP(LTSViewApp)

#endif
