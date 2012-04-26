// Author(s): Rimco Boudewijns
// Copyright: see the accompanying file COPYING or copy at
// https://svn.win.tue.nl/trac/MCRL2/browser/trunk/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//

#include "mainwindow.h"

#include <QFileDialog>
#include <QTextEdit>
#include <QMessageBox>

MainWindow::MainWindow(QWidget *parent) :
  QMainWindow(parent)
{

  m_ui.setupUi(this);
  m_parser = new Parser();

  connect(m_ui.actionNew, SIGNAL(triggered()), this, SLOT(onNew()));
  connect(m_ui.actionOpen, SIGNAL(triggered()), this, SLOT(onOpen()));
  connect(m_ui.actionSave, SIGNAL(triggered()), this, SLOT(onSave()));
  connect(m_ui.actionSave_As, SIGNAL(triggered()), this, SLOT(onSaveAs()));
  connect(m_ui.actionExit, SIGNAL(triggered()), this, SLOT(onExit()));

  connect(m_ui.actionUndo, SIGNAL(triggered()), this, SLOT(onUndo()));
  connect(m_ui.actionRedo, SIGNAL(triggered()), this, SLOT(onRedo()));
  connect(m_ui.actionCut, SIGNAL(triggered()), this, SLOT(onCut()));
  connect(m_ui.actionCopy, SIGNAL(triggered()), this, SLOT(onCopy()));
  connect(m_ui.actionPaste, SIGNAL(triggered()), this, SLOT(onPaste()));
  connect(m_ui.actionDelete, SIGNAL(triggered()), this, SLOT(onDelete()));
  connect(m_ui.actionSelect_All, SIGNAL(triggered()), this, SLOT(onSelectAll()));

  connect(m_ui.actionFind, SIGNAL(triggered()), this, SLOT(onFind()));
  connect(m_ui.actionWrap_mode, SIGNAL(triggered()), this, SLOT(onWrapMode()));
  connect(m_ui.actionReset_perspective, SIGNAL(triggered()), this, SLOT(onResetPerspective()));

  connect(m_ui.actionAbout, SIGNAL(triggered()), this, SLOT(onAbout()));

  connect(m_ui.buttonParse, SIGNAL(clicked()), this, SLOT(onParse()));
  connect(m_parser, SIGNAL(parsed()), this, SLOT(parsed()));

  connect(m_ui.buttonRewrite, SIGNAL(clicked()), this, SLOT(onRewrite()));

  connect(m_ui.documentManager, SIGNAL(tabCloseRequested(int)), this, SLOT(onCloseRequest(int)));

  connect(m_ui.documentManager, SIGNAL(documentCreated(DocumentWidget*)), this, SLOT(formatDocument(DocumentWidget*)));
  connect(m_ui.documentManager, SIGNAL(documentClosed(DocumentWidget*)), this, SLOT(cleanupDocument(DocumentWidget*)));

  connect(m_ui.dockWidgetOutput, SIGNAL(logMessage(QString, QString, QDateTime, QString, QString)), this, SLOT(onLogOutput(QString, QString, QDateTime, QString, QString)));
}

MainWindow::~MainWindow()
{
  m_parser->deleteLater();
}

void MainWindow::closeEvent(QCloseEvent *event)
{
  for (int i = 0; i < m_ui.documentManager->documentCount(); i++)
  {
    if (!this->onCloseRequest(i))
    {
      event->ignore();
      return;
    }
  }
  event->accept();
}

void MainWindow::onNew()
{
  m_ui.documentManager->newFile();
}

void MainWindow::onOpen()
{
  QString fileName(QFileDialog::getOpenFileName(this, tr("Open file"), QString(),
                                                tr("mCRL2 specification (*.mcrl2 *.txt )")));
  if (!fileName.isNull()) {
    m_ui.documentManager->openFile(fileName);
  }
}

void MainWindow::onSave()
{
  this->saveDocument(m_ui.documentManager->currentDocument());
}

void MainWindow::onSaveAs()
{
  QString fileName(QFileDialog::getSaveFileName(this, tr("Save file"), QString(),
                                                tr("mCRL2 specification (*.mcrl2 *.txt )")));
  if (!fileName.isNull()) {
    m_ui.documentManager->saveFile(fileName);
  }
}

void MainWindow::onExit()
{
  this->close();
}

void MainWindow::onUndo()
{
  m_ui.documentManager->currentDocument()->getEditor()->undo();
}

void MainWindow::onRedo()
{
  QMessageBox::information(this,tr("Hoi"),tr("Redo"),QMessageBox::Ok);
  m_ui.documentManager->currentDocument()->getEditor()->redo();
}

void MainWindow::onCut()
{
  m_ui.documentManager->currentDocument()->getEditor()->cut();
}

void MainWindow::onCopy()
{
  m_ui.documentManager->currentDocument()->getEditor()->copy();
}

void MainWindow::onPaste()
{
  m_ui.documentManager->currentDocument()->getEditor()->paste();
}

void MainWindow::onDelete()
{
  m_ui.documentManager->currentDocument()->getEditor()->textCursor().deleteChar();
}

void MainWindow::onSelectAll()
{
  m_ui.documentManager->currentDocument()->getEditor()->selectAll();
}

void MainWindow::onFind()
{
}

void MainWindow::onWrapMode()
{
}

void MainWindow::onResetPerspective()
{
}

void MainWindow::onAbout()
{
}

void MainWindow::onParse()
{
  m_ui.buttonParse->setEnabled(false);
  DocumentWidget *document = m_ui.documentManager->currentDocument();
  QMetaObject::invokeMethod(m_parser, "parse", Qt::QueuedConnection, Q_ARG(QString, document->getEditor()->toPlainText()));
}

void MainWindow::parsed()
{
  m_ui.buttonParse->setEnabled(true);
}

void MainWindow::onRewrite()
{
  m_ui.buttonRewrite->setEnabled(false);
  m_ui.editRewriteOutput->clear();
  DocumentWidget *document = m_ui.documentManager->currentDocument();
  QMetaObject::invokeMethod(document->findChild<Rewriter *>()->getThread(), "rewrite", Qt::QueuedConnection, Q_ARG(QString, document->getEditor()->toPlainText()), Q_ARG(QString, m_ui.editRewriteExpr->text()));
}

void MainWindow::rewritten(QString output)
{
  m_ui.editRewriteOutput->setPlainText(output);
  m_ui.buttonRewrite->setEnabled(true);
}


bool MainWindow::saveDocument(DocumentWidget *document)
{
  QString fileName = document->getFileName();
  if (fileName.isNull()) {
    fileName = QFileDialog::getSaveFileName(this, tr("Save file"), QString(),
                                            tr("mCRL2 specification (*.mcrl2 *.txt )"));
  }
  if (!fileName.isNull()) {
    m_ui.documentManager->saveFile(fileName);
    return true;
  }
  return false;
}

bool MainWindow::onCloseRequest(int index)
{
  DocumentWidget *document = m_ui.documentManager->getDocument(index);

  if (!document->isModified()) {
    m_ui.documentManager->closeDocument(index);
    return true;
  }

  int ret = QMessageBox::question ( this, tr("Specification modified"), tr("Do you want to save your modifications?"), QMessageBox::Yes | QMessageBox::No | QMessageBox::Cancel, QMessageBox::Yes);
  switch(ret)
  {
    case QMessageBox::Yes:
      if (this->saveDocument(document))
      {
        m_ui.documentManager->closeDocument(index);
      }
      break;
    case QMessageBox::No:
      m_ui.documentManager->closeDocument(index);
      break;
    case QMessageBox::Cancel:
      return false;
      break;
  }

  return true;
}

void MainWindow::onLogOutput(QString level, QString hint, QDateTime timestamp, QString message, QString formattedMessage)
{
  m_ui.statusBar->showMessage(formattedMessage, 5000);
}

void MainWindow::formatDocument(DocumentWidget *document)
{
  QTextEdit *editor = document->getEditor();
  editor->setWordWrapMode(QTextOption::NoWrap);

  QFont font;
  font.setFamily("Monospace");
  font.setFixedPitch(true);

  editor->setFont(font);
  Highlighter *highlighter = new Highlighter(editor->document());

  Rewriter *rewriter = new Rewriter(document);
  QMetaObject::invokeMethod(rewriter->getThread(), "setRewriter", Qt::QueuedConnection, Q_ARG(QString, QString("jitty")));
  connect(rewriter->getThread(), SIGNAL(rewritten(QString)), this, SLOT(rewritten(QString)));
}

void MainWindow::cleanupDocument(DocumentWidget *document)
{

}
