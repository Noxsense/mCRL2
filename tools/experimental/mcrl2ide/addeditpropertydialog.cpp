// Author(s): Olav Bunte
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//

#include "addeditpropertydialog.h"
#include "ui_addeditpropertydialog.h"

#include <QMessageBox>
#include <QRegExpValidator>

AddEditPropertyDialog::AddEditPropertyDialog(bool add,
                                             ProcessSystem* processSystem,
                                             FileSystem* fileSystem,
                                             QWidget* parent)
    : QDialog(parent), ui(new Ui::AddEditPropertyDialog)
{
  ui->setupUi(this);

  this->processSystem = processSystem;
  this->fileSystem = fileSystem;
  oldPropertyName = "";
  propertyParsingProcessid = -1;

  ui->propertyNameField->setValidator(
      new QRegExpValidator(QRegExp("[A-Za-z0-9_\\s]*")));

  /* change the ui depending on whether this should be an add or edit property
   *   window */
  if (add)
  {
    windowTitle = "Add Property";
    ui->addEditButton->setText("Add");
  }
  else
  {
    windowTitle = "Edit Property";
    ui->addEditButton->setText("Edit");
  }

  setWindowTitle(windowTitle);
  setWindowFlags(Qt::Window);

  connect(ui->addEditButton, SIGNAL(clicked()), this, SLOT(checkInput()));
  connect(ui->cancelButton, SIGNAL(clicked()), this, SLOT(reject()));
  connect(processSystem, SIGNAL(processFinished(int)), this,
          SLOT(parseResults(int)));
  connect(this, SIGNAL(rejected()), this, SLOT(onRejected()));
}

void AddEditPropertyDialog::resetFocus()
{
  ui->addEditButton->setFocus();
  ui->propertyNameField->setFocus();
}

void AddEditPropertyDialog::clearFields()
{
  ui->propertyNameField->clear();
  ui->propertyTextField->clear();
}

void AddEditPropertyDialog::setProperty(Property property)
{
  ui->propertyNameField->setText(property.name);
  ui->propertyTextField->setPlainText(property.text);
}

Property AddEditPropertyDialog::getProperty()
{
  return Property(ui->propertyNameField->text(),
                  ui->propertyTextField->toPlainText());
}

void AddEditPropertyDialog::setOldPropertyName(QString propertyName)
{
  oldPropertyName = propertyName;
}

void AddEditPropertyDialog::abortPropertyParsing()
{
  if (propertyParsingProcessid >= 0)
  {
    /* we first change propertyParsingProcessid so that parsingResult doesn't
     *   get triggered */
    int parsingid = propertyParsingProcessid;
    propertyParsingProcessid = -1;
    processSystem->abortProcess(parsingid);
  }
}

void AddEditPropertyDialog::checkInput()
{
  QString propertyName = ui->propertyNameField->text();
  QString error = "";

  /* both input fields may not be empty and the propertyname may not exist
   * already */
  if (propertyName.count() == 0)
  {
    error = "The property name may not be empty";
  }
  else if (oldPropertyName != propertyName &&
           fileSystem->propertyNameExists(propertyName))
  {
    error = "A property with this name already exists";
  }
  else if (ui->propertyTextField->toPlainText().count() == 0)
  {
    error = "The property text may not be empty";
  }
  else
  {
    /* save the property, abort the previous parsing process and parse the
     * formula and wait for a reply */
    fileSystem->saveProperty(getProperty());
    abortPropertyParsing();
    propertyParsingProcessid = processSystem->parseProperty(getProperty());
  }

  if (!error.isEmpty())
  {
    QMessageBox msgBox(QMessageBox::Information, windowTitle, error,
                       QMessageBox::Ok, this, Qt::WindowCloseButtonHint);
    msgBox.exec();
  }
}

void AddEditPropertyDialog::parseResults(int processid)
{
  /* check if the process that has finished is the parsing process of this
   *   dialog */
  if (processid == propertyParsingProcessid)
  {
    /* if valid accept, else show message */
    QString error = "";
    QString result = processSystem->getResult(processid);

    if (result == "valid")
    {
      accept();
    }
    else if (result == "invalid")
    {
      error = "The entered formula is not a valid mu-calculus formula. See the "
              "parsing console for more information";
    }
    else
    {
      error = "Could not parse the entered formula. See the parsing console "
              "for more information";
    }

    if (!error.isEmpty())
    {
      QMessageBox msgBox(QMessageBox::Information, windowTitle, error,
                         QMessageBox::Ok, this, Qt::WindowCloseButtonHint);
      msgBox.exec();
    }
  }
}

void AddEditPropertyDialog::onRejected()
{
  /* abort the parsing process */
  abortPropertyParsing();
}

AddEditPropertyDialog::~AddEditPropertyDialog()
{
  delete ui;
}
