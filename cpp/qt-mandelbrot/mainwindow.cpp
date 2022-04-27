#include "ui_mainwindow.h"
#include "mainwindow.h"

#include <QMouseEvent>
#include <QTimer>

#include <iostream>
#include <qnamespace.h>

MainWindow::MainWindow(QWidget* parent)
	: QMainWindow(parent)
	, ui(new Ui::MainWindow)
	, mandelbrot([this]() { this->Schedule(); })
{
	ui->setupUi(this); // this line gives dataraces even in empty solution >_<
}

void MainWindow::paintEvent(QPaintEvent* ev)
{
	QMainWindow::paintEvent(ev);

	QPainter painter(this);
	mandelbrot.Render(width(), height());
	mandelbrot.Paint(painter);
	ev->accept();
}

void MainWindow::Schedule()
{
	QTimer::singleShot(10, this, [this](){ this->update(); });
}
void MainWindow::wheelEvent(QWheelEvent* ev)
{
	QMainWindow::wheelEvent(ev);

	auto d = ev->angleDelta().ry();
	if (d == 0)
		return;
	MandelbrotHolder::PrecType dd = -d / 90.0;
	mandelbrot.Render(width(), height());
	mandelbrot.Scale(dd, width(), height());
	this->update();
	ev->accept();
}

void MainWindow::keyPressEvent(QKeyEvent *ev)
{
	QMainWindow::keyPressEvent(ev);

	if (auto k = ev->key(); k >= Qt::Key_1 && k <= Qt::Key_9)
	{
		mandelbrot.SetPower(k - Qt::Key_1 + 2);
		ev->accept();
	}
	else
	{
		ev->ignore();
	}
}

void MainWindow::mouseReleaseEvent(QMouseEvent* ev)
{
	if (ev->button() == Qt::LeftButton)
	{
		mouseData.enabled = false;
		ev->accept();
	}
	else
	{
		ev->ignore();
	}
}
void MainWindow::mousePressEvent(QMouseEvent* ev)
{
	if (ev->button() == Qt::LeftButton)
	{
		mouseData.enabled = true;
		auto cp = ev->screenPos();
		mouseData.lastX = cp.x();
		mouseData.lastY = cp.y();
		ev->accept();
	}
	else
	{
		ev->ignore();
	}
}
void MainWindow::mouseMoveEvent(QMouseEvent* ev)
{
	QMainWindow::mouseMoveEvent(ev);
	if (!mouseData.enabled)
	{
		ev->ignore();
		return;
	}
	auto curt = std::chrono::system_clock::now();
	auto delta = std::chrono::duration_cast<std::chrono::milliseconds>(curt - mouseData.lastUpd).count();
	mouseData.lastUpd = curt;
	auto cp = ev->screenPos();
	int
		lx = mouseData.lastX,
		ly = mouseData.lastY,
		cx = cp.x(),
		cy = cp.y();
	mouseData.lastX = cx;
	mouseData.lastY = cy;
	mandelbrot.Move(cx - lx, cy - ly);

	ev->accept();
	QMainWindow::update();
}

MainWindow::~MainWindow()
{}
