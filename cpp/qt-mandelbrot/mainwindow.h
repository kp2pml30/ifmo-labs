#pragma once

#include <array>
#include <chrono>

#include <QMainWindow>
#include <QPainter>
#include <QTimer>

#include"mandelbrot.h"

QT_BEGIN_NAMESPACE
namespace Ui
{
	class MainWindow;
}
QT_END_NAMESPACE

class MainWindow : public QMainWindow
{
	Q_OBJECT
public:
	MainWindow(QWidget* parent = nullptr);
	~MainWindow();

	void paintEvent(QPaintEvent*) override;
	void mouseReleaseEvent(QMouseEvent*) override;
	void mousePressEvent(QMouseEvent*) override;
	void mouseMoveEvent(QMouseEvent*) override;
	void wheelEvent(QWheelEvent*) override;

private:
	std::unique_ptr<Ui::MainWindow> ui;
	int scaleAccum = 0;

	MandelbrotHolder mandelbrot;

	struct {
		bool enabled = false;
		int lastX = 0;
		int lastY = 0;
		std::chrono::time_point<std::chrono::system_clock> lastUpd = std::chrono::system_clock::now();
	} mouseData;

	void Schedule();
};
