#set heading(numbering: "1.1")
= HW 1

Вычислите следующие бестиповые $lambda$ термы, используя строгое вычисление

Для каждого из термов выше:
+ Распишите пошаговое вычисление терма (один переход соответствует одному шагу (⟶) операционной семантики).
+ Укажите, находится ли конечный терм в нормальной форме.
+ Является ли он значением?
+ Является ли он тупиковым термом?
+ Переведите исходный терм в безымянное представление. Свободные переменные переводятся так: x ↦ 0, y ↦ 1, z ↦ 2.
+ Распишите пошаговое вычисление терма в безымянном представлении (один переход соответствует одному шагу (⟶) операционной семантики)

== Выражение $(lambda x . space lambda y . space lambda z . space y space x) space (lambda y . space y) space (lambda y . space z)$
=== Редукции
+ $(lambda x . space lambda y . space lambda z . space y space x) space (lambda y . space y) space (lambda y . space z)$
  - $alpha$ equiv: $(lambda a . space lambda b . space lambda c . space b space a) space (lambda d . space d) space (lambda e . space z)$
  - de Bruijn $(lambda lambda lambda 1 space 2) space (lambda 0) space (lambda z)$
+ $(lambda b . space lambda c . space b space (lambda d . space d)) space (lambda e . space z)$
  - de Bruijn $(lambda lambda 1 space (lambda 0)) space (lambda z)$
+ $lambda c . space (lambda e . space z) space (lambda d . space d)$
  - de Bruijn $lambda (lambda z) space (lambda 0)$

=== Ответ
+ $lambda c . space (lambda e . space z) space (lambda d . space d)$
+ находится в нормальной ($lambda$ абстракция)
+ значение ($lambda$ абстракция)
+ не тупиковый (значение)
+ $lambda (lambda 2) space (lambda 0)$

== Выражение $(lambda x . space lambda y . space (lambda z . space x) space y) space (lambda y . space y) space (lambda y . space z)$
=== Редукции
+ $(lambda x . space lambda y . space (lambda z . space x) space y) space (lambda y . space y) space (lambda y . space z)$
  - $alpha$ equiv: $(lambda a . space lambda b . space (lambda c . space a) space b) space (lambda d . space d) space (lambda e . space z)$
  - de Bruijn $(lambda lambda (lambda 2) space 0) space (lambda 0) space (lambda z)$
+ $(lambda b . space (lambda c . space lambda d . space d) space b) space (lambda e . space z)$
  - de Bruijn $(lambda (lambda lambda 0) space 0) space (lambda z)$
+ $(lambda c . space lambda d . space d) space (lambda e . space z)$
  - de Bruijn $(lambda lambda 0) space (lambda z)$
+ $lambda d . space d$
  - de Bruijn $lambda 0$

=== Ответ
+ $lambda d . space d$
+ находится в нормальной ($lambda$ абстракция)
+ значение ($lambda$ абстракция)
+ не тупиковый (значение)
+ $lambda 0$

== Выражение $(lambda x . space lambda y . space (lambda z . space x) space z space y) space (lambda y . space lambda x . space x) space z space x$
=== Редукции
+ $(lambda x . space lambda y . space (lambda z . space x) space z space y) space (lambda y . space lambda x . space x) space z space x$
  - $alpha$ equiv: $(lambda a . space lambda b . space (lambda c . space a) space z space b) space (lambda d . space lambda e . space e) space z space x$
  - de Bruijn $(lambda lambda (lambda 2) space z space 0) space (lambda lambda 0) space z space x$
+ $(lambda b . space (lambda c . space lambda d . space lambda e . space e) space z space b) space z space x$
  - de Bruijn $(lambda (lambda lambda lambda 0) space z space 0) space z space x$
+ $(lambda c . space lambda d . space lambda e . space e) space z space z space x$
  - de Bruijn $(lambda lambda lambda 0) space z space z space x$
+ $(lambda d . space lambda e . space e) space z space x$
  - de Bruijn $(lambda lambda 0) space z space x$
+ $(lambda e . space e) space x$
  - de Bruijn $(lambda 0) space x$
+ $x$
  - de Bruijn $x$

=== Ответ
+ $x$
+ находится в нормальной (свободная переменная)
+ значение (свободная перемменная)
+ не тупиковый (значение)
+ $0$

== Выражение $(lambda x . space lambda y . space x space (x space y)) space (lambda y . space lambda z . space y space (y space z)) space (lambda z . space x space z) space y$
=== Редукции
+ $(lambda x . space lambda y . space x space (x space y)) space (lambda y . space lambda z . space y space (y space z)) space (lambda z . space x space z) space y$
  - $alpha$ equiv: $(lambda a . space lambda b . space a space (a space b)) space (lambda c . space lambda d . space c space (c space d)) space (lambda e . space x space e) space y$
  - de Bruijn $(lambda lambda 1 space (1 space 0)) space (lambda lambda 1 space (1 space 0)) space (lambda x space 0) space y$
+ $(lambda b . space (lambda c . space lambda d . space c space (c space d)) space ((lambda c . space lambda d . space c space (c space d)) space b)) space (lambda e 
. space x space e) space y$
  - $alpha$ equiv: $(lambda b . space (lambda c . space lambda d . space c space (c space d)) space ((lambda a . space lambda e . space a space (a space e)) space b)) space (lambda f . space x space f) space y$
  - de Bruijn $(lambda (lambda lambda 1 space (1 space 0)) space ((lambda lambda 1 space (1 space 0)) space 0)) space (lambda x space 0) space y$
+ $(lambda c . space lambda d . space c space (c space d)) space ((lambda a . space lambda e . space a space (a space e)) space (lambda f . space x space f)) space y$
  - de Bruijn $(lambda lambda 1 space (1 space 0)) space ((lambda lambda 1 space (1 space 0)) space (lambda x space 0)) space y$
+ $(lambda c . space lambda d . space c space (c space d)) space (lambda e . space (lambda f . space x space f) space ((lambda f . space x space f) space e)) space y$
  - $alpha$ equiv: $(lambda c . space lambda d . space c space (c space d)) space (lambda e . space (lambda f . space x space f) space ((lambda a . space x space a) space e)) space y$
  - de Bruijn $(lambda lambda 1 space (1 space 0)) space (lambda (lambda x space 0) space ((lambda x space 0) space 0)) space y$
+ $(lambda d . space (lambda e . space (lambda f . space x space f) space ((lambda a . space x space a) space e)) space ((lambda e . space (lambda f . space x space f) space ((lambda a . space x space a) space e)) space d)) space y$
  - $alpha$ equiv: $(lambda d . space (lambda e . space (lambda f . space x space f) space ((lambda a . space x space a) space e)) space ((lambda b . space (lambda c . space x space c) space ((lambda g . space x space g) space b)) space d)) space y$
  - de Bruijn $(lambda (lambda (lambda x space 0) space ((lambda x space 0) space 0)) space ((lambda (lambda x space 0) space ((lambda x space 0) space 0)) space 0)) space y$
+ $(lambda e . space (lambda f . space x space f) space ((lambda a . space x space a) space e)) space ((lambda b . space (lambda c . space x space c) space ((lambda g . space x space g) space b)) space y)$
  - de Bruijn $(lambda (lambda x space 0) space ((lambda x space 0) space 0)) space ((lambda (lambda x space 0) space ((lambda x space 0) space 0)) space y)$
+ $(lambda e . space (lambda f . space x space f) space ((lambda a . space x space a) space e)) space ((lambda c . space x space c) space ((lambda g . space x space g) space y))$
  - de Bruijn $(lambda (lambda x space 0) space ((lambda x space 0) space 0)) space ((lambda x space 0) space ((lambda x space 0) space y))$
+ $(lambda e . space (lambda f . space x space f) space ((lambda a . space x space a) space e)) space ((lambda c . space x space c) space (x space y))$
  - de Bruijn $(lambda (lambda x space 0) space ((lambda x space 0) space 0)) space ((lambda x space 0) space (x space y))$
+ $(lambda e . space (lambda f . space x space f) space ((lambda a . space x space a) space e)) space (x space (x space y))$
  - de Bruijn $(lambda (lambda x space 0) space ((lambda x space 0) space 0)) space (x space (x space y))$
+ $(lambda f . space x space f) space ((lambda a . space x space a) space (x space (x space y)))$
  - de Bruijn $(lambda x space 0) space ((lambda x space 0) space (x space (x space y)))$
+ $(lambda f . space x space f) space (x space (x space (x space y)))$
  - de Bruijn $(lambda x space 0) space (x space (x space (x space y)))$
+ $x space (x space (x space (x space y)))$
  - de Bruijn $x space (x space (x space (x space y)))$

=== Ответ
+ $x space (x space (x space (x space y)))$
+ находится в нормальной (невозможно вычислять дальше)
+ не значение (применение)
+ тупиковый (в нормальной но не значение)
+ $0 space (0 space (0 space (0 space 1)))$
