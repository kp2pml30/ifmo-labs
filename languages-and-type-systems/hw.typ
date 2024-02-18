#import "typst-prooftree/prooftree.typ": *

#set heading(numbering: "1.1")
#set page(numbering: "1")

#outline(depth: 2)
#pagebreak()

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

#pagebreak()
= HW 2

Типизируйте, постройте дерево вывода типа

Из-за проблем с typst и огромной высоты некоторые деревья будут разбиты =(

== $(lambda x: B -> N. lambda y: B. "succ" (x space y)) space (lambda x: B. "if" x "then" "succ" 0 "else" 0) "true"$

#scale(x: 70%, y: 70%)[
  #prooftree(
    axiom($x: B -> N, y: B tack.r x : B -> N$),
    axiom($x: B -> N, y: B tack.r y : B$),
    rule(n: 2, $x: B -> N, y: B tack.r (x space y) : N$),
    rule($x: B -> N, y: B tack.r ("succ" (x space y)) : N$),
    rule($x: B -> N tack.r (lambda y: B. "succ" (x space y)) : B -> N$),
    rule(label: $P_1 =$, $(lambda x: B -> N. lambda y: B. "succ" (x space y)) : (B -> N) -> B -> N$),
  )

  #prooftree(
    axiom(label: $P_1$, $(lambda x: B -> N. lambda y: B. "succ" (x space y)) : (B -> N) -> B -> N$),

    axiom($x: B tack.r x: B$),
    axiom($x: B tack.r 0: N$),
    rule($x: B tack.r "succ" 0: N$),
    axiom($x: B tack.r 0: N$),
    rule(n: 3, $x: B tack.r "if" x "then" "succ" 0 "else" 0 : N$),
    rule($(lambda x: B. "if" x "then" "succ" 0 "else" 0) : B -> N$),
    rule(n: 2, $(lambda x: B -> N. lambda y: B. "succ" (x space y)) space (lambda x: B. "if" x "then" "succ" 0 "else" 0) : B -> N$),

    axiom($"true": B$),
    rule(n: 2, $(lambda x: B -> N. lambda y: B. "succ" (x space y)) space (lambda x: B. "if" x "then" "succ" 0 "else" 0) "true" : N$),
  )
]

Ответ: $"Nat"$

== $(lambda b: B. "if" b "then" (lambda x: N. lambda y: B. x) "else" (lambda x: N. lambda y: B. y)) "false" 0$

#scale(x: 70%, y: 70%)[
  #prooftree(
    axiom($b: B tack.r b: B$),
    axiom($b: B tack.r (lambda x: N. lambda y: B. x) : N -> B -> N$),
    axiom($b: B tack.r (lambda x: N. lambda y: B. y) : N -> B -> B$),
    rule(n: 3, label: "FAIL!", $b: B tack.r "if" b "then" (lambda x: N. lambda y: B. x) "else" (lambda x: N. lambda y: B. y) : N -> "?"$),
    rule($(lambda b: B. "if" b "then" (lambda x: N. lambda y: B. x) "else" (lambda x: N. lambda y: B. y)) : B -> N -> "?"$),
    axiom($"false": B$),
    rule(n: 2, $(lambda b: B. "if" b "then" (lambda x: N. lambda y: B. x) "else" (lambda x: N. lambda y: B. y)) "false" : N -> "?"$),
    axiom($"0": N$),
    rule(n: 2, $(lambda b: B. "if" b "then" (lambda x: N. lambda y: B. x) "else" (lambda x: N. lambda y: B. y)) "false" 0 : "?"$)
  )
]

Ответ: не типизировалось (см. "FAIL!", разные типы у веток "if")

== $(lambda f: (N -> N) -> N -> N. f space (f space (lambda x: N. x)) space 0) space (lambda z: N -> N. lambda n: N. z space (z space n))$

Читать $f: ...$ как $f: (N -> N) -> N -> N$

#scale(x: 70%, y: 70%)[
  #prooftree(
    axiom($f: ... tack.r f: (N -> N) -> N -> N$),
    axiom($f: ..., x: N tack.r f: (N -> N) -> N -> N$),
    axiom($f: ..., x: N tack.r x : N$),
    rule($f: ... tack.r lambda x: N. x : N -> N$),
    rule(n: 2, $f: ... tack.r f space (lambda x: N. x) : N -> N$),
    rule(n: 2, $f: ... tack.r f space (f space (lambda x: N. x)) : N -> N$),
    axiom($f: ... tack.r 0: N$),
    rule(n: 2, $f: (N -> N) -> N -> N tack.r f space (f space (lambda x: N. x)) space 0 : N$),
    rule(label: $P_1=$, $(lambda f: (N -> N) -> N -> N. f space (f space (lambda x: N. x)) space 0) : ((N -> N) -> N -> N) -> N$),
  )
]

#scale(x: 70%, y: 70%)[
  #prooftree(
    axiom($z: N -> N, n: N tack.r z : N -> N$),
    axiom($z: N -> N, n: N tack.r z : N -> N$),
    axiom($z: N -> N, n: N tack.r n : N$),
    rule(n: 2, $z: N -> N, n: N tack.r z space n : N$),
    rule(n: 2, $z: N -> N, n: N tack.r z space (z space n) : N$),
    rule($z: N -> N tack.r (lambda n: N. z space (z space n)) : N -> N$),
    rule(label: $P_2=$, $(lambda z: N -> N. lambda n: N. z space (z space n)) : (N -> N) -> N -> N$),
  )
]

#scale(x: 70%, y: 70%)[
  #prooftree(
    axiom(label: $P_1$, $(lambda f: .... f space (f space (lambda x: N. x)) space 0) : ((N -> N) -> N -> N) -> N$),
    axiom(label: $P_2$, $(lambda z: N -> N. lambda n: N. z space (z space n)) : (N -> N) -> N -> N$),
    rule(n: 2, $(lambda f: (N -> N) -> N -> N. f space (f space (lambda x: N. x)) space 0) space (lambda z: N -> N. lambda n: N. z space (z space n)) : N$),
  )
]

Ответ: $"Nat"$
