#import "typst-prooftree/prooftree.typ": *

#set heading(numbering: "1.1")
#set page(numbering: "1")

#counter(heading).update(2)

= HW 3

== Построить дерево вывода типов
$(lambda f. (f space { "succ" 0, "iszero" (f space { 0, "false" }).a }).b) (lambda t. { a = t.1, b = t.2 })$

#scale(x: 70%, y: 70%)[
    #prooftree(
        axiom($f: N times B -> {a: N, b: B} tack.r 0: N$),
        rule($f: N times B -> {a: N, b: B} tack.r "succ" 0: N$),

        axiom($f: N times B -> {a: N, b: B} tack.r 0: N$),
        axiom($f: N times B -> {a: N, b: B} tack.r "false": B$),
        rule(n: 2, $f: N times B -> {a: N, b: B} tack.r {0, "false"}: N times B$),
        rule($f: N times B -> {a: N, b: B} tack.r f space { 0, "false" }: {a: N, b: B}$),
        rule($f: N times B -> {a: N, b: B} tack.r f space { 0, "false" }.a: N$),
        rule($f: N times B -> {a: N, b: B} tack.r "iszero" (f space { 0, "false" }.a): B$),

        rule(n: 2, label: $P_1 =$, $f: N times B -> {a: N, b: B} tack.r { "succ" 0, "iszero" (f space { 0, "false" }).a } : N times B$),
    )

    #prooftree(
        axiom(label: $P_1$, $f: N times B -> {a: N, b: B} tack.r { "succ" 0, "iszero" (f space { 0, "false" }).a } : N times B$),
        rule($f: N times B -> {a: N, b: B} tack.r f space { "succ" 0, "iszero" (f space { 0, "false" }).a } : {a: N, b: B}$),
        rule($f: N times B -> {a: N, b: B} tack.r (f space { "succ" 0, "iszero" (f space { 0, "false" }).a }).b : B$),
        rule($(lambda f. (f space { "succ" 0, "iszero" (f space { 0, "false" }).a }).b) : {a: N, b: B} -> B$),

        axiom($t: N times B tack.r t: N times B$),
        rule($t: N times B tack.r t.1: N$),
        axiom($t: N times B tack.r t: N times B$),
        rule($t: N times B tack.r t.2: B$),
        rule(n: 2, $t: N times B tack.r { a = t.1, b = t.2} : { a: N, b: B }$),
        rule($(lambda t. { a = t.1, b = t.2}): N times B -> { a: N, b: B }$),
        rule(n: 2, $(lambda f. (f space { "succ" 0, "iszero" (f space { 0, "false" }).a }).b) space (lambda t. { a = t.1, b = t.2}) : B$)
    )
]

$(lambda f: N times B -> {a: N, b: B}. (f space { "succ" 0, "iszero" (f space { 0, "false" }).a }).b) (lambda t: N times B. { a = t.1, b = t.2 })$



== Пары в просто-типизированном лямбда исчислении
В бестиповом пара: $lambda a. lambda b. lambda f. f space a space b$. Если мы попробуем это типизировать, то получим $forall a. forall b. a -> b -> (forall r. (a -> b -> r) -> r)$, и здесь важно, что квантор над $r$ не поверхностный.

#enum(
  numbering: "a)",
  enum.item[
    + ${"t1", "t2"}$ это $(lambda a. lambda b. lambda f. f space a space b) "t1" "t2"$ (функция в скобках --- общий конструктор, если ее применить получится $lambda f. f "t1" "t2"$)
    + $t.1$ это $lambda a. lambda b. a$, т.е. $"const": T_1 -> T_2 -> T_1$
    + $t.2$ это $lambda a. lambda b. b$, типа $T_1 -> T_2 -> T_2$
    + $T_1 times T_2$ это $forall r. (a -> b -> r) -> r$, что не является типом в просто-типизированном лямбда исчислении, однако, если пара используется лишь один раз, то можно подставить $r$
  ],
  enum.item[
    Почему типизация не сохранится? Поскольку у нас нет кванторов.
    ```hs
    let x: Nat ⨯ Bool = {1, False} in
    foo x.0 x.1
    ```
    Раскроем:
    ```hs
    (\x: ? ->
        foo (x (\a b -> a)) (x (\a b -> b))) (\r -> r 1 False)
    ```
    но мы не можем применить x к двум разно типизированным функциям: $(lambda a. lambda b. a) : "Nat" -> "Bool" -> "Nat"$, а $(lambda a. lambda b. b) : "Nat" -> "Bool" -> "Bool"$, другими словами не можем дать тип $x$ (помечен как "?")
    Рас типизиция не сохранилось, то *ответ*: не сохраняет одновременно  вычисление и типизацию.
  ],
)

== Бонус
Я не знаю подразумевается ли дальшейшее решение при условии наличия кванторов, поскольку в нем придется переходить в System F для аккуратного доказательства с $Lambda$, что, кажется, выходит за рамки курса, но в том случае вычисление сохранится, ниже набросок доказательства

Покажем конструктор:
$(Lambda t_1. Lambda t_2. lambda a: t_1. lambda b: t_2. Lambda r. lambda f: t_1 -> t_2 -> r. f space a space b)$

Проектор: $t_1 times t_2 -> t_1$ выражается как $"pair" t_1 space (lambda a: t_1. lambda b: t_2. t_1)$

Проредуцируем ${x, y}.1$, где ${x, y}: t_1 times t_2$ (все переменные свободные для общности):
+ $((lambda a: t_1. lambda b: t_2. Lambda r. lambda f: t_1 -> t_2 -> r. f space a space b) x space y) space t_1 space (lambda a: t_1. lambda b: t_2. a)$ (просто раскрыли по определениям)
+ $((lambda b: t_2. Lambda r. lambda f: t_1 -> t_2 -> r. f space x space b) y) space t_1 space (lambda a: t_1. lambda b: t_2. a)$
+ $(Lambda r. lambda f: t_1 -> t_2 -> r. f space x space y) space t_1 space (lambda a: t_1. lambda b: t_2. a)$
+ $(lambda f: t_1 -> t_2 -> t_1. f space x space y) space (lambda a: t_1. lambda b: t_2. a)$
+ $(lambda a: t_1. lambda b: t_2. t_1) space x space y$
+ $(lambda b: t_2. x) space y$
+ $x$

Вычисление сохранилось
