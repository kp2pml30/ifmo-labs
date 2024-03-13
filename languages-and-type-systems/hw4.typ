#import "typst-prooftree/prooftree.typ": *

#set heading(numbering: "1.1")
#set page(numbering: "1")

#counter(heading).update(3)

= HW 4

#prooftree(
    axiom($Gamma tack.r t_1 : T$),
    axiom($Gamma, x: T tack.r t_2 : "Bool"$),
    axiom($Gamma, x: T tack.r t_3 : T$),
    axiom($Gamma, x: T tack.r t_4 : "Unit"$),
    rule(n: 4, $Gamma tack.r "for"[T] (x=t_1; t_2; t_3) "do" t_4 : "List"[T]$)
)

== Раскрытие сокращений
```
fix
    (\rec x ->
        if t2
        then (\_ -> cons x (rec t3)) t4
        else [])
    t1
```
$"fix" (lambda "rec" . lambda x: T. "if" t_2 "then" (lambda u: "Unit". "cons" t_4 ("rec" t_3)) t_4 "else" "nil") space t_1$
== Сохранение типизации
Введем сокращения для компактности контекста
- $Alpha eq.triple x: T, "rec" : T -> "List" T$
- $Beta eq.triple Alpha, u: "Unit" eq.triple x: T, "rec" : T -> "List" T, u: "Unit"$
#prooftree(
    axiom($Gamma, Beta tack.r x : T$),

    axiom($Gamma, Beta tack.r "rec" : T -> "List" T$),
    axiom(label: "for", $Gamma, Beta tack.r t_3 : T$),
    rule(n: 2, $Gamma, Beta tack.r "rec" t_3 : "List" T$),

    rule(n: 2, $Gamma, Beta tack.r "cons" x ("rec" t_3) : "List" T$),
    rule($Gamma, Beta tack.r (lambda u: "Unit". "cons" x ("rec" t_3)) : "Unit" -> "List" T$),

    axiom(label: "for", $Gamma, Beta tack.r t_4: "Unit"$),

    rule(n: 2, label: $P_1$, $Gamma, Alpha tack.r (lambda u: "Unit". "cons" x ("rec" t_3)) space t_4 : "List" T$),
)
#scale(x: 70%, y: 70%, origin: left)[
    #prooftree(
        axiom(label: "for", $Gamma, Alpha tack.r t_2 : "Bool"$),

        axiom(label: $P_1$, $Gamma, Alpha tack.r (lambda u: "Unit". "cons" x ("rec" t_3)) space t_4 : "List" T$),

        axiom($Gamma, Alpha tack.r "nil" : "List" T$),

        rule(n: 3, $Gamma, Alpha tack.r "if" t_2 "then" (lambda u: "Unit". "cons" x ("rec" t_3)) space t_4 "else" "nil" : "List" T$),
        rule($Gamma, "rec": T -> "List" T tack.r (lambda x: T. "if" t_2 "then" (lambda u: "Unit". "cons" x ("rec" t_3)) space t_4 "else" "nil" : "List" T) : T -> "List" T$),
        rule($Gamma, "rec": T -> "List" T tack.r (lambda "rec". lambda x: T. "if" t_2 "then" (lambda u: "Unit". "cons" x ("rec" t_3)) space t_4 "else" "nil" : "List" T) : (T -> "List" T) -> T -> "List" T$),
        rule($Gamma tack.r "fix" (lambda "rec". lambda x: T. "if" t_2 "then" (lambda u: "Unit". "cons" x ("rec" t_3)) space t_4 "else" "nil" : "List" T) : T -> "List" T$),

        axiom(label: "for", $Gamma tack.r t_1 : T$),
        rule(n: 2, $Gamma tack.r "fix" (lambda "rec" . lambda x: T. "if" t_2 "then" (lambda u: "Unit". "cons" x space ("rec" t_3)) t_4 "else" "nil") space t_1 : "List" T$)
    )
]

Типизация совпала (в "аксиомы", аннотированные "for" необходимо подставить деревья, использованные для доказательства в выводе с "for")

=== Можно ли убрать T?
It depends. Кажется, что в нашем можно.

Если мы хотим, чтобы у нас не осталось типов-свободных переменных и у нас исчисление по Карри, то нельзя из-за наличия "fix", но, кажется, у нас исчисление по Черчу (есть типы у параметров $lambda$). Единственное место, где $T$ фигурирует не из контекста, это в посылке для $t_1$, потрем прочие места:

$"for" (x=t_1; "false"; x) "do" "unit"$

В такой форме мы можем получить тип из $t_1$, если только не является тавтологией конструкция $tack.r "fix" (lambda x. x) : Y -> Y$. Наша схема аксиом требует тип у параметра лямбды, а значит однозначно получим тип из $t_1$. Более формально: если раньше по любому выражению можно было однозначно понять тип, то это останется правдой благодаря рекурсии по дереву выражения, которое для for будет заходить в дерево для $t_1$ и благодаря конечности дерева рано или поздно дойдет до выражения, не содержащего "for", значит все "for" ниже типизируются при возврате из рекурсии.

Ответ: можно убрать
