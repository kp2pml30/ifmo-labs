# Ручное построение парсера выражений с множествами в стиле python

## Грамматика

### Было

```
Expr = InE
InE = Ore (Inners Ore)*
Innners = in | not in
Ore = (Ore or)? Xore
Xore = (Xore xor)? Ande
Ande = (Ande and)? Atom
Atom = name | '(' Expr ')' | not Atom
```

### Как убирается левая рекурсия:

```
A -> Aa
A -> b
```
меняется на
```
A -> bA'
A' -> aA'
A' -> ε
```

### Стало

```
Expr = InE
InE = Ore (not? in Ore)?
Ore = Xore (or Xore)*
Xore = Ande (xor Ande)*
Ande = Minuse (and Minuse)*
Minuse = Atom (minus Atom)*
Atom = name | '(' Expr ')' | not Atom
```

или строго

```
Expr -> InE
InE -> Ore InE1
InE1 -> EPSILON
InE1 -> Inners Ore InE1
Inners -> in
Inners -> not in
Ore -> Xore Ore1
Ore1 -> EPSILON
Ore1 -> or Xore Ore1
Xore -> Ande Xore1
Xore1 -> EPSILON
Xore1 -> xor Ande Xore1
Ande -> Minuse Ande1
Ande1 -> EPSILON
Ande1 -> and Minuse Ande1
Minus -> Atom Minuse1
Minuse1 -> EPSILON
Minuse1 -> minus Atom Minuse1
Atom -> name
Atom -> lparen Expr rparen
Atom -> not Atom
```

## Множетсва FIRST & FOLLOW

[алгоритм построения](https://neerc.ifmo.ru/wiki/index.php?title=Построение_FIRST_и_FOLLOW)

|Правило|FST            |FOLLOW            |
|-------|---------------|------------------|
|Expr   |FST(Atom)      |rparen \$         |
|InE    |FST(Atom)      |rparen \$         |
|InE1   |FST(Inners) ε  |rparen \$         |
|Inners |not in         |FST(Atom)         |
|Ore    |FST(Atom)      |FLW(InE) in not   |
|Ore1   |or ε           |FLW(Ore)          |
|Xore   |FST(Atom)      |FLW(Ore) or       |
|Xore1  |xor ε          |FLW(Xore)         |
|Ande   |FST(Atom)      |FLW(Xore) xor     |
|Ande1  |and ε          |FLW(Ande)         |
|Minus  |FST(Atom)      |FLW(Ande) and     |
|Minuse1|minus ε        |FLW(Minuse)       |
|Atom   |not lparen name|FLW(Minuse) minus |

рассмотрим основные виды правил и как они преобразовались в FOLLOW:

* `X₂ -> X₁ X₂'`  
	`FST(X₂') = { ε, op } => FLW(X₁) ∪= FLW(X₂) ∪ { op }`
* `X₂' -> ε`
* `X₂' -> op X₁ X₂'`  
	не дает ничего нового `=> FLW(X₁) = FLW(X₂) ∪ { op }`


### Проверка при помощи онлайн-чекера

[чекер](http://smlweb.cpsc.ucalgary.ca/vital-stats.php?grammar=Expr+->+InE.%0D%0AInE+->+Ore+InE1.%0D%0AInE1+->%0D%0A++%7C+Inners+Ore+InE1.%0D%0AInners+->+in.%0D%0AInners+->+not+in.%0D%0AOre+->+Xore+Ore1.%0D%0AOre1+->%0D%0A++%7C+or+Xore+Ore1.%0D%0AXore+->+Ande+Xore1.%0D%0AXore1+->%0D%0A++%7C+xor+Ande+Xore1.%0D%0AAnde+->+Atom+Ande1.%0D%0AAnde1+->%0D%0A++%7C+and+Atom+Ande1.%0D%0AAtom+->+name%0D%0A++%7C+lparen+Expr+rparen%0D%0A++%7C+not+Atom.)
