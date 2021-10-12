## Было

Expr = InE

InE = Ore (Inners Ore)?

Innners = in | not in

Ore = (Ore or)? Xore
Xore = (Xore xor)? Ande
Ande = (Ande and)? Atom

Atom = name | '(' Expr ')' | not Atom

## Как убирается левая рекурсия:

A -> Aa
A -> b
меняется на
A -> bA'
A' -> aA'
A' -> ε

## Стало

Expr = InE
InE = Ore (not? in Ore)?
Ore = Xore (or Xore)*
Xore = Ande (xor Ande)*
Ande = Atom (and Atom)*
Atom = name | '(' Expr ')' | not Atom
