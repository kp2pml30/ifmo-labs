language core;

extend with #letrec-bindings, #let-patterns, #pattern-ascriptions, #letrec-bindings, #letrec-many-bindings;

fn main(n : Nat) -> Nat {
  return letrec x as Nat = y, y as Nat = x in x
}
