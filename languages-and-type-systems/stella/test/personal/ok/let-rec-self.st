language core;

extend with #letrec-bindings, #let-patterns, #pattern-ascriptions, #letrec-bindings;

fn main(n : Nat) -> Nat {
  return letrec x as Nat = x in x
}
