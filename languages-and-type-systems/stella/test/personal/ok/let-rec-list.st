language core;

extend with #letrec-bindings, #let-patterns, #pattern-ascriptions, #letrec-bindings, #lists;

fn main(n : Nat) -> Nat {
  return letrec x as [Nat] = cons(0, x) in List::head(List::tail(List::tail(List::tail(x))))
}
