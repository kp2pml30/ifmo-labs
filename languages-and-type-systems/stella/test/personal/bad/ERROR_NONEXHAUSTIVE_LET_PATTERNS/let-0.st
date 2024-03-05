language core;

extend with #structural-patterns, #natural-literals, #sum-types, #let-bindings, #tuples, #let-patterns;

fn main(n : Nat) -> Nat {
  return let 0 = n in
  n
}
