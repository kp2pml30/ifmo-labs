language core;

extend with #structural-patterns, #natural-literals, #sum-types, #let-bindings, #tuples, #let-patterns;

fn main(n : Nat + Bool) -> Nat {
  return let inl(x) = n in
  n
}
