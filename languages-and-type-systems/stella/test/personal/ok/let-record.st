language core;

extend with #structural-patterns, #natural-literals, #sum-types, #let-bindings, #tuples, #let-patterns, #records, #natural-literals;

fn main(n : Nat) -> Nat {
  return let { y = z, x = w} = {x = 11, y = 12} in
  z
}
