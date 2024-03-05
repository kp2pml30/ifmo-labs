language core;

extend with #structural-patterns, #natural-literals, #sum-types, #let-bindings, #tuples, #let-patterns;

fn main(n : Nat) -> Nat {
  return let x = {1, 2} in
  let {x1, y1} = x in
  x1
}
