namespace Vec

universe u

inductive Vec : (a : Type u) -> Nat -> Type u
| nil : Vec a 0
| cons : {n : Nat} -> a -> Vec a n -> Vec a n.succ

open Vec

-- head: returns the first element of a non-empty vector
def head {a : Type u} {n : Nat} (v : Vec a n.succ) : a :=
  match v with
  | cons x _ => x

-- tail: returns the remaining elements of a non-empty vector
def tail {a : Type u} {n : Nat} (v : Vec a n.succ) : Vec a n :=
  match v with
  | cons _ xs => xs

end Vec
