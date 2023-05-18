abbrev Variable: Type := String
abbrev Index: Type := Nat

inductive Λ : Type
| var : Variable → Λ
| abs : Variable -> Λ → Λ
| app : Λ → Λ → Λ
