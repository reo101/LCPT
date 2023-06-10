theorem mp {a b : Prop} (f : a → b) (x : a) : b := by
  exact f x

namespace Classical

/-- Stability, proved using `em` -/
theorem stab (a : Prop) : ¬¬a -> a := by
  intro hnna
  cases Classical.em a with
    | inl ha =>
      exact ha
    | inr hna =>
      exact absurd hna hnna

/-- Excluded middle, proved using `stab` -/
theorem em' (a : Prop) : a ∨ ¬a := by
  apply stab
  intro u
  apply u
  apply Or.inr
  intro v
  apply u
  apply Or.inl
  exact v

end Classical

macro "⊥" : term => `(False)
macro x:term:35 "∨ꜝ" y:term:35 : term => `(¬$x -> ¬$y -> ⊥)
macro x:term:35 "∧ꜝ" y:term:35 : term => `(¬($x -> $y -> ⊥))
macro "∃ꜝ " x:ident ", " b:term:35 : term => `(¬(∀ $x, ¬$b))
