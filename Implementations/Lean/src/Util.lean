open Classical

theorem stab (a : Prop) (hnna : ¬¬a) : a := by
  cases em a with
    | inl ha =>
      exact ha
    | inr hna =>
      exact absurd hna hnna

theorem mp {a b : Prop} (f : a → b) (x : a) : b := by
  exact f x

theorem em' (a : Prop) : a ∨ ¬a := by
  apply stab
  intro u
  apply u
  apply Or.inr
  intro v
  apply u
  apply Or.inl
  exact v
