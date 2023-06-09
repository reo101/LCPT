import Utilities

variable (A B : Prop)

----------------

theorem fakeAnd: A ∧ꜝ B ↔ A ∧ B := by
  apply Iff.intro
  case mp =>
    intro h
    apply And.intro
    case left =>
      apply Classical.stab
      intro hna
      apply h
      intro ha
      apply False.elim
      exact hna ha
    case right =>
      apply Classical.stab
      intro hnb
      apply h
      intro _ hb
      exact hnb hb
  case mpr =>
    intro ⟨ha, hb⟩
    intro h
    exact h ha hb

theorem fakeOr: A ∨ꜝ B ↔ A ∨ B := by
  apply Iff.intro
  case mp =>
    intro h
    apply Or.inl
    cases Classical.em A with
    | inl ha =>
      exact ha
    | inr hna =>
      sorry
  case mpr =>
    intro haob hna hnb
    cases haob with
    | inl ha =>
      contradiction
    | inr hna =>
      contradiction
