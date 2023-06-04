open Classical

theorem stab (a : Prop) (hnna : ¬¬a) : a := by
  cases em a with
    | inl ha =>
      exact ha
    | inr hna =>
      exact absurd hna hnna

theorem mp {a b : Prop} (f : a → b) (x : a) : b := by
  exact f x

---------------

theorem pierce (a b : Prop) : ((a → b) → a) → a := by
  intro u
  /- cases em a with -/
  /-   | inl ha => -/
  /-     exact ha -/
  /-   | inr hna => -/
  /-     apply h -/
  /-     intro ha -/
  /-     exact absurd ha hna -/
  apply stab
  intro v
  apply @mp a False
  case f =>
    exact v
  case x =>
    apply @mp (a → b) a
    case f =>
      exact u
    case x =>
      intro w
      apply False.elim
      apply @mp a False
      case f =>
        exact v
      case x =>
        exact w
