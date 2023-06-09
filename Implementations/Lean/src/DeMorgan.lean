import Util

section

variable (a b : Prop)
variable (α : Type)
variable (p : α → Prop)

theorem dm1 : ¬(a ∧ b) ↔ (¬a ∨ ¬b) := by
  apply Iff.intro
  case mp =>
    intro u
    apply stab
    intro v
    apply @mp (a ∧ b) False
    case f =>
      exact u
    case x =>
      apply And.intro
      case left =>
        apply stab
        intro w
        apply @mp (¬a ∨ ¬b) False
        case f =>
          exact v
        case x =>
          apply Or.inl
          exact w
      case right =>
        apply stab
        intro w
        apply @mp (¬a ∨ ¬b) False
        case f =>
          exact v
        case x =>
          apply Or.inr
          exact w
  case mpr =>
    intros u v
    apply Or.elim u
    case left =>
      intro x
      apply @mp a False
      case f =>
        exact x
      case x =>
        apply And.left
        exact v
    case right =>
      intro y
      apply @mp b False
      case f =>
        exact y
      case x =>
        apply And.right
        exact v

theorem dm2 : ¬(a ∨ b) ↔ (¬a ∧ ¬b) := by
  apply Iff.intro
  case mp =>
    intro u
    apply And.intro
    case left =>
      intro ha
      apply u
      apply Or.inl
      exact ha
    case right =>
      intro hb
      apply u
      apply Or.inr
      exact hb
  case mpr =>
    intro u
    intro v
    /- match v with -/
    /-  | Or.inl ha => -/
    /-    let hna := u.left -/
    /-    exact hna ha -/
    /-  | Or.inr hb => -/
    /-    let hnb := u.right -/
    /-    exact hnb hb -/
    apply @mp a False
    case f =>
      exact u.left
    case x =>
      apply Or.elim v
      case left =>
        intro x
        exact x
      case right =>
        intro y
        apply False.elim
        apply @mp b False
        case f =>
          exact u.right
        case x =>
          exact y

theorem dm3 : (¬∀x, p x) ↔ (∃x, ¬p x) := by
  apply Iff.intro
  case mp =>
    intro hnfxpx
    apply stab
    intro hnexnpx
    apply hnfxpx
    intro x
    apply stab
    intro hnpx
    apply @mp (∃x, ¬p x) False
    case f =>
      exact hnexnpx
    case x =>
      exact ⟨x, hnpx⟩
  case mpr =>
    intro ⟨x, hnpx⟩
    intros hfxpx
    let hpx := hfxpx x
    exact hnpx hpx

theorem dm4 : (¬∃x, p x) ↔ (∀x, ¬p x) := by
  apply Iff.intro
  case mp =>
    intros u x v
    apply u
    exact Exists.intro x v
  case mpr =>
    intros u v
    apply @mp (∃x, p x) False
    case f =>
      intro ⟨x, hpx⟩
      let hnpx := u x
      exact hnpx hpx
    case x =>
      exact v

end
