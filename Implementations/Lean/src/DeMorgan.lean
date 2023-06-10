import Utilities

section

variable (a b : Prop)
variable (α : Type)
variable (p : α → Prop)

theorem dm1 : ¬(a ∧ b) ↔ (¬a ∨ ¬b) := by
  apply Iff.intro
  case mp =>
    intro hnavb
    apply Classical.stab
    intro hnnavnb
    apply hnnavnb
    apply Or.inl
    intro ha
    apply hnnavnb
    apply Or.inr
    intro hb
    apply hnavb
    exact ⟨ha, hb⟩
  case mpr =>
    intros hnavnb hab
    apply Or.elim hnavnb
    case left =>
      intro hna
      apply hna
      exact hab.left
    case right =>
      intro hnb
      apply hnb
      exact hab.right

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
    match v with
     | Or.inl ha =>
       let hna := u.left
       exact hna ha
     | Or.inr hb =>
       let hnb := u.right
       exact hnb hb

theorem dm3 : (¬∀x, p x) ↔ (∃x, ¬p x) := by
  apply Iff.intro
  case mp =>
    intro hnfxpx
    apply Classical.stab
    intro hnexnpx
    apply hnfxpx
    intro x
    apply Classical.stab
    intro hnpx
    apply hnexnpx
    exact ⟨x, hnpx⟩
  case mpr =>
    intro ⟨x, hnpx⟩
    intro hfxpx
    let hpx := hfxpx x
    exact hnpx hpx

theorem dm4 : (¬∃x, p x) ↔ (∀x, ¬p x) := by
  apply Iff.intro
  case mp =>
    intros hexpx x hpx
    apply hexpx
    exact ⟨x, hpx⟩
  case mpr =>
    intro hfxnpx
    intro ⟨x, hpx⟩
    let hnpx := hfxnpx x
    exact hnpx hpx

theorem t4_7 : (¬¬a -> ¬¬b) -> ¬¬(a -> b) := by
  intro hnnainnb
  intro hnaib
  apply hnaib
  intro ha
  apply False.elim
  apply hnnainnb
  case _ =>
    intro hna
    exact hna ha
  case _ =>
    intro hb
    apply hnaib
    intro _
    exact hb

end
