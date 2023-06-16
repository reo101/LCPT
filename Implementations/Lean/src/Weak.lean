import Utilities

variable (A B : Prop)
variable (α : Type)
variable (α_is_inhabited : Inhabited α)
variable (p : α -> Prop)

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
    apply Classical.stab
    intro hnab
    apply h
    case _ =>
      intro hna
      apply hnab
      apply Or.inl
      exact hna
    case _ =>
      intro hnb
      apply hnab
      apply Or.inr
      exact hnb
  case mpr =>
    intro haob hna hnb
    cases haob with
    | inl ha =>
      contradiction
    | inr hna =>
      contradiction

theorem fakeExists: ∃ꜝ x, p x ↔ ∃ x, p x := by
  apply Iff.intro
  case mp =>
    intro hnfxnpx
    apply Classical.stab
    intro hnexpx
    apply hnexpx
    apply Exists.intro α_is_inhabited.default
    apply Classical.stab
    intro _
    apply hnfxnpx
    intro x
    intro px
    apply hnexpx
    exact ⟨x, px⟩
  case mpr =>
    intro ⟨x, hpx⟩
    intro hfxnpx
    let hnpx := hfxnpx x
    contradiction

theorem t4_9_1: (A -> B) ∨ꜝ (A -> C) -> A -> B ∨ꜝ C := by
  intro h ha hnb hnc
  apply h
  case _ =>
    intro hab
    apply hnb
    apply hab
    exact ha
  case _ =>
    intro hac
    apply hnc
    apply hac
    exact ha

theorem t4_9_2: (A ∨ B -> C) -> (A -> C) ∧ (B -> C) := by
  intro habic
  apply And.intro
  case left =>
    intro ha
    apply habic
    apply Or.inl
    exact ha
  case right =>
    intro hb
    apply habic
    apply Or.inr
    exact hb

theorem t4_9_3: (A -> ∃ꜝ x, p x) -> ∃ꜝ x, (A -> p x) := by
  intro hainfxnpx
  intro hfxnaipx
  let hnaipd := hfxnaipx α_is_inhabited.default
  apply hnaipd
  intro ha
  let hnfxnpx := hainfxnpx ha
  apply False.elim
  apply hnfxnpx
  intro x
  intro hpx
  let naipx := hfxnaipx x
  apply naipx
  intro _
  exact hpx

theorem t4_9_4: (∃ x, (p x -> B)) -> (∀ x, p x) -> B := by
  intro ⟨x, hpxib⟩
  intro hfxpx
  let hpx := hfxpx x
  apply hpxib
  exact hpx
