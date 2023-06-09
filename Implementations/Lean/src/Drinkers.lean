import Utilities

variable (person : Type)
variable [person_is_inhabited : Inhabited person]
variable (drinks : person -> Prop)

---------------

theorem drinkers: (∃ p, drinks p → (∀ p, drinks p)) := by
  apply Classical.stab
  intro u
  apply u
  apply Exists.intro person_is_inhabited.default
  intro _
  intro b
  apply Classical.stab
  intro hndb
  apply u
  apply Exists.intro b
  intro hdb
  apply False.elim
  exact hndb hdb

theorem drinkers_weak: (∀ x, ¬¬drinks x -> drinks x) -> (∃ꜝ x, drinks x -> ∀ x, drinks x) := by
  intro stab
  intro v
  let h1 := v
  specialize h1 person_is_inhabited.default
  apply h1
  intro _
  intro b
  apply stab
  intro bnd
  let h2 := v
  specialize h2 b
  apply h2
  intro bd
  intro _
  apply stab
  intro _
  apply bnd
  exact bd
