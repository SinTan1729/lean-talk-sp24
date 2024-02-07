import Mathlib.Tactic

open Finset

theorem sum_first_n {n : ℕ} : 2 * (range (n + 1)).sum id = n * (n + 1) := by
  induction' n with d hd
  · simp
  · rw [sum_range_succ, mul_add, hd, id.def, Nat.succ_eq_add_one]
    linarith

open Set
variable {α : Type _}
variable {s t u : Set α}

example : s ∪ s ∩ t = s := by
  ext x; constructor
  rintro (xs | xsti)
  · trivial
  · exact And.left xsti
  exact Or.inl
