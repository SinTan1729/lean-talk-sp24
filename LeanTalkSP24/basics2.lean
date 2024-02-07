import Mathlib.Tactic

open Finset

theorem sum_first_n {n : ℕ} : 2 * (range (n + 1)).sum id = n * (n + 1) := by
  induction' n with d hd
  · simp
  · rw [sum_range_succ, mul_add, hd, id.def, Nat.succ_eq_add_one]
    linarith

open Set

example {α : Type _} {s t : Set α} : s ∪ s ∩ t = s := by
  ext x; constructor
  rintro (xs | xsti)
  · trivial
  · exact And.left xsti
  exact Or.inl

-- Examples of definitions
def IsEven (n : ℕ) : Bool := (n%2) = 0
def IsOdd (n : ℕ) : Bool := ¬IsEven n

#eval IsEven 9
#eval IsOdd 9
#eval IsEven 8
#eval IsOdd 8

example {n : ℕ} : IsOdd n ↔ ((n%2) = 1) := by
  constructor
  -- <;>
  · intro h
    unfold IsOdd IsEven at h
    simp at h
    trivial
  · intro h
    unfold IsOdd IsEven
    simp
    trivial

theorem nat_odd_or_even {n : ℕ} : (IsEven n)∨(IsOdd n):= by
  apply or_iff_not_imp_left.mpr
  intro h
  unfold IsOdd
  simp at *
  trivial
