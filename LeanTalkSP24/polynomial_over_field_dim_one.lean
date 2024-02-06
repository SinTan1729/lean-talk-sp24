import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Order.Height
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic

namespace Ideal

namespace Ideal
open LocalRing

variable {R : Type _} [CommRing R] (I : PrimeSpectrum R)

/-- Definitions -/
noncomputable def height : ℕ∞ := Set.chainHeight {J : PrimeSpectrum R | J < I}
noncomputable def krullDim (R : Type _) [CommRing R] : WithBot ℕ∞ := ⨆ (I : PrimeSpectrum R), height I
noncomputable def codimension (J : Ideal R) : WithBot ℕ∞ := ⨅ I ∈ {I : PrimeSpectrum R | J ≤ I.asIdeal}, height I

lemma height_def : height I = Set.chainHeight {J : PrimeSpectrum R | J < I} := rfl
lemma krullDim_def (R : Type _) [CommRing R] : krullDim R = (⨆ (I : PrimeSpectrum R), height I : WithBot ℕ∞) := rfl
lemma krullDim_def' (R : Type _) [CommRing R] : krullDim R = iSup (λ I : PrimeSpectrum R => (height I : WithBot ℕ∞)) := rfl

/-- A lattice structure on WithBot ℕ∞. -/
noncomputable instance : CompleteLattice (WithBot (ℕ∞)) := WithBot.WithTop.completeLattice

/-- Singleton sets have chainHeight 1 -/
lemma singleton_chainHeight_one {α : Type _} {x : α} [Preorder α] : Set.chainHeight {x} = 1 := by
  have le : Set.chainHeight {x} ≤ 1 := by
    unfold Set.chainHeight
    simp only [iSup_le_iff, Nat.cast_le_one]
    intro L h
    unfold Set.subchain at h
    simp only [Set.mem_singleton_iff, Set.mem_setOf_eq] at h
    rcases L with (_ | ⟨a,L⟩)
    . simp only [List.length_nil, zero_le]
    rcases L with (_ | ⟨b,L⟩)
    . simp only [List.length_singleton, le_refl]
    simp only [List.chain'_cons, List.find?, List.mem_cons, forall_eq_or_imp] at h
    rcases h with ⟨⟨h1, _⟩,  ⟨rfl, rfl, _⟩⟩
    exact absurd h1 (lt_irrefl _)
  suffices : Set.chainHeight {x} > 0
  · change _ < _ at this
    rw [←ENat.one_le_iff_pos] at this
    apply le_antisymm <;> trivial
  by_contra x
  simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero, Set.chainHeight_eq_zero_iff, Set.singleton_ne_empty] at x

/-- In a domain, the height of a prime ideal is Bot (0 in this case) iff it's the Bot ideal. -/
@[simp]
lemma height_zero_iff_bot {D: Type _} [CommRing D] [IsDomain D] {P : PrimeSpectrum D} : height P = 0 ↔ P = ⊥ := by
  constructor
  · intro h
    unfold height at h
    simp only [Set.chainHeight_eq_zero_iff] at h
    apply eq_bot_of_minimal
    intro I
    by_contra x
    have : I ∈ {J | J < P} := x
    rw [h] at this
    contradiction
  · intro h
    unfold height
    simp only [bot_eq_zero', Set.chainHeight_eq_zero_iff]
    by_contra spec
    change _ ≠ _ at spec
    rw [← Set.nonempty_iff_ne_empty] at spec
    obtain ⟨J, JlP : J < P⟩ := spec
    have JneP : J ≠ P := ne_of_lt JlP
    rw [h, ←bot_lt_iff_ne_bot, ←h] at JneP
    have := not_lt_of_lt JneP
    contradiction

/-- The ring of polynomials over a field has dimension one. -/
-- It's the exact same lemma as in krull.lean, added ' to avoid conflict
lemma polynomial_over_field_dim_one {K : Type} [Nontrivial K] [Field K] : krullDim (Polynomial K) = 1 := by
  rw [le_antisymm_iff]
  let X := @Polynomial.X K _
  constructor
  · unfold krullDim
    apply @iSup_le (WithBot ℕ∞) _ _ _ _
    intro I
    have PIR : IsPrincipalIdealRing (Polynomial K) := by infer_instance
    by_cases h: I = ⊥
    · rw [← height_zero_iff_bot] at h
      simp only [WithBot.coe_le_one, ge_iff_le]
      rw [h]
      exact bot_le
    · push_neg at h
      have : I.asIdeal ≠ ⊥ := by
        by_contra a
        have : I = ⊥ := PrimeSpectrum.ext I ⊥ a
        contradiction
      have maxI := IsPrime.to_maximal_ideal this
      have sngletn : ∀P, P ∈ {J | J < I} ↔ P = ⊥ := by
          intro P
          constructor
          · intro H
            simp only [Set.mem_setOf_eq] at H
            by_contra x
            push_neg at x
            have : P.asIdeal ≠ ⊥ := by
              by_contra a
              have : P = ⊥ := PrimeSpectrum.ext P ⊥ a
              contradiction
            have maxP := IsPrime.to_maximal_ideal this
            have IneTop := IsMaximal.ne_top maxI
            have : P ≤ I := le_of_lt H
            rw [←PrimeSpectrum.asIdeal_le_asIdeal] at this
            have : P.asIdeal = I.asIdeal := Ideal.IsMaximal.eq_of_le maxP IneTop this
            have : P = I := PrimeSpectrum.ext P I this
            replace H : P ≠ I := ne_of_lt H
            contradiction
          · intro pBot
            simp only [Set.mem_setOf_eq, pBot]
            exact lt_of_le_of_ne bot_le h.symm
      replace sngletn : {J | J < I} = {⊥} := Set.ext sngletn
      unfold height
      rw [sngletn]
      simp only [WithBot.coe_le_one, ge_iff_le]
      exact le_of_eq singleton_chainHeight_one
  · suffices : ∃I : PrimeSpectrum (Polynomial K), 1 ≤ (height I : WithBot ℕ∞)
    · obtain ⟨I, h⟩ := this
      have :  (height I : WithBot ℕ∞) ≤ ⨆ (I : PrimeSpectrum (Polynomial K)), ↑(height I) := by
        apply @le_iSup (WithBot ℕ∞) _ _ _ I
      exact le_trans h this
    have primeX : Prime Polynomial.X := @Polynomial.prime_X K _ _
    have : IsPrime (span {X}) := by
      refine (span_singleton_prime ?hp).mpr primeX
      exact Polynomial.X_ne_zero
    let P := PrimeSpectrum.mk (span {X}) this
    unfold height
    use P
    have : ⊥ ∈ {J | J < P} := by
      simp only [Set.mem_setOf_eq, bot_lt_iff_ne_bot]
      suffices : P.asIdeal ≠ ⊥
      · by_contra x
        rw [PrimeSpectrum.ext_iff] at x
        contradiction
      by_contra x
      simp only [span_singleton_eq_bot] at x
      have := @Polynomial.X_ne_zero K _ _
      contradiction
    have : {J | J < P}.Nonempty := Set.nonempty_of_mem this
    rwa [←Set.one_le_chainHeight_iff, ←WithBot.one_le_coe] at this
