/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinKronecker
import QICLean.Entropy.SupportedMarginalTails

/-!
# Two-site operators as finite sums of product operators

An operator supported on two distinct sites is a sum of at most the fourth
power of the local dimension many products of single-site matrix units.
This reduces its matrix elements between matrix product states to the
weighted product-operator contractions used for local energies.
-/

open Matrix
open scoped BigOperators

namespace TNLean.MPS.AreaLaw

/-- Matrix units at two specified sites, with the identity at every other site. -/
def twoSiteMatrixUnitFactors {ι : Type*} [DecidableEq ι] {q : ℕ}
    (p r : ι) (a b c d : Fin q) : ι → Matrix (Fin q) (Fin q) ℂ :=
  fun j ↦ if j = p then Matrix.single a b 1 else
    if j = r then Matrix.single c d 1 else 1

/-- The product of two placed matrix units enforces their four local labels
and equality of the remaining physical coordinates. -/
theorem rectKronecker_twoSiteMatrixUnitFactors
    {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}
    {p r : ι} (hpr : p ≠ r) (a b c d : Fin q) (σ τ : ι → Fin q) :
    Matrix.rectKronecker (twoSiteMatrixUnitFactors p r a b c d) σ τ =
      if σ p = a ∧ τ p = b ∧ σ r = c ∧ τ r = d ∧
        (∀ j, j ≠ p → j ≠ r → σ j = τ j) then 1 else 0 := by
  classical
  rw [Matrix.rectKronecker_apply]
  split_ifs with h
  · apply Finset.prod_eq_one
    intro j _hj
    by_cases hjp : j = p
    · subst j
      simp [twoSiteMatrixUnitFactors, h.1, h.2.1]
    · by_cases hjr : j = r
      · subst j
        simp [twoSiteMatrixUnitFactors, Ne.symm hpr, h.2.2.1, h.2.2.2.1]
      · simp [twoSiteMatrixUnitFactors, hjp, hjr, Matrix.one_apply, h.2.2.2.2 j hjp hjr]
  · by_contra hprod
    have hentry := Finset.prod_ne_zero_iff.mp hprod
    have hp : σ p = a ∧ τ p = b := by
      simpa [twoSiteMatrixUnitFactors, Matrix.single_apply, eq_comm] using
        hentry p (Finset.mem_univ p)
    have hr : σ r = c ∧ τ r = d := by
      simpa [twoSiteMatrixUnitFactors, Matrix.single_apply, Ne.symm hpr, eq_comm] using
        hentry r (Finset.mem_univ r)
    have hout : ∀ j, j ≠ p → j ≠ r → σ j = τ j := by
      intro j hjp hjr
      simpa [twoSiteMatrixUnitFactors, hjp, hjr, Matrix.one_apply] using
        hentry j (Finset.mem_univ j)
    exact h ⟨hp.1, hp.2, hr.1, hr.2, hout⟩

/-- A reference configuration with the labels at two sites replaced. -/
def twoSiteConfig {ι : Type*} [DecidableEq ι] {q : ℕ}
    (σ₀ : ι → Fin q) (p r : ι) (a c : Fin q) : ι → Fin q :=
  Function.update (Function.update σ₀ p a) r c

/-- A supported matrix entry is read from any fixed reference configuration
with the same two local input and output labels. -/
theorem supported_apply_eq_twoSiteConfig
    {ι : Type*} [DecidableEq ι] {q : ℕ}
    {p r : ι} (hpr : p ≠ r) (σ₀ : ι → Fin q)
    {X : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hX : Entropy.IsSupportedOn X {p, r}) (σ τ : ι → Fin q)
    (hout : ∀ j, j ≠ p → j ≠ r → σ j = τ j) :
    X σ τ = X (twoSiteConfig σ₀ p r (σ p) (σ r))
      (twoSiteConfig σ₀ p r (τ p) (τ r)) := by
  apply hX.2
  · intro j hj
    rcases (show j = p ∨ j = r by simpa using hj) with rfl | rfl <;>
      simp [twoSiteConfig, hpr]
  · intro j hj
    rcases (show j = p ∨ j = r by simpa using hj) with rfl | rfl <;>
      simp [twoSiteConfig, hpr]
  · intro j hj
    have hne : j ≠ p ∧ j ≠ r := by simpa using hj
    exact hout j hne.1 hne.2
  · intro j hj
    have hne : j ≠ p ∧ j ≠ r := by simpa using hj
    simp [twoSiteConfig, hne.1, hne.2]

/-- Every operator supported on two distinct sites is a sum of `q^4` product
operators. Its coefficients are entries read at a fixed reference configuration. -/
theorem supported_eq_sum_twoSiteMatrixUnitFactors
    {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}
    {p r : ι} (hpr : p ≠ r) (σ₀ : ι → Fin q)
    {X : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hX : Entropy.IsSupportedOn X {p, r}) :
    X = ∑ a : Fin q, ∑ b : Fin q, ∑ c : Fin q, ∑ d : Fin q,
      X (twoSiteConfig σ₀ p r a c) (twoSiteConfig σ₀ p r b d) •
        Matrix.rectKronecker (twoSiteMatrixUnitFactors p r a b c d) := by
  classical
  ext σ τ
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    rectKronecker_twoSiteMatrixUnitFactors hpr]
  by_cases hout : ∀ j, j ≠ p → j ≠ r → σ j = τ j
  · rw [supported_apply_eq_twoSiteConfig hpr σ₀ hX σ τ hout]
    have hcontr : ∀ j, j ≠ p → j ≠ r → σ j ≠ τ j →
        X (twoSiteConfig σ₀ p r (σ p) (σ r))
          (twoSiteConfig σ₀ p r (τ p) (τ r)) = 0 := by
      intro j hjp hjr hne
      exact (hne (hout j hjp hjr)).elim
    simpa [ite_and, mul_ite] using hcontr
  · obtain ⟨j, hj⟩ := not_forall.mp hout
    obtain ⟨hjp, hj⟩ := not_imp.mp hj
    obtain ⟨hjr, hne⟩ := not_imp.mp hj
    have hzero : X σ τ = 0 := hX.1 σ τ ⟨j, by simp [hjp, hjr], hne⟩
    simp [hzero, hout]

end TNLean.MPS.AreaLaw
