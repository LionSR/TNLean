/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Arbitrary.Corollaries.WeightedSums

/-!
# Grouping into classes: the form of the classical theorems

Let `(R j)_{j ∈ J}` be admissible tensors, pairwise not related by a scalar and a gauge. A tensor
whose states are `∑_s μ_s ^ N V_N(R_{j(s)})`, for a finite index set with a class map `j` and
nonzero weights `μ`, is compared with a second datum `(j', μ')` of the same kind: the two sums
agree at every positive length exactly when there is a bijection `τ` of the index sets with
`j'(τ s) = j(s)` and `μ_s / μ'_{τ s}` a gauge scalar of `R_{j(s)}`. In words: the blocks agree class
by class with multiplicities, and the weights agree up to the gauge scalars of each class.

## Main definitions

* `MPSTensor.gaugeScalars`: the gauge scalars `Sc(A) = {c | c • A ≃ A}` of a tensor.

## Main results

* `MPSTensor.forall_sum_pow_mul_mpv_eq_iff_exists_equiv_eq_and_div_mem_gaugeScalars`.
-/

namespace MPSTensor

variable {d : ℕ}

/-- The **gauge scalars** of a tensor `A`: the complex numbers `c` with `c • A` gauge related to
`A` (written `Sc(R)`). -/
def gaugeScalars {D : ℕ} (A : MPSTensor d D) : Set ℂ :=
  {c | IsGaugeRelated (c • A) A}

/-- **Classes of factors for weighted sums.** For admissible representatives `R j`, pairwise not
related by a scalar and a gauge, two weighted sums `∑_s μ_s ^ N V_N(R_{cls s})` and `∑_t μ'_t ^ N
V_N(R_{cls' t})` with nonzero weights agree at every positive length exactly when a bijection `τ` of
the index types preserves the classes and sends each weight to one differing from it by a gauge
scalar of its class. -/
theorem forall_sum_pow_mul_mpv_eq_iff_exists_equiv_eq_and_div_mem_gaugeScalars {J : Type*}
    {DR : J → ℕ} {R : ∀ j, MPSTensor d (DR j)}
    (hirr : ∀ j, Matrix.IsIrreducibleAction (R j)) (hlet : ∀ j, ∃ i, R j i ≠ 0)
    (hsep : ∀ j j', j ≠ j' → ∀ c : ℂ, ¬ IsGaugeRelated (c • R j) (R j'))
    {I K : Type*} [Fintype I] [Fintype K] (cls : I → J) (cls' : K → J) {μ : I → ℂ}
    {μ' : K → ℂ} (hμ : ∀ s, μ s ≠ 0) (hμ' : ∀ t, μ' t ≠ 0) :
    (∀ N, 0 < N → ∀ σ : Fin N → Fin d,
        ∑ s, μ s ^ N * mpv (R (cls s)) σ = ∑ t, μ' t ^ N * mpv (R (cls' t)) σ) ↔
      ∃ τ : I ≃ K, ∀ s, cls' (τ s) = cls s ∧ μ s / μ' (τ s) ∈ gaugeScalars (R (cls s)) := by
  have key : ∀ (a b : ℂ), b ≠ 0 → ∀ j j',
      IsGaugeRelated (a • R j) (b • R j') ↔ j' = j ∧ a / b ∈ gaugeScalars (R j) := by
    intro a b hb j j'
    constructor
    · intro h
      have h' : IsGaugeRelated ((a / b) • R j) (R j') := by
        have := h.smul b⁻¹
        rwa [smul_smul, smul_smul, inv_mul_cancel₀ hb, one_smul, inv_mul_eq_div] at this
      by_cases hj : j = j'
      · subst hj
        exact ⟨rfl, h'⟩
      · exact absurd h' (hsep j j' hj _)
    · rintro ⟨rfl, hc⟩
      have h := IsGaugeRelated.smul hc b
      have hab : b * (a / b) = a := by field_simp
      rwa [smul_smul, hab] at h
  exact (forall_sum_pow_mul_mpv_eq_iff_exists_equiv_isGaugeRelated (C := fun s => R (cls s))
    (C' := fun t => R (cls' t)) (fun s => hirr _) (fun s => hlet _) (fun t => hirr _)
    (fun t => hlet _) hμ hμ').trans
    (exists_congr fun τ => forall_congr' fun s => key _ _ (hμ' (τ s)) _ _)

end MPSTensor
