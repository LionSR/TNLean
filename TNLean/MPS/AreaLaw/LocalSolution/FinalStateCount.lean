/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# How many low-energy orthonormal states a gapped Hamiltonian admits

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 722–730), ends the hierarchical construction
with the claim that, once every final state `α^h` lies within energy `ΔE/2` of the ground state,
"it can then be shown that the number of distinct `α^h` is at most `2n`, where `n` is the number
of ground states". The source gives no argument. This file proves the statement for any family
of orthonormal states.

Let `P` be the orthogonal projection onto the ground states, of trace `n`, and suppose that the
Hamiltonian `H` has gap `ΔE` above the ground energy `E₀` in the sense
`H − E₀ ≥ ΔE (1 − P)`. A unit vector `φ` of energy at most `E₀ + θ ΔE` then satisfies
`ΔE (1 − ⟨φ, P φ⟩) ≤ ⟨φ, (H − E₀) φ⟩ ≤ θ ΔE`, so `⟨φ, P φ⟩ ≥ 1 − θ`. For orthonormal `φ_k`,
`∑_k ⟨φ_k, P φ_k⟩ = ∑_k ‖P φ_k‖² ≤ tr P` by Bessel's inequality, so there are at most
`n / (1 − θ)` of them; for `θ = 1/2` this is `2n`.

The hypothesis is the energy under `H`. In the source the `α^h` are eigenvectors of the last
compressed pair operator, and their energy under `H` comes from the final energy estimate
(eq. `hchy`) together with the comparison between `∑_i M_i` and `H`. Documented in
`docs/paper-gaps/hastings05_final_state_count.tex`.

## Main results

* `re_inner_toEuclideanCLM_eq_norm_sq`: `⟨v, P v⟩ = ‖P v‖²` for an orthogonal projection `P`.
* `sum_norm_sq_le_re_trace`: `∑_k ‖P φ_k‖² ≤ tr P` for an orthonormal family `φ`.
* `one_sub_mul_card_le_re_trace`: `(1 − θ) K ≤ tr P` for `K` orthonormal states of energy at
  most `E₀ + θ ΔE`.
* `card_le_two_mul_re_trace`: at most `2 tr P` orthonormal states of energy at most
  `E₀ + ΔE/2`.
-/

open Matrix
open scoped InnerProductSpace

namespace TNLean.MPS.AreaLaw.LocalSolution

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "T" => toEuclideanCLM (𝕜 := ℂ)

/-- For an orthogonal projection `P`, `⟨v, P v⟩` is real and equal to `‖P v‖²`. -/
theorem inner_toEuclideanCLM_eq_inner_self {P : Matrix ι ι ℂ} (hP : IsStarProjection P)
    (v : EuclideanSpace ℂ ι) : ⟪v, T P v⟫_ℂ = ⟪T P v, T P v⟫_ℂ := by
  have h := hP.map (toEuclideanCLM (n := ι) (𝕜 := ℂ))
  calc ⟪v, T P v⟫_ℂ = ⟪v, (T P * T P) v⟫_ℂ := by rw [h.isIdempotentElem.eq]
    _ = ⟪ContinuousLinearMap.adjoint (T P) v, T P v⟫_ℂ := by
        rw [ContinuousLinearMap.adjoint_inner_left]; rfl
    _ = ⟪T P v, T P v⟫_ℂ := by
        rw [← ContinuousLinearMap.star_eq_adjoint, h.isSelfAdjoint.star_eq]

/-- For an orthogonal projection `P`, `re ⟨v, P v⟩ = ‖P v‖²`. -/
theorem re_inner_toEuclideanCLM_eq_norm_sq {P : Matrix ι ι ℂ} (hP : IsStarProjection P)
    (v : EuclideanSpace ℂ ι) : (⟪v, T P v⟫_ℂ).re = ‖T P v‖ ^ 2 := by
  rw [inner_toEuclideanCLM_eq_inner_self hP, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- **Bessel's inequality against a projection.** For an orthogonal projection `P` and an
orthonormal family `φ`, `∑_{k ∈ s} ‖P φ_k‖² ≤ re tr P`. -/
theorem sum_norm_sq_le_re_trace {P : Matrix ι ι ℂ} (hP : IsStarProjection P) {κ : Type*}
    {φ : κ → EuclideanSpace ℂ ι} (hφ : Orthonormal ℂ φ) (s : Finset κ) :
    ∑ k ∈ s, ‖T P (φ k)‖ ^ 2 ≤ (trace P).re := by
  have h := hP.map (toEuclideanCLM (n := ι) (𝕜 := ℂ))
  set e : ι → EuclideanSpace ℂ ι := fun j ↦ EuclideanSpace.single j 1
  -- The `j`-th coordinate of `P φ_k` is `⟨P e_j, φ_k⟩`.
  have hcoord : ∀ k j, ‖(T P (φ k)) j‖ = ‖⟪φ k, T P (e j)⟫_ℂ‖ := fun k j ↦ by
    have : (T P (φ k)) j = ⟪e j, T P (φ k)⟫_ℂ := by
      simp [e, EuclideanSpace.inner_single_left]
    rw [this, norm_inner_symm, ← ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.star_eq_adjoint, h.isSelfAdjoint.star_eq, norm_inner_symm]
  have hdiag : ∀ j, ‖T P (e j)‖ ^ 2 = (P j j).re := fun j ↦ by
    rw [← re_inner_toEuclideanCLM_eq_norm_sq hP, EuclideanSpace.inner_single_left,
      ofLp_toEuclideanCLM]
    simp [e, Matrix.mulVec_single]
  calc ∑ k ∈ s, ‖T P (φ k)‖ ^ 2
      = ∑ k ∈ s, ∑ j, ‖⟪φ k, T P (e j)⟫_ℂ‖ ^ 2 := by
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [EuclideanSpace.norm_sq_eq]
        exact Finset.sum_congr rfl fun j _ ↦ by rw [hcoord]
    _ = ∑ j, ∑ k ∈ s, ‖⟪φ k, T P (e j)⟫_ℂ‖ ^ 2 := Finset.sum_comm
    _ ≤ ∑ j, ‖T P (e j)‖ ^ 2 :=
        Finset.sum_le_sum fun j _ ↦ Orthonormal.sum_inner_products_le _ hφ
    _ = (trace P).re := by
        simp only [hdiag, trace, diag_apply, Complex.re_sum]

/-- **Low-energy orthonormal states and the ground projection.** Let `P` be an orthogonal
projection and `H` a matrix with `H − E₀ ≥ ΔE (1 − P)` for some `ΔE > 0`, in the form
`ΔE (‖v‖² − re⟨v, P v⟩) ≤ re⟨v, H v⟩ − E₀ ‖v‖²` for every `v`. If `φ` is an orthonormal family
whose members `φ_k`, `k ∈ s`, have energy `re⟨φ_k, H φ_k⟩ ≤ E₀ + θ ΔE`, then
`(1 − θ) · #s ≤ re tr P`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 722–730,
for the energy under `H`; documented in `docs/paper-gaps/hastings05_final_state_count.tex`. -/
theorem one_sub_mul_card_le_re_trace {H P : Matrix ι ι ℂ} (hP : IsStarProjection P)
    {E₀ ΔE θ : ℝ} (hΔ : 0 < ΔE)
    (hgap : ∀ v : EuclideanSpace ℂ ι,
      ΔE * (‖v‖ ^ 2 - (⟪v, T P v⟫_ℂ).re) ≤ (⟪v, T H v⟫_ℂ).re - E₀ * ‖v‖ ^ 2)
    {κ : Type*} {φ : κ → EuclideanSpace ℂ ι} (hφ : Orthonormal ℂ φ) (s : Finset κ)
    (hE : ∀ k ∈ s, (⟪φ k, T H (φ k)⟫_ℂ).re ≤ E₀ + θ * ΔE) :
    (1 - θ) * s.card ≤ (trace P).re := by
  have hk : ∀ k ∈ s, 1 - θ ≤ ‖T P (φ k)‖ ^ 2 := fun k hks ↦ by
    have h1 := hgap (φ k)
    rw [hφ.1 k, re_inner_toEuclideanCLM_eq_norm_sq hP] at h1
    have h2 := hE k hks
    have : ΔE * (1 - θ) ≤ ΔE * ‖T P (φ k)‖ ^ 2 := by nlinarith
    exact le_of_mul_le_mul_left this hΔ
  calc (1 - θ) * s.card = ∑ _k ∈ s, (1 - θ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ k ∈ s, ‖T P (φ k)‖ ^ 2 := Finset.sum_le_sum hk
    _ ≤ (trace P).re := sum_norm_sq_le_re_trace hP hφ s

/-- **At most `2n` final states.** Under the gap hypothesis of `one_sub_mul_card_le_re_trace`,
an orthonormal family of states of energy at most `E₀ + ΔE/2` has at most `2 re tr P`
members, twice the number of ground states. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 722–730. -/
theorem card_le_two_mul_re_trace {H P : Matrix ι ι ℂ} (hP : IsStarProjection P)
    {E₀ ΔE : ℝ} (hΔ : 0 < ΔE)
    (hgap : ∀ v : EuclideanSpace ℂ ι,
      ΔE * (‖v‖ ^ 2 - (⟪v, T P v⟫_ℂ).re) ≤ (⟪v, T H v⟫_ℂ).re - E₀ * ‖v‖ ^ 2)
    {κ : Type*} {φ : κ → EuclideanSpace ℂ ι} (hφ : Orthonormal ℂ φ) (s : Finset κ)
    (hE : ∀ k ∈ s, (⟪φ k, T H (φ k)⟫_ℂ).re ≤ E₀ + ΔE / 2) :
    (s.card : ℝ) ≤ 2 * (trace P).re := by
  have := one_sub_mul_card_le_re_trace hP hΔ hgap hφ s (θ := 1 / 2)
    fun k hk ↦ by linarith [hE k hk]
  linarith

end TNLean.MPS.AreaLaw.LocalSolution
