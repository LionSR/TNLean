/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Abstract martingale criterion (quadratic form → norm bound)

**Root-only.** This file isolates the operator-theoretic step of the
martingale-method spectral-gap framework: the quadratic-form inequality
`H² ≥ γ H` for a positive operator `H` implies the norm lower bound
`γ ‖v‖ ≤ ‖H v‖` on the orthogonal complement of `ker H`.

This step is purely operator-theoretic and has no MPS content in its
signature, so it lives in its own `FrustrationFree` namespace. The
MPS-specific theorem `MPSTensor.parentHamiltonian_gapped` (in
`Martingale.Gap`) instantiates it for the parent Hamiltonian.
-/

open scoped BigOperators InnerProductSpace

namespace FrustrationFree

/--
**Abstract martingale criterion (quadratic form ⟹ norm bound).**

Let `H` be a positive linear operator (in the sense of `LinearMap.IsPositive`:
symmetric with `0 ≤ re ⟪H v, v⟫`) on a finite-dimensional complex Hilbert
space satisfying the quadratic-form inequality

    `γ ⟨v, H v⟩ ≤ ⟨H v, H v⟩` for all `v`,

i.e.\ `H² ≥ γ H` as a quadratic form. Then on the orthogonal complement
of `ker H`, `H` is bounded below in norm by `γ`:

    `γ ‖v‖ ≤ ‖H v‖` for all `v ⊥ ker H`.

The positivity hypothesis is essential: it rules out negative eigenvalues of
small magnitude (such as `H = -Id`, which otherwise satisfies
`γ ⟨v, H v⟩ ≤ ⟨H v, H v⟩` vacuously but fails the conclusion). For the MPS
parent Hamiltonian this hypothesis is automatic because `H = ∑ᵢ hᵢ` is a
sum of orthogonal projectors.

This is the operator-theoretic content of the Kastoryano–Lucia /
Nachtergaele martingale method: once the MPS-specific projector
geometry (Friedrichs angle on overlapping local ground spaces plus
the row-sum bound) produces the operator inequality `H² ≥ γ H` for the
PSD operator `H`, the norm lower bound — and hence the spectral gap
for eigenvectors of `H` — follows by the spectral theorem. This lemma
provides the final spectral-theorem step; the remaining MPS-specific
quadratic-form hypothesis is stated separately in
`MPSTensor.parentHamiltonianES_gap_bound_of_friedrichs`. -/
theorem spectralGap_of_martingale {ι : Type*} [Fintype ι] {γ : ℝ} (hγ : 0 < γ)
    {H : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι} (hH : H.IsPositive)
    (hOpIneq : ∀ v, γ * (⟪H v, v⟫_ℂ).re ≤ (⟪H v, H v⟫_ℂ).re) :
    ∀ v ∈ (LinearMap.ker H)ᗮ, γ * ‖v‖ ≤ ‖H v‖ := by
  classical
  -- Spectral setup: diagonalise the positive symmetric operator.
  set n := Fintype.card ι with hn_def
  have hn : Module.finrank ℂ (EuclideanSpace ℂ ι) = n := by
    simp [hn_def]
  have hSym : H.IsSymmetric := hH.isSymmetric
  set b := hSym.eigenvectorBasis hn with hb_def
  set μ : Fin n → ℝ := hSym.eigenvalues hn with hμ_def
  have hμ_nn : ∀ i, 0 ≤ μ i := fun i => hH.nonneg_eigenvalues hn i
  have hHb : ∀ i, H (b i) = ((μ i : ℂ)) • b i := fun i =>
    hSym.apply_eigenvectorBasis hn i
  have hbb : ∀ i j : Fin n, ⟪b i, b j⟫_ℂ = if i = j then (1 : ℂ) else 0 :=
    orthonormal_iff_ite.mp b.orthonormal
  -- Apply the operator inequality to each eigenvector: `γ μᵢ ≤ μᵢ²`.
  have hμ_ineq : ∀ i, γ * μ i ≤ μ i * μ i := by
    intro i
    have key := hOpIneq (b i)
    rw [hHb i] at key
    have e1 : (⟪((μ i : ℂ)) • b i, b i⟫_ℂ).re = μ i := by
      rw [inner_smul_left, hbb i i, if_pos rfl, mul_one, Complex.conj_ofReal,
          Complex.ofReal_re]
    have e2 : (⟪((μ i : ℂ)) • b i, ((μ i : ℂ)) • b i⟫_ℂ).re = μ i * μ i := by
      rw [inner_smul_left, inner_smul_right, hbb i i, if_pos rfl, mul_one,
          Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [e1, e2] at key
    exact key
  -- Combined with `μᵢ ≥ 0`, this gives `μᵢ = 0 ∨ γ ≤ μᵢ` for each `i`.
  have hμ_alt : ∀ i, μ i = 0 ∨ γ ≤ μ i := by
    intro i
    rcases (hμ_nn i).lt_or_eq with hpos | hzero
    · right
      have := hμ_ineq i
      have hpos' : 0 < μ i := hpos
      nlinarith
    · left; exact hzero.symm
  -- Main argument on `v ∈ (ker H)ᗮ`.
  intro v hv
  -- Eigenvectors with zero eigenvalue lie in `ker H`, hence are orthogonal to `v`.
  have hker : ∀ i, μ i = 0 → b i ∈ LinearMap.ker H := by
    intro i hi
    rw [LinearMap.mem_ker, hHb i]
    simp [hi]
  have hv_perp : ∀ i, μ i = 0 → ⟪b i, v⟫_ℂ = 0 := fun i hi =>
    Submodule.inner_right_of_mem_orthogonal (hker i hi) hv
  -- Express `‖v‖²` and `‖Hv‖²` through the eigenvector basis.
  have hv_sq : ‖v‖ ^ 2 = ∑ i, ‖(b.repr v) i‖ ^ 2 := by
    have hiso := b.repr.norm_map v
    rw [← hiso, EuclideanSpace.norm_sq_eq]
  have hHv_sq : ‖H v‖ ^ 2 = ∑ i, (μ i) ^ 2 * ‖(b.repr v) i‖ ^ 2 := by
    have hiso := b.repr.norm_map (H v)
    rw [← hiso, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hSym.eigenvectorBasis_apply_self_apply hn v i, norm_mul, mul_pow,
        RCLike.norm_ofReal, sq_abs]
  -- The quadratic-form bound `γ² ‖v‖² ≤ ‖Hv‖²` is now term-by-term.
  have h_sq : γ ^ 2 * ‖v‖ ^ 2 ≤ ‖H v‖ ^ 2 := by
    rw [hv_sq, hHv_sq, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rcases hμ_alt i with hi | hi
    · have h0 : (b.repr v) i = 0 := by
        rw [b.repr_apply_apply]
        exact hv_perp i hi
      rw [h0, norm_zero]
      simp
    · have hγ_sq : γ ^ 2 ≤ (μ i) ^ 2 :=
        pow_le_pow_left₀ hγ.le hi 2
      have hnn : (0 : ℝ) ≤ ‖(b.repr v) i‖ ^ 2 := sq_nonneg _
      exact mul_le_mul_of_nonneg_right hγ_sq hnn
  -- Take square roots to conclude `γ ‖v‖ ≤ ‖Hv‖`.
  have h1 : (γ * ‖v‖) ^ 2 ≤ ‖H v‖ ^ 2 := by
    rw [mul_pow]; exact h_sq
  have h2 : 0 ≤ γ * ‖v‖ := mul_nonneg hγ.le (norm_nonneg v)
  have h3 : 0 ≤ ‖H v‖ := norm_nonneg _
  have hsqrt := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq h2, Real.sqrt_sq h3] at hsqrt

end FrustrationFree
