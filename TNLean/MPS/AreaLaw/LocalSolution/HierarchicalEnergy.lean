/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.HierarchicalProjection

/-!
# The energy of the final state of Hastings' hierarchical construction

At the end of the hierarchical construction of Section II, Hastings, *Solving gapped
Hamiltonians locally* (arXiv:cond-mat/0508554v3, `References/cond-mat_0508554/proj3new.tex`,
lines 705–720), states that once the deficiency `b_h` of the last level is small, "there is at
least one state `α^h`, and one may show" eq. `hchy`:
`⟨α^h, ∑_i M_i α^h⟩ ≤ ⟨Ψ_a, ∑_i M_i Ψ_a⟩ + N J O(exp[−l_proj/(log₂(N) l_fac)])`.
The source gives no argument. This file proves the step from the deficiency of the final
projection to the energy.

Let `Q` be the projection onto the states kept at the last level and suppose that the ground
state `Ψ` is moved by `Q` by at most `b < 1` in norm, the form in which
`HierarchicalProjection.lean` measures the deficiency of a level. Then `Q Ψ ≠ 0`, the
normalized image `φ = Q Ψ / ‖Q Ψ‖` lies in the range of `Q` and within `2 b` of `Ψ`, and for
every operator `M`, `|⟨φ, M φ⟩ − ⟨Ψ, M Ψ⟩| ≤ 2 ‖M‖ ‖φ − Ψ‖ ≤ 4 ‖M‖ b`. For `M = ∑_{i<N} M_i`
with `‖M_i‖ ≤ J` this is `⟨φ, M φ⟩ ≤ ⟨Ψ, M Ψ⟩ + 4 N J b`, eq. `hchy` with the explicit
constant `4 N J b` in place of `N J O(·)`.

**Scope restriction (the final state):** the state produced is the normalized image of `Ψ_a`,
a unit vector in the span of the final states `α^h`, rather than one of the `α^h` themselves.
The `α^h` are eigenvectors of the last pair operator, not of `∑_i M_i`, so the source's
assertion for a single `α^h` is not derived here. The deficiency `b` of the last level is a
hypothesis; bounding it through all `h` levels is the bookkeeping of the hierarchy.
Documented in `docs/paper-gaps/hastings05_hierarchical_energy.tex`.

## Main results

* `TNLean.MPS.AreaLaw.LocalSolution.abs_re_inner_sub_re_inner_le`:
  `|⟨φ, M φ⟩ − ⟨ψ, M ψ⟩| ≤ 2 ‖M‖ ‖φ − ψ‖` for unit vectors.
* `TNLean.MPS.AreaLaw.LocalSolution.norm_inv_norm_smul_toEuclideanLin_sub_le_two_mul`: the
  normalized image under one projection is within `2 b` of the vector.
* `TNLean.MPS.AreaLaw.LocalSolution.exists_mem_range_re_inner_le_add`: a unit vector in the
  range of `Q` with energy at most `⟨Ψ, M Ψ⟩ + 4 ‖M‖ b`.
* `TNLean.MPS.AreaLaw.LocalSolution.exists_mem_range_re_inner_sum_le_add`: eq. `hchy`, with
  `4 N J b` for `N` terms of norm at most `J`.
-/

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace

namespace TNLean.MPS.AreaLaw.LocalSolution

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Energies of nearby unit vectors.** For unit vectors `φ`, `ψ` and every operator `M`,
`|re⟨φ, M φ⟩ − re⟨ψ, M ψ⟩| ≤ 2 ‖M‖ ‖φ − ψ‖`. -/
theorem abs_re_inner_sub_re_inner_le (M : Matrix ι ι ℂ) {φ ψ : EuclideanSpace ℂ ι}
    (hφ : ‖φ‖ = 1) (hψ : ‖ψ‖ = 1) :
    |(⟪φ, toEuclideanLin M φ⟫_ℂ).re - (⟪ψ, toEuclideanLin M ψ⟫_ℂ).re| ≤
      2 * ‖M‖ * ‖φ - ψ‖ := by
  have e : ⟪φ, toEuclideanLin M φ⟫_ℂ - ⟪ψ, toEuclideanLin M ψ⟫_ℂ =
      ⟪φ - ψ, toEuclideanLin M φ⟫_ℂ + ⟪ψ, toEuclideanLin M (φ - ψ)⟫_ℂ := by
    rw [inner_sub_left, map_sub, inner_sub_right]; ring
  have h1 : ‖⟪φ - ψ, toEuclideanLin M φ⟫_ℂ‖ ≤ ‖M‖ * ‖φ - ψ‖ := by
    refine (norm_inner_le_norm _ _).trans ?_
    have := Entropy.norm_toEuclideanLin_le M φ
    rw [hφ, mul_one] at this
    nlinarith [norm_nonneg (φ - ψ)]
  have h2 : ‖⟪ψ, toEuclideanLin M (φ - ψ)⟫_ℂ‖ ≤ ‖M‖ * ‖φ - ψ‖ := by
    refine (norm_inner_le_norm _ _).trans ?_
    rw [hψ, one_mul]
    exact Entropy.norm_toEuclideanLin_le M _
  rw [← Complex.sub_re, e]
  calc |(⟪φ - ψ, toEuclideanLin M φ⟫_ℂ + ⟪ψ, toEuclideanLin M (φ - ψ)⟫_ℂ).re|
      ≤ ‖⟪φ - ψ, toEuclideanLin M φ⟫_ℂ + ⟪ψ, toEuclideanLin M (φ - ψ)⟫_ℂ‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ‖⟪φ - ψ, toEuclideanLin M φ⟫_ℂ‖ + ‖⟪ψ, toEuclideanLin M (φ - ψ)⟫_ℂ‖ := norm_add_le _ _
    _ ≤ 2 * ‖M‖ * ‖φ - ψ‖ := by linarith

/-- **Normalizing the image under one projection.** If the orthogonal projection `Q` moves the
unit vector `ψ` by at most `b`, the normalized image `Q ψ / ‖Q ψ‖` is within `2 b` of `ψ`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 686–689, for one projection. -/
theorem norm_inv_norm_smul_toEuclideanLin_sub_le_two_mul {Q : Matrix ι ι ℂ}
    {ψ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) {b : ℝ} (h : ‖ψ - toEuclideanLin Q ψ‖ ≤ b) :
    ‖((‖toEuclideanLin Q ψ‖⁻¹ : ℝ) : ℂ) • toEuclideanLin Q ψ - ψ‖ ≤ 2 * b := by
  refine (norm_inv_norm_smul_sub_le hψ).trans ?_
  rw [norm_sub_rev]
  linarith

/-- **A state of the final level with nearly the ground-state energy.** Let `Q` be an orthogonal
projection that moves the unit vector `Ψ` by at most `b < 1`. Then some unit vector `φ` with
`Q φ = φ` satisfies `re⟨φ, M φ⟩ ≤ re⟨Ψ, M Ψ⟩ + 4 ‖M‖ b` for every operator `M`; it is the
normalized image `Q Ψ / ‖Q Ψ‖`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 709–720, eq. `hchy`, with the restriction of the module docstring. -/
theorem exists_mem_range_re_inner_le_add {Q : Matrix ι ι ℂ} (hQ : IsStarProjection Q)
    {Ψ : EuclideanSpace ℂ ι} (hΨ : ‖Ψ‖ = 1) {b : ℝ} (h : ‖Ψ - toEuclideanLin Q Ψ‖ ≤ b)
    (hb : b < 1) :
    ∃ φ : EuclideanSpace ℂ ι, ‖φ‖ = 1 ∧ toEuclideanLin Q φ = φ ∧ ‖φ - Ψ‖ ≤ 2 * b ∧
      ∀ M : Matrix ι ι ℂ,
        (⟪φ, toEuclideanLin M φ⟫_ℂ).re ≤ (⟪Ψ, toEuclideanLin M Ψ⟫_ℂ).re + 4 * ‖M‖ * b := by
  set v := toEuclideanLin Q Ψ with hv
  have hv0 : 0 < ‖v‖ := by
    have := norm_sub_norm_le Ψ (Ψ - v)
    rw [sub_sub_cancel, hΨ] at this
    linarith
  set φ : EuclideanSpace ℂ ι := ((‖v‖⁻¹ : ℝ) : ℂ) • v with hφdef
  have hφ : ‖φ‖ = 1 := by
    rw [hφdef, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ hv0.ne']
  have hQφ : toEuclideanLin Q φ = φ := by
    have hQQ : toEuclideanLin Q (toEuclideanLin Q Ψ) = toEuclideanLin Q Ψ := by
      rw [← toEuclideanLin_mul_apply, hQ.isIdempotentElem.eq]
    rw [hφdef, map_smul, hv, hQQ]
  have hd : ‖φ - Ψ‖ ≤ 2 * b := norm_inv_norm_smul_toEuclideanLin_sub_le_two_mul hΨ h
  refine ⟨φ, hφ, hQφ, hd, fun M ↦ ?_⟩
  have hE := abs_re_inner_sub_re_inner_le M hφ hΨ
  have hM := norm_nonneg M
  have : 2 * ‖M‖ * ‖φ - Ψ‖ ≤ 4 * ‖M‖ * b := by nlinarith
  linarith [le_abs_self ((⟪φ, toEuclideanLin M φ⟫_ℂ).re - (⟪Ψ, toEuclideanLin M Ψ⟫_ℂ).re)]

/-- **Eq. `hchy`.** Let `Q` be an orthogonal projection that moves the unit vector `Ψ` by at most
`b < 1`, and let `M = ∑_{i<N} M_i` with `‖M_i‖ ≤ J`. Then some unit vector `φ` with `Q φ = φ`
has `re⟨φ, M φ⟩ ≤ re⟨Ψ, M Ψ⟩ + 4 N J b`. With `Q` the projection onto the final states and
`b = b_h`, this is eq. `hchy` of Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 709–720, with the explicit constant `4 N J b_h` and the restriction of the module
docstring. -/
theorem exists_mem_range_re_inner_sum_le_add {Q : Matrix ι ι ℂ} (hQ : IsStarProjection Q)
    {Ψ : EuclideanSpace ℂ ι} (hΨ : ‖Ψ‖ = 1) {b : ℝ} (h : ‖Ψ - toEuclideanLin Q Ψ‖ ≤ b)
    (hb : b < 1) {N : ℕ} (Mi : Fin N → Matrix ι ι ℂ) {J : ℝ} (hJ : ∀ i, ‖Mi i‖ ≤ J) :
    ∃ φ : EuclideanSpace ℂ ι, ‖φ‖ = 1 ∧ toEuclideanLin Q φ = φ ∧
      (⟪φ, toEuclideanLin (∑ i, Mi i) φ⟫_ℂ).re ≤
        (⟪Ψ, toEuclideanLin (∑ i, Mi i) Ψ⟫_ℂ).re + 4 * N * J * b := by
  obtain ⟨φ, hφ, hQφ, -, hE⟩ := exists_mem_range_re_inner_le_add hQ hΨ h hb
  refine ⟨φ, hφ, hQφ, (hE _).trans ?_⟩
  have hb0 : 0 ≤ b := (norm_nonneg _).trans h
  have hsum : ‖∑ i, Mi i‖ ≤ N * J := by
    refine (norm_sum_le _ _).trans ?_
    simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hJ i
  have : 4 * ‖∑ i, Mi i‖ * b ≤ 4 * (N * J) * b := by
    have := mul_le_mul_of_nonneg_right hsum hb0
    nlinarith
  linarith

end TNLean.MPS.AreaLaw.LocalSolution
