/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.FinalStateEnergy

/-!
# The closing link of Hastings' periodic chain

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 626–628), takes the chain of `N = 2^h`
supersites periodic, so `∑_i M_i` in eq. `hchy` (lines 709–720) contains the operator
`M_{N,1}` of the link closing the chain into a ring. The binary tree of `h` levels joins the two
halves of each block, which covers the `N - 1` links of the open chain but not `(N, 1)`.

One further window controls it. Inside the range of the final projection `P h 0`, keep the
eigenvectors of the compression of `W = M_{N,1}` with eigenvalue within `x_h` of
`⟨Ψ_a, W Ψ_a⟩`. This is the one-level step of the hierarchy with the second half replaced by
the identity, so its deficiency on `Ψ_a` is the next term `hierarchyDeficiency ε K x (h + 1)` of
the same recursion. Every unit vector `φ` it keeps is kept by `P h 0` and has
`|⟨φ, W φ⟩ - ⟨Ψ_a, W Ψ_a⟩| ≤ x_h`, so eq. `hchy` holds for the periodic sum
`hierarchySum M h 0 + W` with the error `∑_m 2^{h-1-m} x_m + x_h`, and the count of at most
`2n` final states follows from the gap of the periodic sum.

**Local fix (closing-link window):** the source states eq. `hchy` for `∑_i M_i` without
mentioning the link `(N, 1)`, which the windows of its `h` levels do not control. Here the final
states are those kept by one further window for that link, inside the space of the last level,
so eq. `hchy` and the count are proved for this corrected construction rather than for the
source's own states `α^h`. The kept states are combinations of the `α^h`, and no matrix product
form or bond dimension is claimed for them. Documented in
`docs/paper-gaps/hastings05_hierarchical_energy.tex`.

## Main results

* `TNLean.MPS.AreaLaw.LocalSolution.norm_sub_closingLinkWindow_le`: the closing-link window
  moves `Ψ_a` by at most the deficiency of level `h + 1`.
* `TNLean.MPS.AreaLaw.LocalSolution.re_inner_hierarchySum_add_le_add`: eq. `hchy` for the
  periodic sum and every unit vector kept by the closing-link window.
* `TNLean.MPS.AreaLaw.LocalSolution.card_le_two_mul_re_trace_of_closingLink`: at most `2n`
  orthonormal final states under the gap of the periodic sum.
-/

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace

namespace TNLean.MPS.AreaLaw.LocalSolution

open TNLean.MPS.AreaLaw.Hastings

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (P M : ℕ → ℕ → Matrix ι ι ℂ) (c : ℕ → ℕ → ℝ) (x : ℕ → ℝ)

/-- **The closing-link window on the ground state.** In the hierarchy of
`norm_sub_hierarchy_le`, let `W` be Hermitian with `‖(W - c_W) ψ‖ ≤ ε` and `‖W - c_W‖ ≤ K`.
The window of `W` at `c_W` and `x h` inside the range of the final projection `P h 0` is an
orthogonal projection that moves the unit vector `ψ` by at most
`hierarchyDeficiency ε K x (h + 1)`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 626–628 and 668–707, with `W = M_{N,1}` and `ψ = Ψ_a`. -/
theorem norm_sub_closingLinkWindow_le (hP0 : ∀ k, P 0 k = 1)
    (hstep : ∀ m k, P (m + 1) k =
      compressedWindowProjection (P m (2 * k) * P m (2 * k + 1)) (M m k) (c m k) (x m))
    (hcomm : ∀ m k, Commute (P m (2 * k)) (P m (2 * k + 1)))
    (hM : ∀ m k, (M m k).IsHermitian) (hx : ∀ m, 0 < x m) {ψ : EuclideanSpace ℂ ι}
    (hψ : ‖ψ‖ = 1) {ε K : ℝ}
    (hres : ∀ m k, ‖toEuclideanLin (M m k - (c m k : ℂ) • 1) ψ‖ ≤ ε)
    (hK : ∀ m k, ‖M m k - (c m k : ℂ) • 1‖ ≤ K) (h : ℕ) {W : Matrix ι ι ℂ}
    (hW : W.IsHermitian) (cW : ℝ) (hresW : ‖toEuclideanLin (W - (cW : ℂ) • 1) ψ‖ ≤ ε)
    (hKW : ‖W - (cW : ℂ) • 1‖ ≤ K) :
    IsStarProjection (compressedWindowProjection (P h 0) W cW (x h)) ∧
      ‖ψ - toEuclideanLin (compressedWindowProjection (P h 0) W cW (x h)) ψ‖ ≤
        hierarchyDeficiency ε K x (h + 1) := by
  obtain ⟨hP, hD⟩ := norm_sub_hierarchy_le P M c x hP0 hstep hcomm hM hx hψ hres hK h 0
  refine ⟨isStarProjection_compressedWindowProjection hP hW cW (x h), ?_⟩
  set D := hierarchyDeficiency ε K x h
  have hD0 : 0 ≤ D := (norm_nonneg _).trans hD
  have hD' : ‖ψ - toEuclideanLin 1 ψ‖ ≤ D := by
    rwa [toEuclideanLin_one_apply, sub_self, norm_zero]
  have hb := norm_sub_compressedWindowProjection_mul_sq_le hP (IsStarProjection.one _)
    (Commute.one_right _) hW cW (hx h) hψ hresW hD hD'
  rw [mul_one] at hb
  have hε : 0 ≤ ε := (norm_nonneg _).trans hresW
  have hmono : (ε + ‖W - (cW : ℂ) • 1‖ * (2 * D)) / x h ≤ (ε + K * (2 * D)) / x h :=
    div_le_div_of_nonneg_right (by nlinarith) (hx h).le
  have hnn : 0 ≤ (ε + ‖W - (cW : ℂ) • 1‖ * (2 * D)) / x h :=
    div_nonneg (by positivity) (hx h).le
  rw [hierarchyDeficiency_succ]
  refine Real.le_sqrt_of_sq_le (hb.trans ?_)
  have := pow_le_pow_left₀ hnn hmono 2
  linarith

/-- **eq. `hchy` for the periodic sum.** In the hierarchy of `re_inner_hierarchySum_le_add`,
let `W` be Hermitian and `x_W ≥ 0`; the construction takes `x_W = x h`, the radius for which
`norm_sub_closingLinkWindow_le` bounds the deficiency. Every unit vector `φ` kept by the
window of `W` at `re⟨Ψ, W Ψ⟩` and `x_W` inside the range of the final projection `P h 0` satisfies
`re⟨φ, (T + W) φ⟩ ≤ re⟨Ψ, (T + W) Ψ⟩ + ∑ x + x_W`, where `T = hierarchySum M h 0`. With
`W = M_{N,1}` and `Ψ = Ψ_a`, this is eq. `hchy` of Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 709–720, for `∑_i M_i` and each final state. -/
theorem re_inner_hierarchySum_add_le_add (hP0 : ∀ k, P 0 k = 1)
    {Ψ : EuclideanSpace ℂ ι}
    (hstep : ∀ m k, P (m + 1) k = compressedWindowProjection (P m (2 * k) * P m (2 * k + 1))
      (M m k) (⟪Ψ, toEuclideanLin (M m k) Ψ⟫_ℂ).re (x m))
    (hcomm : ∀ m k, Commute (P m (2 * k)) (P m (2 * k + 1)))
    (hM : ∀ m k, (M m k).IsHermitian) (hx : ∀ m, 0 ≤ x m) (h : ℕ) {W : Matrix ι ι ℂ}
    (hW : W.IsHermitian) {xW : ℝ} (hxW : 0 ≤ xW) {φ : EuclideanSpace ℂ ι} (hφ1 : ‖φ‖ = 1)
    (hφ : toEuclideanLin
      (compressedWindowProjection (P h 0) W (⟪Ψ, toEuclideanLin W Ψ⟫_ℂ).re xW) φ = φ) :
    (⟪φ, toEuclideanLin (hierarchySum M h 0 + W) φ⟫_ℂ).re ≤
      (⟪Ψ, toEuclideanLin (hierarchySum M h 0 + W) Ψ⟫_ℂ).re +
        (hierarchySum (fun m _ ↦ x m) h 0 + xW) := by
  have hproj := isStarProjection_hierarchy P M _ x hP0 hstep hcomm hM
  obtain ⟨hQφ, hWφ⟩ :=
    abs_re_inner_sub_le_of_compressedWindowProjection (hproj h 0) hW _ hxW hφ
  have hT := re_inner_hierarchySum_le_add P M x hP0 hstep hcomm hM hx h 0 hφ1 hQφ
  rw [hφ1, one_pow, mul_one, mul_one] at hWφ
  simp only [map_add, LinearMap.add_apply, inner_add_right, Complex.add_re]
  linarith [le_abs_self ((⟪φ, toEuclideanLin W φ⟫_ℂ).re - (⟪Ψ, toEuclideanLin W Ψ⟫_ℂ).re)]

/-- **At most `2n` final states of the periodic chain.** In the setting of
`re_inner_hierarchySum_add_le_add`, let the periodic sum `H = hierarchySum M h 0 + W` have gap
`ΔE` above `E₀` with ground projection `P₀` in the sense of `card_le_two_mul_re_trace`. If
`re⟨Ψ, H Ψ⟩ + ∑ x + x_W ≤ E₀ + ΔE/2`, then every orthonormal family of vectors kept by the
closing-link window has at most `2 re tr P₀` members. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 722–730. -/
theorem card_le_two_mul_re_trace_of_closingLink (hP0 : ∀ k, P 0 k = 1)
    {Ψ : EuclideanSpace ℂ ι}
    (hstep : ∀ m k, P (m + 1) k = compressedWindowProjection (P m (2 * k) * P m (2 * k + 1))
      (M m k) (⟪Ψ, toEuclideanLin (M m k) Ψ⟫_ℂ).re (x m))
    (hcomm : ∀ m k, Commute (P m (2 * k)) (P m (2 * k + 1)))
    (hM : ∀ m k, (M m k).IsHermitian) (hx : ∀ m, 0 ≤ x m) (h : ℕ) {W : Matrix ι ι ℂ}
    (hW : W.IsHermitian) {xW : ℝ} (hxW : 0 ≤ xW)
    {P₀ : Matrix ι ι ℂ} (hP₀ : IsStarProjection P₀) {E₀ ΔE : ℝ} (hΔ : 0 < ΔE)
    (hgap : ∀ v : EuclideanSpace ℂ ι,
      ΔE * (‖v‖ ^ 2 - (⟪v, toEuclideanLin P₀ v⟫_ℂ).re) ≤
        (⟪v, toEuclideanLin (hierarchySum M h 0 + W) v⟫_ℂ).re - E₀ * ‖v‖ ^ 2)
    (hE : (⟪Ψ, toEuclideanLin (hierarchySum M h 0 + W) Ψ⟫_ℂ).re +
      (hierarchySum (fun m _ ↦ x m) h 0 + xW) ≤ E₀ + ΔE / 2)
    {κ : Type*} {φ : κ → EuclideanSpace ℂ ι} (hφ : Orthonormal ℂ φ) (s : Finset κ)
    (hφP : ∀ j ∈ s, toEuclideanLin
      (compressedWindowProjection (P h 0) W (⟪Ψ, toEuclideanLin W Ψ⟫_ℂ).re xW) (φ j) = φ j) :
    (s.card : ℝ) ≤ 2 * (trace P₀).re :=
  card_le_two_mul_re_trace hP₀ hΔ hgap hφ s fun j hj ↦
    (re_inner_hierarchySum_add_le_add P M x hP0 hstep hcomm hM hx h hW hxW (hφ.1 j)
      (hφP j hj)).trans hE

end TNLean.MPS.AreaLaw.LocalSolution
