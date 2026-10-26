/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.ClosingLink
import TNLean.MPS.AreaLaw.LocalSolution.SupersiteHierarchy

/-!
# The final states of the hierarchy on supersites

The theorems of `FinalStateEnergy.lean` and `ClosingLink.lean` on the final states of
Hastings' hierarchical construction (arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 668–730)
assume that the projections of the two halves of every block commute. On the chain of
supersites of lines 609–628 each pair operator `M_{k,k+1}` acts on the block it joins, so by
`commute_supersiteHierarchy` the two halves act on disjoint blocks and commute. This file
restates those theorems with the commutation derived from the supports, so that they no
longer assume it; the deviations below remain.

## Main results

* `TNLean.MPS.AreaLaw.LocalSolution.isStarProjection_supersiteHierarchy`: every projection of
  the hierarchy is an orthogonal projection.
* `TNLean.MPS.AreaLaw.LocalSolution.abs_re_inner_supersiteHierarchySum_sub_le`: a vector kept by
  a block has the expectation of the joining operators below it within the sum of the radii.
* `TNLean.MPS.AreaLaw.LocalSolution.re_inner_supersiteHierarchySum_le_add`: eq. `hchy` for every
  unit vector kept by a block.
* `TNLean.MPS.AreaLaw.LocalSolution.card_le_two_mul_re_trace_of_supersiteHierarchy`: at most
  `2n` orthonormal final states.
* `TNLean.MPS.AreaLaw.LocalSolution.norm_sub_supersiteClosingLinkWindow_le`,
  `TNLean.MPS.AreaLaw.LocalSolution.re_inner_supersiteHierarchySum_add_le_add`,
  `TNLean.MPS.AreaLaw.LocalSolution.card_le_two_mul_re_trace_of_supersiteClosingLink`: the same
  for the window of the link closing the periodic chain.

**Scope restriction (open chain):** `abs_re_inner_supersiteHierarchySum_sub_le`,
`re_inner_supersiteHierarchySum_le_add` and `card_le_two_mul_re_trace_of_supersiteHierarchy`
concern the sum `hierarchySum M h 0` of the joining operators of the binary tree, which covers
the `N - 1` links of the open chain but not the link `(N, 1)` of the source's periodic chain
(lines 626–628). The count therefore assumes the gap of this open-chain sum, not of the periodic
`∑_i M_i`, and the periodic gap does not supply it. The closing-link results below remove this
restriction. Documented in `docs/paper-gaps/hastings05_hierarchical_energy.tex`.

The closing-link results inherit the **Local fix (closing-link window)** of `ClosingLink.lean`:
the final states are those kept by one further window for the link `(N, 1)`, which the source
does not state, so eq. `hchy` and the count hold for this corrected construction. Documented in
`docs/paper-gaps/hastings05_hierarchical_energy.tex`.
-/

open Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace

namespace TNLean.MPS.AreaLaw.LocalSolution

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (blk : ι → ℕ)
variable (P M : ℕ → ℕ → Matrix (ι → Fin d) (ι → Fin d) ℂ) (c : ℕ → ℕ → ℝ) (x : ℕ → ℝ)

/-- **Projections on supersites.** In the hierarchy of `mem_supportedOperators_hierarchy`, with
Hermitian pair operators, every projection is an orthogonal projection. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 609–628 and 668–685. -/
theorem isStarProjection_supersiteHierarchy (hP0 : ∀ k, P 0 k = 1)
    (hstep : ∀ m k, P (m + 1) k =
      compressedWindowProjection (P m (2 * k) * P m (2 * k + 1)) (M m k) (c m k) (x m))
    (hMsupp : ∀ m k, M m k ∈ supportedOperators d (levelBlock blk (m + 1) k))
    (hM : ∀ m k, (M m k).IsHermitian) : ∀ m k, IsStarProjection (P m k) :=
  isStarProjection_hierarchy P M c x hP0 hstep
    (commute_supersiteHierarchy blk P M c x hP0 hstep hMsupp) hM

/-- **eq. `hchy` below one block, on supersites.** The bound of
`abs_re_inner_hierarchySum_sub_le`, with the commutation of the halves derived from the
supports of the pair operators. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 609–628 and 668–720. -/
theorem abs_re_inner_supersiteHierarchySum_sub_le (hP0 : ∀ k, P 0 k = 1)
    (hstep : ∀ m k, P (m + 1) k =
      compressedWindowProjection (P m (2 * k) * P m (2 * k + 1)) (M m k) (c m k) (x m))
    (hMsupp : ∀ m k, M m k ∈ supportedOperators d (levelBlock blk (m + 1) k))
    (hM : ∀ m k, (M m k).IsHermitian) (hx : ∀ m, 0 ≤ x m) :
    ∀ m k {φ : EuclideanSpace ℂ (ι → Fin d)}, toEuclideanLin (P m k) φ = φ →
      |(⟪φ, toEuclideanLin (hierarchySum M m k) φ⟫_ℂ).re - hierarchySum c m k * ‖φ‖ ^ 2| ≤
        hierarchySum (fun m _ ↦ x m) m k * ‖φ‖ ^ 2 :=
  abs_re_inner_hierarchySum_sub_le P M c x hP0 hstep
    (commute_supersiteHierarchy blk P M c x hP0 hstep hMsupp) hM hx

/-- **eq. `hchy` for every final state, on supersites.** The bound of
`re_inner_hierarchySum_le_add`, with the commutation of the halves derived from the supports of
the pair operators. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 609–628 and
709–720, for the links of the open chain as in `re_inner_hierarchySum_le_add`. -/
theorem re_inner_supersiteHierarchySum_le_add (hP0 : ∀ k, P 0 k = 1)
    {Ψ : EuclideanSpace ℂ (ι → Fin d)}
    (hstep : ∀ m k, P (m + 1) k = compressedWindowProjection (P m (2 * k) * P m (2 * k + 1))
      (M m k) (⟪Ψ, toEuclideanLin (M m k) Ψ⟫_ℂ).re (x m))
    (hMsupp : ∀ m k, M m k ∈ supportedOperators d (levelBlock blk (m + 1) k))
    (hM : ∀ m k, (M m k).IsHermitian) (hx : ∀ m, 0 ≤ x m) (m k : ℕ)
    {φ : EuclideanSpace ℂ (ι → Fin d)} (hφ1 : ‖φ‖ = 1) (hφ : toEuclideanLin (P m k) φ = φ) :
    (⟪φ, toEuclideanLin (hierarchySum M m k) φ⟫_ℂ).re ≤
      (⟪Ψ, toEuclideanLin (hierarchySum M m k) Ψ⟫_ℂ).re + hierarchySum (fun m _ ↦ x m) m k :=
  re_inner_hierarchySum_le_add P M x hP0 hstep
    (commute_supersiteHierarchy blk P M _ x hP0 hstep hMsupp) hM hx m k hφ1 hφ

/-- **At most `2n` final states, on supersites.** The count of
`card_le_two_mul_re_trace_of_hierarchy`, with the commutation of the halves derived from the
supports of the pair operators. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 609–628 and 722–730, for the links of the open chain as in
`card_le_two_mul_re_trace_of_hierarchy`. -/
theorem card_le_two_mul_re_trace_of_supersiteHierarchy (hP0 : ∀ k, P 0 k = 1)
    {Ψ : EuclideanSpace ℂ (ι → Fin d)}
    (hstep : ∀ m k, P (m + 1) k = compressedWindowProjection (P m (2 * k) * P m (2 * k + 1))
      (M m k) (⟪Ψ, toEuclideanLin (M m k) Ψ⟫_ℂ).re (x m))
    (hMsupp : ∀ m k, M m k ∈ supportedOperators d (levelBlock blk (m + 1) k))
    (hM : ∀ m k, (M m k).IsHermitian) (hx : ∀ m, 0 ≤ x m) (h : ℕ)
    {P₀ : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hP₀ : IsStarProjection P₀) {E₀ ΔE : ℝ}
    (hΔ : 0 < ΔE)
    (hgap : ∀ v : EuclideanSpace ℂ (ι → Fin d),
      ΔE * (‖v‖ ^ 2 - (⟪v, toEuclideanLin P₀ v⟫_ℂ).re) ≤
        (⟪v, toEuclideanLin (hierarchySum M h 0) v⟫_ℂ).re - E₀ * ‖v‖ ^ 2)
    (hE : (⟪Ψ, toEuclideanLin (hierarchySum M h 0) Ψ⟫_ℂ).re +
      hierarchySum (fun m _ ↦ x m) h 0 ≤ E₀ + ΔE / 2)
    {κ : Type*} {φ : κ → EuclideanSpace ℂ (ι → Fin d)} (hφ : Orthonormal ℂ φ) (s : Finset κ)
    (hφP : ∀ j ∈ s, toEuclideanLin (P h 0) (φ j) = φ j) :
    (s.card : ℝ) ≤ 2 * (trace P₀).re :=
  card_le_two_mul_re_trace_of_hierarchy P M x hP0 hstep
    (commute_supersiteHierarchy blk P M _ x hP0 hstep hMsupp) hM hx h hP₀ hΔ hgap hE hφ s hφP

/-- **The closing-link window on supersites.** The bound of `norm_sub_closingLinkWindow_le`,
with the commutation of the halves derived from the supports of the pair operators. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 609–628 and 668–707. -/
theorem norm_sub_supersiteClosingLinkWindow_le (hP0 : ∀ k, P 0 k = 1)
    (hstep : ∀ m k, P (m + 1) k =
      compressedWindowProjection (P m (2 * k) * P m (2 * k + 1)) (M m k) (c m k) (x m))
    (hMsupp : ∀ m k, M m k ∈ supportedOperators d (levelBlock blk (m + 1) k))
    (hM : ∀ m k, (M m k).IsHermitian) (hx : ∀ m, 0 < x m)
    {ψ : EuclideanSpace ℂ (ι → Fin d)} (hψ : ‖ψ‖ = 1) {ε K : ℝ}
    (hres : ∀ m k, ‖toEuclideanLin (M m k - (c m k : ℂ) • 1) ψ‖ ≤ ε)
    (hK : ∀ m k, ‖M m k - (c m k : ℂ) • 1‖ ≤ K) (h : ℕ)
    {W : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hW : W.IsHermitian) (cW : ℝ)
    (hresW : ‖toEuclideanLin (W - (cW : ℂ) • 1) ψ‖ ≤ ε) (hKW : ‖W - (cW : ℂ) • 1‖ ≤ K) :
    IsStarProjection (compressedWindowProjection (P h 0) W cW (x h)) ∧
      ‖ψ - toEuclideanLin (compressedWindowProjection (P h 0) W cW (x h)) ψ‖ ≤
        hierarchyDeficiency ε K x (h + 1) :=
  norm_sub_closingLinkWindow_le P M c x hP0 hstep
    (commute_supersiteHierarchy blk P M c x hP0 hstep hMsupp) hM hx hψ hres hK h hW cW hresW hKW

/-- **eq. `hchy` for the periodic chain of supersites.** The bound of
`re_inner_hierarchySum_add_le_add`, with the commutation of the halves derived from the supports
of the pair operators. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 609–628 and
709–720. -/
theorem re_inner_supersiteHierarchySum_add_le_add (hP0 : ∀ k, P 0 k = 1)
    {Ψ : EuclideanSpace ℂ (ι → Fin d)}
    (hstep : ∀ m k, P (m + 1) k = compressedWindowProjection (P m (2 * k) * P m (2 * k + 1))
      (M m k) (⟪Ψ, toEuclideanLin (M m k) Ψ⟫_ℂ).re (x m))
    (hMsupp : ∀ m k, M m k ∈ supportedOperators d (levelBlock blk (m + 1) k))
    (hM : ∀ m k, (M m k).IsHermitian) (hx : ∀ m, 0 ≤ x m) (h : ℕ)
    {W : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hW : W.IsHermitian) {xW : ℝ} (hxW : 0 ≤ xW)
    {φ : EuclideanSpace ℂ (ι → Fin d)} (hφ1 : ‖φ‖ = 1)
    (hφ : toEuclideanLin
      (compressedWindowProjection (P h 0) W (⟪Ψ, toEuclideanLin W Ψ⟫_ℂ).re xW) φ = φ) :
    (⟪φ, toEuclideanLin (hierarchySum M h 0 + W) φ⟫_ℂ).re ≤
      (⟪Ψ, toEuclideanLin (hierarchySum M h 0 + W) Ψ⟫_ℂ).re +
        (hierarchySum (fun m _ ↦ x m) h 0 + xW) :=
  re_inner_hierarchySum_add_le_add P M x hP0 hstep
    (commute_supersiteHierarchy blk P M _ x hP0 hstep hMsupp) hM hx h hW hxW hφ1 hφ

/-- **At most `2n` final states of the periodic chain of supersites.** The count of
`card_le_two_mul_re_trace_of_closingLink`, with the commutation of the halves derived from the
supports of the pair operators. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 609–628 and 722–730. -/
theorem card_le_two_mul_re_trace_of_supersiteClosingLink (hP0 : ∀ k, P 0 k = 1)
    {Ψ : EuclideanSpace ℂ (ι → Fin d)}
    (hstep : ∀ m k, P (m + 1) k = compressedWindowProjection (P m (2 * k) * P m (2 * k + 1))
      (M m k) (⟪Ψ, toEuclideanLin (M m k) Ψ⟫_ℂ).re (x m))
    (hMsupp : ∀ m k, M m k ∈ supportedOperators d (levelBlock blk (m + 1) k))
    (hM : ∀ m k, (M m k).IsHermitian) (hx : ∀ m, 0 ≤ x m) (h : ℕ)
    {W : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hW : W.IsHermitian) {xW : ℝ} (hxW : 0 ≤ xW)
    {P₀ : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hP₀ : IsStarProjection P₀) {E₀ ΔE : ℝ}
    (hΔ : 0 < ΔE)
    (hgap : ∀ v : EuclideanSpace ℂ (ι → Fin d),
      ΔE * (‖v‖ ^ 2 - (⟪v, toEuclideanLin P₀ v⟫_ℂ).re) ≤
        (⟪v, toEuclideanLin (hierarchySum M h 0 + W) v⟫_ℂ).re - E₀ * ‖v‖ ^ 2)
    (hE : (⟪Ψ, toEuclideanLin (hierarchySum M h 0 + W) Ψ⟫_ℂ).re +
      (hierarchySum (fun m _ ↦ x m) h 0 + xW) ≤ E₀ + ΔE / 2)
    {κ : Type*} {φ : κ → EuclideanSpace ℂ (ι → Fin d)} (hφ : Orthonormal ℂ φ) (s : Finset κ)
    (hφP : ∀ j ∈ s, toEuclideanLin
      (compressedWindowProjection (P h 0) W (⟪Ψ, toEuclideanLin W Ψ⟫_ℂ).re xW) (φ j) = φ j) :
    (s.card : ℝ) ≤ 2 * (trace P₀).re :=
  card_le_two_mul_re_trace_of_closingLink P M x hP0 hstep
    (commute_supersiteHierarchy blk P M _ x hP0 hstep hMsupp) hM hx h hW hxW hP₀ hΔ hgap hE hφ
    s hφP

end TNLean.MPS.AreaLaw.LocalSolution
