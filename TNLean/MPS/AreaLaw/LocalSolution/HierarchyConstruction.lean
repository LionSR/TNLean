/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.SupersiteFinalState
import TNLean.MPS.AreaLaw.LocalSolution.HierarchicalEnergy

/-!
# Constructing the spectral projections of the hierarchy

Given the Hermitian operators joining the two halves of each block, the projections
are defined recursively from their compressed spectral windows. Their recursion and
initial value are consequences of the definition, rather than hypotheses about an
unspecified family of projections. Local support implies that sibling projections
commute. The residual estimates then give a nonzero retained space whenever the
explicit deficiency bound is less than one.

This is the construction in Hastings, arXiv:cond-mat/0508554v3, Section II,
lines 609–707. The periodic construction uses the additional closing-link window
recorded in `docs/paper-gaps/hastings05_hierarchical_energy.tex`.

**Local fix (deficiency recurrence):** the adaptive windows and
`hierarchyDeficiency_window_le` measure every level against the original state.
The resulting majorant has coefficient `3^h - 1`, rather than the printed
`2^h - 1`, and decay exponent `1/4`. The corrected recurrence is documented in
`docs/paper-gaps/hastings05_hierarchical_projection.tex`.
-/

open Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.MPS.AreaLaw.LocalSolution

section Matrices

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The spectral projection retained by block `k` at level `m`.
Hastings, arXiv:cond-mat/0508554v3, lines 640–642 and 671–685. -/
noncomputable def hierarchyProjection (M : ℕ → ℕ → Matrix n n ℂ)
    (c : ℕ → ℕ → ℝ) (x : ℕ → ℝ) : ℕ → ℕ → Matrix n n ℂ
  | 0, _ => 1
  | m + 1, k => compressedWindowProjection
      (hierarchyProjection M c x m (2 * k) * hierarchyProjection M c x m (2 * k + 1))
      (M m k) (c m k) (x m)

/-- A single supersite is retained without restriction at level zero.
Hastings, arXiv:cond-mat/0508554v3, lines 640–642. -/
@[simp]
theorem hierarchyProjection_zero (M : ℕ → ℕ → Matrix n n ℂ)
    (c : ℕ → ℕ → ℝ) (x : ℕ → ℝ) (k : ℕ) : hierarchyProjection M c x 0 k = 1 := rfl

/-- The next level is the spectral window inside the retained spaces of its two halves.
Hastings, arXiv:cond-mat/0508554v3, lines 671–685. -/
theorem hierarchyProjection_succ (M : ℕ → ℕ → Matrix n n ℂ)
    (c : ℕ → ℕ → ℝ) (x : ℕ → ℝ) (m k : ℕ) :
    hierarchyProjection M c x (m + 1) k = compressedWindowProjection
      (hierarchyProjection M c x m (2 * k) * hierarchyProjection M c x m (2 * k + 1))
      (M m k) (c m k) (x m) := rfl

/-- The additional spectral window for the edge closing the periodic chain.
This is the corrected construction of Hastings, arXiv:cond-mat/0508554v3,
lines 626–628 and 709–730, documented in
`docs/paper-gaps/hastings05_hierarchical_energy.tex`. -/
noncomputable def hierarchyClosingProjection (M : ℕ → ℕ → Matrix n n ℂ)
    (c : ℕ → ℕ → ℝ) (x : ℕ → ℝ) (h : ℕ) (W : Matrix n n ℂ) (cW : ℝ) :
    Matrix n n ℂ :=
  compressedWindowProjection (hierarchyProjection M c x h 0) W cW (x h)

end Matrices

/-- The adaptive window radius for a residual of size `K exp(-r)` and `h` levels.
The deficiency is measured against the original state, as in the corrected recurrence
of `HierarchyLevels.lean`. Hastings, arXiv:cond-mat/0508554v3, lines 676–704. -/
noncomputable def hierarchyWindowRadius (K r : ℝ) (h m : ℕ) : ℝ :=
  K * (Real.exp (-r) + 2 * hierarchyMajorant (Real.exp (-r)) (1 - 1 / (h : ℝ)) m) ^
    (1 / (h : ℝ))

/-- For `h ≥ 2`, the adaptive windows give deficiency at most
`(3^h - 1) exp(-r/4)` after `h` levels. Hastings, arXiv:cond-mat/0508554v3,
lines 696–709, with the corrected recurrence documented in
`docs/paper-gaps/hastings05_hierarchical_projection.tex`. -/
theorem hierarchyDeficiency_window_le {K r : ℝ} (hK : 0 < K) (hr : 0 ≤ r) {h : ℕ}
    (hh : 2 ≤ h) :
    hierarchyDeficiency (K * Real.exp (-r)) K (hierarchyWindowRadius K r h) h ≤
      ((3 : ℝ) ^ h - 1) * Real.exp (-r / 4) := by
  have hbound := (hierarchyDeficiency_le_hierarchyMajorant hK (Real.exp_pos (-r))
    (1 - 1 / (h : ℝ)) h).trans
      (hierarchyMajorant_le_rpow_quarter (Real.exp_pos (-r))
        (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr)) hh)
  change hierarchyDeficiency (K * Real.exp (-r)) K
    (fun m => K * (Real.exp (-r) +
      2 * hierarchyMajorant (Real.exp (-r)) (1 - 1 / (h : ℝ)) m) ^ (1 / (h : ℝ))) h ≤ _
  simpa only [sub_sub_cancel, ← Real.exp_mul, mul_one_div] using hbound

section Supersites

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

/-- The explicitly constructed hierarchy has the deficiency estimate at every level;
commutation of sibling projections follows from their disjoint supersite supports.
Hastings, arXiv:cond-mat/0508554v3, lines 609–707. -/
theorem norm_sub_hierarchyProjection_le (blk : ι → ℕ)
    (M : ℕ → ℕ → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (c : ℕ → ℕ → ℝ) (x : ℕ → ℝ)
    (hMsupp : ∀ m k, M m k ∈ supportedOperators d (levelBlock blk (m + 1) k))
    (hM : ∀ m k, (M m k).IsHermitian) (hx : ∀ m, 0 < x m)
    {ψ : EuclideanSpace ℂ (ι → Fin d)} (hψ : ‖ψ‖ = 1) {ε K : ℝ}
    (hres : ∀ m k, ‖toEuclideanLin (M m k - (c m k : ℂ) • 1) ψ‖ ≤ ε)
    (hK : ∀ m k, ‖M m k - (c m k : ℂ) • 1‖ ≤ K) :
    ∀ m k, IsStarProjection (hierarchyProjection M c x m k) ∧
      ‖ψ - toEuclideanLin (hierarchyProjection M c x m k) ψ‖ ≤
        hierarchyDeficiency ε K x m := by
  exact norm_sub_supersiteHierarchy_le blk (hierarchyProjection M c x) M c x
    (hierarchyProjection_zero M c x) (hierarchyProjection_succ M c x) hMsupp hM hx hψ hres hK

/-- A level whose deficiency is less than one retains a unit vector. The witness is
the normalized image of the given state under the constructed projection.
Hastings, arXiv:cond-mat/0508554v3, lines 645–668 and 696–709. -/
theorem exists_unit_mem_hierarchyProjection (blk : ι → ℕ)
    (M : ℕ → ℕ → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (c : ℕ → ℕ → ℝ) (x : ℕ → ℝ)
    (hMsupp : ∀ m k, M m k ∈ supportedOperators d (levelBlock blk (m + 1) k))
    (hM : ∀ m k, (M m k).IsHermitian) (hx : ∀ m, 0 < x m)
    {ψ : EuclideanSpace ℂ (ι → Fin d)} (hψ : ‖ψ‖ = 1) {ε K : ℝ}
    (hres : ∀ m k, ‖toEuclideanLin (M m k - (c m k : ℂ) • 1) ψ‖ ≤ ε)
    (hK : ∀ m k, ‖M m k - (c m k : ℂ) • 1‖ ≤ K) (h k : ℕ)
    (hsmall : hierarchyDeficiency ε K x h < 1) :
    ∃ φ : EuclideanSpace ℂ (ι → Fin d), ‖φ‖ = 1 ∧
      toEuclideanLin (hierarchyProjection M c x h k) φ = φ ∧
      ‖φ - ψ‖ ≤ 2 * hierarchyDeficiency ε K x h := by
  obtain ⟨hP, hD⟩ := norm_sub_hierarchyProjection_le blk M c x hMsupp hM hx hψ hres hK h k
  obtain ⟨φ, hφ, hPφ, hnear, -⟩ := exists_mem_range_re_inner_le_add hP hψ hD hsmall
  exact ⟨φ, hφ, hPφ, hnear⟩

/-- The constructed periodic projection has the deficiency of one further level.
Hastings, arXiv:cond-mat/0508554v3, lines 696–730, with the closing edge treated
as in `docs/paper-gaps/hastings05_hierarchical_energy.tex`. -/
theorem norm_sub_hierarchyClosingProjection_le (blk : ι → ℕ)
    (M : ℕ → ℕ → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (c : ℕ → ℕ → ℝ) (x : ℕ → ℝ)
    (hMsupp : ∀ m k, M m k ∈ supportedOperators d (levelBlock blk (m + 1) k))
    (hM : ∀ m k, (M m k).IsHermitian) (hx : ∀ m, 0 < x m)
    {ψ : EuclideanSpace ℂ (ι → Fin d)} (hψ : ‖ψ‖ = 1) {ε K : ℝ}
    (hres : ∀ m k, ‖toEuclideanLin (M m k - (c m k : ℂ) • 1) ψ‖ ≤ ε)
    (hK : ∀ m k, ‖M m k - (c m k : ℂ) • 1‖ ≤ K) (h : ℕ)
    {W : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hW : W.IsHermitian) (cW : ℝ)
    (hresW : ‖toEuclideanLin (W - (cW : ℂ) • 1) ψ‖ ≤ ε)
    (hKW : ‖W - (cW : ℂ) • 1‖ ≤ K) :
    IsStarProjection (hierarchyClosingProjection M c x h W cW) ∧
      ‖ψ - toEuclideanLin (hierarchyClosingProjection M c x h W cW) ψ‖ ≤
        hierarchyDeficiency ε K x (h + 1) := by
  exact norm_sub_supersiteClosingLinkWindow_le blk (hierarchyProjection M c x) M c x
    (hierarchyProjection_zero M c x) (hierarchyProjection_succ M c x) hMsupp hM hx
    hψ hres hK h hW cW hresW hKW

/-- The corrected periodic construction retains a unit vector once its explicit
deficiency is less than one. Hastings, arXiv:cond-mat/0508554v3, lines 705–730,
with the closing window of `docs/paper-gaps/hastings05_hierarchical_energy.tex`. -/
theorem exists_unit_mem_hierarchyClosingProjection (blk : ι → ℕ)
    (M : ℕ → ℕ → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (c : ℕ → ℕ → ℝ) (x : ℕ → ℝ)
    (hMsupp : ∀ m k, M m k ∈ supportedOperators d (levelBlock blk (m + 1) k))
    (hM : ∀ m k, (M m k).IsHermitian) (hx : ∀ m, 0 < x m)
    {ψ : EuclideanSpace ℂ (ι → Fin d)} (hψ : ‖ψ‖ = 1) {ε K : ℝ}
    (hres : ∀ m k, ‖toEuclideanLin (M m k - (c m k : ℂ) • 1) ψ‖ ≤ ε)
    (hK : ∀ m k, ‖M m k - (c m k : ℂ) • 1‖ ≤ K) (h : ℕ)
    {W : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hW : W.IsHermitian) (cW : ℝ)
    (hresW : ‖toEuclideanLin (W - (cW : ℂ) • 1) ψ‖ ≤ ε)
    (hKW : ‖W - (cW : ℂ) • 1‖ ≤ K)
    (hsmall : hierarchyDeficiency ε K x (h + 1) < 1) :
    ∃ φ : EuclideanSpace ℂ (ι → Fin d), ‖φ‖ = 1 ∧
      toEuclideanLin (hierarchyClosingProjection M c x h W cW) φ = φ ∧
      ‖φ - ψ‖ ≤ 2 * hierarchyDeficiency ε K x (h + 1) := by
  obtain ⟨hP, hD⟩ := norm_sub_hierarchyClosingProjection_le blk M c x hMsupp hM hx
    hψ hres hK h hW cW hresW hKW
  obtain ⟨φ, hφ, hPφ, hnear, -⟩ := exists_mem_range_re_inner_le_add hP hψ hD hsmall
  exact ⟨φ, hφ, hPφ, hnear⟩

end Supersites

end TNLean.MPS.AreaLaw.LocalSolution
