/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.HierarchyConstruction

/-!
# The nested retained spaces of the hierarchy

A state in the final retained space lies in the retained spaces of both children
at every preceding level. This is the hierarchical, tree-shaped representation
called a generalized matrix product state in Hastings,
arXiv:cond-mat/0508554v3, lines 596–607 and 668–743. No bound on the dimensions
of the intermediate retained spaces is asserted in that source.

**Local fix (closing edge):** the additional periodic window changes the retained
space at the root. Every vector it retains still belongs to the retained spaces
below the root. The correction is recorded in
`docs/paper-gaps/hastings05_hierarchical_energy.tex`.
-/

open Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.MPS.AreaLaw.LocalSolution

section Definition

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A vector belongs to the retained space at every node below a block.
Hastings, arXiv:cond-mat/0508554v3, lines 668–704 and Figure 1(b). -/
def IsRetainedHierarchy (P : ℕ → ℕ → Matrix n n ℂ) :
    ℕ → ℕ → EuclideanSpace ℂ n → Prop
  | 0, k, φ => toEuclideanLin (P 0 k) φ = φ
  | m + 1, k, φ => toEuclideanLin (P (m + 1) k) φ = φ ∧
      IsRetainedHierarchy P m (2 * k) φ ∧ IsRetainedHierarchy P m (2 * k + 1) φ

end Definition

section Supersites

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

/-- A vector retained by a parent spectral window is retained by both child
projections. Hastings, arXiv:cond-mat/0508554v3, lines 671–685. -/
theorem hierarchyProjection_children (blk : ι → ℕ)
    (M : ℕ → ℕ → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (c : ℕ → ℕ → ℝ) (x : ℕ → ℝ)
    (hsupp : ∀ m k, M m k ∈ supportedOperators d (levelBlock blk (m + 1) k))
    (hM : ∀ m k, (M m k).IsHermitian)
    (m k : ℕ) {φ : EuclideanSpace ℂ (ι → Fin d)}
    (hφ : toEuclideanLin (hierarchyProjection M c x (m + 1) k) φ = φ) :
    toEuclideanLin (hierarchyProjection M c x m (2 * k)) φ = φ ∧
      toEuclideanLin (hierarchyProjection M c x m (2 * k + 1)) φ = φ := by
  let P := hierarchyProjection M c x
  have hproj := isStarProjection_supersiteHierarchy blk P M c x
    (hierarchyProjection_zero M c x) (hierarchyProjection_succ M c x) hsupp hM
  have hcomm := commute_supersiteHierarchy blk P M c x
    (hierarchyProjection_zero M c x) (hierarchyProjection_succ M c x) hsupp
  have hQ := (hproj m (2 * k)).mul (hproj m (2 * k + 1)) (hcomm m k)
  have hQφ : toEuclideanLin (P m (2 * k) * P m (2 * k + 1)) φ = φ :=
    toEuclideanLin_eq_of_mul_eq (by
      rw [hierarchyProjection_succ, compressedWindowProjection, ← mul_assoc,
        hQ.isIdempotentElem.eq]) hφ
  constructor
  · exact toEuclideanLin_eq_of_mul_eq
      (by rw [← mul_assoc, (hproj m (2 * k)).isIdempotentElem.eq]) hQφ
  · exact toEuclideanLin_eq_of_mul_eq
      (by rw [← mul_assoc, ← (hcomm m k).eq, mul_assoc,
        (hproj m (2 * k + 1)).isIdempotentElem.eq]) hQφ

/-- Membership in a constructed block projection implies membership in every
retained space below that block. Hastings, arXiv:cond-mat/0508554v3,
lines 668–704 and Figure 1(b). -/
theorem isRetainedHierarchy_of_hierarchyProjection (blk : ι → ℕ)
    (M : ℕ → ℕ → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (c : ℕ → ℕ → ℝ) (x : ℕ → ℝ)
    (hsupp : ∀ m k, M m k ∈ supportedOperators d (levelBlock blk (m + 1) k))
    (hM : ∀ m k, (M m k).IsHermitian) (m k : ℕ)
    {φ : EuclideanSpace ℂ (ι → Fin d)}
    (hφ : toEuclideanLin (hierarchyProjection M c x m k) φ = φ) :
    IsRetainedHierarchy (hierarchyProjection M c x) m k φ := by
  induction m generalizing k with
  | zero => exact hφ
  | succ m ih =>
    obtain ⟨hleft, hright⟩ := hierarchyProjection_children blk M c x hsupp hM m k hφ
    exact ⟨hφ, ih (2 * k) hleft, ih (2 * k + 1) hright⟩

/-- The closing window preserves every previously retained space in the binary
hierarchy. Thus its recombination can be taken at the root of the same tree.
Hastings, arXiv:cond-mat/0508554v3, lines 722–743, with the correction recorded in
`docs/paper-gaps/hastings05_hierarchical_energy.tex`. -/
theorem isRetainedHierarchy_of_hierarchyClosingProjection (blk : ι → ℕ)
    (M : ℕ → ℕ → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (c : ℕ → ℕ → ℝ) (x : ℕ → ℝ)
    (hsupp : ∀ m k, M m k ∈ supportedOperators d (levelBlock blk (m + 1) k))
    (hM : ∀ m k, (M m k).IsHermitian) (h : ℕ)
    (W : Matrix (ι → Fin d) (ι → Fin d) ℂ) (cW : ℝ)
    {φ : EuclideanSpace ℂ (ι → Fin d)}
    (hφ : toEuclideanLin (hierarchyClosingProjection M c x h W cW) φ = φ) :
    IsRetainedHierarchy (hierarchyProjection M c x) h 0 φ := by
  have hP := isStarProjection_supersiteHierarchy blk (hierarchyProjection M c x) M c x
    (hierarchyProjection_zero M c x) (hierarchyProjection_succ M c x) hsupp hM h 0
  apply isRetainedHierarchy_of_hierarchyProjection blk M c x hsupp hM h 0
  exact toEuclideanLin_eq_of_mul_eq (by
    rw [hierarchyClosingProjection, compressedWindowProjection, ← mul_assoc,
      hP.isIdempotentElem.eq]) hφ

end Supersites

end TNLean.MPS.AreaLaw.LocalSolution
