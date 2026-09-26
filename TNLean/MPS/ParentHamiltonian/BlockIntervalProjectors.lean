/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockProjectorSum
import TNLean.MPS.ParentHamiltonian.SpectatorOverlap

/-!
# Joint projectors on overlapping MPS intervals

Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (ii), compares the
joint ground-space projectors on overlapping intervals. Here the overlap
matrix on the common interval is supplied explicitly. Its bound extends
to both full physical ranges without a loss depending on the spectator
lengths. The individual block projector errors remain on the right-hand side.
-/

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace MPSTensor
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} {D : ι → ℕ}

/-- The physical interval comparison underlying Nachtergaele,
arXiv:cond-mat/9410110, Lemma `commutation` (ii), lines 2533--2589.
The matrix bounds the distinct-block ground-space overlaps on the common
interval of length \(L\). The bound is uniform in the spectator lengths
\(K,Q\); the remaining errors are the individual block projector defects. -/
theorem norm_iSup_groundSpaceES_sub_comp_le_of_overlapMatrix
    (A : ∀ i, MPSTensor d (D i)) (K L Q : ℕ) (B : Matrix ι ι ℝ)
    (hdiag : ∀ i, B i i = 0) (hB : ‖B‖ < 1 / 2)
    (hBnonneg : ∀ i j, 0 ≤ B i j)
    (hpair : ∀ i j, i ≠ j → ∀ x ∈ groundSpaceES (A i) L,
      ∀ y ∈ groundSpaceES (A j) L, ‖⟪x, y⟫_ℂ‖ ≤ B i j * ‖x‖ * ‖y‖) :
    let U := fun i ↦ (leftBoundaryMapES (A i) (K + L) Q).range
    let V := fun i ↦ (reassocTailBoundaryMapES (A i) K L Q).range
    let δ := ‖B‖ / (1 - ‖B‖)
    ‖(⨆ i, groundSpaceES (A i) (K + L + Q)).starProjection -
      (⨆ i, U i).starProjection.comp (⨆ i, V i).starProjection‖ ≤
      4 * δ / (1 - δ) ^ 2 + ∑ i,
        ‖(groundSpaceES (A i) (K + L + Q)).starProjection -
          (U i).starProjection.comp (V i).starProjection‖ := by
  have hWU (i : ι) : groundSpaceES (A i) (K + L + Q) ≤
      (leftBoundaryMapES (A i) (K + L) Q).range := by
    rw [← range_groundSpaceMapES,
      ← leftBoundaryMapES_comp_leftVirtualMapES (A i) (K + L) Q]
    exact LinearMap.range_comp_le_range _ _
  exact Submodule.norm_iSup_starProjection_sub_comp_le_of_overlapMatrix
    (fun i ↦ (leftBoundaryMapES (A i) (K + L) Q).range)
    (fun i ↦ (reassocTailBoundaryMapES (A i) K L Q).range)
    (fun i ↦ groundSpaceES (A i) (K + L + Q)) B hdiag hB hWU
    (fun i j hij _ ⟨x, hx⟩ _ ⟨y, hy⟩ ↦ hx ▸ hy ▸
      norm_inner_leftBoundaryMapES_le (A i) (A j) K L Q (hBnonneg i j)
        (hpair i j hij) x y)
    (fun i j hij _ ⟨x, hx⟩ _ ⟨y, hy⟩ ↦ hx ▸ hy ▸
      norm_inner_reassocTailBoundaryMapES_le (A i) (A j) K L Q (hBnonneg i j)
        (hpair i j hij) x y)
    (fun i j hij _ ⟨x, hx⟩ _ ⟨y, hy⟩ ↦ hx ▸ hy ▸
      norm_inner_left_reassocTailBoundaryMapES_le (A i) (A j) K L Q (hBnonneg i j)
        (hpair i j hij) x y)

end MPSTensor
