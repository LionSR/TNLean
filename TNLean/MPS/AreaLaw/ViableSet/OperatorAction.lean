/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.LeftCoordinates
import TNLean.MPS.AreaLaw.OpenMPSOperatorAction

/-!
# Applying operators to vectors of a viable set

Reading an operator on the first `i` sites in the coordinates of a chain of `i` sites
commutes with its action on vectors. Bounds on its operator-Schmidt ranks at the internal
cuts therefore give the multiplicative MPS bond bound in the error-reduction step of LVV.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, Claim
`c:errorreduction`, lines 580–592, especially the bond-dimension assertion at line 591.
-/

open Matrix

namespace TNLean.MPS.AreaLaw

variable {L q i : ℕ}

/-- Reading the left block as a chain commutes with the action of a matrix on it.
LVV13, arXiv:1307.5143v1, `algo53.tex`, Claim `c:errorreduction`, lines 588–591. -/
theorem leftConfigOfFin_toEuclideanLin (hi : i ≤ L)
    (A : LeftBlockMatrix L q i) (v : LeftBlockVector L q i) :
    (fun x ↦ toEuclideanLin A v (leftConfigOfFin x)) =
      A.submatrix leftConfigOfFin leftConfigOfFin *ᵥ (fun x ↦ v (leftConfigOfFin x)) := by
  funext x
  exact ((leftConfigOfFinEquiv hi).sum_comp fun y ↦ A (leftConfigOfFin x) y * v y).symm

/-- The operator-Schmidt ranks of a left operator bound the MPS bond growth of every vector
in the viable set. LVV13, arXiv:1307.5143v1, `algo53.tex`, Claim `c:errorreduction`, line 591.
The effective input bond bound is `max 1 b`, as in `IsLeftOpenMPS`. -/
theorem IsLeftOpenMPS.toEuclideanLin (hi : i ≤ L) {b D : ℕ}
    {v : LeftBlockVector L q i} (hv : IsLeftOpenMPS b v) (A : LeftBlockMatrix L q i)
    (hA : ∀ k : ℕ, 0 < k → k < i →
      operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin i ↦ q) (leftBlock i k)
        (A.submatrix leftConfigOfFin leftConfigOfFin)) ≤ D) :
    IsLeftOpenMPS (D * max 1 b) (toEuclideanLin A v) := by
  let w : EuclideanSpace ℂ (Fin i → Fin q) := WithLp.toLp 2 fun x ↦ v (leftConfigOfFin x)
  have hw := (show IsOpenMPS i q (max 1 b) (fun x ↦ w x) from hv).toEuclideanLin
    (A.submatrix leftConfigOfFin leftConfigOfFin) hA
  change IsOpenMPS i q (max 1 (D * max 1 b))
    (fun x ↦ Matrix.toEuclideanLin A v (leftConfigOfFin x))
  rw [leftConfigOfFin_toEuclideanLin hi]
  apply isOpenMPS_of_internal_cutMatrix_rank_le
    (Matrix.toEuclideanLin (A.submatrix leftConfigOfFin leftConfigOfFin) w)
  intro k hk0 hki
  exact (hw.rank_cutMatrix_le hk0 hki).trans (le_max_right 1 (D * max 1 b))

end TNLean.MPS.AreaLaw
