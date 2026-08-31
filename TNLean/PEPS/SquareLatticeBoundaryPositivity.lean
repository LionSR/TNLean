/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.LPDO
import TNLean.PEPS.SquareLatticeBoundaryMPO

/-!
# Positivity of the local square-lattice PEPS boundary tensor

Under the PEPS renormalization hypothesis, arXiv:1606.00608, lines 716--724,
identifies the contraction in FigureDavid1 with the tensor of the boundary
theory. The same algebraic contraction is a Gram contraction for every
rank-five tensor: the contracted PEPS physical and inward virtual indices form
its local purification ancilla, and the horizontal PEPS virtual space is its
purifying bond. Consequently this contraction is an LPDO and hence an MPDO.

These are stronger algebraic positivity results for the displayed contraction,
not a formalization of the RFP-dependent identification with the boundary
theory. They do not select a row-transfer fixed point or assert the
under-specified boundary renormalization equations shown later in FigureDavid2.
-/

namespace TNLean
namespace PEPS

variable {d Dh Dv : ℕ}

/-- The contraction pattern displayed in FigureDavid1 is a locally purifiable
density operator for every rank-five tensor. Its ancillary coordinate is the
pair consisting of the contracted PEPS physical index and the contracted
inward virtual index, while its purifying bond is the horizontal PEPS virtual
space.

ArXiv:1606.00608, lines 716--724, uses the PEPS RFP hypothesis to identify this
contraction with the boundary-theory tensor. The theorem proves the stronger
algebraic positivity statement for arbitrary `A`; it does not formalize that
identification, select a row-transfer fixed point, or assert the boundary
renormalization equations of FigureDavid2. -/
theorem localBoundaryMPOTensor_isLPDO
    (A : Fin Dh → Fin Dh → Fin Dv → Fin Dv → Fin d → ℂ) :
    MPOTensor.IsLPDO (localBoundaryMPOTensor A) := by
  refine ⟨d * Dv, Dh,
    (fun up k ↦ Matrix.of fun left right ↦
      A left right up k.modNat k.divNat),
    (finProdFinEquiv (m := Dh) (n := Dh)).symm, ?_⟩
  intro upKet upBra
  ext left right
  rw [localBoundaryMPOTensor_apply, Matrix.submatrix_apply, Matrix.sum_apply]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin d × Fin Dv ≃ Fin (d * Dv))]
  rw [Fintype.sum_prod_type]
  simp_rw [Matrix.kroneckerMap_apply, Matrix.map_apply, Matrix.of_apply,
    MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat]
  rfl

/-- The contraction pattern displayed in FigureDavid1 generates a positive
semidefinite matrix product operator on every nonempty chain for every
rank-five tensor.

ArXiv:1606.00608, lines 716--724, invokes the PEPS RFP hypothesis when it
identifies this contraction with the boundary-theory tensor. The present
result concerns only the algebraic contraction and follows from its explicit
local purification; it is independent of the under-specified fixed-point and
channel constructions at lines 725--729. -/
theorem localBoundaryMPOTensor_isMPDO
    (A : Fin Dh → Fin Dh → Fin Dv → Fin Dv → Fin d → ℂ) :
    MPOTensor.IsMPDO (localBoundaryMPOTensor A) :=
  (localBoundaryMPOTensor_isLPDO A).isMPDO

end PEPS
end TNLean
