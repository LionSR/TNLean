/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.LPDO
import TNLean.PEPS.SquareLatticeBoundaryMPO

/-!
# Positivity of the local square-lattice PEPS boundary tensor

The local tensor in FigureDavid1 of arXiv:1606.00608 is a Gram contraction.
The contracted PEPS physical and inward virtual indices form its local
purification ancilla, and the horizontal PEPS virtual space is its purifying
bond. Consequently the tensor is an LPDO and hence an MPDO.

These are local positivity results only. They do not select a row-transfer
fixed point or assert the under-specified boundary renormalization equations
shown later in FigureDavid2.
-/

namespace TNLean
namespace PEPS

variable {d Dh Dv : ℕ}

/-- The local boundary tensor in FigureDavid1 is a locally purifiable density
operator. Its ancillary coordinate is the pair consisting of the contracted
PEPS physical index and the contracted inward virtual index, while its
purifying bond is the horizontal PEPS virtual space.

This is only the local positivity statement implicit in FigureDavid1 of
arXiv:1606.00608, lines 721--724. It does not select a row-transfer fixed point
or assert the boundary renormalization equations of FigureDavid2. -/
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

/-- The local boundary tensor in FigureDavid1 generates a positive
semidefinite matrix product operator on every nonempty chain.

This follows from the explicit local purification of FigureDavid1 in
arXiv:1606.00608, lines 721--724, and is independent of the under-specified
transfer-fixed-point and channel constructions at lines 725--729. -/
theorem localBoundaryMPOTensor_isMPDO
    (A : Fin Dh → Fin Dh → Fin Dv → Fin Dv → Fin d → ℂ) :
    MPOTensor.IsMPDO (localBoundaryMPOTensor A) :=
  (localBoundaryMPOTensor_isLPDO A).isMPDO

end PEPS
end TNLean
