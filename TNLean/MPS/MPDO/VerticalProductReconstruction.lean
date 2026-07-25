/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.VerticalBlockedOperatorRepresentations
import TNLean.MPS.MPDO.VerticalCoisometry
import TNLean.MPS.MPDO.HorizontalBlocking
import TNLean.MPS.CanonicalForm.BNTCharacterization
import TNLean.MPS.CanonicalForm.BNTTransport
import TNLean.MPS.CanonicalForm.NormalCommutant
import TNLean.MPS.MPDO.FigureEightPairwise
import TNLean.MPS.MPDO.BNTFusionCoisometries
import TNLean.MPS.MPDO.NormalizedGroupedSectors
import TNLean.MPS.MPDO.VerticalBNTConstruction
import TNLean.MPS.MPDO.VerticalBNT
import TNLean.MPS.MPDO.VerticalSpectral

/-!
# Coisometric reconstruction of retained vertical products

This file establishes the coisometric reconstruction and retained-copy
coordinates used in the positive fusion decomposition of CPSV16,
Appendix C.4.

## Main results

* `MPSTensor.projectorClosure_and_noPeriodicVectors_of_coisometry_reconstruction`:
  descent of the two canonical spectral properties through an exact
  coisometric reconstruction.
* `verticalCoisometrySquare`: the coisometry induced on the product bond.
* `verticalCopyCoordinateEquiv`: coordinates indexed by a retained BNT copy
  and its internal bond coordinate.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.4, lines 2020--2029
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

noncomputable section

namespace MPSTensor

/-- Projector closure and absence of periodic vectors pass through an exact
coisometric reconstruction.

If $U$ maps the ambient bond space onto retained coordinates, then $U^\dagger$
is an isometry intertwining the retained tensor with the ambient tensor. Exact
reconstruction makes its range reducing, so projector closure descends by
compression and every peripheral eigenvector of the retained tensor is also
one of the ambient tensor.

Source: CPSV16, canonical nonzero-sector decomposition at lines 214--230. -/
theorem projectorClosure_and_noPeriodicVectors_of_coisometry_reconstruction
    {d D n : ℕ} (A : MPSTensor d D) (C : MPSTensor d n)
    (U : Matrix (Fin n) (Fin D) ℂ) (hU : U * Uᴴ = 1)
    (hreconstruct : ∀ i, A i = Uᴴ * C i * U)
    (hClosure : HasInvariantProjectorClosure A)
    (hPer : HasNoPeriodicVectors A) :
    HasInvariantProjectorClosure C ∧ HasNoPeriodicVectors C := by
  let V : Matrix (Fin D) (Fin n) ℂ := Uᴴ
  have hV : Vᴴ * V = 1 := by
    simpa [V] using hU
  have hint : ∀ i, A i * V = V * C i := by
    intro i
    calc
      A i * V = (Uᴴ * C i * U) * Uᴴ := by rw [hreconstruct]
      _ = Uᴴ * C i * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
      _ = V * C i := by rw [hU, Matrix.mul_one]
  have hComm : ∀ i, A i * (V * Vᴴ) = (V * Vᴴ) * A i := by
    intro i
    have hsupportLeft : A i * (V * Vᴴ) = A i := by
      calc
        A i * (V * Vᴴ) = (A i * V) * Vᴴ := (Matrix.mul_assoc _ _ _).symm
        _ = (V * C i) * Vᴴ := by rw [hint]
        _ = A i := by simpa [V] using (hreconstruct i).symm
    have hsupportRight : (V * Vᴴ) * A i = A i := by
      calc
        (V * Vᴴ) * A i = (V * Vᴴ) * (V * C i * Vᴴ) := by
          rw [show A i = V * C i * Vᴴ by simpa [V] using hreconstruct i]
        _ = V * C i * Vᴴ := by
          simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V, hV,
            Matrix.one_mul]
        _ = A i := by simpa [V] using (hreconstruct i).symm
    rw [hsupportLeft, hsupportRight]
  have hcompress : (fun i => Vᴴ * A i * V) = C := by
    funext i
    calc
      Vᴴ * A i * V = Vᴴ * (V * C i * Vᴴ) * V := by
        rw [show A i = V * C i * Vᴴ by simpa [V] using hreconstruct i]
      _ = C i := by
        simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V, hV,
          Matrix.one_mul, Matrix.mul_one]
  constructor
  · rw [← hcompress]
    exact hasInvariantProjectorClosure_compress_of_commutes A hClosure V hV hComm
  · exact hPer.of_isometry_intertwine V hV hint

end MPSTensor

namespace MPOTensor

/-- The Kronecker square of a rectangular vertical coisometry, with both
product index spaces encoded by the standard finite-product equivalence. -/
noncomputable def verticalCoisometrySquare {d n : ℕ}
    (U : Matrix (Fin n) (Fin d) ℂ) :
    Matrix (Fin (n * n)) (Fin (d * d)) ℂ :=
  (U ⊗ₖ U).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

/-- The Kronecker square of a coisometry is again a coisometry. -/
theorem verticalCoisometrySquare_isCoisometry {d n : ℕ}
    (U : Matrix (Fin n) (Fin d) ℂ) (hU : U * Uᴴ = 1) :
    verticalCoisometrySquare U * (verticalCoisometrySquare U)ᴴ = 1 := by
  unfold verticalCoisometrySquare
  rw [Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv.symm _,
    Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU,
    Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

private def verticalCopyLabelEquiv {g : ℕ} (dim mult : Fin g → ℕ) :
    ((α : Fin g) × (Fin (mult α) × Fin (dim α))) ≃
      (p : (α : Fin g) × Fin (mult α)) × Fin (dim p.1) where
  toFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun x := ⟨x.1.1, (x.1.2, x.2)⟩
  left_inv x := by
    rcases x with ⟨α, q, i⟩
    rfl
  right_inv x := by
    rcases x with ⟨⟨α, q⟩, i⟩
    rfl

/-- The assembled vertical bond coordinates, grouped first by a retained BNT
copy and then by a coordinate in its simple bond space.

Source: CPSV16, Appendix C.4, lines 1955--1971. -/
def verticalCopyCoordinateEquiv {g : ℕ} (dim mult : Fin g → ℕ) :
    Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q) ≃
      (p : (α : Fin g) × Fin (mult α)) × Fin (dim p.1) :=
  (verticalSectorFinEquiv dim mult).symm.trans
    (verticalCopyLabelEquiv dim mult)

/-- The inverse copy-coordinate map is the canonical vertical-sector
coordinate map.

Source: CPSV16, Appendix C.4, lines 1955--1971. -/
@[simp]
theorem verticalCopyCoordinateEquiv_symm_apply
    {g : ℕ} (dim mult : Fin g → ℕ)
    (p : (α : Fin g) × Fin (mult α)) (i : Fin (dim p.1)) :
    (verticalCopyCoordinateEquiv dim mult).symm ⟨p, i⟩ =
      verticalSectorFinEquiv dim mult ⟨p.1, (p.2, i)⟩ := by
  rfl

end MPOTensor
