/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Defs
import TNLean.MPS.Core.PhysicalRotation
import QICLean.Kraus.Word

/-!
# Boundary vectors under isometric bond compression

An isometric inclusion intertwining two matrix families carries boundary
matrices of the smaller family to boundary matrices of the larger family.
If the larger family's rows are supported on the included space, the
positive-length periodic vectors also agree. These are the compression
identities used at the endpoints of the direct-sum interpolation in
arXiv:1010.3732, Section II.F.2, equation `eq:sym:omega-gamma`.
-/

open scoped Matrix

namespace MPSTensor

/-- An isometric bond intertwiner transports every open-boundary vector.
Source context: arXiv:1010.3732, Section II.F.2,
`eq:sym:omega-gamma`, restriction to an endpoint summand. -/
theorem groundSpaceMap_eq_of_isometric_bond_intertwiner
    {d D E : ℕ} (A : MPSTensor d D) (B : MPSTensor d E)
    (V : Matrix (Fin D) (Fin E) ℂ) (hV : Vᴴ * V = 1)
    (hInt : ∀ i, A i * V = V * B i) (L : ℕ)
    (X : Matrix (Fin E) (Fin E) ℂ) :
    groundSpaceMap A L (V * X * Vᴴ) = groundSpaceMap B L X := by
  ext σ
  simp only [groundSpaceMap_apply]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Kraus.evalWord_intertwine A B V hInt,
    Matrix.mul_assoc V, Matrix.trace_mul_cycle, hV, Matrix.one_mul]

/-- The smaller boundary space is contained in the larger one under an
isometric bond intertwiner. Source context: arXiv:1010.3732,
Section II.F.2, `eq:sym:omega-gamma`, endpoint parent comparison. -/
theorem groundSpace_le_of_isometric_bond_intertwiner
    {d D E : ℕ} (A : MPSTensor d D) (B : MPSTensor d E)
    (V : Matrix (Fin D) (Fin E) ℂ) (hV : Vᴴ * V = 1)
    (hInt : ∀ i, A i * V = V * B i) (L : ℕ) :
    groundSpace B L ≤ groundSpace A L := by
  rintro x ⟨X, rfl⟩
  exact ⟨V * X * Vᴴ, groundSpaceMap_eq_of_isometric_bond_intertwiner A B V hV hInt L X⟩

/-- Row support on an isometric invariant bond subspace preserves the trace
of every nonempty word. Source context: arXiv:1010.3732,
Section II.F.2, `eq:sym:omega-gamma`, endpoint periodic states. -/
theorem trace_evalWord_eq_of_supported_isometric_bond_intertwiner
    {d D E : ℕ} (A : MPSTensor d D) (B : MPSTensor d E)
    (V : Matrix (Fin D) (Fin E) ℂ) (hV : Vᴴ * V = 1)
    (hInt : ∀ i, A i * V = V * B i)
    (hSupport : ∀ i, V * Vᴴ * A i = A i)
    (w : List (Fin d)) (hw : w ≠ []) :
    (Kraus.evalWord A w).trace = (Kraus.evalWord B w).trace := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons i w =>
    have hsupp : V * Vᴴ * Kraus.evalWord A (i :: w) =
        Kraus.evalWord A (i :: w) := by
      rw [Kraus.evalWord_cons, ← Matrix.mul_assoc, hSupport]
    rw [← hsupp, Matrix.trace_mul_cycle, Kraus.evalWord_intertwine A B V hInt,
      Matrix.trace_mul_cycle, hV, Matrix.one_mul]

/-- The periodic MPS vectors agree at every positive length under supported
isometric bond compression. The empty word is excluded, since its trace
records the bond dimension. Source context: arXiv:1010.3732,
Section II.F.2, `eq:sym:omega-gamma`. -/
theorem mpv_eq_of_supported_isometric_bond_intertwiner
    {d D E N : ℕ} (A : MPSTensor d D) (B : MPSTensor d E)
    (V : Matrix (Fin D) (Fin E) ℂ) (hV : Vᴴ * V = 1)
    (hInt : ∀ i, A i * V = V * B i)
    (hSupport : ∀ i, V * Vᴴ * A i = A i)
    (hN : 0 < N) (σ : Cfg d N) : mpv A σ = mpv B σ := by
  apply trace_evalWord_eq_of_supported_isometric_bond_intertwiner A B V hV hInt hSupport
  exact mt List.ofFn_eq_nil_iff.mp (Nat.ne_of_gt hN)

/-- Physical covariance descends through an isometric bond intertwiner
when the virtual gauge preserves the included subspace.
Source context: arXiv:1010.3732, Section II.F.2,
`eq:1d-sym:jointsym`, restriction of endpoint symmetries. -/
theorem rotatePhysical_gauge_covariance_of_isometric_bond_intertwiner
    {d D E : ℕ} (A : MPSTensor d D) (B : MPSTensor d E)
    (V : Matrix (Fin D) (Fin E) ℂ) (hV : Vᴴ * V = 1)
    (hInt : ∀ i, A i * V = V * B i)
    (U : Matrix (Fin d) (Fin d) ℂ) (X : GL (Fin D) ℂ) (Y : GL (Fin E) ℂ)
    (hXY : (X : Matrix (Fin D) (Fin D) ℂ) * V = V * (Y : Matrix (Fin E) (Fin E) ℂ))
    (hCov : ∀ i, rotatePhysical U A i =
      (X : Matrix (Fin D) (Fin D) ℂ) * A i * X.inv) (i : Fin d) :
    rotatePhysical U B i = (Y : Matrix (Fin E) (Fin E) ℂ) * B i * Y.inv := by
  have hInv : (X.inv : Matrix (Fin D) (Fin D) ℂ) * V = V * Y.inv := by
    have h := congrArg (fun M => (X.inv : Matrix (Fin D) (Fin D) ℂ) * M *
      (Y.inv : Matrix (Fin E) (Fin E) ℂ)) hXY
    simp only [← Matrix.mul_assoc, X.inv_val, Matrix.one_mul] at h
    simpa only [Matrix.mul_assoc, Y.val_inv, Matrix.mul_one] using h.symm
  have hrot : rotatePhysical U A i * V = V * rotatePhysical U B i := by
    simp only [rotatePhysical, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
      Matrix.mul_smul, hInt]
  rw [hCov, Matrix.mul_assoc, hInv, Matrix.mul_assoc,
    ← Matrix.mul_assoc (A i), hInt, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, hXY] at hrot
  have h := congrArg (fun M => Vᴴ * M) hrot
  simpa only [← Matrix.mul_assoc, hV, Matrix.one_mul] using h.symm

end MPSTensor
