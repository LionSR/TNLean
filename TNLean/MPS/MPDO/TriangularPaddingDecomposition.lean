/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.TriangularPhysicalPadding
import TNLean.MPS.MPDO.BoundaryTransport

/-!
# Exact decompositions under triangular physical padding

Padding every physical letter of an exact biorthogonal decomposition in the
same upper-left corner or upper-right column preserves the decomposition.
Its index type, multiplicities, analysis matrices, and synthesis matrices are
unchanged. The assertion also includes an empty target index type.

These are coordinate transports of the fusion and action decompositions in
Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `fusiontensors`,
`eq:orthoW`, `fusiontensors2`, and `eq:orthoV`.
-/

open scoped Matrix BigOperators

namespace MPSTensor.IsBiorthogonalDecomposition

variable {ι : Type*} [Fintype ι] {d D : ℕ} {δ : ι → ℕ}
  {V : ∀ c : ι, Matrix (Fin (δ c)) (Fin D) ℂ}
  {W : ∀ c : ι, Matrix (Fin D) (Fin (δ c)) ℂ}

/-- Upper-left physical padding transports an exact operator decomposition
with precisely the same rectangular analysis and synthesis matrices. -/
theorem operatorPhysicalPadding {O : MPOTensor d D}
    {T : ∀ c : ι, MPOTensor d (δ c)}
    (h : IsBiorthogonalDecomposition O.toMPSTensor (fun c ↦ (T c).toMPSTensor) V W) :
    IsBiorthogonalDecomposition (MPOTensor.operatorPhysicalPadding O).toMPSTensor
      (fun c ↦ (MPOTensor.operatorPhysicalPadding (T c)).toMPSTensor) V W where
  retract := h.retract
  orthogonal := h.orthogonal
  letter q := by
    change MPOTensor.operatorPhysicalPadding O q.divNat q.modNat =
      ∑ c : ι, W c * MPOTensor.operatorPhysicalPadding (T c) q.divNat q.modNat * V c
    generalize q.divNat = i, q.modNat = j
    cases i using Fin.lastCases with
    | last => simp
    | cast i =>
      cases j using Fin.lastCases with
      | last => simp
      | cast j =>
        simpa [MPOTensor.toMPSTensor] using h.letter (finProdFinEquiv (i, j))

/-- Upper-right physical padding transports an exact state decomposition
with precisely the same rectangular analysis and synthesis matrices. -/
theorem statePhysicalPadding {B : MPSTensor d D}
    {A : ∀ c : ι, MPSTensor d (δ c)}
    (h : IsBiorthogonalDecomposition B A V W) :
    IsBiorthogonalDecomposition (MPOTensor.statePhysicalPadding B).toMPSTensor
      (fun c ↦ (MPOTensor.statePhysicalPadding (A c)).toMPSTensor) V W where
  retract := h.retract
  orthogonal := h.orthogonal
  letter q := by
    change MPOTensor.statePhysicalPadding B q.divNat q.modNat =
      ∑ c : ι, W c * MPOTensor.statePhysicalPadding (A c) q.divNat q.modNat * V c
    generalize q.divNat = i, q.modNat = j
    cases i using Fin.lastCases with
    | last => simp
    | cast i =>
      cases j using Fin.lastCases with
      | last => simpa using h.letter i
      | cast j => simp

end MPSTensor.IsBiorthogonalDecomposition
