/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Algebra.Bilinear
import TNLean.Algebra.MatrixFrobenius
import TNLean.Channel.FixedPoint.Algebra
import TNLean.MPS.CanonicalForm.BlockingViaAdjoint
import TNLean.MPS.MPDO.FusionIsometries

/-!
# Algebra-structure witnesses for MPDO renormalization fixed points

This file upgrades the old scaffold for the algebra-structure side of
arXiv:1606.00608, §4.5.

The paper's full statement uses coefficient systems
$c_{\alpha,\beta,\gamma}^{(L)} =
  \operatorname{tr}(\chi_{\alpha,\beta,\gamma}^L)$
and BNT data. That coefficient layer is not yet formalized here. What we do
formalize is the stationary C$^*$-algebra package naturally attached to an MPO
whose blocked transfer maps are idempotent.

More precisely, `AlgebraStructureData` now records a genuine tower of support
`StarSubalgebra`s together with multiplication and inclusion maps realized by the
ambient matrix product and the ambient inclusion. Compatibility with an MPO
tensor `M` means that, for every positive blocked size `n`, the carrier `A n`
coincides with the fixed-point algebra of the adjoint blocked transfer map
`(blockedTransferMap M n).adjoint`.

Under a trace-preserving normalization and a positive-definite fixed point of the
MPO transfer map, an RFP tensor yields a **stationary** algebra tower. Combined
with the transfer-map fusion criterion from `FusionIsometries.lean`, this gives a
one-way bridge

* `isRFP_MPDO_via_algebra_of_isRFP_of_isTP_of_posDef_fixed`
* `isRFP_MPDO_via_algebra_of_isRFP_MPDO_via_fusion_of_isTP_of_posDef_fixed`

from the current fusion formulation to the algebra formulation, under the same
side hypotheses.

## Remaining gap to the paper

The present `CompatibleWith` relation identifies the support algebras with the
adjoint fixed-point algebras of the blocked transfer maps. It does **not** yet
extract the coefficient family `c_{\alpha,\beta,\gamma}^{(L)}` of
Theorem IV.13(ii), nor prove the converse algebra-to-fusion implication. Those
steps still require the BNT / coefficient-comparison layer from Appendix C.3--C.4.

## References

* [CPGSV17] arXiv:1606.00608, §4.5 and Appendix C.3--C.4
* [Wolf12] Wolf, *Quantum Channels & Operations*, Theorem 6.12
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder

noncomputable section

local instance instMatrixNormedAddCommGroup (D : ℕ) :
    NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
  Matrix.toMatrixNormedAddCommGroup (n := Fin D) (𝕜 := ℂ) 1
    (Matrix.frobenius_posDef_one (D := D))

local instance instMatrixInnerProductSpace (D : ℕ) :
    InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
  Matrix.toMatrixInnerProductSpace (n := Fin D) (𝕜 := ℂ) 1
    (Matrix.frobenius_posDef_one (D := D)).posSemidef

namespace MPSTensor

private theorem transferMap_adjoint_apply_eq_adjointMap {d D : ℕ}
    (A : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) :
    (transferMap A).adjoint X = Kraus.adjointMap A X := by
  have h := congrArg (fun F => F X)
    (transferMap_conjTranspose_eq_adjoint (A := A)).symm
  simpa [transferMap_apply, Kraus.adjointMap, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc] using h

end MPSTensor

namespace MPOTensor

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- Algebra-structure data for the stationary support-algebra picture of an MPO.

At blocked size `n`, the support object is a `StarSubalgebra` of bond-space
matrices. The map `m n` is the blocking multiplication, landing in the
size-`2n` support algebra, while `iota n` is the inclusion into the size-`n+1`
support algebra. The fields `m_apply` and `iota_apply` require that these maps
are realized by the ambient matrix product and ambient inclusion. -/
structure AlgebraStructureData (d D : ℕ) where
  /-- Support algebra at blocked size `n`. -/
  A : ℕ → StarSubalgebra ℂ (Matrix (Fin D) (Fin D) ℂ)
  /-- Blocking multiplication at size `n`. -/
  m : ∀ n : ℕ, A n →ₗ[ℂ] A n →ₗ[ℂ] A (2 * n)
  /-- Inclusion map adding one physical site. -/
  iota : ∀ n : ℕ, A n →ₗ[ℂ] A (n + 1)
  /-- `m n` is realized by ambient matrix multiplication. -/
  m_apply : ∀ n : ℕ, ∀ x y : A n,
    ((m n x y : A (2 * n)) : Matrix (Fin D) (Fin D) ℂ) =
      (x : Matrix (Fin D) (Fin D) ℂ) * y
  /-- `iota n` is realized by the ambient inclusion. -/
  iota_apply : ∀ n : ℕ, ∀ x : A n,
    ((iota n x : A (n + 1)) : Matrix (Fin D) (Fin D) ℂ) =
      (x : Matrix (Fin D) (Fin D) ℂ)

namespace AlgebraStructureData

variable {d D : ℕ}

/-- Compatibility between algebra-structure data and an MPO tensor `M`.

The current compatibility condition says that, for every positive blocked size
`n`, the support algebra `A n` is exactly the fixed-point algebra of the
adjoint blocked transfer map. This is a non-vacuous algebra-side condition, but
it is still weaker than the full coefficient statement of Theorem IV.13(ii). -/
def CompatibleWith (data : AlgebraStructureData d D) (M : MPOTensor d D) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ X : Matrix (Fin D) (Fin D) ℂ,
    X ∈ data.A n ↔ (blockedTransferMap M n).adjoint X = X

/-- A constant algebra tower is compatible with `M` as soon as all positive
blocked adjoint transfer maps have the same fixed-point algebra. -/
theorem compatible_of_eq_adjointFixedPoints
    (data : AlgebraStructureData d D) (M : MPOTensor d D)
    (hCompat : ∀ n : ℕ, 0 < n → ∀ X : Matrix (Fin D) (Fin D) ℂ,
      X ∈ data.A n ↔ (blockedTransferMap M n).adjoint X = X) :
    data.CompatibleWith M :=
  hCompat

end AlgebraStructureData

/-- The fixed-point support algebra attached to a trace-preserving MPO tensor and
one of its positive-definite fixed points.

Concretely, this is the fixed-point `StarSubalgebra` of the adjoint transfer map
`(transferMap M).adjoint`, packaged through Wolf Theorem 6.12 for the doubled
MPS tensor `M.toMPSTensor`. -/
noncomputable def faithfulFixedPointSupportAlgebra
    (M : MPOTensor d D) (h_tp : Kraus.IsTP M.toMPSTensor)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : transferMap M ρ = ρ) :
    StarSubalgebra ℂ Mat :=
  Kraus.fixedPoints_starSubalgebra (K := M.toMPSTensor) h_tp hρ
    (by simpa [transferMap_eq_toMPSTensor] using hρ_fix)

/-- Membership in `faithfulFixedPointSupportAlgebra` is fixed-point membership
for the adjoint MPO transfer map. -/
theorem mem_faithfulFixedPointSupportAlgebra_iff
    (M : MPOTensor d D) (h_tp : Kraus.IsTP M.toMPSTensor)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : transferMap M ρ = ρ)
    (X : Mat) :
    X ∈ faithfulFixedPointSupportAlgebra M h_tp hρ hρ_fix ↔
      (transferMap M).adjoint X = X := by
  unfold faithfulFixedPointSupportAlgebra
  rw [Kraus.mem_fixedPoints_starSubalgebra, Kraus.mem_adjointFixedPoints]
  have hAdj : Kraus.adjointMap M.toMPSTensor X = (transferMap M).adjoint X := by
    simpa [transferMap_eq_toMPSTensor] using
      (MPSTensor.transferMap_adjoint_apply_eq_adjointMap (A := M.toMPSTensor) X).symm
  constructor
  · intro h
    rw [hAdj] at h
    exact h
  · intro h
    rw [hAdj]
    exact h

namespace AlgebraStructureData

/-- The stationary algebra tower attached to a faithful fixed point of the MPO
transfer map.

All support algebras are the same `StarSubalgebra`, multiplication is ordinary
matrix multiplication, and the inclusion maps are identities. -/
noncomputable def stationaryOfFaithfulFixedPoint
    (M : MPOTensor d D) (h_tp : Kraus.IsTP M.toMPSTensor)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : transferMap M ρ = ρ) :
    AlgebraStructureData d D := by
  let S : StarSubalgebra ℂ Mat := faithfulFixedPointSupportAlgebra M h_tp hρ hρ_fix
  refine
    { A := fun _ => S
      m := fun _ => LinearMap.mul ℂ ↥S
      iota := fun _ => LinearMap.id
      m_apply := ?_
      iota_apply := ?_ }
  · intro n x y
    rfl
  · intro n x
    rfl

/-- The stationary tower from a faithful fixed point is compatible with any RFP
MPO tensor, because all positive blocked transfer maps agree with `transferMap M`. -/
theorem stationaryOfFaithfulFixedPoint_compatible
    (M : MPOTensor d D) (h_tp : Kraus.IsTP M.toMPSTensor)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : transferMap M ρ = ρ)
    (hRFP : IsRFP M) :
    (stationaryOfFaithfulFixedPoint M h_tp hρ hρ_fix).CompatibleWith M := by
  simp only [AlgebraStructureData.CompatibleWith]
  intro n hn X
  change X ∈ faithfulFixedPointSupportAlgebra M h_tp hρ hρ_fix ↔
    (blockedTransferMap M n).adjoint X = X
  rw [mem_faithfulFixedPointSupportAlgebra_iff (M := M) h_tp hρ hρ_fix X]
  have hAdj : LinearMap.adjoint ((MPSTensor.transferMap M.toMPSTensor) ^ n) =
      LinearMap.adjoint (MPSTensor.transferMap M.toMPSTensor) := by
    simpa [blockedTransferMap_eq_pow, transferMap_eq_toMPSTensor] using
      congrArg LinearMap.adjoint
        (blockedTransferMap_eq_transferMap_of_isRFP (M := M) hRFP hn)
  simp [blockedTransferMap_eq_pow, transferMap_eq_toMPSTensor, hAdj]

end AlgebraStructureData

/-- The algebra-structure formulation of MPDO RFP used in this file.

An MPO tensor satisfies `IsRFP_MPDO_via_algebra` when it admits algebra-structure
support data compatible with its blocked adjoint transfer maps. -/
def IsRFP_MPDO_via_algebra (M : MPOTensor d D) : Prop :=
  ∃ data : AlgebraStructureData d D, data.CompatibleWith M

/-- Backwards-compatible alias for the previous scaffold name.

The old definition was vacuous. The new alias points to the non-vacuous algebra
predicate above. -/
abbrev IsRFP_MPDO_via_algebra_scaffold (M : MPOTensor d D) : Prop :=
  IsRFP_MPDO_via_algebra M

/-- A trace-preserving MPO with a positive-definite fixed point admits a
stationary algebra tower as soon as it is an RFP. -/
theorem isRFP_MPDO_via_algebra_of_isRFP_of_isTP_of_posDef_fixed
    {M : MPOTensor d D} (hRFP : IsRFP M) (h_tp : Kraus.IsTP M.toMPSTensor)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : transferMap M ρ = ρ) :
    IsRFP_MPDO_via_algebra M := by
  refine ⟨AlgebraStructureData.stationaryOfFaithfulFixedPoint M h_tp hρ hρ_fix, ?_⟩
  exact AlgebraStructureData.stationaryOfFaithfulFixedPoint_compatible
    (M := M) (h_tp := h_tp) hρ hρ_fix hRFP

/-- Under the same side hypotheses, the transfer-map fusion formulation implies
this algebra formulation. -/
theorem isRFP_MPDO_via_algebra_of_isRFP_MPDO_via_fusion_of_isTP_of_posDef_fixed
    {M : MPOTensor d D} (hFusion : IsRFP_MPDO_via_fusion M)
    (h_tp : Kraus.IsTP M.toMPSTensor) {ρ : Mat} (hρ : ρ.PosDef)
    (hρ_fix : transferMap M ρ = ρ) :
    IsRFP_MPDO_via_algebra M := by
  exact isRFP_MPDO_via_algebra_of_isRFP_of_isTP_of_posDef_fixed
    (M := M) (isRFP_of_isRFP_MPDO_via_fusion hFusion) h_tp hρ hρ_fix

end MPOTensor

end
