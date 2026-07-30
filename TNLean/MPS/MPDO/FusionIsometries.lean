/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Module.Submodule.LinearMap
import TNLean.MPS.Core.BlockingTransfer
import TNLean.MPS.MPDO.PureRecovery
import TNLean.MPS.MPDO.RFP

/-!
# Transfer-retract formulations of the MPDO renormalization fixed point

These definitions isolate the transfer-map content underlying the
fusion-isometry picture of arXiv:1606.00608 Section 4.5
(Cirac–Pérez-García–Schuch–Verstraete): they record when the blocked transfer
map factors through its support algebra as a retract, which is the idempotence
criterion, not the physical fusion isometry of two tensors into one. For each
blocked size `n ≥ 1`, the doubled-index blocked tensor of an MPO has a blocked
transfer map `Eₙ` acting on bond-space matrices, and the support algebra is
modeled by a subspace through which `Eₙ` factors as a retract.

Concretely, `TransferRetractData M n` specifies a support subspace `𝒜ₙ`, a
forward map `Tₙ : M_D(ℂ) → 𝒜ₙ`, and a backward map `Sₙ : 𝒜ₙ → M_D(ℂ)` with
`Tₙ ∘ Sₙ = id_{𝒜ₙ}` and `Sₙ ∘ Tₙ = Eₙ`. The retract identity forces
`Eₙ² = Eₙ`; conversely any idempotent blocked transfer map factors through its
range. This yields an equivalence between `MPOTensor.IsRFP` and the
transfer-retract formulation.

The physical fusion isometries of Theorem 4.14(iii) are the object
`BNTFusionIsometryFamily`, recorded in
`TNLean/MPS/MPDO/BNTFusionIsometries.lean`.

## Main declarations

* `blockedTransferMap`: the transfer map of the `n`-site blocked doubled-index
  MPS tensor.
* `TransferRetractData`: retract structure whose characteristic identity is the
  blocked transfer map.
* `IsRFP_MPDO_via_transferRetract`: existence of such structures for every positive blocked
  size.
* `isRFP_MPDO_via_transferRetract_iff_isRFP`: equivalence with the MPDO RFP predicate.
* `MPSTensor.toMPOTensor_isRFP_MPDO_via_transferRetract_iff_isTransferIdempotent`:
  pure-state recovery for the diagonal MPO embedding.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608, Section 4.5
  (Cirac–Pérez-García–Schuch–Verstraete, Ann. Phys. 378, 100–149).
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- The bond-space matrix algebra on which the blocked transfer map acts. -/
abbrev FusionBondSpace (D : ℕ) : Type :=
  Matrix (Fin D) (Fin D) ℂ

/-! ## Transfer-map-level retract data -/

/-- The blocked transfer map of an MPO tensor, obtained by viewing `M` as a
Doubled-index MPS tensor and blocking `n` physical sites. -/
noncomputable def blockedTransferMap (M : MPOTensor d D) (n : ℕ) :
    FusionBondSpace D →ₗ[ℂ] FusionBondSpace D :=
  MPSTensor.transferMap
    (d := MPSTensor.blockPhysDim (d * d) n) (D := D)
    (MPSTensor.blockTensor (d := d * d) (D := D) M.toMPSTensor n)

/-- Blocking an MPO tensor in the doubled-index MPS picture raises the transfer
map to the corresponding power. -/
@[simp] theorem blockedTransferMap_eq_pow (M : MPOTensor d D) (n : ℕ) :
    blockedTransferMap M n = (transferMap M) ^ n := by
  simpa only [blockedTransferMap, transferMap_eq_toMPSTensor] using
    (MPSTensor.transferMap_blockTensor (A := M.toMPSTensor) (L := n))

/-- At blocked size `1`, the blocked transfer map is the original transfer map. -/
@[simp] theorem blockedTransferMap_one (M : MPOTensor d D) :
    blockedTransferMap M 1 = transferMap M := by
  rw [blockedTransferMap_eq_pow (M := M), pow_one]

/-- Transfer-retract datum at blocked size `n`.

A support subspace of bond-space matrices together with a retract whose
characteristic map is the blocked transfer map.  This is the
transfer-map-level content of the idempotence criterion, not the paper's
physical fusion isometry (see `BNTFusionIsometryFamily` for those). -/
structure TransferRetractData (M : MPOTensor d D) (n : ℕ) where
  /-- The support subspace through which the blocked transfer map factors. -/
  supportAlgebra : Submodule ℂ (FusionBondSpace D)
  /-- Forward map `T_n : M_D(ℂ) → 𝒜_n`. -/
  T : FusionBondSpace D →ₗ[ℂ] supportAlgebra
  /-- Backward map `S_n : 𝒜_n → M_D(ℂ)`. -/
  S : supportAlgebra →ₗ[ℂ] FusionBondSpace D
  /-- The retract identity `T_n ∘ S_n = id_{𝒜_n}`. -/
  hTS : T ∘ₗ S = LinearMap.id
  /-- The characteristic identity `S_n ∘ T_n = E_n` for the blocked transfer
  map `E_n`. -/
  hST : S ∘ₗ T = blockedTransferMap M n

namespace TransferRetractData

variable {M : MPOTensor d D} {n : ℕ}

/-- Any transfer-retract witness forces the blocked transfer map at the same
size to be idempotent. -/
theorem blockedTransferMap_idempotent (F : TransferRetractData M n) :
    blockedTransferMap M n ∘ₗ blockedTransferMap M n = blockedTransferMap M n := by
  calc
    blockedTransferMap M n ∘ₗ blockedTransferMap M n
        = (F.S ∘ₗ F.T) ∘ₗ (F.S ∘ₗ F.T) := by rw [F.hST]
    _ = F.S ∘ₗ (F.T ∘ₗ F.S) ∘ₗ F.T := by simp only [LinearMap.comp_assoc]
    _ = F.S ∘ₗ LinearMap.id ∘ₗ F.T := by rw [F.hTS]
    _ = F.S ∘ₗ F.T := by
      simp only [LinearMap.id_comp]
    _ = blockedTransferMap M n := F.hST

/-- An idempotent blocked transfer map yields a canonical transfer-retract
witness by factoring through its range. -/
noncomputable def ofBlockedTransferMapIdempotent
    (hE : blockedTransferMap M n ∘ₗ blockedTransferMap M n = blockedTransferMap M n) :
    TransferRetractData M n where
  supportAlgebra := (blockedTransferMap M n).range
  T := LinearMap.codRestrict (blockedTransferMap M n).range (blockedTransferMap M n)
    (fun x => ⟨x, rfl⟩)
  S := (blockedTransferMap M n).range.subtype
  hTS := by
    apply LinearMap.ext
    intro x
    rcases x with ⟨x, hx⟩
    rcases hx with ⟨y, rfl⟩
    apply Subtype.ext
    change blockedTransferMap M n (blockedTransferMap M n y) = blockedTransferMap M n y
    simpa only [LinearMap.comp_apply] using congrArg (fun f => f y) hE
  hST :=
    LinearMap.subtype_comp_codRestrict
      (blockedTransferMap M n)
      (blockedTransferMap M n).range
      (fun x => ⟨x, rfl⟩)

/-- A level-`1` transfer-retract witness implies the MPDO RFP condition. -/
theorem isRFP (F : TransferRetractData M 1) : IsRFP M := by
  simpa only [IsRFP, blockedTransferMap_one] using F.blockedTransferMap_idempotent

end TransferRetractData

/-- A one-site transfer-retract datum is equivalent to the MPDO RFP condition.

The forward direction is the retract calculation
\(E_1^2 = S_1T_1S_1T_1 = S_1T_1\).  The reverse direction factors the
idempotent transfer map through its range.  This is a definitional unfolding:
the source's Appendix C.4 constructs physical trace-preserving CP maps on the
physical indices, not this bond-space retract. -/
theorem transferRetractData_one_iff_isRFP (M : MPOTensor d D) :
    Nonempty (TransferRetractData M 1) ↔ IsRFP M := by
  constructor
  · rintro ⟨F⟩
    exact F.isRFP
  · intro hM
    exact ⟨TransferRetractData.ofBlockedTransferMapIdempotent
      (M := M) (n := 1) (by simpa only [IsRFP, blockedTransferMap_one] using hM)⟩

/-- If `M` is already an MPDO renormalization fixed point, then every positive
blocked transfer map coincides with the original transfer map. -/
theorem blockedTransferMap_eq_transferMap_of_isRFP {M : MPOTensor d D}
    (hM : IsRFP M) {n : ℕ} (hn : 0 < n) :
    blockedTransferMap M n = transferMap M := by
  have hIdem : IsIdempotentElem (transferMap M) := hM
  simpa only [blockedTransferMap_eq_pow] using hIdem.pow_eq (Nat.ne_of_gt hn)

/-- Under the MPDO RFP condition, every positive blocked transfer map is
idempotent. -/
theorem blockedTransferMap_idempotent_of_isRFP {M : MPOTensor d D}
    (hM : IsRFP M) {n : ℕ} (hn : 0 < n) :
    blockedTransferMap M n ∘ₗ blockedTransferMap M n = blockedTransferMap M n := by
  rw [blockedTransferMap_eq_transferMap_of_isRFP hM hn]
  exact hM

/-- Transfer-retract formulation of the MPDO RFP condition.

For every positive blocked size `n`, the blocked transfer map of `M` factors as
`S_n ∘ T_n` through some support subspace `𝒜_n`, with `T_n ∘ S_n = id_{𝒜_n}`. -/
def IsRFP_MPDO_via_transferRetract (M : MPOTensor d D) : Prop :=
  ∀ n : ℕ, 0 < n → Nonempty (TransferRetractData M n)

/-- The transfer-retract formulation implies the MPDO RFP condition. -/
theorem isRFP_of_isRFP_MPDO_via_transferRetract {M : MPOTensor d D}
    (hM : IsRFP_MPDO_via_transferRetract M) : IsRFP M := by
  obtain ⟨F⟩ := hM 1 Nat.one_pos
  exact F.isRFP

/-- An MPDO renormalization fixed point admits transfer-retract structures at
every positive blocking size. -/
theorem isRFP_MPDO_via_transferRetract_of_isRFP {M : MPOTensor d D}
    (hM : IsRFP M) : IsRFP_MPDO_via_transferRetract M := by
  intro n hn
  exact ⟨TransferRetractData.ofBlockedTransferMapIdempotent
    (M := M)
    (n := n)
    (blockedTransferMap_idempotent_of_isRFP hM hn)⟩

/-- The transfer-retract formulation is equivalent to the current mixed-state
RFP predicate. -/
theorem isRFP_MPDO_via_transferRetract_iff_isRFP (M : MPOTensor d D) :
    IsRFP_MPDO_via_transferRetract M ↔ IsRFP M := by
  constructor
  · exact isRFP_of_isRFP_MPDO_via_transferRetract
  · exact isRFP_MPDO_via_transferRetract_of_isRFP

/-- The all-blocked transfer-retract formulation is equivalent to a one-site
transfer-retract datum.

Follows from the equivalence with `IsRFP` and the one-site criterion. -/
theorem isRFP_MPDO_via_transferRetract_iff_transferRetractData_one (M : MPOTensor d D) :
    IsRFP_MPDO_via_transferRetract M ↔ Nonempty (TransferRetractData M 1) := by
  rw [isRFP_MPDO_via_transferRetract_iff_isRFP, transferRetractData_one_iff_isRFP]

end MPOTensor

namespace MPSTensor

open MPOTensor

variable {d D : ℕ}

/-- For a pure MPS embedded diagonally as an MPO, the transfer-retract
formulation recovers the original pure-state RFP condition. -/
theorem toMPOTensor_isRFP_MPDO_via_transferRetract_iff_isTransferIdempotent (A : MPSTensor d D) :
    MPOTensor.IsRFP_MPDO_via_transferRetract A.toMPOTensor ↔ IsTransferIdempotent A := by
  rw [MPOTensor.isRFP_MPDO_via_transferRetract_iff_isRFP,
    toMPOTensor_isRFP_iff_isTransferIdempotent]

end MPSTensor
