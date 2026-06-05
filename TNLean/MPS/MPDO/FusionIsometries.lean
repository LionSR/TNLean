/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Module.Submodule.LinearMap
import TNLean.MPS.Core.BlockingTransfer
import TNLean.MPS.MPDO.PureRecovery
import TNLean.MPS.MPDO.RFP

/-!
# Fusion-isometry formulations of the MPDO renormalization fixed point

This file gives the **fusion-isometry** side of the equivalence stated in
arXiv:1606.00608 Section 4.5 (Cirac–Pérez-García–Schuch–Verstraete). In the notation
of the paper, a fusion isometry at blocked size `n` is a pair of linear maps
`T`, `S` between the physical space of `n` blocked sites and the corresponding
support algebra of the tensor, with `T ∘ S = id` on the support algebra and
`S ∘ T` the orthogonal projection onto its image in the physical space.
Iterated applications of `T` and `S` reproduce the doubled-tensor transfer-map
dynamics described by `MPOTensor.IsRFP` in `TNLean/MPS/MPDO/RFP.lean`. This file
develops the transfer-map side of the fusion-isometry picture: a
fusion-isometry witness at blocked size `n` is a retract factorization of the
blocked transfer map through a support subspace of bond-space matrices.
Concretely, if `Eₙ` denotes the blocked transfer map of `M`, then
`FusionIsometryData M n` specifies a support subspace `𝒜ₙ`, a forward map
`Tₙ : phys → 𝒜ₙ`, and a backward map `Sₙ : 𝒜ₙ → phys` with
`Tₙ ∘ Sₙ = id_{𝒜ₙ}` and `Sₙ ∘ Tₙ = Eₙ`. The retract identity forces
`Eₙ^2 = Eₙ`; conversely any idempotent blocked transfer map factors through its
range. This yields an equivalence between `MPOTensor.IsRFP` and the
transfer-map-level fusion formulation.

## Main declarations

* `blockedTransferMap`: the transfer map of the `n`-site blocked doubled-index
  MPS tensor.
* `FusionIsometryData`: retract structure whose characteristic identity is the
  blocked transfer map.
* `IsRFP_MPDO_via_fusion`: existence of such structures for every positive blocked
  size.
* `isRFP_MPDO_via_fusion_iff_isRFP`: equivalence with the MPDO RFP predicate.
* `MPSTensor.toMPOTensor_isRFP_MPDO_via_fusion_iff_isRFP`: pure-state recovery
  for the diagonal MPO embedding.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608, Section 4.5 and Appendix C.4
  (Cirac–Pérez-García–Schuch–Verstraete, Ann. Phys. 378, 100–149).
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- The *physical space at blocked size `n`*.

In the present transfer-map formulation this is the bond-space matrix algebra on
which the blocked transfer map acts. -/
abbrev FusionPhysicalSpace (D : ℕ) : Type :=
  Matrix (Fin D) (Fin D) ℂ

/-! ## Transfer-map-level fusion data -/

/-- The blocked transfer map of an MPO tensor, obtained by viewing `M` as a
Doubled-index MPS tensor and blocking `n` physical sites. -/
noncomputable def blockedTransferMap (M : MPOTensor d D) (n : ℕ) :
    FusionPhysicalSpace D →ₗ[ℂ] FusionPhysicalSpace D :=
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

/-- Transfer-map-level fusion-isometry structure at blocked size `n`.

This records the transfer-map part of the paper's fusion-isometry picture: a
support subspace of bond-space matrices together with a retract whose
characteristic map is the blocked transfer map. It is separate from the
Hilbert-space isometry statement for the support algebra. -/
structure FusionIsometryData (M : MPOTensor d D) (n : ℕ) where
  /-- The support subspace through which the blocked transfer map factors. -/
  supportAlgebra : Submodule ℂ (FusionPhysicalSpace D)
  /-- Forward map `T_n : phys → 𝒜_n`. -/
  T : FusionPhysicalSpace D →ₗ[ℂ] supportAlgebra
  /-- Backward map `S_n : 𝒜_n → phys`. -/
  S : supportAlgebra →ₗ[ℂ] FusionPhysicalSpace D
  /-- The retract identity `T_n ∘ S_n = id_{𝒜_n}`. -/
  hTS : T ∘ₗ S = LinearMap.id
  /-- The characteristic identity `S_n ∘ T_n = E_n` for the blocked transfer
  map `E_n`. -/
  hST : S ∘ₗ T = blockedTransferMap M n

namespace FusionIsometryData

variable {M : MPOTensor d D} {n : ℕ}

/-- Any transfer-map-level fusion-isometry witness forces the blocked transfer map
at the same size to be idempotent. -/
theorem blockedTransferMap_idempotent (F : FusionIsometryData M n) :
    blockedTransferMap M n ∘ₗ blockedTransferMap M n = blockedTransferMap M n := by
  calc
    blockedTransferMap M n ∘ₗ blockedTransferMap M n
        = (F.S ∘ₗ F.T) ∘ₗ (F.S ∘ₗ F.T) := by rw [F.hST]
    _ = F.S ∘ₗ (F.T ∘ₗ F.S) ∘ₗ F.T := by simp only [LinearMap.comp_assoc]
    _ = F.S ∘ₗ LinearMap.id ∘ₗ F.T := by rw [F.hTS]
    _ = F.S ∘ₗ F.T := by
      simp only [LinearMap.id_comp]
    _ = blockedTransferMap M n := F.hST

/-- An idempotent blocked transfer map yields a canonical fusion-isometry witness
by factoring through its range. -/
noncomputable def ofBlockedTransferMapIdempotent
    (hE : blockedTransferMap M n ∘ₗ blockedTransferMap M n = blockedTransferMap M n) :
    FusionIsometryData M n where
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

/-- A level-`1` fusion-isometry witness implies the MPDO RFP condition. -/
theorem isRFP (F : FusionIsometryData M 1) : IsRFP M := by
  simpa only [IsRFP, blockedTransferMap_one] using F.blockedTransferMap_idempotent

end FusionIsometryData

/-- A one-site transfer-map fusion retract is equivalent to the MPDO RFP
condition.

The forward direction is the retract calculation
\(E_1^2 = S_1T_1S_1T_1 = S_1T_1\).  The reverse direction factors the
idempotent transfer map through its range.

Source: arXiv:1606.00608, Theorem IV.13(i), and Appendix C.4, lines
2065--2085 of `Papers/1606.00608/MPDO-22-12-17-2.tex`, where the converse
algebra-to-fusion proof constructs the one-step maps \(T\) and \(S\). -/
theorem fusionIsometryData_one_iff_isRFP (M : MPOTensor d D) :
    Nonempty (FusionIsometryData M 1) ↔ IsRFP M := by
  constructor
  · rintro ⟨F⟩
    exact F.isRFP
  · intro hM
    exact ⟨FusionIsometryData.ofBlockedTransferMapIdempotent
      (M := M) (n := 1) (by simpa only [blockedTransferMap_one] using hM)⟩

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

/-- Transfer-map-level fusion-isometry formulation of the MPDO RFP condition.

For every positive blocked size `n`, the blocked transfer map of `M` factors as
`S_n ∘ T_n` through some support subspace `𝒜_n`, with `T_n ∘ S_n = id_{𝒜_n}`. -/
def IsRFP_MPDO_via_fusion (M : MPOTensor d D) : Prop :=
  ∀ n : ℕ, 0 < n → Nonempty (FusionIsometryData M n)

/-- The transfer-map-level fusion formulation implies the MPDO RFP condition. -/
theorem isRFP_of_isRFP_MPDO_via_fusion {M : MPOTensor d D}
    (hM : IsRFP_MPDO_via_fusion M) : IsRFP M := by
  obtain ⟨F⟩ := hM 1 Nat.one_pos
  exact F.isRFP

/-- An MPDO renormalization fixed point admits transfer-map-level fusion structures
at every positive blocking size. -/
theorem isRFP_MPDO_via_fusion_of_isRFP {M : MPOTensor d D}
    (hM : IsRFP M) : IsRFP_MPDO_via_fusion M := by
  intro n hn
  exact ⟨FusionIsometryData.ofBlockedTransferMapIdempotent
    (M := M)
    (n := n)
    (blockedTransferMap_idempotent_of_isRFP hM hn)⟩

/-- The transfer-map-level fusion formulation is equivalent to the current
mixed-state RFP predicate. -/
theorem isRFP_MPDO_via_fusion_iff_isRFP (M : MPOTensor d D) :
    IsRFP_MPDO_via_fusion M ↔ IsRFP M := by
  constructor
  · exact isRFP_of_isRFP_MPDO_via_fusion
  · exact isRFP_MPDO_via_fusion_of_isRFP

/-- The all-blocked transfer-map fusion formulation is equivalent to a
one-site fusion retract.

Thus, in the present transfer-map formulation, an algebra-to-fusion proof may
be reduced to constructing the one-step retract appearing in Appendix C.4 of
arXiv:1606.00608. -/
theorem isRFP_MPDO_via_fusion_iff_fusionIsometryData_one (M : MPOTensor d D) :
    IsRFP_MPDO_via_fusion M ↔ Nonempty (FusionIsometryData M 1) := by
  rw [isRFP_MPDO_via_fusion_iff_isRFP, fusionIsometryData_one_iff_isRFP]

end MPOTensor

namespace MPSTensor

open MPOTensor

variable {d D : ℕ}

/-- For a pure MPS embedded diagonally as an MPO, the transfer-map-level
fusion formulation recovers the original pure-state RFP condition. -/
theorem toMPOTensor_isRFP_MPDO_via_fusion_iff_isRFP (A : MPSTensor d D) :
    MPOTensor.IsRFP_MPDO_via_fusion A.toMPOTensor ↔ IsRFP A := by
  rw [MPOTensor.isRFP_MPDO_via_fusion_iff_isRFP, toMPOTensor_isRFP_iff_isRFP]

end MPSTensor
