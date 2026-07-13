/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.InverseMapPhysicalSectorFactorization

/-!
# Zero-weight physical-sector reparameterization

If the left tensor of a physical sector vanishes, its right tensor may be replaced by zero
without changing the physical-slice factorization. The neighboring operators whose source is
that sector then vanish, while those with an active source are unchanged.

For the inverse-map factorization, every sector of zero Hayashi weight has vanishing left tensor.
The construction therefore removes the outgoing neighboring contractions of zero-weight sectors
while retaining every physical direct summand.

## References

- [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, equations `formK` and `etarl`, lines 1434--1445
- `docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`
-/

open scoped Matrix BigOperators

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- Replace the right tensor of every inactive sector by zero.

The physical direct sum, its factor spaces, and its physical isometry are retained. The hypothesis
that the left tensor already vanishes on every inactive sector makes the same-sector product
unchanged.

This is the zero-weight reparameterization permitted by the factorization in arXiv:1606.00608,
Appendix C.2, equations `formK` and `etarl`, lines 1434--1445. Its role in removing spurious
outgoing edges from zero-weight Hayashi sectors is recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`. -/
noncomputable def zeroRightTensorOnInactive (F : PhysicalSectorFactorization K)
    (active : Fin F.sectorCount → Prop) [DecidablePred active]
    (hleft : ∀ k, ¬ active k → ∀ beta, F.leftTensor k beta = 0) :
    PhysicalSectorFactorization K where
  sectorCount := F.sectorCount
  leftDim := F.leftDim
  rightDim := F.rightDim
  leftDim_pos := F.leftDim_pos
  rightDim_pos := F.rightDim_pos
  sectorEquiv := F.sectorEquiv
  physicalIsometry := F.physicalIsometry
  physicalIsometry_isometry := F.physicalIsometry_isometry
  leftTensor := F.leftTensor
  rightTensor := fun k alpha ↦ if active k then F.rightTensor k alpha else 0
  factorization := by
    classical
    intro beta alpha
    rw [F.factorization beta alpha]
    congr 1
    funext k
    by_cases hk : active k
    · change Matrix.kroneckerMap (· * ·) (F.leftTensor k beta) (F.rightTensor k alpha) =
        Matrix.kroneckerMap (· * ·) (F.leftTensor k beta)
          (if active k then F.rightTensor k alpha else 0)
      simp [hk]
    · change Matrix.kroneckerMap (· * ·) (F.leftTensor k beta) (F.rightTensor k alpha) =
        Matrix.kroneckerMap (· * ·) (F.leftTensor k beta)
          (if active k then F.rightTensor k alpha else 0)
      simp [hk, hleft k hk beta]

@[simp] private theorem zeroRightTensorOnInactive_leftTensor
    (F : PhysicalSectorFactorization K) (active : Fin F.sectorCount → Prop)
    [DecidablePred active]
    (hleft : ∀ k, ¬ active k → ∀ beta, F.leftTensor k beta = 0)
    (k : Fin F.sectorCount) (beta : Fin D) :
    (F.zeroRightTensorOnInactive active hleft).leftTensor k beta =
      F.leftTensor k beta := rfl

@[simp] private theorem zeroRightTensorOnInactive_rightTensor
    (F : PhysicalSectorFactorization K) (active : Fin F.sectorCount → Prop)
    [DecidablePred active]
    (hleft : ∀ k, ¬ active k → ∀ beta, F.leftTensor k beta = 0)
    (k : Fin F.sectorCount) (alpha : Fin D) :
    (F.zeroRightTensorOnInactive active hleft).rightTensor k alpha =
      if active k then F.rightTensor k alpha else 0 := rfl

/-- The neighboring operator is unchanged on an active source sector and vanishes on an inactive
source sector after the right tensor is replaced by zero.

Source: arXiv:1606.00608, Appendix C.2, equation `etarl`, lines 1441--1445. The
zero-weight application is recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`. -/
theorem zeroRightTensorOnInactive_neighboringOperator
    (F : PhysicalSectorFactorization K) (active : Fin F.sectorCount → Prop)
    [DecidablePred active]
    (hleft : ∀ k, ¬ active k → ∀ beta, F.leftTensor k beta = 0)
    (k h : Fin F.sectorCount) :
    (F.zeroRightTensorOnInactive active hleft).neighboringOperator k h =
      if active k then F.neighboringOperator k h else 0 := by
  classical
  by_cases hk : active k
  · rw [if_pos hk]
    ext x y
    simp [neighboringOperator_apply, hk]
  · rw [if_neg hk]
    apply Matrix.ext
    intro x y
    rw [neighboringOperator_apply]
    simp only [zeroRightTensorOnInactive_leftTensor,
      zeroRightTensorOnInactive_rightTensor, if_neg hk]
    change (∑ _alpha : Fin D, 0 * F.leftTensor h _alpha x.2 y.2) = 0
    simp

end MPOTensor.PhysicalSectorFactorization

namespace MPOTensor

variable {d D : ℕ}
variable {rho : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}

/-- A zero Hayashi weight makes the corresponding inverse-map left tensor vanish.

Source: arXiv:1606.00608, Appendix C.2, equations `Qketc` and `formK`, lines 1415--1439;
the factor $p_k$ is attached to the left tensor in the chosen factorization. The zero-weight
boundary is recorded in `docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`. -/
@[simp] theorem sectorTensorL_eq_zero_of_weight_eq_zero
    (K : MPOTensor d D) (hK : K.IsInjective) (hη : EtaStructure rho)
    (R : Matrix (Fin D) (Fin D) ℂ) (α₁ β₃ : Fin D) (k : Fin hη.m) (beta : Fin D)
    (hk : hη.p k = 0) :
    sectorTensorL K hK hη R α₁ β₃ k beta = 0 := by
  ext x y
  simp [sectorTensorL, hk]

/-- A zero Hayashi weight makes every inverse-map neighboring operator entering that sector
vanish.

Source: arXiv:1606.00608, Appendix C.2, equation `etarl`, lines 1441--1445. The zero-weight
boundary is recorded in `docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`. -/
theorem sectorEta_eq_zero_of_target_weight_eq_zero
    (K : MPOTensor d D) (hK : K.IsInjective) (hη : EtaStructure rho)
    (R : Matrix (Fin D) (Fin D) ℂ) (α₁ β₃ : Fin D) (k h : Fin hη.m)
    (hh : hη.p h = 0) :
    sectorEta K hK hη R α₁ β₃ k h = 0 := by
  ext x y
  simp [sectorEta, Matrix.sum_apply,
    sectorTensorL_eq_zero_of_weight_eq_zero K hK hη R α₁ β₃ h _ hh]

/-- The inverse-map physical-sector factorization with every zero-weight source right tensor set
to zero.

All physical sectors and factor spaces are retained. Since the left tensor of a zero-weight sector
already vanishes, this changes neither the physical-slice factorization nor any sector of nonzero
weight. It removes the outgoing neighboring contractions which arise solely from the unused right
tensor of a zero-weight sector.

**Local fix (zero-weight sectors):** The Hayashi structure used here permits summands of weight
zero. Retaining their physical spaces while setting their unused right tensors to zero is recorded
in `docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, equations `formK` and `etarl`, lines 1434--1445. -/
noncomputable def zeroWeightReparameterizedInverseMapPhysicalSectorFactorization
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ) (hρ : IsThreeSiteClosure K R rho)
    (hη : EtaStructure rho) (α₁ β₃ : Fin D) (hm : R β₃ α₁ ≠ 0) :
    PhysicalSectorFactorization K := by
  classical
  let F := inverseMapPhysicalSectorFactorization K hK R hρ hη α₁ β₃ hm
  exact F.zeroRightTensorOnInactive
    (fun k ↦ hη.p k ≠ 0)
    (fun k hk beta ↦ sectorTensorL_eq_zero_of_weight_eq_zero
      K hK hη R α₁ β₃ k beta (not_ne_iff.mp hk))

/-- The neighboring operator after the zero-weight reparameterization agrees with the original
inverse-map operator on a nonzero-weight source and vanishes on a zero-weight source.

Source: arXiv:1606.00608, Appendix C.2, equation `etarl`, lines 1441--1445. The need to
remove outgoing edges of zero-weight sectors is recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`. -/
theorem zeroWeightReparameterizedInverseMapPhysicalSectorFactorization_neighboringOperator
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ) (hρ : IsThreeSiteClosure K R rho)
    (hη : EtaStructure rho) (α₁ β₃ : Fin D) (hm : R β₃ α₁ ≠ 0)
    (k h : Fin hη.m) :
    (zeroWeightReparameterizedInverseMapPhysicalSectorFactorization
      K hK R hρ hη α₁ β₃ hm).neighboringOperator k h =
      if hη.p k ≠ 0 then sectorEta K hK hη R α₁ β₃ k h else 0 := by
  classical
  unfold zeroWeightReparameterizedInverseMapPhysicalSectorFactorization
  rw [PhysicalSectorFactorization.zeroRightTensorOnInactive_neighboringOperator]
  split
  · rw [inverseMapPhysicalSectorFactorization_neighboringOperator_eq_sectorEta]
  · rfl

end MPOTensor
