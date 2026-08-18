/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSum
import TNLean.MPS.RFP.AppendixBStructuralData

/-!
# Appendix B virtual-bond support

This file constructs the rank-one virtual bond projector, its adjacent
three-site placements, and the corresponding two-site bond insertion and
contraction maps from arXiv:1606.00608, equations (3.17)--(3.18).
-/

open scoped Matrix BigOperators InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

/-! ### The virtual bond projector -/

/-- The squared norm
\(\langle\varphi,\varphi\rangle=\sum_b\lambda_b^2\) of the Appendix B bond
vector \(\varphi=\sum_b\lambda_b\lvert b,b\rangle\).

Source: arXiv:1606.00608, equations (3.17)--(3.18), lines 564--578. -/
noncomputable def AppendixBStructuralData.virtualBondNormSq
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) : ℂ :=
  ∑ k : Fin D, (hStruct.Λ k : ℂ) * (hStruct.Λ k : ℂ)

/-- Strict positivity of the bond weights makes the squared bond norm nonzero
whenever the virtual space is nonempty.

Source: arXiv:1606.00608, equation (3.18), lines 573--578. -/
theorem AppendixBStructuralData.virtualBondNormSq_ne_zero
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    [Nonempty (Fin D)] : hStruct.virtualBondNormSq ≠ 0 := by
  let k₀ : Fin D := Classical.choice inferInstance
  have hnonneg : ∀ k ∈ Finset.univ, 0 ≤ hStruct.Λ k * hStruct.Λ k := by
    intro k _
    exact mul_nonneg (le_of_lt (hStruct.hΛ_pos k)) (le_of_lt (hStruct.hΛ_pos k))
  have hpos : 0 < ∑ k : Fin D, hStruct.Λ k * hStruct.Λ k := by
    apply Finset.sum_pos' hnonneg
    exact ⟨k₀, Finset.mem_univ k₀, mul_pos (hStruct.hΛ_pos k₀) (hStruct.hΛ_pos k₀)⟩
  have hc : ((∑ k : Fin D, hStruct.Λ k * hStruct.Λ k : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hpos
  simpa [AppendixBStructuralData.virtualBondNormSq] using hc

/-- The rank-one orthogonal projector onto
\(\mathbb C\varphi\), written in the pair-index basis.

Source: arXiv:1606.00608, equations (3.17)--(3.18), lines 564--578. -/
noncomputable def AppendixBStructuralData.virtualBondProjection
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    ((Fin D × Fin D → ℂ) →ₗ[ℂ] (Fin D × Fin D → ℂ)) where
  toFun v p :=
    if p.1 = p.2 then
      (hStruct.Λ p.1 : ℂ) / hStruct.virtualBondNormSq *
        ∑ k : Fin D, (hStruct.Λ k : ℂ) * v (k, k)
    else 0
  map_add' v w := by
    funext p
    by_cases hp : p.1 = p.2
    · simp only [hp, ite_true, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    · simp only [Pi.add_apply, hp, ite_false, add_zero]
  map_smul' c v := by
    funext p
    by_cases hp : p.1 = p.2
    · simp [hp, Finset.mul_sum, mul_assoc, mul_comm]
    · simp [hp]

/-- Replace the virtual bond joining sites zero and one by the diagonal basis
vector indexed by `k`, leaving the four remaining virtual indices unchanged. -/
def AppendixBStructuralData.replaceVirtualBond01
    {A : MPSTensor d D} (_hStruct : AppendixBStructuralData A)
    (p : Fin 3 → Fin D × Fin D) (k : Fin D) : Fin 3 → Fin D × Fin D :=
  fun t ↦ if t = 0 then ((p 0).1, k) else if t = 1 then (k, (p 1).2) else p t

/-- Replace the virtual bond joining sites one and two by the diagonal basis
vector indexed by `k`, leaving the four remaining virtual indices unchanged. -/
def AppendixBStructuralData.replaceVirtualBond12
    {A : MPSTensor d D} (_hStruct : AppendixBStructuralData A)
    (p : Fin 3 → Fin D × Fin D) (k : Fin D) : Fin 3 → Fin D × Fin D :=
  fun t ↦ if t = 1 then ((p 1).1, k) else if t = 2 then (k, (p 2).2) else p t

/-- Replacing the first virtual bond updates the outgoing index at site zero. -/
@[simp] theorem AppendixBStructuralData.replaceVirtualBond01_zero
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (p : Fin 3 → Fin D × Fin D) (k : Fin D) :
    hStruct.replaceVirtualBond01 p k 0 = ((p 0).1, k) := by
  simp [AppendixBStructuralData.replaceVirtualBond01]

/-- Replacing the first virtual bond updates the incoming index at site one. -/
@[simp] theorem AppendixBStructuralData.replaceVirtualBond01_one
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (p : Fin 3 → Fin D × Fin D) (k : Fin D) :
    hStruct.replaceVirtualBond01 p k 1 = (k, (p 1).2) := by
  simp [AppendixBStructuralData.replaceVirtualBond01]

/-- Replacing the first virtual bond leaves site two unchanged. -/
@[simp] theorem AppendixBStructuralData.replaceVirtualBond01_two
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (p : Fin 3 → Fin D × Fin D) (k : Fin D) :
    hStruct.replaceVirtualBond01 p k 2 = p 2 := by
  simp [AppendixBStructuralData.replaceVirtualBond01]

/-- Replacing the second virtual bond leaves site zero unchanged. -/
@[simp] theorem AppendixBStructuralData.replaceVirtualBond12_zero
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (p : Fin 3 → Fin D × Fin D) (k : Fin D) :
    hStruct.replaceVirtualBond12 p k 0 = p 0 := by
  simp [AppendixBStructuralData.replaceVirtualBond12]

/-- Replacing the second virtual bond updates the outgoing index at site one. -/
@[simp] theorem AppendixBStructuralData.replaceVirtualBond12_one
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (p : Fin 3 → Fin D × Fin D) (k : Fin D) :
    hStruct.replaceVirtualBond12 p k 1 = ((p 1).1, k) := by
  simp [AppendixBStructuralData.replaceVirtualBond12]

/-- Replacing the second virtual bond updates the incoming index at site two. -/
@[simp] theorem AppendixBStructuralData.replaceVirtualBond12_two
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (p : Fin 3 → Fin D × Fin D) (k : Fin D) :
    hStruct.replaceVirtualBond12 p k 2 = (k, (p 2).2) := by
  simp [AppendixBStructuralData.replaceVirtualBond12]

/-- The replacement of the two adjacent virtual bonds is independent of its
order. -/
theorem AppendixBStructuralData.replaceVirtualBonds_commute
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (p : Fin 3 → Fin D × Fin D) (k l : Fin D) :
    hStruct.replaceVirtualBond01 (hStruct.replaceVirtualBond12 p l) k =
      hStruct.replaceVirtualBond12 (hStruct.replaceVirtualBond01 p k) l := by
  funext t
  fin_cases t <;> simp

/-- The placement of the virtual bond projector on the bond joining sites zero
and one of three virtual pairs.

Source: arXiv:1606.00608, equations (3.17)--(3.18), lines 564--578. -/
noncomputable def AppendixBStructuralData.leftVirtualBondProjection
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    (((Fin 3 → Fin D × Fin D) → ℂ) →ₗ[ℂ]
      ((Fin 3 → Fin D × Fin D) → ℂ)) where
  toFun v p :=
    if (p 0).2 = (p 1).1 then
      (hStruct.Λ (p 0).2 : ℂ) / hStruct.virtualBondNormSq *
        ∑ k : Fin D, (hStruct.Λ k : ℂ) * v (hStruct.replaceVirtualBond01 p k)
    else 0
  map_add' v w := by
    funext p
    by_cases hp : (p 0).2 = (p 1).1
    · simp only [hp, ite_true, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    · simp only [Pi.add_apply, hp, ite_false, add_zero]
  map_smul' c v := by
    funext p
    by_cases hp : (p 0).2 = (p 1).1
    · simp [hp, Finset.mul_sum, mul_assoc, mul_comm]
    · simp [hp]

/-- The placement of the virtual bond projector on the bond joining sites one
and two of three virtual pairs.

Source: arXiv:1606.00608, equations (3.17)--(3.18), lines 564--578. -/
noncomputable def AppendixBStructuralData.rightVirtualBondProjection
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    (((Fin 3 → Fin D × Fin D) → ℂ) →ₗ[ℂ]
      ((Fin 3 → Fin D × Fin D) → ℂ)) where
  toFun v p :=
    if (p 1).2 = (p 2).1 then
      (hStruct.Λ (p 1).2 : ℂ) / hStruct.virtualBondNormSq *
        ∑ k : Fin D, (hStruct.Λ k : ℂ) * v (hStruct.replaceVirtualBond12 p k)
    else 0
  map_add' v w := by
    funext p
    by_cases hp : (p 1).2 = (p 2).1
    · simp only [hp, ite_true, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    · simp only [Pi.add_apply, hp, ite_false, add_zero]
  map_smul' c v := by
    funext p
    by_cases hp : (p 1).2 = (p 2).1
    · simp [hp, Finset.mul_sum, mul_assoc, mul_comm]
    · simp [hp]

/-- The two adjacent placements of the rank-one virtual bond projector commute.
They act on the two disjoint contracted bonds among three virtual site pairs.

Source: arXiv:1606.00608, equations (3.17)--(3.18), lines 564--578. -/
theorem AppendixBStructuralData.leftVirtualBondProjection_comp_right
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    hStruct.leftVirtualBondProjection.comp hStruct.rightVirtualBondProjection =
      hStruct.rightVirtualBondProjection.comp hStruct.leftVirtualBondProjection := by
  apply LinearMap.ext
  intro v
  funext p
  by_cases h01 : (p 0).2 = (p 1).1
  · by_cases h12 : (p 1).2 = (p 2).1
    · suffices
          (hStruct.Λ (p 1).1 : ℂ) / hStruct.virtualBondNormSq *
              ∑ x, (hStruct.Λ x : ℂ) *
                ((hStruct.Λ (p 2).1 : ℂ) / hStruct.virtualBondNormSq *
                  ∑ k, (hStruct.Λ k : ℂ) *
                    v (hStruct.replaceVirtualBond12
                      (hStruct.replaceVirtualBond01 p x) k)) =
            (hStruct.Λ (p 2).1 : ℂ) / hStruct.virtualBondNormSq *
              ∑ x, (hStruct.Λ x : ℂ) *
                ((hStruct.Λ (p 1).1 : ℂ) / hStruct.virtualBondNormSq *
                  ∑ k, (hStruct.Λ k : ℂ) *
                    v (hStruct.replaceVirtualBond01
                      (hStruct.replaceVirtualBond12 p x) k)) by
        simpa [LinearMap.comp_apply,
          AppendixBStructuralData.leftVirtualBondProjection,
          AppendixBStructuralData.rightVirtualBondProjection, h01, h12]
      simp_rw [← hStruct.replaceVirtualBonds_commute]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring
    · simp [LinearMap.comp_apply, AppendixBStructuralData.leftVirtualBondProjection,
        AppendixBStructuralData.rightVirtualBondProjection, h01, h12]
  · simp [LinearMap.comp_apply, AppendixBStructuralData.leftVirtualBondProjection,
      AppendixBStructuralData.rightVirtualBondProjection, h01]

/-! ### The two-site virtual bond -/

/-- Replace the contracted virtual bond in two virtual site pairs by the
diagonal basis vector indexed by `k`. -/
def AppendixBStructuralData.replaceTwoSiteVirtualBond
    {A : MPSTensor d D} (_hStruct : AppendixBStructuralData A)
    (p : Fin 2 → Fin D × Fin D) (k : Fin D) : Fin 2 → Fin D × Fin D :=
  fun t ↦ if t = 0 then ((p 0).1, k) else (k, (p 1).2)

/-- Two-site bond replacement updates the outgoing index at site zero. -/
@[simp] theorem AppendixBStructuralData.replaceTwoSiteVirtualBond_zero
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (p : Fin 2 → Fin D × Fin D) (k : Fin D) :
    hStruct.replaceTwoSiteVirtualBond p k 0 = ((p 0).1, k) := by
  simp [AppendixBStructuralData.replaceTwoSiteVirtualBond]

/-- Two-site bond replacement updates the incoming index at site one. -/
@[simp] theorem AppendixBStructuralData.replaceTwoSiteVirtualBond_one
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (p : Fin 2 → Fin D × Fin D) (k : Fin D) :
    hStruct.replaceTwoSiteVirtualBond p k 1 = (k, (p 1).2) := by
  simp [AppendixBStructuralData.replaceTwoSiteVirtualBond]

/-- The rank-one virtual bond projector acting on the contracted indices of two
virtual site pairs and as the identity on their outer indices.

Source: arXiv:1606.00608, equations (3.17)--(3.18), lines 564--578. -/
noncomputable def AppendixBStructuralData.twoSiteVirtualBondProjection
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    (((Fin 2 → Fin D × Fin D) → ℂ) →ₗ[ℂ]
      ((Fin 2 → Fin D × Fin D) → ℂ)) where
  toFun v p :=
    if (p 0).2 = (p 1).1 then
      (hStruct.Λ (p 0).2 : ℂ) / hStruct.virtualBondNormSq *
        ∑ k : Fin D,
          (hStruct.Λ k : ℂ) * v (hStruct.replaceTwoSiteVirtualBond p k)
    else 0
  map_add' v w := by
    funext p
    by_cases hp : (p 0).2 = (p 1).1
    · simp only [hp, ite_true, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    · simp only [Pi.add_apply, hp, ite_false, add_zero]
  map_smul' c v := by
    funext p
    by_cases hp : (p 0).2 = (p 1).1
    · simp [hp, Finset.mul_sum, mul_assoc, mul_comm]
    · simp [hp]

/-- The two-site virtual configuration with outer indices `a,c` and diagonal
bond index `k`. -/
def AppendixBStructuralData.twoSiteVirtualBondConfig
    {A : MPSTensor d D} (_hStruct : AppendixBStructuralData A)
    (a c k : Fin D) : Fin 2 → Fin D × Fin D :=
  fun t ↦ if t = 0 then (a, k) else (k, c)

/-- The first site of a two-site virtual bond configuration is `(a, k)`. -/
@[simp] theorem AppendixBStructuralData.twoSiteVirtualBondConfig_zero
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) (a c k : Fin D) :
    hStruct.twoSiteVirtualBondConfig a c k 0 = (a, k) := by
  simp [AppendixBStructuralData.twoSiteVirtualBondConfig]

/-- The second site of a two-site virtual bond configuration is `(k, c)`. -/
@[simp] theorem AppendixBStructuralData.twoSiteVirtualBondConfig_one
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) (a c k : Fin D) :
    hStruct.twoSiteVirtualBondConfig a c k 1 = (k, c) := by
  simp [AppendixBStructuralData.twoSiteVirtualBondConfig]

/-- Contract a two-site virtual coefficient tensor against the normalized bond
vector while retaining its two outer indices. -/
noncomputable def AppendixBStructuralData.twoSiteVirtualBoundaryContraction
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    (((Fin 2 → Fin D × Fin D) → ℂ) →ₗ[ℂ] (Fin D × Fin D → ℂ)) where
  toFun v ac := hStruct.virtualBondNormSq⁻¹ *
    ∑ k : Fin D, (hStruct.Λ k : ℂ) *
      v (hStruct.twoSiteVirtualBondConfig ac.1 ac.2 k)
  map_add' v w := by
    funext ac
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    funext ac
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring_nf

/-- Insert the bond vector
\(\varphi=\sum_b\lambda_b\lvert b,b\rangle\) between two virtual site pairs.

For outer-boundary coefficients \(v_{a,c}\), the resulting four-index tensor is
\[
  (I_\varphi v)_{(a,b),(b',c)}
  =\delta_{b,b'}\lambda_b v_{a,c}.
\]

Source: arXiv:1606.00608, equations (3.17)--(3.18), lines 564--578. -/
noncomputable def AppendixBStructuralData.twoSiteBondInsertion
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    ((Fin D × Fin D → ℂ) →ₗ[ℂ] ((Fin 2 → Fin D × Fin D) → ℂ)) where
  toFun v p :=
    if (p 0).2 = (p 1).1 then
      (hStruct.Λ (p 0).2 : ℂ) * v ((p 0).1, (p 1).2)
    else 0
  map_add' v w := by
    funext p
    by_cases h : (p 0).2 = (p 1).1
    · simp [h, mul_add]
    · simp [h]
  map_smul' c v := by
    funext p
    by_cases h : (p 0).2 = (p 1).1
    · simp [h, mul_assoc, mul_comm]
    · simp [h]

/-- Replacing the contracted bond while retaining the outer indices gives the
canonical virtual-bond configuration. -/
theorem AppendixBStructuralData.replaceTwoSiteVirtualBond_eq_config
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (p : Fin 2 → Fin D × Fin D) (k : Fin D) :
    hStruct.replaceTwoSiteVirtualBond p k =
      hStruct.twoSiteVirtualBondConfig (p 0).1 (p 1).2 k := by
  funext t
  fin_cases t <;> simp

/-- The two-site virtual bond projector is bond insertion after contraction of
the same bond.

Source: arXiv:1606.00608, equations (3.17)--(3.18), lines 564--578. -/
theorem AppendixBStructuralData.twoSiteVirtualBondProjection_eq_comp
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    hStruct.twoSiteVirtualBondProjection =
      hStruct.twoSiteBondInsertion.comp hStruct.twoSiteVirtualBoundaryContraction := by
  apply LinearMap.ext
  intro v
  funext p
  by_cases hp : (p 0).2 = (p 1).1
  · suffices
        (hStruct.Λ (p 1).1 : ℂ) / hStruct.virtualBondNormSq *
            ∑ k, (hStruct.Λ k : ℂ) * v (hStruct.replaceTwoSiteVirtualBond p k) =
          (hStruct.Λ (p 1).1 : ℂ) *
            (hStruct.virtualBondNormSq⁻¹ *
              ∑ k, (hStruct.Λ k : ℂ) *
                v (hStruct.twoSiteVirtualBondConfig (p 0).1 (p 1).2 k)) by
      simpa [AppendixBStructuralData.twoSiteVirtualBondProjection,
        AppendixBStructuralData.twoSiteBondInsertion,
        AppendixBStructuralData.twoSiteVirtualBoundaryContraction, hp]
    simp_rw [hStruct.replaceTwoSiteVirtualBond_eq_config]
    ring_nf
  · simp [AppendixBStructuralData.twoSiteVirtualBondProjection,
      AppendixBStructuralData.twoSiteBondInsertion, hp]

/-- If the bond vector is nonzero, its virtual support projector fixes every
inserted-bond vector.

Source: arXiv:1606.00608, equations (3.17)--(3.18), lines 564--578. -/
theorem AppendixBStructuralData.twoSiteVirtualBondProjection_apply_insertion
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (hφ : hStruct.virtualBondNormSq ≠ 0) (v : Fin D × Fin D → ℂ) :
    hStruct.twoSiteVirtualBondProjection (hStruct.twoSiteBondInsertion v) =
      hStruct.twoSiteBondInsertion v := by
  have hsum : (∑ k : Fin D, (hStruct.Λ k : ℂ) ^ 2) ≠ 0 := by
    simpa [AppendixBStructuralData.virtualBondNormSq, pow_two] using hφ
  funext p
  by_cases hp : (p 0).2 = (p 1).1
  · simp [AppendixBStructuralData.twoSiteVirtualBondProjection,
      AppendixBStructuralData.twoSiteBondInsertion,
      AppendixBStructuralData.replaceTwoSiteVirtualBond, hp,
      AppendixBStructuralData.virtualBondNormSq]
    field_simp [hsum]
    have hv : (∑ x : Fin D,
        (hStruct.Λ x : ℂ) ^ 2 * v ((p 0).1, (p 1).2)) =
        (∑ x : Fin D, (hStruct.Λ x : ℂ) ^ 2) * v ((p 0).1, (p 1).2) := by
      rw [Finset.sum_mul]
    rw [hv]
    ac_rfl
  · simp [AppendixBStructuralData.twoSiteVirtualBondProjection,
      AppendixBStructuralData.twoSiteBondInsertion, hp]

/-- For a nonzero bond vector, the two-site virtual bond projector is
idempotent.

Source: arXiv:1606.00608, equations (3.17)--(3.18), lines 564--578. -/
theorem AppendixBStructuralData.twoSiteVirtualBondProjection_idempotent
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (hφ : hStruct.virtualBondNormSq ≠ 0) :
    hStruct.twoSiteVirtualBondProjection * hStruct.twoSiteVirtualBondProjection =
      hStruct.twoSiteVirtualBondProjection := by
  apply LinearMap.ext
  intro v
  rw [Module.End.mul_apply]
  rw [show hStruct.twoSiteVirtualBondProjection v =
      hStruct.twoSiteBondInsertion
        (hStruct.twoSiteVirtualBoundaryContraction v) by
    exact LinearMap.congr_fun hStruct.twoSiteVirtualBondProjection_eq_comp v]
  rw [hStruct.twoSiteVirtualBondProjection_apply_insertion hφ]


end MPSTensor
