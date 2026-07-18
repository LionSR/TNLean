/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTThreeSiteCollapse
import TNLean.MPS.MPDO.HayashiSectorComparison

/-!
# Comparison of BNT and quantum-Markov sectors

This module compares the outer inverse contraction of a finite family of
basis-of-normal-tensors sectors with the blocks of a chosen quantum-Markov
decomposition of the same three-site operator.

The comparison is the entrywise form of the principal identity in
arXiv:1606.00608, Appendix C.2, lines 1719--1732.  The Markov weight remains
explicit; no nonvanishing, positivity, saturated-area-law, zero-correlation-
length, or sector-ownership hypothesis enters the identity.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d g : ℕ} {dim : Fin g → ℕ}

/-- The left factor obtained by contracting a simultaneous block inverse with
the left density matrix in a quantum-Markov sector.

Source: arXiv:1606.00608, Appendix C.2, lines 1719--1725. -/
def bntMarkovLeftFactor
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ)
    (hη : EtaStructure ρ) (x : MPSTensor.BlockEntryIndex dim)
    (k : Fin hη.m) (l l' : Fin (hη.dL k)) : ℂ :=
  ∑ i : Fin d, ∑ j : Fin d,
    C x (i, j) * hη.ρ_left k (i, l) (j, l')

/-- The right factor obtained by contracting a simultaneous block inverse with
the right density matrix in a quantum-Markov sector.

Source: arXiv:1606.00608, Appendix C.2, lines 1719--1725. -/
def bntMarkovRightFactor
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ)
    (hη : EtaStructure ρ) (x : MPSTensor.BlockEntryIndex dim)
    (k : Fin hη.m) (r r' : Fin (hη.dR k)) : ℂ :=
  ∑ i : Fin d, ∑ j : Fin d,
    C x (i, j) * hη.ρ_right k (r, i) (r', j)

/-- The outer inverse contraction, expressed in quantum-Markov coordinates.
It vanishes between distinct Markov sectors; within sector `k` it is the
weight `p_k` times the product of the left and right factors.

Source: arXiv:1606.00608, Appendix C.2, lines 1719--1725. -/
theorem outerInverseContraction_markov_block
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ)
    (hη : EtaStructure ρ) (x y : MPSTensor.BlockEntryIndex dim)
    (k k' : Fin hη.m)
    (l : Fin (hη.dL k)) (r : Fin (hη.dR k))
    (l' : Fin (hη.dL k')) (r' : Fin (hη.dR k')) :
    Matrix.reindex hη.decompB hη.decompB
        ((hη.U_B : Matrix (Fin d) (Fin d) ℂ) *
          outerInverseContraction C ρ x y *
          (hη.U_B : Matrix (Fin d) (Fin d) ℂ)ᴴ)
        ⟨k, (l, r)⟩ ⟨k', (l', r')⟩ =
      if h : k = k' then
        (hη.p k : ℂ) * bntMarkovLeftFactor C hη x k l (h ▸ l') *
          bntMarkovRightFactor C hη y k r (h ▸ r')
      else 0 := by
  classical
  let b : Fin d := hη.decompB.symm ⟨k, (l, r)⟩
  let b' : Fin d := hη.decompB.symm ⟨k', (l', r')⟩
  let U : Matrix (Fin d) (Fin d) ℂ := hη.U_B
  have hsector (i₁ j₁ i₃ j₃ : Fin d) :
      (∑ i₂ : Fin d, ∑ j₂ : Fin d,
        U b i₂ * ρ (i₁, i₂, i₃) (j₁, j₂, j₃) *
          (starRingEnd ℂ) (U b' j₂)) =
        if h : k = k' then
          (hη.p k : ℂ) * hη.ρ_left k (i₁, l) (j₁, h ▸ l') *
            hη.ρ_right k (r, i₃) (h ▸ r', j₃)
        else 0 := by
    have hs := congrFun (congrFun hη.h_state
      (i₁, (⟨k, (l, r)⟩, i₃))) (j₁, (⟨k', (l', r')⟩, j₃))
    rw [Matrix.reindex_apply, Matrix.submatrix_apply] at hs
    have hleft : (HayashiMarkov.abcEquiv hη.decompB).symm
        (i₁, (⟨k, (l, r)⟩, i₃)) = (i₁, b, i₃) := by
      simp [HayashiMarkov.abcEquiv, b]
    have hright : (HayashiMarkov.abcEquiv hη.decompB).symm
        (j₁, (⟨k', (l', r')⟩, j₃)) = (j₁, b', j₃) := by
      simp [HayashiMarkov.abcEquiv, b']
    rw [hleft, hright] at hs
    rw [HayashiMarkov.liftB_conj_apply] at hs
    rw [HayashiMarkov.blockState_apply] at hs
    simpa [b, b', U] using hs
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  change (U * outerInverseContraction C ρ x y * Uᴴ) b b' = _
  have hExpand :
      (U * outerInverseContraction C ρ x y * Uᴴ) b b' =
        ∑ i₁ : Fin d, ∑ j₁ : Fin d, ∑ i₃ : Fin d, ∑ j₃ : Fin d,
          C x (i₁, j₁) * C y (i₃, j₃) *
            (∑ i₂ : Fin d, ∑ j₂ : Fin d,
              U b i₂ * ρ (i₁, i₂, i₃) (j₁, j₂, j₃) *
                (starRingEnd ℂ) (U b' j₂)) := by
    simp_rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, Complex.star_def]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [outerInverseContraction]
    let rotate :
        (Fin d × Fin d × Fin d × Fin d × Fin d × Fin d) ≃
          (Fin d × Fin d × Fin d × Fin d × Fin d × Fin d) := {
      toFun := fun ⟨i₂, j₂, i₁, j₁, i₃, j₃⟩ ↦ (i₁, j₁, i₃, j₃, i₂, j₂)
      invFun := fun ⟨i₁, j₁, i₃, j₃, i₂, j₂⟩ ↦
        (i₂, j₂, i₁, j₁, i₃, j₃)
      left_inv := by rintro ⟨i₂, j₂, i₁, j₁, i₃, j₃⟩; rfl
      right_inv := by rintro ⟨i₁, j₁, i₃, j₃, i₂, j₂⟩; rfl }
    let G : Fin d × Fin d × Fin d × Fin d × Fin d × Fin d → ℂ :=
      fun ⟨i₂, j₂, i₁, j₁, i₃, j₃⟩ ↦
        U b i₂ * (C x (i₁, j₁) * C y (i₃, j₃) *
          ρ (i₁, i₂, i₃) (j₁, j₂, j₃)) * (starRingEnd ℂ) (U b' j₂)
    have hperm :
        (∑ i₂, ∑ j₂, ∑ i₁, ∑ j₁, ∑ i₃, ∑ j₃,
          U b i₂ * (C x (i₁, j₁) * C y (i₃, j₃) *
            ρ (i₁, i₂, i₃) (j₁, j₂, j₃)) * (starRingEnd ℂ) (U b' j₂)) =
        ∑ i₁, ∑ j₁, ∑ i₃, ∑ j₃, ∑ i₂, ∑ j₂,
          U b i₂ * (C x (i₁, j₁) * C y (i₃, j₃) *
            ρ (i₁, i₂, i₃) (j₁, j₂, j₃)) * (starRingEnd ℂ) (U b' j₂) := by
      have hflat : (∑ z, G z) =
          ∑ i₂, ∑ j₂, ∑ i₁, ∑ j₁, ∑ i₃, ∑ j₃,
            U b i₂ * (C x (i₁, j₁) * C y (i₃, j₃) *
              ρ (i₁, i₂, i₃) (j₁, j₂, j₃)) * (starRingEnd ℂ) (U b' j₂) := by
        simp only [Fintype.sum_prod_type, G]
      have hflat' : (∑ z, G (rotate.symm z)) =
          ∑ i₁, ∑ j₁, ∑ i₃, ∑ j₃, ∑ i₂, ∑ j₂,
            U b i₂ * (C x (i₁, j₁) * C y (i₃, j₃) *
              ρ (i₁, i₂, i₃) (j₁, j₂, j₃)) * (starRingEnd ℂ) (U b' j₂) := by
        simp [Fintype.sum_prod_type, G, rotate]
      rw [← hflat, ← hflat']
      exact (Equiv.sum_comp rotate.symm G).symm
    calc
      _ = ∑ i₂, ∑ j₂, ∑ i₁, ∑ j₁, ∑ i₃, ∑ j₃,
          U b i₂ * (C x (i₁, j₁) * C y (i₃, j₃) *
            ρ (i₁, i₂, i₃) (j₁, j₂, j₃)) * (starRingEnd ℂ) (U b' j₂) := by
        refine Finset.sum_congr rfl fun i₂ _ => Finset.sum_congr rfl fun j₂ _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i₁ _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j₁ _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i₃ _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ i₁, ∑ j₁, ∑ i₃, ∑ j₃, ∑ i₂, ∑ j₂,
          U b i₂ * (C x (i₁, j₁) * C y (i₃, j₃) *
            ρ (i₁, i₂, i₃) (j₁, j₂, j₃)) * (starRingEnd ℂ) (U b' j₂) := hperm
      _ = _ := by
        refine Finset.sum_congr rfl fun i₁ _ => ?_
        refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun i₃ _ =>
          Finset.sum_congr rfl fun j₃ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i₂ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j₂ _ => ?_
        ring
  rw [hExpand]
  simp_rw [hsector]
  by_cases hkk : k = k'
  · subst k'
    simp only [reduceDIte]
    simp only [bntMarkovLeftFactor, bntMarkovRightFactor]
    rw [show (hη.p k : ℂ) *
        (∑ i, ∑ j, C x (i, j) * hη.ρ_left k (i, l) (j, l')) *
        (∑ i, ∑ j, C y (i, j) * hη.ρ_right k (r, i) (r', j)) =
      (hη.p k : ℂ) *
        (∑ i, ∑ j, C y (i, j) * hη.ρ_right k (r, i) (r', j)) *
        (∑ i, ∑ j, C x (i, j) * hη.ρ_left k (i, l) (j, l')) by ring]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j₁ _ => ?_
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i₃ _ => ?_
    refine Finset.sum_congr rfl fun j₃ _ => ?_
    ring
  · simp [hkk]

/-- The entrywise identity obtained by comparing the quantum-Markov and
basis-of-normal-tensors expressions for the same outer inverse contraction.
The Markov side vanishes unless the two middle-space indices belong to the
same Markov sector.  The basis-of-normal-tensors side vanishes unless the two
inverse tensors select the same normal sector.

**Local fix (tail index):** the closing entry is
$R_s(\beta_3,\alpha_1)$, as forced by the matrix-unit trace identity.  This is
the corrected orientation of the single-sector display at lines 1422--1438,
recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, lines 1719--1732. -/
theorem isMPOBlockLeftInverse_bnt_markov_key_formula
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (x y : MPSTensor.BlockEntryIndex dim) (k k' : Fin hη.m)
    (l : Fin (hη.dL k)) (r : Fin (hη.dR k))
    (l' : Fin (hη.dL k')) (r' : Fin (hη.dR k')) :
    (if h : k = k' then
        (hη.p k : ℂ) * bntMarkovLeftFactor C hη x k l (h ▸ l') *
          bntMarkovRightFactor C hη y k r (h ▸ r')
      else 0) =
      if h : x.1 = y.1 then
        R x.1 (h.symm ▸ y.2.2) x.2.1 *
          Matrix.reindex hη.decompB hη.decompB
            ((hη.U_B : Matrix (Fin d) (Fin d) ℂ) *
              physicalSlice (K x.1) x.2.2 (h.symm ▸ y.2.1) *
              (hη.U_B : Matrix (Fin d) (Fin d) ℂ)ᴴ)
            ⟨k, (l, r)⟩ ⟨k', (l', r')⟩
      else 0 := by
  classical
  rw [← outerInverseContraction_markov_block C hη x y k k' l r l' r']
  have hcollapse :
      outerInverseContraction C ρ x y =
        if h : x.1 = y.1 then
          R x.1 (h.symm ▸ y.2.2) x.2.1 •
            physicalSlice (K x.1) x.2.2 (h.symm ▸ y.2.1)
        else 0 := by
    ext i₂ j₂
    rw [isMPOBlockLeftInverse_outer_inverse_threeSite_collapse hC hρ]
    by_cases hxy : x.1 = y.1
    · simp [hxy, physicalSlice]
      ring
    · simp [hxy]
  rw [hcollapse]
  by_cases hxy : x.1 = y.1
  · simp [hxy, smul_eq_mul]
  · simp [hxy]

/-- Distinct Markov sectors give a zero block of every physical slice in a
fixed basis-of-normal-tensors sector, once the nonzero closing entry selected
in the source is fixed.

**Local fix (tail index):** the nonzero closing entry is
$R_s(\beta_3,\alpha_1)$, as forced by the matrix-unit trace identity.  This is
the corrected orientation of the single-sector display at lines 1422--1438,
recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, equation `Qks`, lines 1730--1735. -/
theorem isMPOBlockLeftInverse_bnt_markov_offdiagonal
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (s : Fin g) {α₁ β₃ : Fin (dim s)} (hm : R s β₃ α₁ ≠ 0)
    (β₁ α₃ : Fin (dim s)) {k k' : Fin hη.m} (hkk' : k ≠ k')
    (l : Fin (hη.dL k)) (r : Fin (hη.dR k))
    (l' : Fin (hη.dL k')) (r' : Fin (hη.dR k')) :
    Matrix.reindex hη.decompB hη.decompB
        ((hη.U_B : Matrix (Fin d) (Fin d) ℂ) *
          physicalSlice (K s) β₁ α₃ *
          (hη.U_B : Matrix (Fin d) (Fin d) ℂ)ᴴ)
        ⟨k, (l, r)⟩ ⟨k', (l', r')⟩ = 0 := by
  classical
  have hkey := isMPOBlockLeftInverse_bnt_markov_key_formula hC hρ hη
    (⟨s, α₁, β₁⟩) (⟨s, α₃, β₃⟩) k k' l r l' r'
  simp [hkk'] at hkey
  simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using
    hkey.resolve_left hm

end MPOTensor
