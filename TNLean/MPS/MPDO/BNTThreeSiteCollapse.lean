/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BiCFDerivation.Core

/-!
# Three-site contraction of a basis of normal tensors

For a family of MPO tensors, a three-site operator can be closed against one
virtual matrix in each basis-of-normal-tensors sector.  A simultaneous left
inverse on the physical letters selects both the sector and a virtual matrix
unit.  Applying two such inverse tensors at the outer sites leaves one entry of
the middle tensor and one entry of the closing matrix.

This is the algebraic contraction used in the simple-tensor argument of
arXiv:1606.00608, Appendix C.2.  No positivity, saturated-area-law, or
zero-correlation-length assumption enters this contraction.

The single-sector counterpart is `MPOTensor.IsThreeSiteClosure`, with its
inverse-map contraction proved in
`MPOTensor.inverseMap_threeSite_closure_collapse`.  The present statements
retain a finite family of basis-of-normal-tensors sectors and use one inverse
which selects the sector together with the two virtual indices.
They use `MPSTensor.IsMPOBlockLeftInverse`, defined in
`BiCFDerivation.Core`, to characterize a coefficient matrix that simultaneously
inverts every sector of the family.

## Main definitions

* `MPOTensor.IsThreeSiteFamilyClosure`: a sum of three-site closures over a
  family of sectors.

## Main statements

* `MPOTensor.isMPOBlockLeftInverse_outer_inverse_threeSite_collapse`: two outer
  inverse contractions leave the middle slice and the closing entry in the
  selected sector.
* `MPOTensor.exists_isMPOBlockLeftInverse_outer_inverse_threeSite_collapse`:
  the simultaneous inverse and collapse follow from a one-letter simultaneous
  word span.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.2, lines 1415--1438, 1666--1676, and 1719--1732.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d g : ℕ} {dim : Fin g → ℕ}

/-- A tripartite operator is a sum of three-site closures of a family of MPO
tensors when each sector is closed against its own virtual matrix:
\[
  \rho_{i_1i_2i_3,j_1j_2j_3}
  =\sum_s\operatorname{tr}
    (K_s^{i_1j_1}K_s^{i_2j_2}K_s^{i_3j_3}R_s).
\]

Source: arXiv:1606.00608, Appendix C.2, equation `sigma3bka`, lines
1343--1348, and its Case II use at lines 1726--1732. -/
def IsThreeSiteFamilyClosure
    (K : (s : Fin g) → MPOTensor d (dim s))
    (R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ)
    (ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ) : Prop :=
  ∀ i₁ i₂ i₃ j₁ j₂ j₃,
    ρ (i₁, i₂, i₃) (j₁, j₂, j₃) =
      ∑ s : Fin g, Matrix.trace (K s i₁ j₁ * K s i₂ j₂ * K s i₃ j₃ * R s)

/-- Contract a tripartite operator with inverse tensors at its first and third
sites, leaving a matrix on the middle physical space.

This is the sector-family form of the outer-site contraction in the Case I
calculation at lines 1415--1438.  The same construction is used with sector
projectors in equation `Qketc2`, lines 1719--1725.

Source: arXiv:1606.00608, Appendix C.2, lines 1415--1438 and 1719--1725. -/
def outerInverseContraction
    (C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ)
    (ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ)
    (x y : MPSTensor.BlockEntryIndex dim) : Matrix (Fin d) (Fin d) ℂ :=
  fun i₂ j₂ ↦ ∑ i₁ : Fin d, ∑ j₁ : Fin d, ∑ i₃ : Fin d, ∑ j₃ : Fin d,
    C x (i₁, j₁) * C y (i₃, j₃) * ρ (i₁, i₂, i₃) (j₁, j₂, j₃)

/-- Applying simultaneous inverse tensors at the two outer sites of a
three-site family closure selects a common sector.  If the two inverse tensors
carry different sector labels, the contraction is zero.  If their label is
$s$, the contraction is
\[
  K_s^{i_2j_2}(\beta_1,\alpha_3)
  R_s(\beta_3,\alpha_1).
\]
Thus the middle slice has virtual indices $(\beta_1,\alpha_3)$ and the closing
entry has indices $(\beta_3,\alpha_1)$.

**Local fix (tail index):** the closing entry is
$R_s(\beta_3,\alpha_1)$, as forced by the matrix-unit trace identity.  This is
the corrected orientation of the single-sector display at lines 1422--1438,
recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

This is the sector-family form of the Case I contraction at lines 1415--1438,
used with the basis-of-normal-tensors inverse from lines 1666--1676 in the
Case II calculation at lines 1719--1732.  Compare the single-sector identity
`MPOTensor.inverseMapThreeSiteContraction_eq`.

Source: arXiv:1606.00608, Appendix C.2, lines 1415--1438, 1666--1676,
and 1719--1732. -/
theorem isMPOBlockLeftInverse_outer_inverse_threeSite_collapse
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ)
    (x y : MPSTensor.BlockEntryIndex dim) (i₂ j₂ : Fin d) :
    outerInverseContraction C ρ x y i₂ j₂ =
      if h : x.1 = y.1 then
        K x.1 i₂ j₂ x.2.2 (h.symm ▸ y.2.1) * R x.1 (h.symm ▸ y.2.2) x.2.1
      else 0 := by
  classical
  rcases x with ⟨sx, alpha₁, beta₁⟩
  rcases y with ⟨sy, alpha₃, beta₃⟩
  let x : MPSTensor.BlockEntryIndex dim := ⟨sx, alpha₁, beta₁⟩
  let y : MPSTensor.BlockEntryIndex dim := ⟨sy, alpha₃, beta₃⟩
  unfold IsThreeSiteFamilyClosure at hρ
  rw [outerInverseContraction]
  simp_rw [hρ]
  have hInv (z : MPSTensor.BlockEntryIndex dim) (s : Fin g) :
      (∑ i : Fin d, ∑ j : Fin d, C z (i, j) • K s i j) =
        if h : z.1 = s then
          Matrix.single (h ▸ z.2.1) (h ▸ z.2.2) (1 : ℂ)
        else 0 := by
    ext alpha beta
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases hzs : z.1 = s
    · subst s
      rw [hC z.1 z.1 z.2.1 z.2.2 alpha beta]
      by_cases ha : z.2.1 = alpha <;> by_cases hb : z.2.2 = beta <;>
        simp [ha, hb]
    · simpa [hzs] using hC z.1 s z.2.1 z.2.2 alpha beta
  let L (z : MPSTensor.BlockEntryIndex dim) (s : Fin g) :
      Matrix (Fin (dim s)) (Fin (dim s)) ℂ :=
    ∑ i : Fin d, ∑ j : Fin d, C z (i, j) • K s i j
  let sectorFirstEquiv :
      (Fin d × Fin d × Fin d × Fin d × Fin g) ≃
        (Fin g × Fin d × Fin d × Fin d × Fin d) := {
    toFun := fun ⟨i₁, j₁, i₃, j₃, s⟩ ↦ (s, i₁, j₁, i₃, j₃)
    invFun := fun ⟨s, i₁, j₁, i₃, j₃⟩ ↦ (i₁, j₁, i₃, j₃, s)
    left_inv := by rintro ⟨i₁, j₁, i₃, j₃, s⟩; rfl
    right_inv := by rintro ⟨s, i₁, j₁, i₃, j₃⟩; rfl }
  have sum_sector_first
      (f : Fin d → Fin d → Fin d → Fin d → Fin g → ℂ) :
      (∑ i₁, ∑ j₁, ∑ i₃, ∑ j₃, ∑ s, f i₁ j₁ i₃ j₃ s) =
        ∑ s, ∑ i₁, ∑ j₁, ∑ i₃, ∑ j₃, f i₁ j₁ i₃ j₃ s := by
    let G : Fin g × Fin d × Fin d × Fin d × Fin d → ℂ :=
      fun ⟨s, i₁, j₁, i₃, j₃⟩ ↦ f i₁ j₁ i₃ j₃ s
    simpa [Fintype.sum_prod_type, G, sectorFirstEquiv] using
      Equiv.sum_comp sectorFirstEquiv G
  let swapOuterPairsEquiv :
      (Fin d × Fin d × Fin d × Fin d) ≃ (Fin d × Fin d × Fin d × Fin d) := {
    toFun := fun ⟨i₃, j₃, i₁, j₁⟩ ↦ (i₁, j₁, i₃, j₃)
    invFun := fun ⟨i₁, j₁, i₃, j₃⟩ ↦ (i₃, j₃, i₁, j₁)
    left_inv := by rintro ⟨i₃, j₃, i₁, j₁⟩; rfl
    right_inv := by rintro ⟨i₁, j₁, i₃, j₃⟩; rfl }
  have sum_pair_swap (f : Fin d → Fin d → Fin d → Fin d → ℂ) :
      (∑ i₃, ∑ j₃, ∑ i₁, ∑ j₁, f i₁ j₁ i₃ j₃) =
        ∑ i₁, ∑ j₁, ∑ i₃, ∑ j₃, f i₁ j₁ i₃ j₃ := by
    let G : Fin d × Fin d × Fin d × Fin d → ℂ :=
      fun ⟨i₁, j₁, i₃, j₃⟩ ↦ f i₁ j₁ i₃ j₃
    simpa [Fintype.sum_prod_type, G, swapOuterPairsEquiv] using
      Equiv.sum_comp swapOuterPairsEquiv G
  have hRegroup :
      (∑ i₁ : Fin d, ∑ j₁ : Fin d, ∑ i₃ : Fin d, ∑ j₃ : Fin d,
          C x (i₁, j₁) * C y (i₃, j₃) *
            ∑ s : Fin g, Matrix.trace (K s i₁ j₁ * K s i₂ j₂ * K s i₃ j₃ * R s)) =
        ∑ s : Fin g, Matrix.trace (L x s * K s i₂ j₂ * L y s * R s) := by
    simp only [L, Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    simp_rw [Finset.mul_sum]
    rw [sum_sector_first]
    apply Finset.sum_congr rfl
    intro s _
    rw [sum_pair_swap]
    apply Finset.sum_congr rfl
    intro i₁ _
    apply Finset.sum_congr rfl
    intro j₁ _
    apply Finset.sum_congr rfl
    intro i₃ _
    apply Finset.sum_congr rfl
    intro j₃ _
    ring
  rw [hRegroup]
  have hL (z : MPSTensor.BlockEntryIndex dim) (s : Fin g) :
      L z s = if h : z.1 = s then
        Matrix.single (h ▸ z.2.1) (h ▸ z.2.2) (1 : ℂ)
      else 0 := hInv z s
  simp_rw [hL]
  by_cases hxy : x.1 = y.1
  · have hsysx : sx = sy := by simpa [x, y] using hxy
    subst sy
    rw [dif_pos rfl, Finset.sum_eq_single sx]
    · simp [x, y, Matrix.trace_single_mul]
    · intro s _ hs
      have hxs : sx ≠ s := Ne.symm hs
      simp [x, y, hxs]
    · simp
  · rw [dif_neg hxy]
    apply Finset.sum_eq_zero
    intro s _
    by_cases hxs : x.1 = s
    · have hys : y.1 ≠ s := by
        intro hys
        exact hxy (hxs.trans hys.symm)
      simp [hxs, hys]
    · simp [hxs]

/-- A one-letter simultaneous word span supplies inverse tensors whose two
outer contractions of every three-site family closure leave the selected
middle slice and closing entry.

**Local fix (tail index):** the closing entry has the corrected orientation
$R_s(\beta_3,\alpha_1)$ documented in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

The corrected orientation comes from the Case I display at lines 1422--1438;
the family inverse is constructed at lines 1666--1676 and used in Case II at
lines 1719--1732.

Source: arXiv:1606.00608, Appendix C.2, lines 1422--1438, 1666--1676,
and 1719--1732. -/
theorem exists_isMPOBlockLeftInverse_outer_inverse_threeSite_collapse
    (K : (s : Fin g) → MPOTensor d (dim s))
    (hSpan : MPSTensor.WordTupleSpanTop (fun s ↦ (K s).toMPSTensor) 1) :
    ∃ C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ,
      MPSTensor.IsMPOBlockLeftInverse K C ∧
        ∀ (R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ)
          (ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ),
          IsThreeSiteFamilyClosure K R ρ →
            ∀ (x y : MPSTensor.BlockEntryIndex dim) (i₂ j₂ : Fin d),
              outerInverseContraction C ρ x y i₂ j₂ =
                if h : x.1 = y.1 then
                  K x.1 i₂ j₂ x.2.2 (h.symm ▸ y.2.1) *
                    R x.1 (h.symm ▸ y.2.2) x.2.1
                else 0 := by
  obtain ⟨C, hC⟩ := hSpan.exists_mpo_block_left_inverse
  refine ⟨C, hC, ?_⟩
  intro R ρ hρ
  exact isMPOBlockLeftInverse_outer_inverse_threeSite_collapse hC hρ

end MPOTensor
