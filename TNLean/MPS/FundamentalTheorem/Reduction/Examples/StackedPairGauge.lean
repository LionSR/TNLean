/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Kraus.Injectivity
import TNLean.MPS.FundamentalTheorem.Reduction.ProjectorWeightedSum

/-!
# The adapted inner-bond basis shared by the P6 renormalization fixed points

The length-dependent renormalization fixed points of the P6 work
(`Notes/OpenProblemsTN/checks/p6_examples_compression_data.md`, examples 1 and 4) are stacked
products of two matrix product operator tensors whose bond space is a tensor square
`ℂ² ⊗ ℂ²`. The stacked bond space `ℂ² ⊗ [ℂ² ⊗ ℂ²] ⊗ ℂ²` then carries a four-dimensional inner
bond, the two half-bonds joined by the letter sum, and the two examples share one adapted basis
of that inner bond: the two Bell vectors `(1, 0, 0, ±1)` followed by the two coordinate vectors
orthogonal to them (`p6_examples_compression_data.md`, §1.3).

This file records that shared geometry once: the reordering of the stacked bond coordinates
into inner and outer factors, the adapted basis and its inverse, the two rank-one idempotents it
produces, and the arithmetic that turns an identity between integer matrices into the
projector-weighted decomposition required by
`MPSTensor.MultiBlockCompression.ofProjectorSum`.

## Main definitions

* `P6Compression.pairReorder`: the reordering of the stacked bond space into the inner bond
  times the outer block space.
* `P6Compression.pairU`, `P6Compression.pairUinv`: the adapted basis of the inner bond.
* `P6Compression.pairProjInt`: the two rank-one idempotents, over the integers.
* `P6Compression.pairBlockInt`: a weighted block placed in the stacked bond coordinates.

## Main results

* `P6Compression.stackedPair_letter_identity`: an integer letter identity, together with the
  matching scalar identity, gives the projector-weighted decomposition of the stacked tensor.
* `P6Compression.isNormal_of_single_eq_smul`: a tensor whose letters realise every matrix unit
  up to a nonzero factor is normal at blocking length one.
-/

open scoped Matrix Kronecker

namespace P6Compression

open MPSTensor

/-! ### The reordering of the stacked bond space -/

/-- The reordering of the stacked bond space. A stacked bond coordinate is a quadruple
`(L₁, R₁, L₂, R₂)` of bits, encoded as `8 L₁ + 4 R₁ + 2 L₂ + R₂`; the inner bond is
`(R₁, L₂)`, encoded as `2 R₁ + L₂`, and the outer block space is `(L₁, R₂)`, encoded as
`2 L₁ + R₂` (`p6_examples_compression_data.md`, §1.2). -/
def pairReorder : Fin 4 × Fin 4 ≃ Fin 16 where
  toFun x := ![![0, 1, 8, 9], ![2, 3, 10, 11], ![4, 5, 12, 13], ![6, 7, 14, 15]] x.1 x.2
  invFun m :=
    (![0, 0, 1, 1, 2, 2, 3, 3, 0, 0, 1, 1, 2, 2, 3, 3] m,
      ![0, 1, 0, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 2, 3] m)
  left_inv := by decide
  right_inv := by decide

/-! ### The adapted basis of the inner bond -/

/-- The adapted basis of the inner bond, in the ordered basis `|00⟩, |01⟩, |10⟩, |11⟩`: the two
Bell vectors followed by the two coordinate vectors orthogonal to them
(`p6_examples_compression_data.md`, §1.3). -/
def pairUInt : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 1; 1, 0, 0, -1; 0, 1, 0, 0; 0, 0, 1, 0]

/-- Twice the inverse of the adapted basis of the inner bond; the factor two is what clears the
denominators of the Bell projectors. -/
def pairUinvInt : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 1, 0, 0; 0, 0, 2, 0; 0, 0, 0, 2; 1, -1, 0, 0]

/-- The adapted basis of the inner bond. -/
def pairU : Matrix (Fin 4) (Fin 4) ℂ := complexOfInt pairUInt

/-- The inverse of the adapted basis of the inner bond. -/
noncomputable def pairUinv : Matrix (Fin 4) (Fin 4) ℂ := (2 : ℂ)⁻¹ • complexOfInt pairUinvInt

private theorem pairUInt_mul_pairUinvInt :
    pairUInt * pairUinvInt = (2 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by decide

private theorem pairUinvInt_mul_pairUInt :
    pairUinvInt * pairUInt = (2 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by decide

theorem pairU_mul_pairUinv : pairU * pairUinv = 1 := by
  rw [pairU, pairUinv, Matrix.mul_smul, ← complexOfInt_mul, pairUInt_mul_pairUinvInt,
    complexOfInt_zsmul, complexOfInt_one, smul_smul]
  norm_num

theorem pairUinv_mul_pairU : pairUinv * pairU = 1 := by
  rw [pairU, pairUinv, Matrix.smul_mul, ← complexOfInt_mul, pairUinvInt_mul_pairUInt,
    complexOfInt_zsmul, complexOfInt_one, smul_smul]
  norm_num

/-! ### The two weighted slots -/

/-- The two weighted slots of a stacked pair fixed point. -/
abbrev pairSlots : Finset (Fin 2) := Finset.univ

/-- The inner-bond basis vector carrying each weighted slot: the two Bell vectors. -/
def pairJ : Fin 2 → Fin 4 := ![0, 1]

/-- The labelling of the adapted basis of the inner bond by the two weighted slots and the two
remaining basis vectors. -/
def pairRho : {s // s ∈ pairSlots} ⊕ Fin 2 ≃ Fin 4 where
  toFun := Sum.elim (fun s => pairJ s.1) ![2, 3]
  invFun
    | 0 => Sum.inl ⟨0, Finset.mem_univ 0⟩
    | 1 => Sum.inl ⟨1, Finset.mem_univ 1⟩
    | 2 => Sum.inr 0
    | 3 => Sum.inr 1
  left_inv := by decide
  right_inv := by decide

theorem pairRho_inl (s : {s // s ∈ pairSlots}) : pairRho (Sum.inl s) = pairJ s.1 := rfl

/-- The two rank-one idempotents of the inner bond, over the integers: twice the Bell
projectors. -/
def pairProjInt (s : Fin 2) : Matrix (Fin 4) (Fin 4) ℤ :=
  basisProj pairUInt pairUinvInt (pairJ s)

theorem basisProj_pairJ (s : Fin 2) :
    basisProj pairU pairUinv (pairJ s) = (2 : ℂ)⁻¹ • complexOfInt (pairProjInt s) := by
  rw [pairU, pairUinv, basisProj_smul, pairProjInt, complexOfInt_basisProj]

/-! ### From an integer letter identity to a projector-weighted decomposition -/

variable {d : ℕ}

/-- A weighted block of a stacked pair fixed point, placed in the stacked bond coordinates, over
the integers. -/
def pairBlockInt (CInt : Fin 2 → Fin d → Matrix (Fin 4) (Fin 4) ℤ) (s : Fin 2) (a : Fin d) :
    Matrix (Fin 16) (Fin 16) ℤ :=
  (pairProjInt s ⊗ₖ CInt s a).submatrix pairReorder.symm pairReorder.symm

/-- **The projector-weighted decomposition of a stacked pair fixed point.** If the stacked
tensor and the two target blocks are rescaled integer tensors, if the weights satisfy the scalar
identity `n μ_s / (2 c_C) = k_s c_B`, and if the rescaled letters satisfy the integer identity
`n B^a = ∑_s k_s (Π_s ⊗ C_s^a)`, then the stacked tensor is the projector-weighted sum required
by `MPSTensor.MultiBlockCompression.ofProjectorSum`. -/
theorem stackedPair_letter_identity {B : MPSTensor d 16} {C : Fin 2 → MPSTensor d 4}
    {μ : Fin 2 → ℂ} {cB cC : ℂ} {BInt : Fin d → Matrix (Fin 16) (Fin 16) ℤ}
    {CInt : Fin 2 → Fin d → Matrix (Fin 4) (Fin 4) ℤ} {n : ℤ} {k : Fin 2 → ℤ}
    (hn : (n : ℂ) ≠ 0) (hB : ∀ a, B a = cB • complexOfInt (BInt a))
    (hC : ∀ s a, C s a = cC • complexOfInt (CInt s a))
    (hscal : ∀ s, (n : ℂ) * (μ s * ((2 : ℂ)⁻¹ * cC)) = (k s : ℂ) * cB)
    (hint : ∀ a, n • BInt a = ∑ s, k s • pairBlockInt CInt s a) (a : Fin d) :
    B a = (∑ s ∈ pairSlots, μ s •
      (basisProj pairU pairUinv (pairJ s) ⊗ₖ C s a)).submatrix
        pairReorder.symm pairReorder.symm := by
  have hrhs : (∑ s ∈ pairSlots, μ s •
        (basisProj pairU pairUinv (pairJ s) ⊗ₖ C s a)).submatrix
          pairReorder.symm pairReorder.symm =
      ∑ s : Fin 2, (μ s * ((2 : ℂ)⁻¹ * cC)) • complexOfInt (pairBlockInt CInt s a) := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.kroneckerMap_apply, basisProj_pairJ, hC, complexOfInt_apply, pairBlockInt]
    refine Finset.sum_congr rfl fun s _ => ?_
    push_cast
    ring
  have hi : (n : ℂ) • complexOfInt (BInt a) =
      ∑ s : Fin 2, (k s : ℂ) • complexOfInt (pairBlockInt CInt s a) := by
    rw [← complexOfInt_zsmul, hint a, complexOfInt_sum]
    exact Finset.sum_congr rfl fun s _ => complexOfInt_zsmul _ _
  rw [hrhs, hB a]
  refine smul_right_injective (Matrix (Fin 16) (Fin 16) ℂ) hn ?_
  calc (n : ℂ) • (cB • complexOfInt (BInt a))
      = cB • ((n : ℂ) • complexOfInt (BInt a)) := smul_comm _ _ _
    _ = cB • ∑ s : Fin 2, (k s : ℂ) • complexOfInt (pairBlockInt CInt s a) := by rw [hi]
    _ = ∑ s : Fin 2, (cB * (k s : ℂ)) • complexOfInt (pairBlockInt CInt s a) := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun s _ => smul_smul _ _ _
    _ = (n : ℂ) • ∑ s : Fin 2,
          (μ s * ((2 : ℂ)⁻¹ * cC)) • complexOfInt (pairBlockInt CInt s a) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [smul_smul, hscal s, mul_comm]

/-! ### Normality at blocking length one -/

/-- **Normality from a table of scaled matrix units.** A tensor whose letters are rescaled
integer matrices and which realises every matrix unit as a nonzero integer multiple of one of
its letters spans the full matrix algebra, hence is normal at blocking length one. -/
theorem isNormal_of_single_eq_smul {D : ℕ} {A : MPSTensor d D}
    (AInt : Fin d → Matrix (Fin D) (Fin D) ℤ) {c : ℂ} (hc : c ≠ 0)
    (hA : ∀ a, A a = c • complexOfInt (AInt a)) (ℓ : Fin D → Fin D → Fin d)
    (w : Fin D → Fin D → ℤ) (hw : ∀ x y, w x y ≠ 0)
    (h : ∀ x y, AInt (ℓ x y) = w x y • Matrix.single x y 1) :
    Kraus.IsNormal A := by
  refine Kraus.IsInjective.isNormal (top_unique fun X _ => ?_)
  have hsingle : ∀ x y : Fin D,
      complexOfInt (Matrix.single x y (1 : ℤ)) = Matrix.single x y (1 : ℂ) := by
    intro x y
    ext p q
    simp [complexOfInt, Matrix.single_apply]
  have hmem : ∀ x y : Fin D,
      Matrix.single x y (1 : ℂ) ∈ Submodule.span ℂ (Set.range A) := by
    intro x y
    have hAl : A (ℓ x y) = (c * (w x y : ℂ)) • Matrix.single x y (1 : ℂ) := by
      rw [hA, h x y, complexOfInt_zsmul, smul_smul, hsingle]
    have hne : c * (w x y : ℂ) ≠ 0 :=
      mul_ne_zero hc (Int.cast_ne_zero.mpr (hw x y))
    have hmul := Submodule.smul_mem (Submodule.span ℂ (Set.range A)) (c * (w x y : ℂ))⁻¹
      (Submodule.subset_span (Set.mem_range_self (ℓ x y)))
    rwa [hAl, smul_smul, inv_mul_cancel₀ hne, one_smul] at hmul
  rw [Matrix.matrix_eq_sum_single X]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using
    Submodule.smul_mem _ (X i j) (hmem i j)

end P6Compression
