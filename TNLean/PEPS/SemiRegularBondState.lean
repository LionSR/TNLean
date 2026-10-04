/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegionPhysicalMap
import TNLean.Algebra.ComplexSqrt

/-!
# Coherent bond states under restoration of representation multiplicities

The multiplicity-restoring bond isometry maps a matrix unit to the normalized
sum over equal multiplicity labels. Its coefficient matrix is an isometry,
and its product over any finite family of bonds carries every coherent sum
of weighted bond vectors to the corresponding sum of repeated bond vectors.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Section 7,
`Papers/1001.3807/paper_v3.tex`, lines 2992–3019. The input label may record
an irreducible block and its row and column. This module concerns the displayed
bond-vector sums; rewriting the site tensors with the source's fourth-root
weights is separate.
-/

open scoped Matrix BigOperators

namespace TNLean.PEPS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (μ : ι → Type*) [∀ i, Fintype (μ i)] [∀ i, DecidableEq (μ i)]

/-- The coefficient matrix of the multiplicity-restoring bond map. The row
contains an original matrix-unit label and two multiplicity labels; only equal
multiplicity labels have nonzero coefficients. Source: SCP10, Section 7,
lines 3008–3019. -/
noncomputable def multiplicityBondCoefficientMatrix :
    Matrix (Σ i, μ i × μ i) ι ℂ :=
  fun r c => if r.1 = c ∧ r.2.1 = r.2.2 then
    (Real.sqrt (Fintype.card (μ r.1) : ℝ) : ℂ)⁻¹ else 0

/-- Restoration of multiplicities is an isometry on the entire input bond space.
Source: SCP10, Section 7, lines 3008–3019. -/
theorem multiplicityBondCoefficientMatrix_isIsometry [∀ i, Nonempty (μ i)] :
    Matrix.IsIsometry (multiplicityBondCoefficientMatrix μ) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    multiplicityBondCoefficientMatrix, Fintype.sum_sigma, Fintype.sum_prod_type,
    Matrix.one_apply]
  rw [Finset.sum_eq_single i]
  · by_cases h : i = j
    · subst j
      simp only [true_and, Complex.star_def, mul_ite, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true, map_inv₀, Complex.conj_ofReal]
      simp_rw [Complex.ofReal_sqrt_inv_mul_self _ (Nat.cast_nonneg _),
        Complex.ofReal_natCast]
      change (∑ _ : μ i, (Fintype.card (μ i) : ℂ)⁻¹) = 1
      simp [nsmul_eq_mul, Fintype.card_ne_zero]
    · simp [h]
  · intro b _ hbi
    simp [hbi, apply_ite]
  · simp

/-- The action of the bond isometry on any input vector is supported on equal
multiplicity labels. Source: SCP10, Section 7, lines 3008–3019. -/
theorem multiplicityBondCoefficientMatrix_mulVec (x : ι → ℂ)
    (r : Σ i, μ i × μ i) :
    (multiplicityBondCoefficientMatrix μ *ᵥ x) r =
      if r.2.1 = r.2.2 then
        (Real.sqrt (Fintype.card (μ r.1) : ℝ) : ℂ)⁻¹ * x r.1 else 0 := by
  simp [Matrix.mulVec, dotProduct, multiplicityBondCoefficientMatrix, ite_mul,
    ite_and]

/-- The coefficient isometry carries square-root-weighted bond vectors to the
corresponding repeated bond vectors. Source: SCP10, Section 7, lines 2992–3007. -/
theorem multiplicityBondCoefficientMatrix_mulVec_sqrt [∀ i, Nonempty (μ i)]
    (x : ι → ℂ) :
    multiplicityBondCoefficientMatrix μ *ᵥ
      (fun i => (Real.sqrt (Fintype.card (μ i) : ℝ) : ℂ) * x i) =
        fun r => if r.2.1 = r.2.2 then x r.1 else 0 := by
  ext r
  rw [multiplicityBondCoefficientMatrix_mulVec]
  split_ifs
  · rw [← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
      (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr Fintype.card_pos))), one_mul]
  · rfl

section CoherentStates

variable {Edge Q : Type*} [Fintype Edge] [LinearOrder Edge] [Fintype Q]
variable [∀ i, Nonempty (μ i)]

omit [Fintype Edge] in
/-- The product of the multiplicity-restoring bond maps is an isometry on any
finite set of bonds. Source: SCP10, Section 7, lines 3008–3019. -/
theorem regionPhysicalProductMatrix_multiplicityBond_isIsometry (R : Finset Edge) :
    Matrix.IsIsometry (regionPhysicalProductMatrix R
      (fun _ : Edge => multiplicityBondCoefficientMatrix μ)) :=
  regionPhysicalProductMatrix_isIsometry
    (In := fun _ : Edge => ι) (Out := fun _ : Edge => Σ i, μ i × μ i) R
    (fun _ : Edge => multiplicityBondCoefficientMatrix μ)
    (fun _ => multiplicityBondCoefficientMatrix_isIsometry μ)

omit [Fintype Edge] in
/-- The product bond transformation preserves every overlap, including the norm
of any coherent bond state. Source: SCP10, Section 7, lines 3008–3019. -/
theorem regionPhysicalMap_multiplicityBond_dotProduct (R : Finset Edge)
    (ψ φ : ({e // e ∈ R} → ι) → ℂ) :
    star (regionPhysicalMap R (fun _ : Edge => multiplicityBondCoefficientMatrix μ) ψ) ⬝ᵥ
      regionPhysicalMap R (fun _ : Edge => multiplicityBondCoefficientMatrix μ) φ =
        star ψ ⬝ᵥ φ := by
  simp only [regionPhysicalMap, Matrix.mulVecLin_apply]
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    show (regionPhysicalProductMatrix R
      (fun _ : Edge => multiplicityBondCoefficientMatrix μ)).conjTranspose *
      regionPhysicalProductMatrix R
        (fun _ : Edge => multiplicityBondCoefficientMatrix μ) = 1
      from regionPhysicalProductMatrix_multiplicityBond_isIsometry μ R,
    Matrix.vecMul_one]

omit [Fintype Edge] in
/-- Every coherent sum of square-root-weighted bond products is carried to
its repeated-multiplicity counterpart by a product of bond isometries.
Source: SCP10, Section 7, lines 2992–3019. The labels may encode the
irreducible block and both matrix indices. -/
theorem regionPhysicalMap_multiplicityBond_superposition (R : Finset Edge)
    (w : Q → ℂ) (x : Edge → Q → ι → ℂ) :
    regionPhysicalMap R (fun _ : Edge => multiplicityBondCoefficientMatrix μ)
      (fun σ => ∑ q, w q * ∏ e : {e // e ∈ R},
        (Real.sqrt (Fintype.card (μ (σ e)) : ℝ) : ℂ) * x e.1 q (σ e)) =
      fun τ => ∑ q, w q * ∏ e : {e // e ∈ R},
        if (τ e).2.1 = (τ e).2.2 then x e.1 q (τ e).1 else 0 := by
  ext τ
  simp only [regionPhysicalMap_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  calc
    _ = w q * ∑ σ : {e // e ∈ R} → ι, ∏ e : {e // e ∈ R},
        multiplicityBondCoefficientMatrix μ (τ e) (σ e) *
          ((Real.sqrt (Fintype.card (μ (σ e)) : ℝ) : ℂ) * x e.1 q (σ e)) := by
      simp only [Finset.mul_sum, Finset.prod_mul_distrib, mul_left_comm]
    _ = w q * ∏ e : {e // e ∈ R}, ∑ i : ι,
        multiplicityBondCoefficientMatrix μ (τ e) i *
          ((Real.sqrt (Fintype.card (μ i) : ℝ) : ℂ) * x e.1 q i) := by
      rw [Fintype.prod_sum]
    _ = _ := by
      congr 1
      apply Finset.prod_congr rfl
      intro e _
      exact congr_fun (multiplicityBondCoefficientMatrix_mulVec_sqrt μ (x e.1 q)) (τ e)

end CoherentStates

end TNLean.PEPS
