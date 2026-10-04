/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.BalancedGramContraction
import TNLean.MPS.MPU.AffineGramTransfer

/-!
# The success amplitude of a balanced interval merger

The balanced inverse square-root contraction has Hilbert--Schmidt norm
equal to the bond dimension. Dividing by that dimension gives a
normalized virtual-bond contraction. Applying it to two adjacent weighted
intervals gives the weighted parent interval multiplied by the inverse
bond dimension. If the parent is an isometry, the success Gram is the
inverse square of the bond dimension times the identity.

This is the joining-cut calculation in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. The parent isometry is
established separately by the affine Gram normalization argument. The
identities here do not assert the complete recursive circuit theorem.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace MPUCircuit

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The balanced joining contraction divided by its Hilbert--Schmidt norm.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def normalizedBalancedGramContraction (P : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (Fintype.card ι : ℂ)⁻¹ • balancedGramContraction P

/-- The normalized joining contraction has vectorized squared norm one.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem normalizedBalancedGramContraction_vec_inner {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    star (vec (normalizedBalancedGramContraction P)) ⬝ᵥ
      vec (normalizedBalancedGramContraction P) = 1 := by
  have hc : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [normalizedBalancedGramContraction, Matrix.vec_smul, star_smul,
    dotProduct_smul, smul_dotProduct, balancedGramContraction_vec_inner hP]
  simp [hc, pow_two]

/-- The normalized joining contraction cancels both middle weights and gives
exactly the inverse bond dimension times the parent coefficient.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem weighted_interval_normalized_contraction
    {l n : Type*} [Fintype l] [Fintype n]
    (A : Matrix l ι ℂ) (B : Matrix ι n ℂ)
    (L : Matrix l l ℂ) (R : Matrix n n ℂ)
    {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    (L * A * CFC.sqrt (dualGramMetric P)) *
      normalizedBalancedGramContraction P * (CFC.sqrt P * B * R) =
      (Fintype.card ι : ℂ)⁻¹ • (L * (A * B) * R) := by
  rw [normalizedBalancedGramContraction, balancedGramContraction,
    Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (CFC.sqrt (dualGramMetric P)),
    Matrix.mul_nonsing_inv _ (dualGramMetric_posDef hP).isUnit_det_cfc_sqrt,
    Matrix.one_mul, ← Matrix.mul_assoc (CFC.sqrt P)⁻¹,
    Matrix.nonsing_inv_mul _ hP.isUnit_det_cfc_sqrt, Matrix.one_mul]

/-- Vectorized coefficients obtained by contracting the inner bonds of two weighted intervals.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def contractedWeightedIntervals
    {o i o' i' l n : Type*}
    (X : o → i → Matrix l ι ℂ) (Y : o' → i' → Matrix ι n ℂ)
    (C : Matrix ι ι ℂ) : Matrix ((o × o') × (n × l)) (i × i') ℂ :=
  fun p b ↦ vec (X p.1.1 b.1 * C * Y p.1.2 b.2) p.2

/-- Balanced contraction of two adjacent intervals gives the parent interval
with success amplitude equal to the inverse bond dimension.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem contractedWeightedIntervals_balanced
    {o i o' i' l n : Type*} [Fintype l] [Fintype n]
    (A : o → i → Matrix l ι ℂ) (B : o' → i' → Matrix ι n ℂ)
    (L : Matrix l l ℂ) (R : Matrix n n ℂ)
    {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    contractedWeightedIntervals
      (fun a b ↦ L * A a b * CFC.sqrt (dualGramMetric P))
      (fun a b ↦ CFC.sqrt P * B a b * R)
      (normalizedBalancedGramContraction P) =
      (Fintype.card ι : ℂ)⁻¹ •
        vectorizedWeightedInterval
          (fun (a : o × o') (b : i × i') ↦ A a.1 b.1 * B a.2 b.2) L R := by
  ext p b
  exact congrArg (fun M ↦ vec M p.2)
    (weighted_interval_normalized_contraction (A p.1.1 b.1) (B p.1.2 b.2) L R hP)

open scoped Classical in
/-- An isometric parent makes the merger probability uniform on the entire
physical input space, including all off-diagonal Gram entries.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem contractedWeightedIntervals_balanced_gram
    {o i o' i' l n : Type*}
    [Fintype o] [Fintype o'] [Fintype l] [Fintype n]
    (A : o → i → Matrix l ι ℂ) (B : o' → i' → Matrix ι n ℂ)
    (L : Matrix l l ℂ) (R : Matrix n n ℂ)
    {P : Matrix ι ι ℂ} (hP : P.PosDef)
    (hV : (vectorizedWeightedInterval
      (fun (a : o × o') (b : i × i') ↦ A a.1 b.1 * B a.2 b.2) L R)ᴴ *
      vectorizedWeightedInterval
        (fun (a : o × o') (b : i × i') ↦ A a.1 b.1 * B a.2 b.2) L R = 1) :
    let W := contractedWeightedIntervals
      (fun a b ↦ L * A a b * CFC.sqrt (dualGramMetric P))
      (fun a b ↦ CFC.sqrt P * B a b * R)
      (normalizedBalancedGramContraction P)
    Wᴴ * W = ((Fintype.card ι : ℂ)⁻¹)^2 • (1 : Matrix (i × i') (i × i') ℂ) := by
  dsimp only
  rw [contractedWeightedIntervals_balanced A B L R hP]
  simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hV, pow_two]
  simp

end MPUCircuit
