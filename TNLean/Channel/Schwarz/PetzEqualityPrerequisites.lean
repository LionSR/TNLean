/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Schwarz.PetzRecoverySupport
import TNLean.Channel.Schwarz.SSAEqualityDPI
import TNLean.Analysis.SuperoperatorResolvent
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Singular-support prerequisites for equality in data processing

This file records analytic identities needed to study equality in the
relative-entropy data-processing inequality without imposing invertibility on
the positive semidefinite matrices.

## Main result

* `Matrix.PosSemidef.supportInvSqrt_kronecker_maximallyMixed` computes the
  support inverse square root of a maximally mixed extension.
* `Matrix.PosSemidef.supportInvSqrt_kronecker_maximallyMixed_mul_mul` cancels
  the dimension factors in the corresponding support sandwich.
* `quantumRelativeEntropy_kronecker_support` proves ancilla additivity on the
  finite-relative-entropy support domain.
* `quantumRelativeEntropy_weyl_average_eq_summand_of_partialTraceRight_eq`
  propagates saturation of partial-trace data processing to each summand in the
  finite Weyl average.
* `quantumRelativeEntropy_weyl_jensen_eq_of_partialTraceRight_eq` identifies
  saturation of the finite Jensen inequality in the Weyl proof.
* `Matrix.partialTraceRightPetzMap_eq_of_weyl_identity_sandwich` reduces the
  identity-summand support sandwich to the native raw partial-trace Petz map.
* `Matrix.weyl_resolvent_defect_identity` proves the positive-definite,
  fixed-`t` squared-defect identity for the finite Weyl family.
* `Matrix.weyl_resolvent_eq_of_defect_eq_zero` shows that zero defect gives
  the common resolvent solution for every Weyl summand.

## References

* P. Hayden, R. Jozsa, D. Petz, and A. Winter, *Structure of States Which
  Satisfy Strong Subadditivity of Quantum Entropy with Equality*, Theorem 3,
  arXiv:quant-ph/0304007v2.
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace Matrix

/-- The support inverse square root of a positive semidefinite left factor
tensored with the maximally mixed right factor is the lifted support inverse
square root multiplied by the square root of the right dimension.

This is the functional-calculus normalization in the identity-summand
specialization of Hayden--Jozsa--Petz--Winter,
arXiv:quant-ph/0304007v2, Theorem 3, equation (8). -/
theorem PosSemidef.supportInvSqrt_kronecker_maximallyMixed
    {m : Type*} [Fintype m] [DecidableEq m] {dC : ℕ} [NeZero dC]
    {σ : Matrix m m ℂ} (hσ : σ.PosSemidef) :
    (hσ.kronecker maximallyMixed_posDef.posSemidef).supportInvSqrt =
      (Real.sqrt dC : ℂ) •
        (hσ.supportInvSqrt ⊗ₖ (1 : Matrix (ZMod dC) (ZMod dC) ℂ)) := by
  have hdCpos : (0 : ℝ) < dC := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dC)
  have hbase := Matrix.PosSemidef.supportInvSqrt_smul
    (hσ.kronecker (Matrix.PosSemidef.one (n := ZMod dC))) (inv_pos.mpr hdCpos)
  convert hbase using 1
  · congr 1
    rw [Matrix.kronecker_smul, ← Complex.coe_smul, Complex.ofReal_inv,
      Complex.ofReal_natCast]
  · rw [Matrix.PosSemidef.supportInvSqrt_kronecker_one, Real.sqrt_inv, inv_inv]
    · rw [Complex.coe_smul]

/-- Sandwiching a left-tensored matrix by the support inverse square root of a
maximally-mixed extension cancels the dimension factors and gives the unital
left tensor embedding.

This is the tensor normalization needed to reduce the identity Weyl summand to
the support Petz formula in Hayden--Jozsa--Petz--Winter,
arXiv:quant-ph/0304007v2, Theorem 3, equation (8). -/
theorem PosSemidef.supportInvSqrt_kronecker_maximallyMixed_mul_mul
    {m : Type*} [Fintype m] [DecidableEq m] {dC : ℕ} [NeZero dC]
    {σ X : Matrix m m ℂ} (hσ : σ.PosSemidef) :
    let hbarσ := hσ.kronecker maximallyMixed_posDef.posSemidef
    hbarσ.supportInvSqrt *
        (X ⊗ₖ ((dC : ℂ)⁻¹ • (1 : Matrix (ZMod dC) (ZMod dC) ℂ))) *
        hbarσ.supportInvSqrt =
      leftKroneckerEmbed (n := ZMod dC)
        (hσ.supportInvSqrt * X * hσ.supportInvSqrt) := by
  dsimp only
  rw [Matrix.PosSemidef.supportInvSqrt_kronecker_maximallyMixed hσ,
    Matrix.kronecker_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.leftKroneckerEmbed_apply]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.mul_one]
  have hdC : (dC : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne dC
  have hsqrt : ((Real.sqrt dC : ℝ) : ℂ) * ((dC : ℂ)⁻¹ * Real.sqrt dC) = 1 := by
    rw [mul_comm (dC : ℂ)⁻¹, ← mul_assoc, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by positivity), Complex.ofReal_natCast, mul_inv_cancel₀ hdC]
  rw [hsqrt, one_smul]

/-- If the identity summand of the finite Weyl mixture satisfies the support
Petz sandwich identity, then the native raw partial-trace Petz map recovers the
original matrix.

The sandwich hypothesis is the operator equality that must still be obtained
from equality in the finite Weyl Jensen step. This theorem performs only the
algebraic reduction of that hypothesis to the support formula in
Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2, Theorem 3,
equation (8); it does not derive the hypothesis from scalar relative-entropy
equality. -/
theorem partialTraceRightPetzMap_eq_of_weyl_identity_sandwich
    {dS dC : ℕ} [NeZero dC]
    {ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hσ : σ.PosSemidef)
    (hSandwich :
      let hbarσ := (PosSemidef.partialTraceRight hσ).kronecker
        maximallyMixed_posDef.posSemidef
      hσ.isHermitian.cfc Real.sqrt *
          (hbarσ.supportInvSqrt *
            (partialTraceRight ρ ⊗ₖ
              ((dC : ℂ)⁻¹ • (1 : Matrix (ZMod dC) (ZMod dC) ℂ))) *
            hbarσ.supportInvSqrt) *
          hσ.isHermitian.cfc Real.sqrt = ρ) :
    partialTraceRightPetzMap σ hσ (partialTraceRight ρ) = ρ := by
  rw [partialTraceRightPetzMap_apply]
  rw [← Matrix.PosSemidef.supportInvSqrt_kronecker_maximallyMixed_mul_mul
    (X := partialTraceRight ρ) (PosSemidef.partialTraceRight hσ)]
  exact hSandwich

end Matrix

/-- **Ancilla additivity on the singular support domain.** Let `ρ` and `σ` be
positive semidefinite matrices with `ker σ ⊆ ker ρ`, and let `τ` be a positive
semidefinite matrix of unit trace. Then
`D(ρ ⊗ τ ‖ σ ⊗ τ) = D(ρ ‖ σ)`.

The singular tensor-logarithm formula introduces the support projections of
`ρ`, `σ`, and `τ`. The common ancilla-logarithm contribution cancels because
the kernel inclusion makes both system support projections absorb `ρ`; the
remaining factor is multiplied by `trace τ = 1`.

This removes the positive-definite scope restriction from the ancilla identity
used in the Weyl-twirl route to partial-trace data processing. It is an analytic
prerequisite for the equality implication in Hayden--Jozsa--Petz--Winter,
arXiv:quant-ph/0304007v2, Theorem 3; it does not itself assert recovery. -/
theorem quantumRelativeEntropy_kronecker_support
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {ρ σ : Matrix m m ℂ} {τ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hτ : τ.PosSemidef)
    (hτtrace : τ.trace = 1)
    (hsupp : ∀ v : m → ℂ, σ.mulVec v = 0 → ρ.mulVec v = 0) :
    quantumRelativeEntropy (ρ ⊗ₖ τ) (σ ⊗ₖ τ) =
      quantumRelativeEntropy ρ σ := by
  have hσabsorb :
      hσ.isHermitian.supportProj * ρ * hσ.isHermitian.supportProj = ρ :=
    Matrix.IsHermitian.supportProj_mul_mul_supportProj_of_mulVec_kernel_le
      hσ.isHermitian hρ.isHermitian hsupp
  have hρPσ : ρ * hσ.isHermitian.supportProj = ρ := by
    calc
      ρ * hσ.isHermitian.supportProj =
          (hσ.isHermitian.supportProj * ρ * hσ.isHermitian.supportProj) *
            hσ.isHermitian.supportProj := by rw [hσabsorb]
      _ = hσ.isHermitian.supportProj * ρ *
          (hσ.isHermitian.supportProj * hσ.isHermitian.supportProj) := by
            simp only [Matrix.mul_assoc]
      _ = hσ.isHermitian.supportProj * ρ * hσ.isHermitian.supportProj := by
            rw [hσ.isHermitian.supportProj_idem]
      _ = ρ := hσabsorb
  have hρPρ : ρ * hρ.isHermitian.supportProj = ρ :=
    hρ.isHermitian.mul_supportProj_self
  have hτPτ : τ * hτ.isHermitian.supportProj = τ :=
    hτ.isHermitian.mul_supportProj_self
  rw [quantumRelativeEntropy, quantumRelativeEntropy,
    Matrix.log_kronecker_posSemidef hρ hτ,
    Matrix.log_kronecker_posSemidef hσ hτ]
  simp only [Matrix.mul_sub, Matrix.mul_add, ← Matrix.mul_kronecker_mul,
    Matrix.trace_sub, Matrix.trace_add, Matrix.trace_kronecker,
    Complex.sub_re, Complex.add_re]
  rw [hρPρ, hρPσ, hτPτ, hτtrace]
  ring_nf

/-- **Partial-trace saturation propagates to every Weyl summand.** Let `ρ` and
`σ` be positive semidefinite matrices with `ker σ ⊆ ker ρ`. If their relative
entropy is unchanged by the right partial trace, then the relative entropy of
the finite Weyl average equals that of each Weyl-conjugated pair.

The Weyl average is first identified by the normalized identity
\[
d_C^{-2}\sum_{c,e}(\mathbf 1_S\otimes W(c,e))X
  (\mathbf 1_S\otimes W(c,e))^\dagger
  = (\operatorname{tr}_C X)\otimes(d_C^{-1}\mathbf 1_C).
\]
Singular-support ancilla additivity reduces its relative entropy to that of the
marginals, while unitary invariance reduces the chosen summand to
\(D(\rho\Vert\sigma)\). The saturation hypothesis identifies these two values.

This is an equality-propagation prerequisite for Hayden--Jozsa--Petz--Winter,
arXiv:quant-ph/0304007v2, Theorem 3 and equation (8); it does not assert the
equality condition for joint convexity or Petz recovery. -/
theorem quantumRelativeEntropy_weyl_average_eq_summand_of_partialTraceRight_eq
    {dS dC : ℕ} [NeZero dC]
    {ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hsupp : ∀ v : Fin dS × ZMod dC → ℂ, σ.mulVec v = 0 → ρ.mulVec v = 0)
    (heq : quantumRelativeEntropy ρ σ =
      quantumRelativeEntropy (partialTraceRight ρ) (partialTraceRight σ))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ dC) (a b : ZMod dC) :
    quantumRelativeEntropy
        (((dC : ℂ) ^ 2)⁻¹ • ∑ c : ZMod dC, ∑ e : ZMod dC,
          ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e) * ρ *
            ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e)ᴴ)
        (((dC : ℂ) ^ 2)⁻¹ • ∑ c : ZMod dC, ∑ e : ZMod dC,
          ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e) * σ *
            ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e)ᴴ) =
      quantumRelativeEntropy
        (((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ a b) * ρ *
          ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ a b)ᴴ)
        (((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ a b) * σ *
          ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ a b)ᴴ) := by
  classical
  have hsuppM : ∀ w : Fin dS → ℂ,
      (partialTraceRight σ).mulVec w = 0 → (partialTraceRight ρ).mulVec w = 0 :=
    fun _ hw => partialTraceRight_support hσ hsupp hw
  calc
    quantumRelativeEntropy
        (((dC : ℂ) ^ 2)⁻¹ • ∑ c : ZMod dC, ∑ e : ZMod dC,
          ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e) * ρ *
            ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e)ᴴ)
        (((dC : ℂ) ^ 2)⁻¹ • ∑ c : ZMod dC, ∑ e : ZMod dC,
          ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e) * σ *
            ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e)ᴴ) =
        quantumRelativeEntropy
          (partialTraceRight ρ ⊗ₖ
            ((dC : ℂ)⁻¹ • (1 : Matrix (ZMod dC) (ZMod dC) ℂ)))
          (partialTraceRight σ ⊗ₖ
            ((dC : ℂ)⁻¹ • (1 : Matrix (ZMod dC) (ZMod dC) ℂ))) := by
              rw [sum_kronecker_one_weyl_conj hζ ρ,
                sum_kronecker_one_weyl_conj hζ σ]
    _ = quantumRelativeEntropy (partialTraceRight ρ) (partialTraceRight σ) :=
      quantumRelativeEntropy_kronecker_support hρ.partialTraceRight
        hσ.partialTraceRight maximallyMixed_posDef.posSemidef maximallyMixed_trace hsuppM
    _ = quantumRelativeEntropy ρ σ := heq.symm
    _ = quantumRelativeEntropy
        (((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ a b) * ρ *
          ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ a b)ᴴ)
        (((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ a b) * σ *
          ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ a b)ᴴ) := by
            exact (quantumRelativeEntropy_weyl_conj_eq hρ.isHermitian
              hσ.isHermitian hζ a b).symm

/-- **Partial-trace saturation saturates the finite Weyl Jensen inequality.**
Let ρ and σ be positive semidefinite matrices with ker σ ⊆ ker ρ. If their
relative entropy is unchanged by the right partial trace, then the relative
entropy of the finite Weyl average equals the uniform average of the relative
entropies of the Weyl-conjugated pairs.

This is the first equality-sensitive inequality in the finite Weyl proof of
partial-trace data processing. It is a scalar equality-propagation prerequisite
for Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2, Theorem 3 and equation
(8); it does not characterize equality in joint convexity or assert an operator
intertwining or Petz recovery identity. -/
theorem quantumRelativeEntropy_weyl_jensen_eq_of_partialTraceRight_eq
    {dS dC : ℕ} [NeZero dC]
    {ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hsupp : ∀ v : Fin dS × ZMod dC → ℂ, σ.mulVec v = 0 → ρ.mulVec v = 0)
    (heq : quantumRelativeEntropy ρ σ =
      quantumRelativeEntropy (partialTraceRight ρ) (partialTraceRight σ))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ dC) :
    quantumRelativeEntropy
        (((dC : ℂ) ^ 2)⁻¹ • ∑ c : ZMod dC, ∑ e : ZMod dC,
          ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e) * ρ *
            ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e)ᴴ)
        (((dC : ℂ) ^ 2)⁻¹ • ∑ c : ZMod dC, ∑ e : ZMod dC,
          ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e) * σ *
            ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e)ᴴ) =
      ∑ c : ZMod dC, ∑ e : ZMod dC, ((dC : ℝ) ^ 2)⁻¹ •
        quantumRelativeEntropy
          (((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e) * ρ *
            ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e)ᴴ)
          (((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e) * σ *
            ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e)ᴴ) := by
  classical
  have hterm (c e : ZMod dC) :
      quantumRelativeEntropy
          (((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e) * ρ *
            ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e)ᴴ)
          (((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e) * σ *
            ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e)ᴴ) =
        quantumRelativeEntropy ρ σ := by
    exact quantumRelativeEntropy_weyl_conj_eq hρ.isHermitian hσ.isHermitian
      hζ c e
  have haverage :
      quantumRelativeEntropy
          (((dC : ℂ) ^ 2)⁻¹ • ∑ c : ZMod dC, ∑ e : ZMod dC,
            ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e) * ρ *
              ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e)ᴴ)
          (((dC : ℂ) ^ 2)⁻¹ • ∑ c : ZMod dC, ∑ e : ZMod dC,
            ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e) * σ *
              ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e)ᴴ) =
        quantumRelativeEntropy ρ σ := by
    calc
      _ = quantumRelativeEntropy
          (((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ 0 0) * ρ *
            ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ 0 0)ᴴ)
          (((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ 0 0) * σ *
            ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ 0 0)ᴴ) :=
        quantumRelativeEntropy_weyl_average_eq_summand_of_partialTraceRight_eq
          hρ hσ hsupp heq hζ 0 0
      _ = quantumRelativeEntropy ρ σ := hterm 0 0
  rw [haverage]
  simp_rw [hterm]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
    smul_eq_mul]
  have hdC : (dC : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne dC
  field_simp [hdC]

namespace Matrix

variable {n : Type*} [Fintype n]

private lemma star_mulVec_dotProduct (S : Matrix n n ℂ) (hS : S.IsHermitian)
    (x y : n → ℂ) :
    star (S *ᵥ x) ⬝ᵥ y = star x ⬝ᵥ (S *ᵥ y) := by
  rw [star_mulVec, ← Matrix.dotProduct_mulVec, hS.eq]

variable [DecidableEq n]

private lemma resolvent_residual_expand (S : Matrix n n ℂ) (hS : S.PosDef)
    (b x : n → ℂ) :
    dotProduct (star (b - S *ᵥ x)) (S⁻¹ *ᵥ (b - S *ᵥ x)) =
      dotProduct (star b) (S⁻¹ *ᵥ b) - dotProduct (star b) x -
        dotProduct (star x) b + dotProduct (star x) (S *ᵥ x) := by
  letI : Invertible S := hS.isUnit.invertible
  have hinv (y : n → ℂ) : S⁻¹ *ᵥ (S *ᵥ y) = y := by
    rw [mulVec_mulVec, inv_mul_of_invertible, one_mulVec]
  have hinv' (y : n → ℂ) : S *ᵥ (S⁻¹ *ᵥ y) = y := by
    rw [mulVec_mulVec, mul_inv_of_invertible, one_mulVec]
  simp only [star_sub, sub_dotProduct, mulVec_sub, dotProduct_sub, hinv]
  rw [star_mulVec_dotProduct S hS.isHermitian]
  rw [hinv']
  rw [star_mulVec_dotProduct S hS.isHermitian]
  ring

private theorem resolvent_residual_identity
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (S : ι → Matrix n n ℂ) (b : ι → n → ℂ)
    (hS : ∀ i, (S i).PosDef) :
    let Sbar := ∑ i, S i
    let bbar := ∑ i, b i
    let x := Sbar⁻¹ *ᵥ bbar
    ∑ i, dotProduct (star (b i - S i *ᵥ x))
      ((S i)⁻¹ *ᵥ (b i - S i *ᵥ x)) =
      (∑ i, dotProduct (star (b i)) ((S i)⁻¹ *ᵥ b i)) -
        dotProduct (star bbar) (Sbar⁻¹ *ᵥ bbar) := by
  classical
  dsimp only
  let Sbar : Matrix n n ℂ := ∑ i, S i
  let bbar : n → ℂ := ∑ i, b i
  let x : n → ℂ := Sbar⁻¹ *ᵥ bbar
  have hSbar : Sbar.PosDef := by
    exact Matrix.posDef_sum Finset.univ_nonempty (fun i _ ↦ hS i)
  letI : Invertible Sbar := hSbar.isUnit.invertible
  have hx : Sbar *ᵥ x = bbar := by
    simp only [x, mulVec_mulVec, mul_inv_of_invertible, one_mulVec]
  have hsumStarB : ∑ i, star (b i) = star bbar := by
    ext j
    simp [bbar]
  have hsumB : ∑ i, b i = bbar := rfl
  have hsumSx : ∑ i, S i *ᵥ x = Sbar *ᵥ x := by
    simpa [Sbar] using (Matrix.sum_mulVec Finset.univ S x).symm
  change (∑ i, dotProduct (star (b i - S i *ᵥ x))
      ((S i)⁻¹ *ᵥ (b i - S i *ᵥ x))) =
    (∑ i, dotProduct (star (b i)) ((S i)⁻¹ *ᵥ b i)) -
      dotProduct (star bbar) x
  simp_rw [resolvent_residual_expand (hS := hS _)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hleft : ∑ i, dotProduct (star (b i)) x = dotProduct (star bbar) x := by
    rw [← hsumStarB]
    simpa using (sum_dotProduct Finset.univ (fun i ↦ star (b i)) x).symm
  have hright : ∑ i, dotProduct (star x) (b i) = dotProduct (star x) bbar := by
    rw [← hsumB]
    simpa using (dotProduct_sum (star x) Finset.univ b).symm
  have hlast : ∑ i, dotProduct (star x) (S i *ᵥ x) =
      dotProduct (star x) (Sbar *ᵥ x) := by
    rw [← hsumSx]
    simpa using (dotProduct_sum (star x) Finset.univ (fun i ↦ S i *ᵥ x)).symm
  rw [hleft, hright, hlast, hx]
  ring

omit [DecidableEq n] in
private lemma sum_norm_sq_eq_re_dotProduct (y : n → ℂ) :
    ∑ p, ‖y p‖ ^ 2 = (dotProduct (star y) y).re := by
  simp [dotProduct, Complex.sq_norm, ← Complex.normSq_eq_conj_mul_self]

private lemma sqrt_inv_mulVec_normSq (S : Matrix n n ℂ) (hS : S.PosDef)
    (r : n → ℂ) :
    ∑ p, ‖((CFC.sqrt S)⁻¹ *ᵥ r) p‖ ^ 2 =
      (dotProduct (star r) (S⁻¹ *ᵥ r)).re := by
  let Q : Matrix n n ℂ := CFC.sqrt S
  have hSnonneg : 0 ≤ S := hS.posSemidef.nonneg
  have hQQ : Q * Q = S := by
    simpa [Q] using CFC.sqrt_mul_sqrt_self S hSnonneg
  have hQunit : IsUnit Q := by
    change IsUnit (CFC.sqrt S)
    rw [CFC.isUnit_sqrt_iff_isStrictlyPositive,
      Matrix.isStrictlyPositive_iff_posDef]
    exact hS
  letI : Invertible Q := hQunit.invertible
  letI : Invertible S := hS.isUnit.invertible
  have hQherm : Q.IsHermitian := by
    change Qᴴ = Q
    simpa only [Q, star_eq_conjTranspose] using
      (CFC.sqrt_nonneg (a := S)).isSelfAdjoint.star_eq
  let y : n → ℂ := Q⁻¹ *ᵥ r
  have hy : Q *ᵥ y = r := by
    simp only [y, mulVec_mulVec, mul_inv_of_invertible, one_mulVec]
  have hSinv : S⁻¹ = Q⁻¹ * Q⁻¹ := by
    rw [← hQQ, Matrix.mul_inv_rev]
  have hcancel : (Q⁻¹ * Q⁻¹) *ᵥ (Q *ᵥ y) = Q⁻¹ *ᵥ y := by
    rw [mulVec_mulVec, Matrix.mul_assoc, inv_mul_of_invertible,
      Matrix.mul_one]
  have hquad : dotProduct (star r) (S⁻¹ *ᵥ r) =
      dotProduct (star y) y := by
    rw [← hy, hSinv, hcancel, star_mulVec_dotProduct Q hQherm]
    rw [mulVec_mulVec, mul_inv_of_invertible, one_mulVec]
  calc
    ∑ p, ‖((CFC.sqrt S)⁻¹ *ᵥ r) p‖ ^ 2 =
        (dotProduct (star y) y).re := by
          simpa only [Q, y] using sum_norm_sq_eq_re_dotProduct y
    _ = (dotProduct (star r) (S⁻¹ *ᵥ r)).re := congrArg Complex.re hquad.symm

private lemma sqrt_defect_eq_sqrt_inv_residual
    (S : Matrix n n ℂ) (hS : S.PosDef) (b x : n → ℂ) :
    (CFC.sqrt S)⁻¹ *ᵥ b - CFC.sqrt S *ᵥ x =
      (CFC.sqrt S)⁻¹ *ᵥ (b - S *ᵥ x) := by
  let Q : Matrix n n ℂ := CFC.sqrt S
  have hQunit : IsUnit Q := by
    change IsUnit (CFC.sqrt S)
    rw [CFC.isUnit_sqrt_iff_isStrictlyPositive,
      Matrix.isStrictlyPositive_iff_posDef]
    exact hS
  letI : Invertible Q := hQunit.invertible
  have hQQ : Q * Q = S := by
    simpa [Q] using CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  change Q⁻¹ *ᵥ b - Q *ᵥ x = Q⁻¹ *ᵥ (b - S *ᵥ x)
  rw [mulVec_sub]
  congr 1
  rw [← hQQ, mulVec_mulVec, ← Matrix.mul_assoc,
    inv_mul_of_invertible, Matrix.one_mul]

private theorem resolvent_sqrt_defect_identity
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (S : ι → Matrix n n ℂ) (b : ι → n → ℂ)
    (hS : ∀ i, (S i).PosDef) :
    let Sbar := ∑ i, S i
    let bbar := ∑ i, b i
    let x := Sbar⁻¹ *ᵥ bbar
    ∑ i, ∑ p, ‖((CFC.sqrt (S i))⁻¹ *ᵥ b i -
      CFC.sqrt (S i) *ᵥ x) p‖ ^ 2 =
      ∑ i, (dotProduct (star (b i)) ((S i)⁻¹ *ᵥ b i)).re -
        (dotProduct (star bbar) (Sbar⁻¹ *ᵥ bbar)).re := by
  classical
  dsimp only
  let Sbar : Matrix n n ℂ := ∑ i, S i
  let bbar : n → ℂ := ∑ i, b i
  let x : n → ℂ := Sbar⁻¹ *ᵥ bbar
  have hresComplex :
      ∑ i, dotProduct (star (b i - S i *ᵥ x))
          ((S i)⁻¹ *ᵥ (b i - S i *ᵥ x)) =
        (∑ i, dotProduct (star (b i)) ((S i)⁻¹ *ᵥ b i)) -
          dotProduct (star bbar) (Sbar⁻¹ *ᵥ bbar) := by
    simpa only [x, bbar, Sbar] using resolvent_residual_identity S b hS
  have hres := congrArg Complex.re hresComplex
  change (∑ i, ∑ p, ‖((CFC.sqrt (S i))⁻¹ *ᵥ b i -
      CFC.sqrt (S i) *ᵥ x) p‖ ^ 2) = _
  calc
    ∑ i, ∑ p, ‖((CFC.sqrt (S i))⁻¹ *ᵥ b i -
        CFC.sqrt (S i) *ᵥ x) p‖ ^ 2 =
        ∑ i, (dotProduct (star (b i - S i *ᵥ x))
          ((S i)⁻¹ *ᵥ (b i - S i *ᵥ x))).re := by
            apply Finset.sum_congr rfl
            intro i _
            rw [sqrt_defect_eq_sqrt_inv_residual (S i) (hS i),
              sqrt_inv_mulVec_normSq (S i) (hS i)]
    _ = ∑ i, (dotProduct (star (b i)) ((S i)⁻¹ *ᵥ b i)).re -
        (dotProduct (star bbar) (Sbar⁻¹ *ᵥ bbar)).re := by
          simpa only [Complex.re_sum, Complex.sub_re] using hres

private theorem resolvent_eq_of_sqrt_defect_sum_eq_zero
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (S : ι → Matrix n n ℂ) (b : ι → n → ℂ)
    (hS : ∀ i, (S i).PosDef)
    (hzero :
      let Sbar := ∑ i, S i
      let bbar := ∑ i, b i
      let x := Sbar⁻¹ *ᵥ bbar
      ∑ i, ∑ p, ‖((CFC.sqrt (S i))⁻¹ *ᵥ b i -
        CFC.sqrt (S i) *ᵥ x) p‖ ^ 2 = 0) :
    ∀ i, (S i)⁻¹ *ᵥ b i = (∑ j, S j)⁻¹ *ᵥ (∑ j, b j) := by
  classical
  let Sbar : Matrix n n ℂ := ∑ i, S i
  let bbar : n → ℂ := ∑ i, b i
  let x : n → ℂ := Sbar⁻¹ *ᵥ bbar
  change (∑ i, ∑ p, ‖((CFC.sqrt (S i))⁻¹ *ᵥ b i -
      CFC.sqrt (S i) *ᵥ x) p‖ ^ 2) = 0 at hzero
  have hi (i : ι) : ∑ p, ‖((CFC.sqrt (S i))⁻¹ *ᵥ b i -
      CFC.sqrt (S i) *ᵥ x) p‖ ^ 2 = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ ↦ Finset.sum_nonneg (fun p _ ↦ sq_nonneg _))).mp hzero i
      (Finset.mem_univ i)
  intro i
  have hm : (CFC.sqrt (S i))⁻¹ *ᵥ b i -
      CFC.sqrt (S i) *ᵥ x = 0 := by
    funext p
    have hp : ‖((CFC.sqrt (S i))⁻¹ *ᵥ b i -
        CFC.sqrt (S i) *ᵥ x) p‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun q _ ↦ sq_nonneg _)).mp (hi i) p
        (Finset.mem_univ p)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hp)
  let Q : Matrix n n ℂ := CFC.sqrt (S i)
  have hQunit : IsUnit Q := by
    change IsUnit (CFC.sqrt (S i))
    rw [CFC.isUnit_sqrt_iff_isStrictlyPositive,
      Matrix.isStrictlyPositive_iff_posDef]
    exact hS i
  letI : Invertible Q := hQunit.invertible
  letI : Invertible (S i) := (hS i).isUnit.invertible
  have hresInv : Q⁻¹ *ᵥ (b i - S i *ᵥ x) = 0 := by
    rw [← sqrt_defect_eq_sqrt_inv_residual (S i) (hS i) (b i) x]
    exact hm
  have hres : b i - S i *ᵥ x = 0 := by
    have hcancel : Q *ᵥ (Q⁻¹ *ᵥ (b i - S i *ᵥ x)) = b i - S i *ᵥ x := by
      calc
        Q *ᵥ (Q⁻¹ *ᵥ (b i - S i *ᵥ x)) =
            (Q * Q⁻¹) *ᵥ (b i - S i *ᵥ x) := mulVec_mulVec _ _ _
        _ = b i - S i *ᵥ x := by rw [mul_inv_of_invertible, one_mulVec]
    calc
      b i - S i *ᵥ x = Q *ᵥ (Q⁻¹ *ᵥ (b i - S i *ᵥ x)) := hcancel.symm
      _ = 0 := by rw [hresInv, Matrix.mulVec_zero]
  have hb : b i = S i *ᵥ x := sub_eq_zero.mp hres
  change (S i)⁻¹ *ᵥ b i = x
  rw [hb, mulVec_mulVec, inv_mul_of_invertible, one_mulVec]

end Matrix

namespace Matrix

/-- **The fixed-resolvent defect identity for the finite Weyl family.**
Let `A g` and `B g` be the uniformly weighted Weyl conjugates of positive
definite matrices `ρ` and `σ`. For `t > 0`, the squared norm of the
square-root resolvent defect is the difference between the sum of the
summand quadratic forms and the quadratic form of their average.

The vectorization is `X ↦ Matrix.vec Xᵀ`; hence
`A ⊗ₖ 1 + t • (1 ⊗ₖ Bᵀ)` represents `X ↦ A * X + t • (X * B)`.
This is the finite-Weyl specialization of Jenčová--Ruskai,
arXiv:0903.2895v4, Appendix, lines 1313--1343. It is a
fixed-`t`, positive-definite statement and does not derive vanishing of the
defect from relative-entropy equality.

**Scope restriction (positive definite, fixed `t`):** The source equality
analysis also uses integration in `t` and limiting arguments for singular
matrices. Those steps are not asserted here. Documented in
`docs/paper-gaps/cpsv16_ssa_equality_hayashi_markov.tex`. -/
theorem weyl_resolvent_defect_identity
    {dS dC : ℕ} [NeZero dC]
    {ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ dC) {t : ℝ} (ht : 0 < t) :
    let U := fun g : ZMod dC × ZMod dC ↦
      (1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ g.1 g.2
    let q : ℝ := ((dC : ℝ) ^ 2)⁻¹
    let A := fun g ↦ q • (U g * ρ * (U g)ᴴ)
    let B := fun g ↦ q • (U g * σ * (U g)ᴴ)
    let Abar := ∑ g, A g
    let Bbar := ∑ g, B g
    let S := fun g ↦ A g ⊗ₖ (1 : Matrix (Fin dS × ZMod dC)
        (Fin dS × ZMod dC) ℂ) +
      t • ((1 : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) ⊗ₖ (B g)ᵀ)
    let Sbar := Abar ⊗ₖ (1 : Matrix (Fin dS × ZMod dC)
        (Fin dS × ZMod dC) ℂ) +
      t • ((1 : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) ⊗ₖ Bbarᵀ)
    let b := fun g ↦ Matrix.vec (B g)ᵀ
    let bbar := Matrix.vec Bbarᵀ
    let x := Sbar⁻¹ *ᵥ bbar
    ∑ g, ∑ p, ‖((CFC.sqrt (S g))⁻¹ *ᵥ b g -
      CFC.sqrt (S g) *ᵥ x) p‖ ^ 2 =
      ∑ g, (dotProduct (star (b g)) ((S g)⁻¹ *ᵥ b g)).re -
        (dotProduct (star bbar) (Sbar⁻¹ *ᵥ bbar)).re := by
  classical
  dsimp only
  let N := Fin dS × ZMod dC
  let G := ZMod dC × ZMod dC
  let U : G → Matrix N N ℂ := fun g ↦
    (1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ g.1 g.2
  let q : ℝ := ((dC : ℝ) ^ 2)⁻¹
  let A : G → Matrix N N ℂ := fun g ↦ q • (U g * ρ * (U g)ᴴ)
  let B : G → Matrix N N ℂ := fun g ↦ q • (U g * σ * (U g)ᴴ)
  let Abar : Matrix N N ℂ := ∑ g, A g
  let Bbar : Matrix N N ℂ := ∑ g, B g
  let S : G → Matrix (N × N) (N × N) ℂ := fun g ↦
    A g ⊗ₖ (1 : Matrix N N ℂ) +
      t • ((1 : Matrix N N ℂ) ⊗ₖ (B g)ᵀ)
  let Sbar : Matrix (N × N) (N × N) ℂ :=
    Abar ⊗ₖ (1 : Matrix N N ℂ) +
      t • ((1 : Matrix N N ℂ) ⊗ₖ Bbarᵀ)
  let b : G → N × N → ℂ := fun g ↦ Matrix.vec (B g)ᵀ
  let bbar : N × N → ℂ := Matrix.vec Bbarᵀ
  let x : N × N → ℂ := Sbar⁻¹ *ᵥ bbar
  have hdCpos : (0 : ℝ) < dC := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dC)
  have hqpos : 0 < q := by
    simp only [q]
    positivity
  have hU (g : G) : U g ∈ unitary (Matrix N N ℂ) := by
    exact Matrix.kronecker_mem_unitary (Submonoid.one_mem _)
      (weyl_mem_unitary hζ g.1 g.2)
  have hA (g : G) : (A g).PosDef := by
    have hc := posDef_conj_unitary hρ ⟨U g, hU g⟩
    simpa only [A, star_eq_conjTranspose] using hc.smul hqpos
  have hB (g : G) : (B g).PosDef := by
    have hc := posDef_conj_unitary hσ ⟨U g, hU g⟩
    simpa only [B, star_eq_conjTranspose] using hc.smul hqpos
  have hS (g : G) : (S g).PosDef :=
    superop_leftRight_posDef ht (hA g) (hB g)
  have hsumS : ∑ g, S g = Sbar := by
    ext ⟨a, b⟩ ⟨c, d⟩
    simp only [S, Sbar, Abar, Bbar, Matrix.sum_apply, Matrix.add_apply,
      Matrix.smul_apply, Matrix.kroneckerMap_apply, Matrix.transpose_apply,
      Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.smul_sum]
  have hsumb : ∑ g, b g = bbar := by
    ext ⟨a, c⟩
    simp only [b, bbar, Bbar, Matrix.vec, Matrix.transpose_apply,
      Matrix.sum_apply, Finset.sum_apply]
  have hdef := resolvent_sqrt_defect_identity S b hS
  change (∑ g, ∑ p, ‖((CFC.sqrt (S g))⁻¹ *ᵥ b g -
      CFC.sqrt (S g) *ᵥ x) p‖ ^ 2) =
    ∑ g, (dotProduct (star (b g)) ((S g)⁻¹ *ᵥ b g)).re -
      (dotProduct (star bbar) (Sbar⁻¹ *ᵥ bbar)).re
  simpa only [hsumS, hsumb, x] using hdef

/-- **The source-`A` fixed-resolvent defect identity for the finite Weyl
family.** Under the notation of `weyl_resolvent_defect_identity`, replacing
the source vectors `vec (B g)ᵀ` by `vec (A g)ᵀ` gives the second nonnegative
defect family needed in the relative-entropy integral representation.

This is the source `X_j = A_j K`, with `K = 1`, in Jenčová--Ruskai,
arXiv:0903.2895v4, §4 and Appendix. It remains a positive-definite,
fixed-`t` statement. -/
theorem weyl_sourceA_resolvent_defect_identity
    {dS dC : ℕ} [NeZero dC]
    {ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ dC) {t : ℝ} (ht : 0 < t) :
    let U := fun g : ZMod dC × ZMod dC ↦
      (1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ g.1 g.2
    let q : ℝ := ((dC : ℝ) ^ 2)⁻¹
    let A := fun g ↦ q • (U g * ρ * (U g)ᴴ)
    let B := fun g ↦ q • (U g * σ * (U g)ᴴ)
    let Abar := ∑ g, A g
    let Bbar := ∑ g, B g
    let S := fun g ↦ A g ⊗ₖ (1 : Matrix (Fin dS × ZMod dC)
        (Fin dS × ZMod dC) ℂ) +
      t • ((1 : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) ⊗ₖ (B g)ᵀ)
    let Sbar := Abar ⊗ₖ (1 : Matrix (Fin dS × ZMod dC)
        (Fin dS × ZMod dC) ℂ) +
      t • ((1 : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) ⊗ₖ Bbarᵀ)
    let a := fun g ↦ Matrix.vec (A g)ᵀ
    let abar := Matrix.vec Abarᵀ
    let x := Sbar⁻¹ *ᵥ abar
    ∑ g, ∑ p, ‖((CFC.sqrt (S g))⁻¹ *ᵥ a g -
      CFC.sqrt (S g) *ᵥ x) p‖ ^ 2 =
      ∑ g, (dotProduct (star (a g)) ((S g)⁻¹ *ᵥ a g)).re -
        (dotProduct (star abar) (Sbar⁻¹ *ᵥ abar)).re := by
  classical
  dsimp only
  let N := Fin dS × ZMod dC
  let G := ZMod dC × ZMod dC
  let U : G → Matrix N N ℂ := fun g ↦
    (1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ g.1 g.2
  let q : ℝ := ((dC : ℝ) ^ 2)⁻¹
  let A : G → Matrix N N ℂ := fun g ↦ q • (U g * ρ * (U g)ᴴ)
  let B : G → Matrix N N ℂ := fun g ↦ q • (U g * σ * (U g)ᴴ)
  let Abar : Matrix N N ℂ := ∑ g, A g
  let Bbar : Matrix N N ℂ := ∑ g, B g
  let S : G → Matrix (N × N) (N × N) ℂ := fun g ↦
    A g ⊗ₖ (1 : Matrix N N ℂ) +
      t • ((1 : Matrix N N ℂ) ⊗ₖ (B g)ᵀ)
  let Sbar : Matrix (N × N) (N × N) ℂ :=
    Abar ⊗ₖ (1 : Matrix N N ℂ) +
      t • ((1 : Matrix N N ℂ) ⊗ₖ Bbarᵀ)
  let a : G → N × N → ℂ := fun g ↦ Matrix.vec (A g)ᵀ
  let abar : N × N → ℂ := Matrix.vec Abarᵀ
  let x : N × N → ℂ := Sbar⁻¹ *ᵥ abar
  have hdCpos : (0 : ℝ) < dC := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dC)
  have hqpos : 0 < q := by
    simp only [q]
    positivity
  have hU (g : G) : U g ∈ unitary (Matrix N N ℂ) := by
    exact Matrix.kronecker_mem_unitary (Submonoid.one_mem _)
      (weyl_mem_unitary hζ g.1 g.2)
  have hA (g : G) : (A g).PosDef := by
    have hc := posDef_conj_unitary hρ ⟨U g, hU g⟩
    simpa only [A, star_eq_conjTranspose] using hc.smul hqpos
  have hB (g : G) : (B g).PosDef := by
    have hc := posDef_conj_unitary hσ ⟨U g, hU g⟩
    simpa only [B, star_eq_conjTranspose] using hc.smul hqpos
  have hS (g : G) : (S g).PosDef :=
    superop_leftRight_posDef ht (hA g) (hB g)
  have hsumS : ∑ g, S g = Sbar := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [S, Sbar, Abar, Bbar, Matrix.sum_apply, Matrix.add_apply,
      Matrix.smul_apply, Matrix.kroneckerMap_apply, Matrix.transpose_apply,
      Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.smul_sum]
  have hsuma : ∑ g, a g = abar := by
    ext ⟨i, j⟩
    simp only [a, abar, Abar, Matrix.vec, Matrix.transpose_apply,
      Matrix.sum_apply, Finset.sum_apply]
  have hdef := resolvent_sqrt_defect_identity S a hS
  change (∑ g, ∑ p, ‖((CFC.sqrt (S g))⁻¹ *ᵥ a g -
      CFC.sqrt (S g) *ᵥ x) p‖ ^ 2) =
    ∑ g, (dotProduct (star (a g)) ((S g)⁻¹ *ᵥ a g)).re -
      (dotProduct (star abar) (Sbar⁻¹ *ᵥ abar)).re
  simpa only [hsumS, hsuma, x] using hdef

/-- **Zero Weyl defect gives the common fixed-resolvent solution.**
In the positive-definite finite Weyl family, if the difference of resolvent
quadratic forms in `weyl_resolvent_defect_identity` vanishes at a fixed
`t > 0`, then every summand has the same resolvent solution as the average.
Taking `g = (0, 0)` gives the identity-Weyl summand required in the
partial-trace equality argument.

This is the zero-defect conclusion of Jenčová--Ruskai,
arXiv:0903.2895v4, §4, lines 652--674, using the squared-defect expansion
from Appendix, lines 1313--1343. It does not assert that equality of
relative entropies makes the
displayed defect vanish.

**Scope restriction (positive definite, fixed `t`):** The implication from
relative-entropy equality to zero defect, integration in `t`, and singular
supports remain outside this theorem. Documented in
`docs/paper-gaps/cpsv16_ssa_equality_hayashi_markov.tex`. -/
theorem weyl_resolvent_eq_of_defect_eq_zero
    {dS dC : ℕ} [NeZero dC]
    {ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ dC) {t : ℝ} (ht : 0 < t)
    (hzero :
      let U := fun g : ZMod dC × ZMod dC ↦
        (1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ g.1 g.2
      let q : ℝ := ((dC : ℝ) ^ 2)⁻¹
      let A := fun g ↦ q • (U g * ρ * (U g)ᴴ)
      let B := fun g ↦ q • (U g * σ * (U g)ᴴ)
      let Abar := ∑ g, A g
      let Bbar := ∑ g, B g
      let S := fun g ↦ A g ⊗ₖ (1 : Matrix (Fin dS × ZMod dC)
          (Fin dS × ZMod dC) ℂ) +
        t • ((1 : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) ⊗ₖ (B g)ᵀ)
      let Sbar := Abar ⊗ₖ (1 : Matrix (Fin dS × ZMod dC)
          (Fin dS × ZMod dC) ℂ) +
        t • ((1 : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) ⊗ₖ Bbarᵀ)
      let b := fun g ↦ Matrix.vec (B g)ᵀ
      let bbar := Matrix.vec Bbarᵀ
      ∑ g, (dotProduct (star (b g)) ((S g)⁻¹ *ᵥ b g)).re -
        (dotProduct (star bbar) (Sbar⁻¹ *ᵥ bbar)).re = 0) :
    let U := fun g : ZMod dC × ZMod dC ↦
      (1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ g.1 g.2
    let q : ℝ := ((dC : ℝ) ^ 2)⁻¹
    let A := fun g ↦ q • (U g * ρ * (U g)ᴴ)
    let B := fun g ↦ q • (U g * σ * (U g)ᴴ)
    let Abar := ∑ g, A g
    let Bbar := ∑ g, B g
    let S := fun g ↦ A g ⊗ₖ (1 : Matrix (Fin dS × ZMod dC)
        (Fin dS × ZMod dC) ℂ) +
      t • ((1 : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) ⊗ₖ (B g)ᵀ)
    let Sbar := Abar ⊗ₖ (1 : Matrix (Fin dS × ZMod dC)
        (Fin dS × ZMod dC) ℂ) +
      t • ((1 : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) ⊗ₖ Bbarᵀ)
    let b := fun g ↦ Matrix.vec (B g)ᵀ
    let bbar := Matrix.vec Bbarᵀ
    ∀ g, (S g)⁻¹ *ᵥ b g = Sbar⁻¹ *ᵥ bbar := by
  classical
  dsimp only at hzero ⊢
  let N := Fin dS × ZMod dC
  let G := ZMod dC × ZMod dC
  let U : G → Matrix N N ℂ := fun g ↦
    (1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ g.1 g.2
  let q : ℝ := ((dC : ℝ) ^ 2)⁻¹
  let A : G → Matrix N N ℂ := fun g ↦ q • (U g * ρ * (U g)ᴴ)
  let B : G → Matrix N N ℂ := fun g ↦ q • (U g * σ * (U g)ᴴ)
  let Abar : Matrix N N ℂ := ∑ g, A g
  let Bbar : Matrix N N ℂ := ∑ g, B g
  let S : G → Matrix (N × N) (N × N) ℂ := fun g ↦
    A g ⊗ₖ (1 : Matrix N N ℂ) +
      t • ((1 : Matrix N N ℂ) ⊗ₖ (B g)ᵀ)
  let Sbar : Matrix (N × N) (N × N) ℂ :=
    Abar ⊗ₖ (1 : Matrix N N ℂ) +
      t • ((1 : Matrix N N ℂ) ⊗ₖ Bbarᵀ)
  let b : G → N × N → ℂ := fun g ↦ Matrix.vec (B g)ᵀ
  let bbar : N × N → ℂ := Matrix.vec Bbarᵀ
  let x : N × N → ℂ := Sbar⁻¹ *ᵥ bbar
  change (∑ g, (dotProduct (star (b g)) ((S g)⁻¹ *ᵥ b g)).re -
      (dotProduct (star bbar) (Sbar⁻¹ *ᵥ bbar)).re) = 0 at hzero
  change ∀ g, (S g)⁻¹ *ᵥ b g = Sbar⁻¹ *ᵥ bbar
  have hdCpos : (0 : ℝ) < dC := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dC)
  have hqpos : 0 < q := by
    simp only [q]
    positivity
  have hU (g : G) : U g ∈ unitary (Matrix N N ℂ) := by
    exact Matrix.kronecker_mem_unitary (Submonoid.one_mem _)
      (weyl_mem_unitary hζ g.1 g.2)
  have hA (g : G) : (A g).PosDef := by
    have hc := posDef_conj_unitary hρ ⟨U g, hU g⟩
    simpa only [A, star_eq_conjTranspose] using hc.smul hqpos
  have hB (g : G) : (B g).PosDef := by
    have hc := posDef_conj_unitary hσ ⟨U g, hU g⟩
    simpa only [B, star_eq_conjTranspose] using hc.smul hqpos
  have hS (g : G) : (S g).PosDef :=
    superop_leftRight_posDef ht (hA g) (hB g)
  have hsumS : ∑ g, S g = Sbar := by
    ext ⟨a, b⟩ ⟨c, d⟩
    simp only [S, Sbar, Abar, Bbar, Matrix.sum_apply, Matrix.add_apply,
      Matrix.smul_apply, Matrix.kroneckerMap_apply, Matrix.transpose_apply,
      Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.smul_sum]
  have hsumb : ∑ g, b g = bbar := by
    ext ⟨a, c⟩
    simp only [b, bbar, Bbar, Matrix.vec, Matrix.transpose_apply,
      Matrix.sum_apply, Finset.sum_apply]
  have hdef := resolvent_sqrt_defect_identity S b hS
  have hnormZero :
      ∑ g, ∑ p, ‖((CFC.sqrt (S g))⁻¹ *ᵥ b g -
        CFC.sqrt (S g) *ᵥ x) p‖ ^ 2 = 0 := by
    calc
      _ = ∑ g, (dotProduct (star (b g)) ((S g)⁻¹ *ᵥ b g)).re -
          (dotProduct (star bbar) (Sbar⁻¹ *ᵥ bbar)).re := by
            simpa only [hsumS, hsumb, x] using hdef
      _ = 0 := hzero
  have hall := resolvent_eq_of_sqrt_defect_sum_eq_zero S b hS
    (by simpa only [hsumS, hsumb, x] using hnormZero)
  intro g
  simpa only [hsumS, hsumb] using hall g

end Matrix
