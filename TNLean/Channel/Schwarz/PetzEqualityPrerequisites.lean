/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Schwarz.PetzRecoverySupport
import TNLean.Channel.Schwarz.SSAEqualityDPI

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

## References

* P. Hayden, R. Jozsa, D. Petz, and A. Winter, *Structure of States Which
  Satisfy Strong Subadditivity of Quantum Entropy with Equality*, Theorem 3,
  arXiv:quant-ph/0304007v2.
-/

open scoped Matrix Kronecker ComplexOrder Matrix.Norms.L2Operator
open Matrix

/-- The support inverse square root of a positive semidefinite left factor
tensored with the maximally mixed right factor is the lifted support inverse
square root multiplied by the square root of the right dimension.

This is the functional-calculus normalization in the identity-summand
specialization of Hayden--Jozsa--Petz--Winter,
arXiv:quant-ph/0304007v2, Theorem 3, equation (8). -/
theorem Matrix.PosSemidef.supportInvSqrt_kronecker_maximallyMixed
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
theorem Matrix.PosSemidef.supportInvSqrt_kronecker_maximallyMixed_mul_mul
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
theorem Matrix.partialTraceRightPetzMap_eq_of_weyl_identity_sandwich
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
