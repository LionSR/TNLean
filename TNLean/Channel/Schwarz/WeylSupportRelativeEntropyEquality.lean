/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Schwarz.SupportRelativeEntropyEquality
import TNLean.Channel.Schwarz.PetzEqualityPrerequisites

/-!
# Support-relative-modular equality for the finite Weyl family

This file specializes the finite-family support-relative-entropy equality
theorem to the Weyl family used in the proof of data processing under a partial
trace.

## Main result

* `Matrix.weyl_supportRelativeModular_resolvent_mulVec_eq_of_partialTraceRight_eq`
  turns saturation of partial-trace data processing on the finite-relative-
  entropy support domain into the projected common relative-modular resolvent
  for every Weyl summand and the full Weyl sum.

## References

* A. Jenčová and M. B. Ruskai, arXiv:0903.2895v4, lines 717--720 and
  766--793.
* P. Hayden, R. Jozsa, D. Petz, and A. Winter,
  arXiv:quant-ph/0304007v2, Theorem 3 and equation (8).

The finite-Weyl argument is the project's analytic route toward the recovery
implication that precedes the separate structural characterization invoked in
CPSV16, Lemma `Lsigma3`. CPSV16 does not present this Weyl/resolvent route, and
the result below is not the direct-sum Markov decomposition asserted there.
-/

open scoped Matrix ComplexOrder MatrixOrder Kronecker
open Matrix

namespace Matrix

/-- An unweighted conjugate in the finite Weyl family. -/
noncomputable def unweightedWeylConjugate
    {dS dC : ℕ} [NeZero dC] (ζ : ℂ)
    (M : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ)
    (g : ZMod dC × ZMod dC) :
    Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ :=
  let U := (1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ g.1 g.2
  U * M * Uᴴ

/-- The sum of the unweighted finite Weyl conjugates. -/
noncomputable def unweightedWeylSum
    {dS dC : ℕ} [NeZero dC] (ζ : ℂ)
    (M : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) :
    Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ :=
  ∑ g, unweightedWeylConjugate ζ M g

/-- Positive semidefiniteness is preserved by an unweighted Weyl conjugation. -/
theorem PosSemidef.unweightedWeylConjugate
    {dS dC : ℕ} [NeZero dC]
    {M : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hM : M.PosSemidef) (ζ : ℂ) (g : ZMod dC × ZMod dC) :
    (unweightedWeylConjugate ζ M g).PosSemidef :=
  hM.mul_mul_conjTranspose_same
    ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ g.1 g.2)

/-- The unweighted finite Weyl sum of a positive-semidefinite matrix is
positive semidefinite. -/
theorem PosSemidef.unweightedWeylSum
    {dS dC : ℕ} [NeZero dC]
    {M : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hM : M.PosSemidef) (ζ : ℂ) :
    (unweightedWeylSum ζ M).PosSemidef := by
  rw [Matrix.unweightedWeylSum]
  exact Matrix.posSemidef_sum Finset.univ fun g _ ↦
    hM.unweightedWeylConjugate ζ g

/-- The zero-index unweighted Weyl conjugate is the original matrix. -/
@[simp] theorem unweightedWeylConjugate_zero_zero
    {dS dC : ℕ} [NeZero dC] (ζ : ℂ)
    (M : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) :
    unweightedWeylConjugate ζ M (0, 0) = M := by
  simp [unweightedWeylConjugate, weyl, weylShift, weylClock]

/-- Saturation of relative entropy under the right partial trace gives the
support-restricted common relative-modular resolvent for every Weyl summand
and the full, unweighted Weyl sum.

The scalar Jensen equality is converted to the relative-entropy equality for
the unweighted family by support-domain homogeneity. The local projection is
essential: the source proves equality on the support of the local reference
matrix, not ambient resolvent equality.

The positive-semidefinite support convention is that of Jenčová--Ruskai,
arXiv:0903.2895v4, lines 717--720; their common-resolvent equality argument is
at lines 766--793. This finite-Weyl specialization is used toward
Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2, Theorem 3,
equation (8). -/
theorem weyl_supportRelativeModular_resolvent_mulVec_eq_of_partialTraceRight_eq
    {dS dC : ℕ} [NeZero dC]
    {ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hsupp : ∀ v : Fin dS × ZMod dC → ℂ, σ *ᵥ v = 0 → ρ *ᵥ v = 0)
    (heq : quantumRelativeEntropy ρ σ =
      quantumRelativeEntropy (partialTraceRight ρ) (partialTraceRight σ))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ dC)
    {t : ℝ} (ht : 0 < t) (g : ZMod dC × ZMod dC) :
    let hBg := hσ.unweightedWeylConjugate ζ g
    let hBsum := hσ.unweightedWeylSum ζ
    let Q := (1 : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) ⊗ₖ
      hBg.isHermitian.supportProjᵀ
    Q *ᵥ
        ((t • (1 : Matrix
            ((Fin dS × ZMod dC) × (Fin dS × ZMod dC))
            ((Fin dS × ZMod dC) × (Fin dS × ZMod dC)) ℂ) +
          unweightedWeylConjugate ζ ρ g ⊗ₖ hBg.supportInvᵀ)⁻¹ *ᵥ
            Matrix.vec
              (1 : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ)ᵀ) =
      Q *ᵥ
        ((t • (1 : Matrix
            ((Fin dS × ZMod dC) × (Fin dS × ZMod dC))
            ((Fin dS × ZMod dC) × (Fin dS × ZMod dC)) ℂ) +
          unweightedWeylSum ζ ρ ⊗ₖ hBsum.supportInvᵀ)⁻¹ *ᵥ
            Matrix.vec
              (1 : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ)ᵀ) := by
  classical
  let A := unweightedWeylConjugate ζ ρ
  let B := unweightedWeylConjugate ζ σ
  have hA (i : ZMod dC × ZMod dC) : (A i).PosSemidef :=
    hρ.unweightedWeylConjugate ζ i
  have hB (i : ZMod dC × ZMod dC) : (B i).PosSemidef :=
    hσ.unweightedWeylConjugate ζ i
  have hU (i : ZMod dC × ZMod dC) :
      ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ i.1 i.2) ∈
        unitary (Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) :=
    Matrix.kronecker_mem_unitary (Submonoid.one_mem _)
      (weyl_mem_unitary hζ i.1 i.2)
  have hker (i : ZMod dC × ZMod dC)
      (v : Fin dS × ZMod dC → ℂ) (hv : B i *ᵥ v = 0) :
      A i *ᵥ v = 0 := by
    let U := (1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ i.1 i.2
    have hUunit : IsUnit U :=
      Unitary.isUnit_coe (U := ⟨U, hU i⟩)
    have hσv : σ *ᵥ (Uᴴ *ᵥ v) = 0 := by
      apply Matrix.mulVec_injective_of_isUnit hUunit
      simpa [B, unweightedWeylConjugate, U, Matrix.mulVec_mulVec,
        Matrix.mul_assoc] using hv
    have hρv := hsupp (Uᴴ *ᵥ v) hσv
    simpa [A, unweightedWeylConjugate, U, Matrix.mulVec_mulVec,
      Matrix.mul_assoc] using congrArg U.mulVec hρv
  have hAbar : (∑ i, A i).PosSemidef :=
    Matrix.posSemidef_sum Finset.univ fun i _ ↦ hA i
  have hBbar : (∑ i, B i).PosSemidef :=
    Matrix.posSemidef_sum Finset.univ fun i _ ↦ hB i
  have hsumker (v : Fin dS × ZMod dC → ℂ)
      (hv : (∑ i, B i) *ᵥ v = 0) : (∑ i, A i) *ᵥ v = 0 := by
    rw [Matrix.sum_mulVec]
    apply Finset.sum_eq_zero
    intro i _
    exact hker i v
      (Matrix.PosSemidef.mulVec_eq_zero_of_sum_mulVec_eq_zero hB hv i)
  let q : ℝ := ((dC : ℝ) ^ 2)⁻¹
  have hq : 0 < q := by
    have hdC : (0 : ℝ) < dC := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dC)
    dsimp [q]
    positivity
  have hsat := quantumRelativeEntropy_weyl_jensen_eq_of_partialTraceRight_eq
    hρ hσ hsupp heq hζ
  have hscaled :
      quantumRelativeEntropy (q • ∑ i, A i) (q • ∑ i, B i) =
        q * quantumRelativeEntropy (∑ i, A i) (∑ i, B i) :=
    quantumRelativeEntropy_smul_support hAbar hBbar hsumker hq
  have hqsmul (M : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) :
      q • M = (((dC : ℂ) ^ 2)⁻¹) • M := by
    ext i j
    norm_num [q]
  have hsat' :
      quantumRelativeEntropy (q • ∑ i, A i) (q • ∑ i, B i) =
        q * ∑ i, quantumRelativeEntropy (A i) (B i) := by
    rw [hqsmul, hqsmul]
    simp_rw [Fintype.sum_prod_type]
    simp_rw [Finset.mul_sum]
    simpa only [A, B, unweightedWeylConjugate, q, smul_eq_mul] using hsat
  have hrel :
      quantumRelativeEntropy (∑ i, A i) (∑ i, B i) =
        ∑ i, quantumRelativeEntropy (A i) (B i) := by
    apply (mul_left_cancel₀ hq.ne')
    rw [← hscaled]
    exact hsat'
  simpa only [A, B, unweightedWeylSum] using
    supportRelativeModular_resolvent_mulVec_eq_of_relativeEntropy_sum_eq
      A B hA hB hker hrel ht g

end Matrix
