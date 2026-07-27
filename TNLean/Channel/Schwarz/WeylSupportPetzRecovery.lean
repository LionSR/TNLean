/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Schwarz.SupportRelativeModular
import TNLean.Channel.Schwarz.PetzRecoverySupport
import TNLean.Channel.Schwarz.WeylSupportRelativeEntropyEquality

/-!
# Petz recovery from support-relative Weyl equality

This file derives the support-domain square-root ratio, support sandwich, and
raw Petz recovery identity from saturation of relative entropy under a right
partial trace.

## Main results

* `Matrix.weyl_support_sqrt_ratio_eq_of_partialTraceRight_eq` identifies the
  square-root ratios on the support of the reference matrix.
* `Matrix.weyl_support_identity_sandwich_of_partialTraceRight_eq` proves the
  support Petz sandwich.
* `Matrix.partialTraceRightPetzMap_eq_of_relativeEntropy_eq` proves raw
  recovery by the partial-trace Petz map.
* `Matrix.partialTraceRightPetzChannel_recovery_of_dpi_equality` gives the
  arbitrary-index density-state result for the completed Petz channel.

## References

* A. Jenčová and M. B. Ruskai, arXiv:0903.2895v4, lines 788--793.
* P. Hayden, R. Jozsa, D. Petz, and A. Winter,
  arXiv:quant-ph/0304007v2, Theorem 3 and equation (8).

This analytic recovery step precedes the separate direct-sum structure invoked
in CPSV16, Lemma `Lsigma3`; CPSV16 does not present the Weyl/resolvent argument.
-/

open scoped Matrix ComplexOrder MatrixOrder Kronecker
open Matrix

namespace Matrix

/-- Saturation under the right partial trace identifies the square-root ratio
of the original pair with that of its maximally mixed extension on the support
of the reference matrix.

The support projection is essential: Jenčová--Ruskai,
arXiv:0903.2895v4, lines 788--793, obtain the common relative-modular
resolvent only on the complement of the kernel and pass through functional
calculus; here this is specialized to the square root. This is the analytic
square-root step toward the Petz identity in
Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2, Theorem 3,
equation (8). -/
theorem weyl_support_sqrt_ratio_eq_of_partialTraceRight_eq
    {dS dC : ℕ} [NeZero dC]
    {ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hsupp : ∀ v : Fin dS × ZMod dC → ℂ, σ *ᵥ v = 0 → ρ *ᵥ v = 0)
    (heq : quantumRelativeEntropy ρ σ =
      quantumRelativeEntropy (partialTraceRight ρ) (partialTraceRight σ)) :
    let barρ := partialTraceRight ρ ⊗ₖ
      ((dC : ℂ)⁻¹ • (1 : Matrix (ZMod dC) (ZMod dC) ℂ))
    let barσ := partialTraceRight σ ⊗ₖ
      ((dC : ℂ)⁻¹ • (1 : Matrix (ZMod dC) (ZMod dC) ℂ))
    let hbarσ : barσ.PosSemidef := hσ.partialTraceRight.kronecker
      maximallyMixed_posDef.posSemidef
    (CFC.sqrt ρ * hσ.supportInvSqrt) * hσ.isHermitian.supportProj =
      (CFC.sqrt barρ * hbarσ.supportInvSqrt) *
        hσ.isHermitian.supportProj := by
  classical
  let barρ := partialTraceRight ρ ⊗ₖ
    ((dC : ℂ)⁻¹ • (1 : Matrix (ZMod dC) (ZMod dC) ℂ))
  let barσ := partialTraceRight σ ⊗ₖ
    ((dC : ℂ)⁻¹ • (1 : Matrix (ZMod dC) (ZMod dC) ℂ))
  have hbarρ : barρ.PosSemidef :=
    hρ.partialTraceRight.kronecker maximallyMixed_posDef.posSemidef
  have hbarσ : barσ.PosSemidef :=
    hσ.partialTraceRight.kronecker maximallyMixed_posDef.posSemidef
  change (CFC.sqrt ρ * hσ.supportInvSqrt) * hσ.isHermitian.supportProj =
    (CFC.sqrt barρ * hbarσ.supportInvSqrt) * hσ.isHermitian.supportProj
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ dC :=
    ⟨_, Complex.isPrimitiveRoot_exp dC (NeZero.ne dC)⟩
  have hres : ∀ {t : ℝ}, 0 < t →
      ((1 : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) ⊗ₖ
          hσ.isHermitian.supportProjᵀ) *ᵥ
          ((t • (1 : Matrix
              ((Fin dS × ZMod dC) × (Fin dS × ZMod dC))
              ((Fin dS × ZMod dC) × (Fin dS × ZMod dC)) ℂ) +
            ρ ⊗ₖ (hσ.supportInvSqrt * hσ.supportInvSqrt)ᵀ)⁻¹ *ᵥ
              Matrix.vec
                (1 : Matrix (Fin dS × ZMod dC)
                  (Fin dS × ZMod dC) ℂ)ᵀ) =
        ((1 : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) ⊗ₖ
          hσ.isHermitian.supportProjᵀ) *ᵥ
          ((t • (1 : Matrix
              ((Fin dS × ZMod dC) × (Fin dS × ZMod dC))
              ((Fin dS × ZMod dC) × (Fin dS × ZMod dC)) ℂ) +
            unweightedWeylSum ζ ρ ⊗ₖ
              ((hσ.unweightedWeylSum ζ).supportInvSqrt *
                (hσ.unweightedWeylSum ζ).supportInvSqrt)ᵀ)⁻¹ *ᵥ
              Matrix.vec
                (1 : Matrix (Fin dS × ZMod dC)
                  (Fin dS × ZMod dC) ℂ)ᵀ) := by
    intro t ht
    have hraw :=
      weyl_supportRelativeModular_resolvent_mulVec_eq_of_partialTraceRight_eq
        hρ hσ hsupp heq hζ ht (0, 0)
    convert hraw using 1 <;>
      simp only [unweightedWeylConjugate_zero_zero, PosSemidef.supportInv] <;>
      congr
    all_goals exact (unweightedWeylConjugate_zero_zero ζ σ).symm
  have hratio :=
    supportRelativeModular_sqrt_ratio_eq_of_resolvent_mulVec_eq
      hρ hσ (hρ.unweightedWeylSum ζ) (hσ.unweightedWeylSum ζ) hres
  have hc : 0 < ((dC : ℝ) ^ 2) := by
    have hdC : (0 : ℝ) < dC := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dC)
    positivity
  have hratioScaled :
      (CFC.sqrt ρ * hσ.supportInvSqrt) * hσ.isHermitian.supportProj =
        (CFC.sqrt (((dC : ℝ) ^ 2) • barρ) *
            (hbarσ.smul hc.le).supportInvSqrt) *
          hσ.isHermitian.supportProj := by
    convert hratio using 1
    all_goals rw [unweightedWeylSum_eq_smul_partialTraceRight_kronecker hζ]
    all_goals congr
    exact (unweightedWeylSum_eq_smul_partialTraceRight_kronecker hζ σ).symm
  rw [hbarρ.sqrt_smul hc.le, hbarσ.supportInvSqrt_smul hc] at hratioScaled
  have hsqrtc : Real.sqrt ((dC : ℝ) ^ 2) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hc
  simpa only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    inv_mul_cancel₀ hsqrtc, one_smul] using hratioScaled

/-- Saturation under the right partial trace gives the identity-Weyl support
Petz sandwich.

The projected square-root ratio is converted to a Gram-matrix identity on the
support of `σ`, then the kernel inclusion absorbs `ρ` on both sides. This is
the algebraic Gram step after the support functional-calculus conclusion of
Jenčová--Ruskai, arXiv:0903.2895v4, lines 788--793. It supplies the sandwich
entering Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2, Theorem 3,
equation (8). -/
theorem weyl_support_identity_sandwich_of_partialTraceRight_eq
    {dS dC : ℕ} [NeZero dC]
    {ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hsupp : ∀ v : Fin dS × ZMod dC → ℂ, σ *ᵥ v = 0 → ρ *ᵥ v = 0)
    (heq : quantumRelativeEntropy ρ σ =
      quantumRelativeEntropy (partialTraceRight ρ) (partialTraceRight σ)) :
    let hbarσ := hσ.partialTraceRight.kronecker
      maximallyMixed_posDef.posSemidef
    hσ.isHermitian.cfc Real.sqrt *
        (hbarσ.supportInvSqrt *
          (partialTraceRight ρ ⊗ₖ
            ((dC : ℂ)⁻¹ • (1 : Matrix (ZMod dC) (ZMod dC) ℂ))) *
          hbarσ.supportInvSqrt) *
        hσ.isHermitian.cfc Real.sqrt = ρ := by
  let barρ := partialTraceRight ρ ⊗ₖ
    ((dC : ℂ)⁻¹ • (1 : Matrix (ZMod dC) (ZMod dC) ℂ))
  let barσ := partialTraceRight σ ⊗ₖ
    ((dC : ℂ)⁻¹ • (1 : Matrix (ZMod dC) (ZMod dC) ℂ))
  have hbarρ : barρ.PosSemidef :=
    hρ.partialTraceRight.kronecker maximallyMixed_posDef.posSemidef
  have hbarσ : barσ.PosSemidef :=
    hσ.partialTraceRight.kronecker maximallyMixed_posDef.posSemidef
  change hσ.isHermitian.cfc Real.sqrt *
      (hbarσ.supportInvSqrt * barρ * hbarσ.supportInvSqrt) *
      hσ.isHermitian.cfc Real.sqrt = ρ
  apply supportRelativeModular_sandwich_eq_of_sqrt_ratio_eq
    hρ hσ hbarρ hbarσ hsupp
  exact weyl_support_sqrt_ratio_eq_of_partialTraceRight_eq hρ hσ hsupp heq

/-- Equality in right-partial-trace data processing on the finite-relative-
entropy support domain implies recovery by the raw partial-trace Petz map.

This is the raw support-map identity entering the Weyl-coordinate
support-domain recovery implication of Hayden--Jozsa--Petz--Winter,
arXiv:quant-ph/0304007v2, Theorem 3, equation (8). It is an analytic input
preceding, not the direct-sum decomposition of, CPSV16, Lemma `Lsigma3`. -/
theorem partialTraceRightPetzMap_eq_of_relativeEntropy_eq
    {dS dC : ℕ} [NeZero dC]
    {ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hsupp : ∀ v : Fin dS × ZMod dC → ℂ, σ *ᵥ v = 0 → ρ *ᵥ v = 0)
    (heq : quantumRelativeEntropy ρ σ =
      quantumRelativeEntropy (partialTraceRight ρ) (partialTraceRight σ)) :
    partialTraceRightPetzMap σ hσ (partialTraceRight ρ) = ρ := by
  apply partialTraceRightPetzMap_eq_of_weyl_identity_sandwich hσ
  exact weyl_support_identity_sandwich_of_partialTraceRight_eq
    hρ hσ hsupp heq

/-- Equality in right-partial-trace data processing is invariant under
equivalence reindexing of both tensor factors. -/
private theorem quantumRelativeEntropy_partialTraceRight_eq_submatrix_prod_equiv
    {L R L' R' : Type*}
    [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
    [Fintype L'] [DecidableEq L'] [Fintype R'] [DecidableEq R']
    {ρ σ : Matrix (L × R) (L × R) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (eL : L ≃ L') (eR : R ≃ R')
    (heq : quantumRelativeEntropy ρ σ =
      quantumRelativeEntropy (partialTraceRight ρ) (partialTraceRight σ)) :
    quantumRelativeEntropy
        (ρ.submatrix (eL.prodCongr eR).symm (eL.prodCongr eR).symm)
        (σ.submatrix (eL.prodCongr eR).symm (eL.prodCongr eR).symm) =
      quantumRelativeEntropy
        (partialTraceRight
          (ρ.submatrix (eL.prodCongr eR).symm (eL.prodCongr eR).symm))
        (partialTraceRight
          (σ.submatrix (eL.prodCongr eR).symm
            (eL.prodCongr eR).symm)) := by
  rw [quantumRelativeEntropy_submatrix_equiv
      hρ.isHermitian hσ.isHermitian (eL.prodCongr eR),
    partialTraceRight_submatrix_prod_equiv eL eR ρ,
    partialTraceRight_submatrix_prod_equiv eL eR σ,
    quantumRelativeEntropy_submatrix_equiv
      (partialTraceRight_isHermitian hρ.isHermitian)
      (partialTraceRight_isHermitian hσ.isHermitian) eL]
  exact heq

/-- Reindexing a square matrix along an equivalence is injective. -/
private theorem eq_of_submatrix_equiv_eq
    {m n : Type*} (e : m ≃ n) {A B : Matrix m m ℂ}
    (h : A.submatrix e.symm e.symm = B.submatrix e.symm e.symm) :
    A = B := by
  ext i j
  have hij := congrArg (fun M => M (e i) (e j)) h
  simpa only [Matrix.submatrix_apply, Equiv.symm_apply_apply] using hij

/-- Transport raw Petz recovery from a finite Weyl coordinate model along
specified equivalences of the two tensor factors. -/
private theorem partialTraceRightPetzMap_eq_of_relativeEntropy_eq_of_equiv
    {L R : Type*} [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R]
    {dL dR : ℕ} [NeZero dR]
    (eL : L ≃ Fin dL) (eR : R ≃ ZMod dR)
    {ρ σ : Matrix (L × R) (L × R) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hsupp : ∀ v : L × R → ℂ, σ *ᵥ v = 0 → ρ *ᵥ v = 0)
    (heq : quantumRelativeEntropy ρ σ =
      quantumRelativeEntropy (partialTraceRight ρ) (partialTraceRight σ)) :
    partialTraceRightPetzMap σ hσ (partialTraceRight ρ) = ρ := by
  let e := eL.prodCongr eR
  have hρ' : (ρ.submatrix e.symm e.symm).PosSemidef :=
    hρ.submatrix e.symm
  have hσ' : (σ.submatrix e.symm e.symm).PosSemidef :=
    hσ.submatrix e.symm
  have hsupp' := mulVec_submatrix_support e hsupp
  have hptrρ :
      partialTraceRight (ρ.submatrix e.symm e.symm) =
        (partialTraceRight ρ).submatrix eL.symm eL.symm :=
    partialTraceRight_submatrix_prod_equiv eL eR ρ
  have heq' :
      quantumRelativeEntropy
          (ρ.submatrix e.symm e.symm)
          (σ.submatrix e.symm e.symm) =
        quantumRelativeEntropy
          (partialTraceRight (ρ.submatrix e.symm e.symm))
          (partialTraceRight (σ.submatrix e.symm e.symm)) :=
    quantumRelativeEntropy_partialTraceRight_eq_submatrix_prod_equiv
      hρ hσ eL eR heq
  have hbase :=
    partialTraceRightPetzMap_eq_of_relativeEntropy_eq
      hρ' hσ' hsupp' heq'
  rw [hptrρ,
    partialTraceRightPetzMap_submatrix_prod_equiv eL eR σ hσ
      (partialTraceRight ρ)] at hbase
  exact eq_of_submatrix_equiv_eq e hbase

/-- Equality in right-partial-trace data processing on an arbitrary finite
product index implies recovery by the raw partial-trace Petz map.

The coordinate-free statement is obtained by transporting the finite Weyl
model above along equivalences of both tensor factors. It is the
right-partial-trace forward implication of Hayden--Jozsa--Petz--Winter,
arXiv:quant-ph/0304007v2, Theorem 3 and equation (8), on the explicit
finite-relative-entropy support domain. -/
theorem partialTraceRightPetzMap_eq_of_relativeEntropy_eq_general_support
    {L R : Type*} [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R] [Nonempty R]
    {ρ σ : Matrix (L × R) (L × R) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hsupp : ∀ v : L × R → ℂ, σ *ᵥ v = 0 → ρ *ᵥ v = 0)
    (heq : quantumRelativeEntropy ρ σ =
      quantumRelativeEntropy (partialTraceRight ρ) (partialTraceRight σ)) :
    partialTraceRightPetzMap σ hσ (partialTraceRight ρ) = ρ := by
  classical
  set dL := Fintype.card L
  set dR := Fintype.card R
  letI : NeZero dR := ⟨by simp [dR, Fintype.card_ne_zero (α := R)]⟩
  set eL : L ≃ Fin dL := Fintype.equivFin L
  set eR : R ≃ ZMod dR :=
    (Fintype.equivFin R).trans (ZMod.finEquiv dR).toEquiv
  exact partialTraceRightPetzMap_eq_of_relativeEntropy_eq_of_equiv
    eL eR hρ hσ hsupp heq

/-- Equality in right-partial-trace data processing for density matrices
implies recovery by the completed partial-trace Petz channel.

This is the right-partial-trace forward implication of
Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2, Theorem 3 and
equation (8), on the explicit finite-relative-entropy support domain. The raw
support formula gives the recovery identity; the channel's off-support
preparation term is the separately chosen trace-preserving completion and
vanishes on the recovered marginal. -/
theorem partialTraceRightPetzChannel_recovery_of_dpi_equality
    {L R : Type*} [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R]
    {ρ σ : Matrix (L × R) (L × R) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hρtrace : ρ.trace = 1) (hσtrace : σ.trace = 1)
    (hsupp : ∀ v : L × R → ℂ, σ *ᵥ v = 0 → ρ *ᵥ v = 0)
    (heq : quantumRelativeEntropy ρ σ =
      quantumRelativeEntropy (partialTraceRight ρ) (partialTraceRight σ)) :
    partialTraceRightPetzChannel σ hσ (partialTraceRight ρ) = ρ := by
  classical
  let ρIndex := Classical.choice (nonempty_of_trace_eq_one ρ hρtrace)
  let σIndex := Classical.choice (nonempty_of_trace_eq_one σ hσtrace)
  letI : Nonempty L := ⟨ρIndex.1⟩
  letI : Nonempty R := ⟨σIndex.2⟩
  rw [partialTraceRightPetzChannel_apply_partialTraceRight_of_support
    hρ hσ hsupp]
  exact partialTraceRightPetzMap_eq_of_relativeEntropy_eq_general_support
    hρ hσ hsupp heq

end Matrix
