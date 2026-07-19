/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.RelativeEntropyResolventIntegral
import TNLean.Analysis.ResolventFunctionalCalculus
import TNLean.Channel.Schwarz.PetzEqualityPrerequisites
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The positive-definite finite-Weyl relative-entropy gap

This file specializes the positive-definite resolvent representation of
relative entropy to the finite uniform Weyl family used in the partial-trace
data-processing argument.

## Main results

* `Matrix.weyl_relativeEntropy_gap_integral` proves the exact formula
  `Gap = ∫ (DefA(t) + t DefB(t)) / (1 + t)`.
* `Matrix.weyl_sourceB_defect_eq_zero_of_gap_eq_zero` proves that equality of
  the scalar relative entropies forces the source-`B` defect to vanish for
  every `t > 0`.
* `Matrix.weyl_resolvent_eq_of_relativeEntropy_gap_eq_zero` combines this with
  the fixed-resolvent result to obtain the common source-`B` solution.
* `Matrix.weyl_identity_sandwich_of_partialTraceRight_eq` passes from the
  common resolvent through the relative modular square root to the
  positive-definite identity-Weyl sandwich.
* `Matrix.partialTraceRightPetzMap_eq_of_relativeEntropy_eq_posDef` concludes
  positive-definite recovery by the raw partial-trace Petz map.

## References

* A. Jenčová and M. B. Ruskai, *A Unified Treatment of Convexity of Relative
  Entropy and Related Trace Functions, with Conditions for Equality*,
  arXiv:0903.2895v4, §4 and Appendix, especially lines 658–680.
-/

open Filter MeasureTheory Set Topology
open scoped Matrix ComplexOrder MatrixOrder Kronecker
open Matrix

namespace Matrix

/-- A uniformly weighted conjugate in the finite Weyl family. -/
noncomputable def weightedWeylConjugate
    {dS dC : ℕ} [NeZero dC] (ζ : ℂ)
    (M : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ)
    (g : ZMod dC × ZMod dC) :
    Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ :=
  let U := (1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ g.1 g.2
  (((dC : ℝ) ^ 2)⁻¹) • (U * M * Uᴴ)

/-- The sum of the uniformly weighted finite Weyl conjugates. -/
noncomputable def weightedWeylAverage
    {dS dC : ℕ} [NeZero dC] (ζ : ℂ)
    (M : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) :
    Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ :=
  ∑ g, weightedWeylConjugate ζ M g

/-- The source-`A` quadratic-resolvent defect of the finite Weyl family. -/
noncomputable def weylSourceAResolventDefect
    {dS dC : ℕ} [NeZero dC] (ζ : ℂ)
    (ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ)
    (t : ℝ) : ℝ :=
  ∑ g, sourceAResolventQuadratic
      (weightedWeylConjugate ζ ρ g) (weightedWeylConjugate ζ σ g) t -
    sourceAResolventQuadratic
      (weightedWeylAverage ζ ρ) (weightedWeylAverage ζ σ) t

/-- The source-`B` quadratic-resolvent defect of the finite Weyl family. -/
noncomputable def weylSourceBResolventDefect
    {dS dC : ℕ} [NeZero dC] (ζ : ℂ)
    (ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ)
    (t : ℝ) : ℝ :=
  ∑ g, sourceBResolventQuadratic
      (weightedWeylConjugate ζ ρ g) (weightedWeylConjugate ζ σ g) t -
    sourceBResolventQuadratic
      (weightedWeylAverage ζ ρ) (weightedWeylAverage ζ σ) t

/-- The finite-Weyl Jensen gap of quantum relative entropy. -/
noncomputable def weylRelativeEntropyGap
    {dS dC : ℕ} [NeZero dC] (ζ : ℂ)
    (ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) : ℝ :=
  ∑ g, quantumRelativeEntropy
      (weightedWeylConjugate ζ ρ g) (weightedWeylConjugate ζ σ g) -
    quantumRelativeEntropy
      (weightedWeylAverage ζ ρ) (weightedWeylAverage ζ σ)

private lemma weightedWeylConjugate_posDef
    {dS dC : ℕ} [NeZero dC]
    {M : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hM : M.PosDef) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ dC)
    (g : ZMod dC × ZMod dC) :
    (weightedWeylConjugate ζ M g).PosDef := by
  let U : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ :=
    (1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ g.1 g.2
  have hU : U ∈ unitary
      (Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) := by
    exact Matrix.kronecker_mem_unitary (Submonoid.one_mem _)
      (weyl_mem_unitary hζ g.1 g.2)
  have hq : 0 < ((dC : ℝ) ^ 2)⁻¹ := by
    have hdC : (0 : ℝ) < dC := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dC)
    positivity
  have hc := posDef_conj_unitary hM ⟨U, hU⟩
  simpa only [weightedWeylConjugate, U, star_eq_conjTranspose] using
    hc.smul hq

private lemma weightedWeylAverage_posDef
    {dS dC : ℕ} [NeZero dC]
    {M : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hM : M.PosDef) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ dC) :
    (weightedWeylAverage ζ M).PosDef := by
  rw [weightedWeylAverage]
  exact Matrix.posDef_sum Finset.univ_nonempty fun g _ =>
    weightedWeylConjugate_posDef hM hζ g

private lemma sum_sum_smul
    {ι κ M R : Type*} [Fintype ι] [Fintype κ] [AddCommMonoid M]
    [Monoid R] [DistribMulAction R M] (r : R) (f : ι → κ → M) :
    (∑ i, ∑ j, r • f i j) = r • ∑ i, ∑ j, f i j := by
  rw [Finset.smul_sum (r := r) (s := Finset.univ)]
  simp_rw [Finset.smul_sum (r := r) (s := Finset.univ)]

private lemma trace_sum_re_eq
    {dS dC : ℕ} [NeZero dC]
    (B : ZMod dC × ZMod dC →
      Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) :
    ∑ g, (Matrix.trace (B g)).re = (Matrix.trace (∑ g, B g)).re := by
  rw [← Complex.re_sum, ← Matrix.trace_sum]

/-- The weighted finite Weyl average is the right partial trace tensored with
the maximally mixed right factor. -/
theorem weightedWeylAverage_eq_partialTraceRight_kronecker
    {dS dC : ℕ} [NeZero dC] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ dC)
    (M : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) :
    weightedWeylAverage ζ M =
      partialTraceRight M ⊗ₖ
        ((dC : ℂ)⁻¹ • (1 : Matrix (ZMod dC) (ZMod dC) ℂ)) := by
  calc
    weightedWeylAverage ζ M =
        ((dC : ℂ) ^ 2)⁻¹ • ∑ c : ZMod dC, ∑ e : ZMod dC,
          ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e) * M *
            ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e)ᴴ := by
      rw [weightedWeylAverage, Fintype.sum_prod_type]
      simp only [weightedWeylConjugate]
      rw [sum_sum_smul]
      ext i j
      norm_num
    _ = partialTraceRight M ⊗ₖ
        ((dC : ℂ)⁻¹ • (1 : Matrix (ZMod dC) (ZMod dC) ℂ)) :=
      sum_kronecker_one_weyl_conj hζ M

/-- The zero-index Weyl summand is the uniformly scaled original matrix. -/
private lemma weightedWeylConjugate_zero_zero
    {dS dC : ℕ} [NeZero dC] (ζ : ℂ)
    (M : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) :
    weightedWeylConjugate ζ M (0, 0) = ((dC : ℝ) ^ 2)⁻¹ • M := by
  simp [weightedWeylConjugate, weyl, weylShift, weylClock]

/-- Saturation under the right partial trace makes the coefficient-correct
positive-definite finite-Weyl relative-entropy gap vanish.

The finite Jensen saturation theorem places the uniform coefficient outside
each relative entropy. The positive-scalar homogeneity of relative entropy
identifies that expression with the sum of the relative entropies of the
uniformly weighted Weyl conjugates used in `weylRelativeEntropyGap`.

This is the normalization identity in the finite-Weyl proof of partial-trace
data processing associated with Hayden--Jozsa--Petz--Winter,
arXiv:quant-ph/0304007v2, Theorem 3 and equation (8).

**Scope restriction (positive definite):** The singular-support extension is
not asserted here. Documented in
`docs/paper-gaps/cpsv16_ssa_equality_hayashi_markov.tex`. -/
theorem weylRelativeEntropyGap_eq_zero_of_partialTraceRight_eq
    {dS dC : ℕ} [NeZero dC]
    {ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (heq : quantumRelativeEntropy ρ σ =
      quantumRelativeEntropy (partialTraceRight ρ) (partialTraceRight σ))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ dC) :
    weylRelativeEntropyGap ζ ρ σ = 0 := by
  classical
  have hsupp : ∀ v : Fin dS × ZMod dC → ℂ, σ.mulVec v = 0 → ρ.mulVec v = 0 := by
    intro v hv
    have hv0 : v = 0 := by
      apply Matrix.mulVec_injective_of_isUnit hσ.isUnit
      simpa using hv
    simp [hv0]
  have hsat := quantumRelativeEntropy_weyl_jensen_eq_of_partialTraceRight_eq
    hρ.posSemidef hσ.posSemidef hsupp heq hζ
  let q : ℝ := ((dC : ℝ) ^ 2)⁻¹
  let U := fun g : ZMod dC × ZMod dC =>
    (1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ g.1 g.2
  have hq : 0 < q := by
    have hdC : (0 : ℝ) < dC := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dC)
    dsimp [q]
    positivity
  have hU (g : ZMod dC × ZMod dC) : U g ∈ unitary
      (Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) := by
    exact Matrix.kronecker_mem_unitary (Submonoid.one_mem _)
      (weyl_mem_unitary hζ g.1 g.2)
  have hρg (g : ZMod dC × ZMod dC) : (U g * ρ * (U g)ᴴ).PosDef :=
    posDef_conj_unitary hρ ⟨U g, hU g⟩
  have hσg (g : ZMod dC × ZMod dC) : (U g * σ * (U g)ᴴ).PosDef :=
    posDef_conj_unitary hσ ⟨U g, hU g⟩
  rw [weylRelativeEntropyGap]
  have hterm (g : ZMod dC × ZMod dC) :
      quantumRelativeEntropy (weightedWeylConjugate ζ ρ g)
          (weightedWeylConjugate ζ σ g) =
        q * quantumRelativeEntropy (U g * ρ * (U g)ᴴ)
          (U g * σ * (U g)ᴴ) := by
    simpa only [weightedWeylConjugate, q, U] using
      quantumRelativeEntropy_smul_posDef (hA := hρg g) (hB := hσg g) hq
  rw [Finset.sum_congr rfl (fun g _ => hterm g)]
  rw [← Finset.mul_sum]
  have haverageρ : weightedWeylAverage ζ ρ =
      (((dC : ℂ) ^ 2)⁻¹ • ∑ c : ZMod dC, ∑ e : ZMod dC,
        ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e) * ρ *
          ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e)ᴴ) := by
    rw [weightedWeylAverage, Fintype.sum_prod_type]
    simp only [weightedWeylConjugate]
    rw [sum_sum_smul]
    ext i j
    norm_num
  have haverageσ : weightedWeylAverage ζ σ =
      (((dC : ℂ) ^ 2)⁻¹ • ∑ c : ZMod dC, ∑ e : ZMod dC,
        ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e) * σ *
          ((1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ c e)ᴴ) := by
    rw [weightedWeylAverage, Fintype.sum_prod_type]
    simp only [weightedWeylConjugate]
    rw [sum_sum_smul]
    ext i j
    norm_num
  rw [sub_eq_zero, haverageρ, haverageσ, hsat]
  simp only [q, U, smul_eq_mul, Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]

/-- **The coefficient-correct finite-Weyl relative-entropy gap formula.**
For positive-definite `ρ` and `σ`, the finite-Weyl Jensen gap is
\[
 \int_0^\infty
 \frac{\operatorname{Def}_A(t)+t\operatorname{Def}_B(t)}{1+t}\,dt.
\]
In particular, neither source family is omitted and the source-`B` defect has
the coefficient `t` dictated by the scalar logarithmic representation.

This is the finite-Weyl specialization of Jenčová--Ruskai,
arXiv:0903.2895v4, §4, at `p=1`.

**Scope restriction (positive definite):** Singular supports and the later
Petz sandwich are not asserted here. Documented in
`docs/paper-gaps/cpsv16_ssa_equality_hayashi_markov.tex`. -/
theorem weyl_relativeEntropy_gap_integral
    {dS dC : ℕ} [NeZero dC]
    {ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ dC) :
    weylRelativeEntropyGap ζ ρ σ =
      ∫ t : ℝ in Ioi 0,
        (weylSourceAResolventDefect ζ ρ σ t +
          t * weylSourceBResolventDefect ζ ρ σ t) / (1 + t) := by
  classical
  let A := fun g : ZMod dC × ZMod dC => weightedWeylConjugate ζ ρ g
  let B := fun g : ZMod dC × ZMod dC => weightedWeylConjugate ζ σ g
  let Abar := weightedWeylAverage ζ ρ
  let Bbar := weightedWeylAverage ζ σ
  have hA (g : ZMod dC × ZMod dC) : (A g).PosDef :=
    weightedWeylConjugate_posDef hρ hζ g
  have hB (g : ZMod dC × ZMod dC) : (B g).PosDef :=
    weightedWeylConjugate_posDef hσ hζ g
  have hAbar : Abar.PosDef := weightedWeylAverage_posDef hρ hζ
  have hBbar : Bbar.PosDef := weightedWeylAverage_posDef hσ hζ
  have hInt (g : ZMod dC × ZMod dC) :
      IntegrableOn (relativeEntropyResolventIntegrand (A g) (B g)) (Ioi 0) :=
    relativeEntropyResolventIntegrand_integrableOn (hA g) (hB g)
  have hIntBar :
      IntegrableOn (relativeEntropyResolventIntegrand Abar Bbar) (Ioi 0) :=
    relativeEntropyResolventIntegrand_integrableOn hAbar hBbar
  rw [weylRelativeEntropyGap]
  change (∑ g, quantumRelativeEntropy (A g) (B g)) -
    quantumRelativeEntropy Abar Bbar = _
  simp_rw [quantumRelativeEntropy_resolvent_integral (hA _) (hB _)]
  rw [quantumRelativeEntropy_resolvent_integral hAbar hBbar]
  rw [← integral_finsetSum Finset.univ (fun g _ => hInt g),
    ← integral_sub (integrable_finsetSum Finset.univ (fun g _ => hInt g)) hIntBar]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [relativeEntropyResolventIntegrand, weylSourceAResolventDefect,
    weylSourceBResolventDefect, A, B, Abar, Bbar]
  rw [← Finset.sum_div]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have htrace : ∑ g, (Matrix.trace (B g)).re = (Matrix.trace Bbar).re := by
    exact trace_sum_re_eq B
  rw [htrace]
  ring

/-- The source-`A` finite-Weyl defect is continuous for positive resolvent
parameter. -/
theorem weylSourceAResolventDefect_continuousOn
    {dS dC : ℕ} [NeZero dC]
    {ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ dC) :
    ContinuousOn (weylSourceAResolventDefect ζ ρ σ) (Ioi 0) := by
  classical
  let A := fun g : ZMod dC × ZMod dC => weightedWeylConjugate ζ ρ g
  let B := fun g : ZMod dC × ZMod dC => weightedWeylConjugate ζ σ g
  let Abar := weightedWeylAverage ζ ρ
  let Bbar := weightedWeylAverage ζ σ
  have hA (g : ZMod dC × ZMod dC) : (A g).PosDef :=
    weightedWeylConjugate_posDef hρ hζ g
  have hB (g : ZMod dC × ZMod dC) : (B g).PosDef :=
    weightedWeylConjugate_posDef hσ hζ g
  have hAbar : Abar.PosDef := weightedWeylAverage_posDef hρ hζ
  have hBbar : Bbar.PosDef := weightedWeylAverage_posDef hσ hζ
  have hsum : ContinuousOn
      (fun t => ∑ g, sourceAResolventQuadratic (A g) (B g) t) (Ioi 0) :=
    continuousOn_finsetSum Finset.univ fun g _ =>
      sourceAResolventQuadratic_continuousOn (hA g) (hB g)
  have hbar : ContinuousOn
      (sourceAResolventQuadratic Abar Bbar) (Ioi 0) :=
    sourceAResolventQuadratic_continuousOn hAbar hBbar
  change ContinuousOn (fun t =>
    (∑ g, sourceAResolventQuadratic (A g) (B g) t) -
      sourceAResolventQuadratic Abar Bbar t) (Ioi 0)
  exact hsum.sub hbar

/-- The source-`B` finite-Weyl defect is continuous for positive resolvent
parameter. -/
theorem weylSourceBResolventDefect_continuousOn
    {dS dC : ℕ} [NeZero dC]
    {ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ dC) :
    ContinuousOn (weylSourceBResolventDefect ζ ρ σ) (Ioi 0) := by
  classical
  let A := fun g : ZMod dC × ZMod dC => weightedWeylConjugate ζ ρ g
  let B := fun g : ZMod dC × ZMod dC => weightedWeylConjugate ζ σ g
  let Abar := weightedWeylAverage ζ ρ
  let Bbar := weightedWeylAverage ζ σ
  have hA (g : ZMod dC × ZMod dC) : (A g).PosDef :=
    weightedWeylConjugate_posDef hρ hζ g
  have hB (g : ZMod dC × ZMod dC) : (B g).PosDef :=
    weightedWeylConjugate_posDef hσ hζ g
  have hAbar : Abar.PosDef := weightedWeylAverage_posDef hρ hζ
  have hBbar : Bbar.PosDef := weightedWeylAverage_posDef hσ hζ
  have hsum : ContinuousOn
      (fun t => ∑ g, sourceBResolventQuadratic (A g) (B g) t) (Ioi 0) :=
    continuousOn_finsetSum Finset.univ fun g _ =>
      sourceBResolventQuadratic_continuousOn (hA g) (hB g)
  have hbar : ContinuousOn
      (sourceBResolventQuadratic Abar Bbar) (Ioi 0) :=
    sourceBResolventQuadratic_continuousOn hAbar hBbar
  change ContinuousOn (fun t =>
    (∑ g, sourceBResolventQuadratic (A g) (B g) t) -
      sourceBResolventQuadratic Abar Bbar t) (Ioi 0)
  exact hsum.sub hbar

/-- The source-`A` finite-Weyl resolvent defect is nonnegative at every
positive resolvent parameter. -/
theorem weylSourceAResolventDefect_nonneg
    {dS dC : ℕ} [NeZero dC]
    {ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ dC) {t : ℝ} (ht : 0 < t) :
    0 ≤ weylSourceAResolventDefect ζ ρ σ t := by
  classical
  let N := Fin dS × ZMod dC
  let G := ZMod dC × ZMod dC
  let U : G → Matrix N N ℂ := fun g =>
    (1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ g.1 g.2
  let q : ℝ := ((dC : ℝ) ^ 2)⁻¹
  let A : G → Matrix N N ℂ := fun g => q • (U g * ρ * (U g)ᴴ)
  let B : G → Matrix N N ℂ := fun g => q • (U g * σ * (U g)ᴴ)
  let Abar : Matrix N N ℂ := ∑ g, A g
  let Bbar : Matrix N N ℂ := ∑ g, B g
  let S : G → Matrix (N × N) (N × N) ℂ := fun g =>
    A g ⊗ₖ (1 : Matrix N N ℂ) +
      t • ((1 : Matrix N N ℂ) ⊗ₖ (B g)ᵀ)
  let Sbar : Matrix (N × N) (N × N) ℂ :=
    Abar ⊗ₖ (1 : Matrix N N ℂ) +
      t • ((1 : Matrix N N ℂ) ⊗ₖ Bbarᵀ)
  let a : G → N × N → ℂ := fun g => Matrix.vec (A g)ᵀ
  let abar : N × N → ℂ := Matrix.vec Abarᵀ
  let x : N × N → ℂ := Sbar⁻¹ *ᵥ abar
  have hid :
      ∑ g, ∑ p, ‖((CFC.sqrt (S g))⁻¹ *ᵥ a g -
        CFC.sqrt (S g) *ᵥ x) p‖ ^ 2 =
        ∑ g, sourceAResolventQuadratic (A g) (B g) t -
          sourceAResolventQuadratic Abar Bbar t := by
    have h := weyl_sourceA_resolvent_defect_identity hρ hσ hζ ht
    simpa only [U, q, A, B, Abar, Bbar, S, Sbar, a, abar, x,
      sourceAResolventQuadratic] using h
  have hnonneg :
      0 ≤ ∑ g, sourceAResolventQuadratic (A g) (B g) t -
        sourceAResolventQuadratic Abar Bbar t := by
    rw [← hid]
    positivity
  simpa only [weylSourceAResolventDefect, weightedWeylConjugate,
    weightedWeylAverage, U, q, A, B, Abar, Bbar] using hnonneg

/-- The source-`B` finite-Weyl resolvent defect is nonnegative at every
positive resolvent parameter. -/
theorem weylSourceBResolventDefect_nonneg
    {dS dC : ℕ} [NeZero dC]
    {ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ dC) {t : ℝ} (ht : 0 < t) :
    0 ≤ weylSourceBResolventDefect ζ ρ σ t := by
  classical
  let N := Fin dS × ZMod dC
  let G := ZMod dC × ZMod dC
  let U : G → Matrix N N ℂ := fun g =>
    (1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ g.1 g.2
  let q : ℝ := ((dC : ℝ) ^ 2)⁻¹
  let A : G → Matrix N N ℂ := fun g => q • (U g * ρ * (U g)ᴴ)
  let B : G → Matrix N N ℂ := fun g => q • (U g * σ * (U g)ᴴ)
  let Abar : Matrix N N ℂ := ∑ g, A g
  let Bbar : Matrix N N ℂ := ∑ g, B g
  let S : G → Matrix (N × N) (N × N) ℂ := fun g =>
    A g ⊗ₖ (1 : Matrix N N ℂ) +
      t • ((1 : Matrix N N ℂ) ⊗ₖ (B g)ᵀ)
  let Sbar : Matrix (N × N) (N × N) ℂ :=
    Abar ⊗ₖ (1 : Matrix N N ℂ) +
      t • ((1 : Matrix N N ℂ) ⊗ₖ Bbarᵀ)
  let b : G → N × N → ℂ := fun g => Matrix.vec (B g)ᵀ
  let bbar : N × N → ℂ := Matrix.vec Bbarᵀ
  let x : N × N → ℂ := Sbar⁻¹ *ᵥ bbar
  have hid :
      ∑ g, ∑ p, ‖((CFC.sqrt (S g))⁻¹ *ᵥ b g -
        CFC.sqrt (S g) *ᵥ x) p‖ ^ 2 =
        ∑ g, sourceBResolventQuadratic (A g) (B g) t -
          sourceBResolventQuadratic Abar Bbar t := by
    have h := weyl_resolvent_defect_identity hρ hσ hζ ht
    simpa only [U, q, A, B, Abar, Bbar, S, Sbar, b, bbar, x,
      sourceBResolventQuadratic] using h
  have hnonneg :
      0 ≤ ∑ g, sourceBResolventQuadratic (A g) (B g) t -
        sourceBResolventQuadratic Abar Bbar t := by
    rw [← hid]
    positivity
  simpa only [weylSourceBResolventDefect, weightedWeylConjugate,
    weightedWeylAverage, U, q, A, B, Abar, Bbar] using hnonneg

/-- The coefficient-correct finite-Weyl gap integrand is integrable on the
positive half-line. This assertion is separate from the value of its integral,
so it can be used in the equality case. -/
theorem weylRelativeEntropyGapIntegrand_integrableOn
    {dS dC : ℕ} [NeZero dC]
    {ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ dC) :
    IntegrableOn (fun t : ℝ =>
      (weylSourceAResolventDefect ζ ρ σ t +
        t * weylSourceBResolventDefect ζ ρ σ t) / (1 + t)) (Ioi 0) := by
  classical
  let A := fun g : ZMod dC × ZMod dC => weightedWeylConjugate ζ ρ g
  let B := fun g : ZMod dC × ZMod dC => weightedWeylConjugate ζ σ g
  let Abar := weightedWeylAverage ζ ρ
  let Bbar := weightedWeylAverage ζ σ
  have hA (g : ZMod dC × ZMod dC) : (A g).PosDef :=
    weightedWeylConjugate_posDef hρ hζ g
  have hB (g : ZMod dC × ZMod dC) : (B g).PosDef :=
    weightedWeylConjugate_posDef hσ hζ g
  have hAbar : Abar.PosDef := weightedWeylAverage_posDef hρ hζ
  have hBbar : Bbar.PosDef := weightedWeylAverage_posDef hσ hζ
  have hInt (g : ZMod dC × ZMod dC) :
      IntegrableOn (relativeEntropyResolventIntegrand (A g) (B g)) (Ioi 0) :=
    relativeEntropyResolventIntegrand_integrableOn (hA g) (hB g)
  have hIntBar :
      IntegrableOn (relativeEntropyResolventIntegrand Abar Bbar) (Ioi 0) :=
    relativeEntropyResolventIntegrand_integrableOn hAbar hBbar
  have hbase : IntegrableOn (fun t =>
      (∑ g, relativeEntropyResolventIntegrand (A g) (B g) t) -
        relativeEntropyResolventIntegrand Abar Bbar t) (Ioi 0) :=
    (integrable_finsetSum Finset.univ fun g _ => hInt g).sub hIntBar
  refine hbase.congr_fun ?_ measurableSet_Ioi
  intro t ht
  simp only [relativeEntropyResolventIntegrand, weylSourceAResolventDefect,
    weylSourceBResolventDefect, A, B, Abar, Bbar]
  rw [← Finset.sum_div]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have htrace : ∑ g, (Matrix.trace (B g)).re = (Matrix.trace Bbar).re := by
    exact trace_sum_re_eq B
  rw [htrace]
  ring

/-- The coefficient-correct finite-Weyl gap integrand is continuous on the
positive half-line. -/
theorem weylRelativeEntropyGapIntegrand_continuousOn
    {dS dC : ℕ} [NeZero dC]
    {ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ dC) :
    ContinuousOn (fun t : ℝ =>
      (weylSourceAResolventDefect ζ ρ σ t +
        t * weylSourceBResolventDefect ζ ρ σ t) / (1 + t)) (Ioi 0) := by
  have hA := weylSourceAResolventDefect_continuousOn hρ hσ hζ
  have hB := weylSourceBResolventDefect_continuousOn hρ hσ hζ
  have hnum := hA.add (continuousOn_id.mul hB)
  have hden : ContinuousOn (fun t : ℝ => 1 + t) (Ioi 0) :=
    continuousOn_const.add continuousOn_id
  exact hnum.div hden fun t ht hzero => by
    have ht0 : 0 < t := ht
    have : 0 < 1 + t := by linarith
    exact (ne_of_gt this) hzero

/-- The coefficient-correct finite-Weyl gap integrand is nonnegative on the
positive half-line. -/
theorem weylRelativeEntropyGapIntegrand_nonneg
    {dS dC : ℕ} [NeZero dC]
    {ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ dC)
    {t : ℝ} (ht : 0 < t) :
    0 ≤ (weylSourceAResolventDefect ζ ρ σ t +
      t * weylSourceBResolventDefect ζ ρ σ t) / (1 + t) := by
  have hA := weylSourceAResolventDefect_nonneg hρ hσ hζ ht
  have hB := weylSourceBResolventDefect_nonneg hρ hσ hζ ht
  exact div_nonneg (add_nonneg hA (mul_nonneg (le_of_lt ht) hB)) (by linarith)

/-- If the positive-definite finite-Weyl relative-entropy gap vanishes, then
the source-`B` resolvent defect vanishes at every `t > 0`.

The passage from almost-everywhere vanishing to pointwise vanishing uses the
continuity of both defect families. The domain is explicitly `t > 0`; no
claim is made at the endpoint `t = 0`.

This is the equality argument of Jenčová--Ruskai,
arXiv:0903.2895v4, §4, lines 652--674.

**Scope restriction (positive definite):** Singular supports and the Petz
sandwich remain outside this theorem. Documented in
`docs/paper-gaps/cpsv16_ssa_equality_hayashi_markov.tex`. -/
theorem weyl_sourceB_defect_eq_zero_of_gap_eq_zero
    {dS dC : ℕ} [NeZero dC]
    {ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ dC)
    (hgap : weylRelativeEntropyGap ζ ρ σ = 0) :
    ∀ {t : ℝ}, 0 < t → weylSourceBResolventDefect ζ ρ σ t = 0 := by
  let f : ℝ → ℝ := fun t =>
    (weylSourceAResolventDefect ζ ρ σ t +
      t * weylSourceBResolventDefect ζ ρ σ t) / (1 + t)
  have hfInt : IntegrableOn f (Ioi 0) :=
    weylRelativeEntropyGapIntegrand_integrableOn hρ hσ hζ
  have hfCont : ContinuousOn f (Ioi 0) :=
    weylRelativeEntropyGapIntegrand_continuousOn hρ hσ hζ
  have hfNonneg : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ f t := by
    intro t ht
    exact weylRelativeEntropyGapIntegrand_nonneg hρ hσ hζ ht
  have hIntZero : ∫ t in Ioi (0 : ℝ), f t = 0 := by
    rw [← weyl_relativeEntropy_gap_integral hρ hσ hζ]
    exact hgap
  have haeNonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hfNonneg t ht
  have haeZero : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae haeNonneg hfInt).mp hIntZero
  have hpointZero : EqOn f 0 (Ioi (0 : ℝ)) :=
    Measure.eqOn_open_of_ae_eq haeZero isOpen_Ioi hfCont continuousOn_const
  intro t ht
  have hfZero : f t = 0 := hpointZero ht
  have hden : (1 + t : ℝ) ≠ 0 := by linarith
  have hsum : weylSourceAResolventDefect ζ ρ σ t +
      t * weylSourceBResolventDefect ζ ρ σ t = 0 := by
    rcases (div_eq_zero_iff.mp hfZero) with h | h
    · exact h
    · exact (hden h).elim
  have hA := weylSourceAResolventDefect_nonneg hρ hσ hζ ht
  have hB := weylSourceBResolventDefect_nonneg hρ hσ hζ ht
  nlinarith

/-- Equality in the positive-definite finite-Weyl relative-entropy inequality
gives the common source-`B` fixed-resolvent solution for every `t > 0`.

This combines the coefficient-correct integral equality argument with
`weyl_resolvent_eq_of_defect_eq_zero`; it corresponds to the equality
analysis of Jenčová--Ruskai, arXiv:0903.2895v4, §4 and Appendix.

**Scope restriction (positive definite):** The inverse-square-root integral
and singular-support extension are not asserted here. Documented in
`docs/paper-gaps/cpsv16_ssa_equality_hayashi_markov.tex`. -/
theorem weyl_resolvent_eq_of_relativeEntropy_gap_eq_zero
    {dS dC : ℕ} [NeZero dC]
    {ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ dC)
    (hgap : weylRelativeEntropyGap ζ ρ σ = 0)
    {t : ℝ} (ht : 0 < t) :
    let U := fun g : ZMod dC × ZMod dC =>
      (1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ g.1 g.2
    let q : ℝ := ((dC : ℝ) ^ 2)⁻¹
    let A := fun g => q • (U g * ρ * (U g)ᴴ)
    let B := fun g => q • (U g * σ * (U g)ᴴ)
    let Abar := ∑ g, A g
    let Bbar := ∑ g, B g
    let S := fun g => A g ⊗ₖ (1 : Matrix (Fin dS × ZMod dC)
        (Fin dS × ZMod dC) ℂ) +
      t • ((1 : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) ⊗ₖ (B g)ᵀ)
    let Sbar := Abar ⊗ₖ (1 : Matrix (Fin dS × ZMod dC)
        (Fin dS × ZMod dC) ℂ) +
      t • ((1 : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) ⊗ₖ Bbarᵀ)
    let b := fun g => Matrix.vec (B g)ᵀ
    let bbar := Matrix.vec Bbarᵀ
    ∀ g, (S g)⁻¹ *ᵥ b g = Sbar⁻¹ *ᵥ bbar := by
  apply weyl_resolvent_eq_of_defect_eq_zero hρ hσ hζ ht
  simpa only [weylSourceBResolventDefect, sourceBResolventQuadratic,
    weightedWeylConjugate, weightedWeylAverage] using
    weyl_sourceB_defect_eq_zero_of_gap_eq_zero hρ hσ hζ hgap ht

/-- Saturation of relative entropy under the right partial trace gives the
common source-`B` fixed-resolvent solution for every positive parameter.

This combines the finite-Weyl Jensen saturation theorem, positive-scalar
homogeneity, and the coefficient-correct gap integral. It is the
positive-definite resolvent conclusion corresponding to Jenčová--Ruskai,
arXiv:0903.2895v4, §4 and Appendix.

**Scope restriction (positive definite):** The inverse-square-root limit and
singular-support extension are not asserted here. Documented in
`docs/paper-gaps/cpsv16_ssa_equality_hayashi_markov.tex`. -/
theorem weyl_resolvent_eq_of_partialTraceRight_eq
    {dS dC : ℕ} [NeZero dC]
    {ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (heq : quantumRelativeEntropy ρ σ =
      quantumRelativeEntropy (partialTraceRight ρ) (partialTraceRight σ))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ dC)
    {t : ℝ} (ht : 0 < t) :
    let U := fun g : ZMod dC × ZMod dC =>
      (1 : Matrix (Fin dS) (Fin dS) ℂ) ⊗ₖ weyl ζ g.1 g.2
    let q : ℝ := ((dC : ℝ) ^ 2)⁻¹
    let A := fun g => q • (U g * ρ * (U g)ᴴ)
    let B := fun g => q • (U g * σ * (U g)ᴴ)
    let Abar := ∑ g, A g
    let Bbar := ∑ g, B g
    let S := fun g => A g ⊗ₖ (1 : Matrix (Fin dS × ZMod dC)
        (Fin dS × ZMod dC) ℂ) +
      t • ((1 : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) ⊗ₖ (B g)ᵀ)
    let Sbar := Abar ⊗ₖ (1 : Matrix (Fin dS × ZMod dC)
        (Fin dS × ZMod dC) ℂ) +
      t • ((1 : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) ⊗ₖ Bbarᵀ)
    let b := fun g => Matrix.vec (B g)ᵀ
    let bbar := Matrix.vec Bbarᵀ
    ∀ g, (S g)⁻¹ *ᵥ b g = Sbar⁻¹ *ᵥ bbar := by
  exact weyl_resolvent_eq_of_relativeEntropy_gap_eq_zero hρ hσ hζ
    (weylRelativeEntropyGap_eq_zero_of_partialTraceRight_eq hρ hσ heq hζ) ht

/-- Saturation under the right partial trace identifies the positive square-root
ratio of the original pair with that of its uniform Weyl average.

The common resolvent is first rewritten as a relative-modular resolvent and
then passed through the positive square-root functional calculus, following
Jenčová--Ruskai, arXiv:0903.2895v4, lines 658–680.

**Scope restriction (positive definite):** The singular-support extension is
not asserted here. Documented in
`docs/paper-gaps/cpsv16_ssa_equality_hayashi_markov.tex`. -/
theorem weyl_sqrt_ratio_eq_of_partialTraceRight_eq
    {dS dC : ℕ} [NeZero dC]
    {ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (heq : quantumRelativeEntropy ρ σ =
      quantumRelativeEntropy (partialTraceRight ρ) (partialTraceRight σ)) :
    let barρ := partialTraceRight ρ ⊗ₖ
      ((dC : ℂ)⁻¹ • (1 : Matrix (ZMod dC) (ZMod dC) ℂ))
    CFC.sqrt ρ * hσ.posSemidef.supportInvSqrt =
      CFC.sqrt barρ *
        ((partialTraceRight_posDef hσ).kronecker
          maximallyMixed_posDef).posSemidef.supportInvSqrt := by
  classical
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ dC :=
    ⟨_, Complex.isPrimitiveRoot_exp dC (NeZero.ne dC)⟩
  let aZero := weightedWeylConjugate ζ ρ (0, 0)
  let bZero := weightedWeylConjugate ζ σ (0, 0)
  let aBar := weightedWeylAverage ζ ρ
  let bBar := weightedWeylAverage ζ σ
  have haZero : aZero.PosDef := weightedWeylConjugate_posDef hρ hζ (0, 0)
  have hbZero : bZero.PosDef := weightedWeylConjugate_posDef hσ hζ (0, 0)
  have haBar : aBar.PosDef := weightedWeylAverage_posDef hρ hζ
  have hbBar : bBar.PosDef := weightedWeylAverage_posDef hσ hζ
  have hmodularResolvent : ∀ {t : ℝ}, 0 < t →
      (t • (1 : Matrix ((Fin dS × ZMod dC) × (Fin dS × ZMod dC))
          ((Fin dS × ZMod dC) × (Fin dS × ZMod dC)) ℂ) +
        aZero ⊗ₖ (bZero⁻¹)ᵀ)⁻¹ *ᵥ
          Matrix.vec (1 : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ)ᵀ =
      (t • (1 : Matrix ((Fin dS × ZMod dC) × (Fin dS × ZMod dC))
          ((Fin dS × ZMod dC) × (Fin dS × ZMod dC)) ℂ) +
        aBar ⊗ₖ (bBar⁻¹)ᵀ)⁻¹ *ᵥ
          Matrix.vec (1 : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ)ᵀ := by
    intro t ht
    calc
      _ = (aZero ⊗ₖ (1 : Matrix (Fin dS × ZMod dC)
              (Fin dS × ZMod dC) ℂ) +
            t • ((1 : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) ⊗ₖ
              bZeroᵀ))⁻¹ *ᵥ Matrix.vec bZeroᵀ :=
        (sourceB_resolvent_eq_relativeModular haZero hbZero ht).symm
      _ = (aBar ⊗ₖ (1 : Matrix (Fin dS × ZMod dC)
              (Fin dS × ZMod dC) ℂ) +
            t • ((1 : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ) ⊗ₖ
              bBarᵀ))⁻¹ *ᵥ Matrix.vec bBarᵀ := by
        simpa only [aZero, bZero, aBar, bBar, weightedWeylConjugate,
          weightedWeylAverage] using
          (weyl_resolvent_eq_of_partialTraceRight_eq hρ hσ heq hζ ht (0, 0))
      _ = _ := sourceB_resolvent_eq_relativeModular haBar hbBar ht
  have hsqrt := sqrt_mulVec_eq_of_resolvent_mulVec_eq
    (haZero.kronecker hbZero.inv.transpose).posSemidef
    (haBar.kronecker hbBar.inv.transpose).posSemidef hmodularResolvent
  rw [relativeModular_sqrt_mulVec_vec_one haZero hbZero,
    relativeModular_sqrt_mulVec_vec_one haBar hbBar] at hsqrt
  have hratio : CFC.sqrt aZero * (CFC.sqrt bZero)⁻¹ =
      CFC.sqrt aBar * (CFC.sqrt bBar)⁻¹ :=
    Matrix.transpose_injective (Matrix.vec_inj.mp hsqrt)
  have hqpos : 0 < ((dC : ℝ) ^ 2)⁻¹ := by
    have hdC : (0 : ℝ) < dC := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dC)
    positivity
  have haZeroEq : aZero = ((dC : ℝ) ^ 2)⁻¹ • ρ :=
    weightedWeylConjugate_zero_zero ζ ρ
  have hbZeroEq : bZero = ((dC : ℝ) ^ 2)⁻¹ • σ :=
    weightedWeylConjugate_zero_zero ζ σ
  have haBarEq : aBar = partialTraceRight ρ ⊗ₖ
      ((dC : ℂ)⁻¹ • (1 : Matrix (ZMod dC) (ZMod dC) ℂ)) :=
    weightedWeylAverage_eq_partialTraceRight_kronecker hζ ρ
  have hbBarEq : bBar = partialTraceRight σ ⊗ₖ
      ((dC : ℂ)⁻¹ • (1 : Matrix (ZMod dC) (ZMod dC) ℂ)) :=
    weightedWeylAverage_eq_partialTraceRight_kronecker hζ σ
  rw [haZeroEq, hbZeroEq, haBarEq, hbBarEq,
    hρ.posSemidef.sqrt_smul hqpos.le,
    hσ.posSemidef.sqrt_smul hqpos.le] at hratio
  have hsqrtq : Real.sqrt (((dC : ℝ) ^ 2)⁻¹) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hqpos
  letI : Invertible (Real.sqrt (((dC : ℝ) ^ 2)⁻¹) : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast hsqrtq)
  have hsqrtσunit : IsUnit (CFC.sqrt σ) := by
    exact (CFC.isUnit_sqrt_iff σ hσ.posSemidef.nonneg).2 hσ.isUnit
  have hsqrtσdet : IsUnit (CFC.sqrt σ).det :=
    (Matrix.isUnit_iff_isUnit_det (CFC.sqrt σ)).mp hsqrtσunit
  have hinvScale :
      (Real.sqrt (((dC : ℝ) ^ 2)⁻¹) • CFC.sqrt σ)⁻¹ =
        (Real.sqrt (((dC : ℝ) ^ 2)⁻¹))⁻¹ • (CFC.sqrt σ)⁻¹ := by
    change (((Real.sqrt (((dC : ℝ) ^ 2)⁻¹) : ℂ) • CFC.sqrt σ)⁻¹ =
      (((Real.sqrt (((dC : ℝ) ^ 2)⁻¹))⁻¹ : ℝ) : ℂ) • (CFC.sqrt σ)⁻¹)
    rw [Complex.ofReal_inv]
    simpa only [invOf_eq_inv] using
      Matrix.inv_smul (A := CFC.sqrt σ)
        (Real.sqrt (((dC : ℝ) ^ 2)⁻¹) : ℂ) hsqrtσdet
  rw [hinvScale] at hratio
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    inv_mul_cancel₀ hsqrtq, one_smul] at hratio
  rw [PosDef.supportInvSqrt_eq_inv_sqrt hσ,
    PosDef.supportInvSqrt_eq_inv_sqrt
      ((partialTraceRight_posDef hσ).kronecker maximallyMixed_posDef)]
  exact hratio

/-- Saturation under the right partial trace gives the identity-Weyl Petz
sandwich in the positive-definite case.

The square-root ratio equality is converted to the sandwich by taking its
Gram matrix and cancelling the invertible square root of `σ`. This is the
positive-definite recovery step corresponding to Jenčová--Ruskai,
arXiv:0903.2895v4, lines 658–680, and Hayden--Jozsa--Petz--Winter,
arXiv:quant-ph/0304007v2, Theorem 3, equation (8).

**Scope restriction (positive definite):** The singular-support extension is
not asserted here. Documented in
`docs/paper-gaps/cpsv16_ssa_equality_hayashi_markov.tex`. -/
theorem weyl_identity_sandwich_of_partialTraceRight_eq
    {dS dC : ℕ} [NeZero dC]
    {ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (heq : quantumRelativeEntropy ρ σ =
      quantumRelativeEntropy (partialTraceRight ρ) (partialTraceRight σ)) :
    let hbarσ := (PosSemidef.partialTraceRight hσ.posSemidef).kronecker
      maximallyMixed_posDef.posSemidef
    hσ.isHermitian.cfc Real.sqrt *
        (hbarσ.supportInvSqrt *
          (partialTraceRight ρ ⊗ₖ
            ((dC : ℂ)⁻¹ • (1 : Matrix (ZMod dC) (ZMod dC) ℂ))) *
          hbarσ.supportInvSqrt) *
        hσ.isHermitian.cfc Real.sqrt = ρ := by
  classical
  let barρ := partialTraceRight ρ ⊗ₖ
    ((dC : ℂ)⁻¹ • (1 : Matrix (ZMod dC) (ZMod dC) ℂ))
  let barσ := partialTraceRight σ ⊗ₖ
    ((dC : ℂ)⁻¹ • (1 : Matrix (ZMod dC) (ZMod dC) ℂ))
  have hbarρ : barρ.PosDef :=
    (partialTraceRight_posDef hρ).kronecker maximallyMixed_posDef
  have hbarσ : barσ.PosDef :=
    (partialTraceRight_posDef hσ).kronecker maximallyMixed_posDef
  have hratio := weyl_sqrt_ratio_eq_of_partialTraceRight_eq hρ hσ heq
  dsimp only at hratio
  rw [PosDef.supportInvSqrt_eq_inv_sqrt hσ,
    PosDef.supportInvSqrt_eq_inv_sqrt hbarσ] at hratio
  change CFC.sqrt ρ * (CFC.sqrt σ)⁻¹ =
    CFC.sqrt barρ * (CFC.sqrt barσ)⁻¹ at hratio
  have hsqrtρ : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ := by
    exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)).isHermitian.eq
  have hsqrtσ : (CFC.sqrt σ)ᴴ = CFC.sqrt σ := by
    exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σ)).isHermitian.eq
  have hsqrtBarρ : (CFC.sqrt barρ)ᴴ = CFC.sqrt barρ := by
    exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg barρ)).isHermitian.eq
  have hsqrtBarσ : (CFC.sqrt barσ)ᴴ = CFC.sqrt barσ := by
    exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg barσ)).isHermitian.eq
  have hgram := congrArg (fun X => Xᴴ * X) hratio
  have hleftGram :
      (CFC.sqrt ρ * (CFC.sqrt σ)⁻¹)ᴴ *
          (CFC.sqrt ρ * (CFC.sqrt σ)⁻¹) =
        (CFC.sqrt σ)⁻¹ * ρ * (CFC.sqrt σ)⁻¹ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
      hsqrtρ, hsqrtσ]
    calc
      ((CFC.sqrt σ)⁻¹ * CFC.sqrt ρ) *
            (CFC.sqrt ρ * (CFC.sqrt σ)⁻¹) =
          (CFC.sqrt σ)⁻¹ * (CFC.sqrt ρ * CFC.sqrt ρ) *
            (CFC.sqrt σ)⁻¹ := by noncomm_ring
      _ = (CFC.sqrt σ)⁻¹ * ρ * (CFC.sqrt σ)⁻¹ := by
        rw [CFC.sqrt_mul_sqrt_self ρ hρ.posSemidef.nonneg]
  have hrightGram :
      (CFC.sqrt barρ * (CFC.sqrt barσ)⁻¹)ᴴ *
          (CFC.sqrt barρ * (CFC.sqrt barσ)⁻¹) =
        (CFC.sqrt barσ)⁻¹ * barρ * (CFC.sqrt barσ)⁻¹ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
      hsqrtBarρ, hsqrtBarσ]
    calc
      ((CFC.sqrt barσ)⁻¹ * CFC.sqrt barρ) *
            (CFC.sqrt barρ * (CFC.sqrt barσ)⁻¹) =
          (CFC.sqrt barσ)⁻¹ * (CFC.sqrt barρ * CFC.sqrt barρ) *
            (CFC.sqrt barσ)⁻¹ := by noncomm_ring
      _ = (CFC.sqrt barσ)⁻¹ * barρ * (CFC.sqrt barσ)⁻¹ := by
        rw [CFC.sqrt_mul_sqrt_self barρ hbarρ.posSemidef.nonneg]
  have hgram' :
      (CFC.sqrt σ)⁻¹ * ρ * (CFC.sqrt σ)⁻¹ =
        (CFC.sqrt barσ)⁻¹ * barρ * (CFC.sqrt barσ)⁻¹ := by
    exact hleftGram.symm.trans (hgram.trans hrightGram)
  have hsqrtσunit : IsUnit (CFC.sqrt σ) :=
    (CFC.isUnit_sqrt_iff σ hσ.posSemidef.nonneg).2 hσ.isUnit
  letI : Invertible (CFC.sqrt σ) := hsqrtσunit.invertible
  have hsandwich : CFC.sqrt σ *
      ((CFC.sqrt barσ)⁻¹ * barρ * (CFC.sqrt barσ)⁻¹) *
      CFC.sqrt σ = ρ := by
    rw [← hgram']
    calc
      CFC.sqrt σ * ((CFC.sqrt σ)⁻¹ * ρ * (CFC.sqrt σ)⁻¹) * CFC.sqrt σ =
          (CFC.sqrt σ * (CFC.sqrt σ)⁻¹) * ρ *
            ((CFC.sqrt σ)⁻¹ * CFC.sqrt σ) := by noncomm_ring
      _ = ρ := by
        rw [mul_inv_of_invertible, inv_mul_of_invertible,
          Matrix.one_mul, Matrix.mul_one]
  have hsqrtCfc : hσ.isHermitian.cfc Real.sqrt = CFC.sqrt σ := by
    rw [← hσ.isHermitian.cfc_eq, ← cfcₙ_eq_cfc]
    exact (CFC.sqrt_eq_real_sqrt σ hσ.posSemidef.nonneg).symm
  have hbarSupport :
      ((PosSemidef.partialTraceRight hσ.posSemidef).kronecker
        maximallyMixed_posDef.posSemidef).supportInvSqrt =
          (CFC.sqrt barσ)⁻¹ := by
    convert PosDef.supportInvSqrt_eq_inv_sqrt hbarσ using 1
  dsimp only
  rw [hsqrtCfc, hbarSupport]
  exact hsandwich

/-- Positive-definite equality in right-partial-trace data processing implies
recovery by the native raw Petz map.

This is the positive-definite specialization of Hayden--Jozsa--Petz--Winter,
arXiv:quant-ph/0304007v2, Theorem 3, equation (8). -/
theorem partialTraceRightPetzMap_eq_of_relativeEntropy_eq_posDef
    {dS dC : ℕ} [NeZero dC]
    {ρ σ : Matrix (Fin dS × ZMod dC) (Fin dS × ZMod dC) ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (heq : quantumRelativeEntropy ρ σ =
      quantumRelativeEntropy (partialTraceRight ρ) (partialTraceRight σ)) :
    partialTraceRightPetzMap σ hσ.posSemidef (partialTraceRight ρ) = ρ := by
  apply partialTraceRightPetzMap_eq_of_weyl_identity_sandwich hσ.posSemidef
  exact weyl_identity_sandwich_of_partialTraceRight_eq hρ hσ heq

end Matrix
