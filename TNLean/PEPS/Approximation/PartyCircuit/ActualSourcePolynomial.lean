/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Compression.SourceSampling.Approximation

/-!
# Polynomial sample count for an actual circuit

For every real accuracy exponent, round that exponent up only in the explicit
sample count. The same global sample then gives the desired inverse-power error.
The count depends on the source-count and gate-resource bounds, but not on private
dimensions or original source ranks.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 174–175,
269–277, 364–369 and 548–558.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-polynomial-bounds; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/

noncomputable section
open MeasureTheory Matrix ManyBody QICLean.ComplexGaussian
open scoped Matrix ComplexConjugate NNReal

namespace QuantumCircuit.Party.SourceCircuit

variable {P : Type} [Fintype P] [DecidableEq P] {X Y G : P → Type} [∀ p, Fintype (X p)]
  [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] [∀ p, Fintype (G p)]
  {d : P → ℕ}

open Classical in
/-- The actual sampled physical operator has inverse-power accuracy with an
explicit polynomial bound on the same positive sample count. The Schmidt data and
sample are constructed, and the accuracy exponent may be any real number. The output register of
every party is read through `e` as a physical register of dimension `d p` and a private register;
the input is prepared by an allowed source-free word. -/
theorem exists_sourceSample_polynomial_error_le (e : ∀ p, Y p ≃ Fin (d p) × G p)
    (w : SourceCircuit X Y) (hw : w.IsLocalContractive)
    (lifetime : ℕ) (B D : ℝ≥0) (hB : 1 ≤ B) (hD : 1 ≤ D)
    (hlifetime : ∀ p, w.participationCount p ≤ lifetime)
    (hcoeff : ∀ j : w.gateLocations, ∑ ξ : w.branchLabels j, ‖w.branchCoefficient j ξ‖ ≤ B)
    (hphysical : ∀ p, (d p : ℝ≥0) ≤ D)
    (L C_N C_B C_D p : ℝ) (n₀ m₀ r₀ : ℕ)
    (hL : 1 ≤ L) (hCN : 1 ≤ C_N) (hCB : 0 ≤ C_B)
    (hN : (Fintype.card w.sourceLocations : ℝ) ≤ C_N * L ^ n₀)
    (hBbound : (B : ℝ) ≤ C_B * L ^ m₀) (hDbound : (D : ℝ) ≤ C_D * L ^ r₀)
    (p₀ : Word (fun _ ↦ Unit) X) (hp₀ : p₀.IsAllowed) (hp₀s : p₀.sources = []) :
    let q := ⌈p⌉₊
    let Q := (B : ℝ) ^ (4 * lifetime) * (D : ℝ) ^ 4
    let k := binomialSampleCount (max 1 (Fintype.card w.sourceLocations)) Q (L ^ q)⁻¹
    0 < k ∧ (k : ℝ) <
      (64 * C_N ^ 2 * (C_B ^ (4 * lifetime) * C_D ^ 4) ^ 2 + 2) *
        L ^ (2 * (n₀ + 4 * lifetime * m₀ + 4 * r₀ + q)) ∧
    ∃ (lam : ∀ s : w.sourceLocations, w.branchLabels s.1 →
        Fin (min (w.sourceDims s).1 (w.sourceDims s).2) → ℝ)
      (E : ∀ s : w.sourceLocations, w.branchLabels s.1 →
        Matrix (w.leftBasis s) (Fin (min (w.sourceDims s).1 (w.sourceDims s).2)) ℂ)
      (F : ∀ s : w.sourceLocations, w.branchLabels s.1 →
        Matrix (w.rightBasis s) (Fin (min (w.sourceDims s).1 (w.sourceDims s).2)) ℂ),
      (∀ s ξ, (∀ j, 0 ≤ lam s ξ j) ∧ ∑ j, lam s ξ j = 1 ∧
        (E s ξ)ᴴ * E s ξ = 1 ∧ (F s ξ)ᴴ * F s ξ = 1 ∧
        schmidtFrameVector (lam s ξ) (E s ξ) (F s ξ) = (w.sourceVectorAt s ξ).ofLp) ∧
      ∃ ω : SourceGaussianSamples w k,
        let ψ : EuclideanSpace ℂ (Config X) :=
          Matrix.toEuclideanLin p₀.op (WithLp.toLp 2 fun _ ↦ 1)
        rectangularTraceNorm
          (physicalSourceReplacedDensity w
              (fun s ξ ζ ↦ sampledSourceMatrix w k lam E F s ξ ζ ω) (partyReadout e)
              (euclideanOuterProduct ψ ψ) -
            physicalDensity w (partyReadout e) (euclideanOuterProduct ψ ψ)) ≤ L ^ (-p) / 4 := by
  intro q Q k
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hε : 0 < (L ^ q)⁻¹ := by positivity
  have hεone : (L ^ q)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL)
  have hsmall : (L ^ q)⁻¹ ≤ L ^ (-p) := by
    calc
      _ = L ^ (-(q : ℝ)) := by rw [Real.rpow_neg hLpos.le, Real.rpow_natCast]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL (neg_le_neg (Nat.le_ceil p))
  refine ⟨(binomialSampleCount_bounds _ Q _).1,
    binomialSampleCount_lt_of_cost_power_bounds _ lifetime B D L C_N C_B C_D
      n₀ m₀ r₀ q hL hCN hCB B.coe_nonneg D.coe_nonneg hN hBbound hDbound, ?_⟩
  obtain ⟨lam, E, F, hframes, ω, hω⟩ := exists_sourceSample_lifetime_error_le
    e w hw lifetime B D hB hD hlifetime hcoeff hphysical (L ^ q)⁻¹ hε hεone p₀ hp₀ hp₀s
  exact ⟨lam, E, F, hframes, ω, hω.trans (div_le_div_of_nonneg_right hsmall (by norm_num))⟩

end QuantumCircuit.Party.SourceCircuit
