/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.MinimalCutGramMetrics
import TNLean.MPS.MPU.PrefixGramReindex
import TNLean.MPS.Preparation.MinimalCutRepresentationIntervals

/-!
# Simultaneous coherent interval isometries of a finite unitary

The same minimal cut bases define every physical interval by coordinate
restriction. Their interval tensors multiply exactly across an intermediate
cut and reproduce the actual longer prefix factors. Physical regrouping
preserves the prefix Gram affine hull, so the metrics chosen simultaneously
from the original finite unitary make every weighted interval an isometry.

The final theorem assumes only unitarity, positive physical dimension, and
positive length. It supplies the same bases and metrics for all intervals;
no independent interval metric or isometry witness is supplied. Its Gram
identity includes arbitrary internally entangled interval inputs.

Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

open Matrix
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace MPUCircuit

/-- Sitewise pairing commutes with joining a physical prefix and interval.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem pairPhysicalConfig_joinCutPrefix {d N j k : ℕ}
    (x y : MPSPreparation.CutPrefixConfig d N j)
    (z w : MPSPreparation.CutIntervalConfig d N j k) :
    pairPhysicalConfig (MPSPreparation.joinCutPrefix j k x z)
        (MPSPreparation.joinCutPrefix j k y w) =
      MPSPreparation.joinCutPrefix j k (pairPhysicalConfig x y) (pairPhysicalConfig z w) := by
  funext s
  by_cases h : s.val < j <;> simp [pairPhysicalConfig, MPSPreparation.joinCutPrefix, h]

/-- The operator interval tensor obtained by fixing its paired physical
output and input configuration in the coherent minimal cut representation.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def minimalOperatorInterval {d N : ℕ}
    (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) k))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k))
    {j k : ℕ} (hjk : j ≤ k) :
    MPSPreparation.CutIntervalConfig d N j k → MPSPreparation.CutIntervalConfig d N j k →
      Matrix (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) j))
        (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) k)) ℂ :=
  fun x y ↦ MPSPreparation.cutIntervalMatrix (operatorCoefficientTensor U) B hjk
    (pairPhysicalConfig x y)

/-- The longer operator prefix is exactly the shorter operator prefix
multiplied by its constructed middle interval, after regrouping physical
configurations.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem minimalOperatorPrefix_concat {d N : ℕ}
    (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) k))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k))
    {j k : ℕ} (hjk : j ≤ k) :
    (fun (a : MPSPreparation.CutPrefixConfig d N j ×
          MPSPreparation.CutIntervalConfig d N j k)
        (b : MPSPreparation.CutPrefixConfig d N j ×
          MPSPreparation.CutIntervalConfig d N j k) (_ : Unit) q ↦
      minimalOperatorPrefixFactor U B k (MPSPreparation.joinCutPrefix j k a.1 a.2)
        (MPSPreparation.joinCutPrefix j k b.1 b.2) q) =
      (fun a b ↦ (Matrix.of fun (_ : Unit) q ↦ minimalOperatorPrefixFactor U B j a.1 b.1 q) *
        minimalOperatorInterval U B hjk a.2 b.2) := by
  classical
  ext a b t q
  change MPSPreparation.cutPrefixMatrix (operatorCoefficientTensor U) B k
      (pairPhysicalConfig (MPSPreparation.joinCutPrefix j k a.1 a.2)
        (MPSPreparation.joinCutPrefix j k b.1 b.2)) q =
    ∑ p, MPSPreparation.cutPrefixMatrix (operatorCoefficientTensor U) B j
      (pairPhysicalConfig a.1 b.1) p *
        MPSPreparation.cutIntervalMatrix (operatorCoefficientTensor U) B hjk
          (pairPhysicalConfig a.2 b.2) p q
  rw [pairPhysicalConfig_joinCutPrefix]
  exact MPSPreparation.cutPrefixMatrix_interval (operatorCoefficientTensor U) B hjk
    (pairPhysicalConfig a.1 b.1) (pairPhysicalConfig a.2 b.2) q

/-- The Gram affine hull of the concatenated prefix and interval equals
the actual longer-cut prefix hull. This identity includes arbitrary
internally entangled prefix input densities.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem prefixGramAffineHull_minimalOperatorPrefix_concat {d N : ℕ}
    (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) k))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k))
    {j k : ℕ} (hjk : j ≤ k) :
    prefixGramAffineHull
      (fun (a : MPSPreparation.CutPrefixConfig d N j ×
            MPSPreparation.CutIntervalConfig d N j k)
          (b : MPSPreparation.CutPrefixConfig d N j ×
            MPSPreparation.CutIntervalConfig d N j k) ↦
        (Matrix.of fun (_ : Unit) q ↦ minimalOperatorPrefixFactor U B j a.1 b.1 q) *
          minimalOperatorInterval U B hjk a.2 b.2) =
      prefixGramAffineHull
        (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B k aa bb q) := by
  rw [← minimalOperatorPrefix_concat]
  exact prefixGramAffineHull_physical_reindex
    (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B k aa bb q)
    (MPSPreparation.cutPrefixIntervalConfigEquiv d N j k hjk)
    (MPSPreparation.cutPrefixIntervalConfigEquiv d N j k hjk)

open scoped Classical in
/-- A metric in the earlier cut hull and a positive metric normalizing
the later cut hull make the constructed interval an isometry. The whole
input Gram is determined, including off-diagonal entries and entangled inputs.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem minimalOperatorInterval_isometry_of_cut_metrics {d N : ℕ}
    (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) k))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k))
    {j k : ℕ} (hjk : j ≤ k)
    {P : Matrix (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) j))
      (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) j)) ℂ}
    (hP : P ∈ prefixGramAffineHull
      (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B j aa bb q))
    (hPpos : P.PosSemidef)
    {Q : Matrix (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) k))
      (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) k)) ℂ}
    (hQpos : Q.PosSemidef)
    (hQ : ∀ X ∈ prefixGramAffineHull
      (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B k aa bb q),
      trace (X * Q) = 1) :
    (vectorizedWeightedInterval (minimalOperatorInterval U B hjk) (CFC.sqrt P) (CFC.sqrt Q))ᴴ *
      vectorizedWeightedInterval (minimalOperatorInterval U B hjk) (CFC.sqrt P) (CFC.sqrt Q) =
        1 := by
  have hnorm : ∀ X ∈ prefixGramAffineHull
      (fun (a : MPSPreparation.CutPrefixConfig d N j ×
            MPSPreparation.CutIntervalConfig d N j k)
          (b : MPSPreparation.CutPrefixConfig d N j ×
            MPSPreparation.CutIntervalConfig d N j k) ↦
        (Matrix.of fun (_ : Unit) q ↦ minimalOperatorPrefixFactor U B j a.1 b.1 q) *
          minimalOperatorInterval U B hjk a.2 b.2), trace (X * Q) = 1 := by
    intro X hX
    rw [prefixGramAffineHull_minimalOperatorPrefix_concat] at hX
    exact hQ X hX
  have hiso := vectorizedWeightedInterval_isometry_of_prefixGramAffineHull
    (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B j aa bb q)
    (minimalOperatorInterval U B hjk) hP hPpos hQpos hnorm
  ext b c
  have h := congrFun (congrFun hiso b) c
  by_cases hbc : b = c
  · simpa only [Matrix.one_apply, ite_eq_left hbc] using h
  · simpa only [Matrix.one_apply, ite_eq_right hbc] using h

/-- Sitewise pairing commutes with joining consecutive physical intervals.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem pairPhysicalConfig_joinCutInterval {d N j k l : ℕ}
    (x y : MPSPreparation.CutIntervalConfig d N j k)
    (z w : MPSPreparation.CutIntervalConfig d N k l) :
    pairPhysicalConfig (MPSPreparation.joinCutInterval j k l x z)
        (MPSPreparation.joinCutInterval j k l y w) =
      MPSPreparation.joinCutInterval j k l
        (pairPhysicalConfig x y) (pairPhysicalConfig z w) := by
  funext s
  by_cases h : s.val < k <;> simp [pairPhysicalConfig, MPSPreparation.joinCutInterval, h]

/-- The constructed operator interval tensors multiply exactly across
an intermediate cut, with both physical output and input configurations
joined in their chain order.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem minimalOperatorInterval_comp {d N : ℕ}
    (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) k))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k))
    {j k l : ℕ} (hjk : j ≤ k) (hkl : k ≤ l)
    (x y : MPSPreparation.CutIntervalConfig d N j k)
    (z w : MPSPreparation.CutIntervalConfig d N k l) :
    minimalOperatorInterval U B (hjk.trans hkl)
        (MPSPreparation.joinCutInterval j k l x z)
        (MPSPreparation.joinCutInterval j k l y w) =
      minimalOperatorInterval U B hjk x y * minimalOperatorInterval U B hkl z w := by
  change MPSPreparation.cutIntervalMatrix (operatorCoefficientTensor U) B (hjk.trans hkl)
      (pairPhysicalConfig (MPSPreparation.joinCutInterval j k l x z)
        (MPSPreparation.joinCutInterval j k l y w)) =
    MPSPreparation.cutIntervalMatrix (operatorCoefficientTensor U) B hjk (pairPhysicalConfig x y) *
      MPSPreparation.cutIntervalMatrix (operatorCoefficientTensor U) B hkl (pairPhysicalConfig z w)
  rw [pairPhysicalConfig_joinCutInterval, MPSPreparation.cutIntervalMatrix_comp]

open scoped Classical in
/-- A finite unitary admits one endpoint-compatible minimal cut-basis
family and one simultaneously chosen balanced metric family that make
every consecutive interval isometric. All factorization and interval
isometry identities are derived; no boundary metric, factorization, span,
or interval-isometry witness is assumed.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_simultaneous_balanced_interval_isometries_of_unitary {d N : ℕ}
    (hd : 0 < d) (hN : 0 < N)
    (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hU : U ∈ unitaryGroup (Fin N → Fin d) ℂ) :
    ∃ B : ∀ k, Module.Basis (Fin (MPSPreparation.cutCoefficientRank
        (operatorCoefficientTensor U) k))
        ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k),
      (∀ q, (B 0 q).val = 1) ∧
      (∀ q, (B N q).val = MPSPreparation.fullCutVector (operatorCoefficientTensor U)) ∧
      ∃ P : ∀ j : Fin (N + 1),
          Matrix (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) j.val))
            (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) j.val)) ℂ,
        (∀ j, P j ∈ prefixGramAffineHull
            (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B j.val aa bb q) ∧
          (P j).PosDef ∧ (dualGramMetric (P j)).PosDef ∧
          (∀ X ∈ prefixGramAffineHull
              (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B j.val aa bb q),
            trace (X * dualGramMetric (P j)) = 1) ∧
          trace ((dualGramMetric (P j))⁻¹ * (P j)⁻¹) =
            (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) j.val : ℂ) ^ 2) ∧
        ∀ (j k : Fin (N + 1)) (hjk : j.val ≤ k.val),
          (vectorizedWeightedInterval (minimalOperatorInterval U B hjk)
              (CFC.sqrt (P j)) (CFC.sqrt (dualGramMetric (P k))))ᴴ *
            vectorizedWeightedInterval (minimalOperatorInterval U B hjk)
              (CFC.sqrt (P j)) (CFC.sqrt (dualGramMetric (P k))) = 1 := by
  obtain ⟨B, hB0, hBN, P, hP⟩ :=
    exists_cutBases_simultaneous_balanced_metrics_of_unitary hd hN U hU
  refine ⟨B, hB0, hBN, P, hP, ?_⟩
  intro j k hjk
  exact minimalOperatorInterval_isometry_of_cut_metrics U B hjk (hP j).1
    (hP j).2.1.posSemidef (hP k).2.2.1.posSemidef (hP k).2.2.2.1

end MPUCircuit
