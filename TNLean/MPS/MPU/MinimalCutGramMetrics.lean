/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.MinimalPhysicalCuts
import TNLean.MPS.MPU.PhysicalCutConfigurations
import TNLean.MPS.MPU.SimultaneousGramMetrics
import TNLean.MPS.Preparation.MinimalCutRepresentationFactorization

/-!
# Balanced cut metrics of a finite unitary

The physical coefficient tensor of a finite unitary admits minimal cut bases.
Separating the paired physical letters gives explicit operator prefix and
suffix factors. Their product is an exact reindexing of the original unitary,
and their physical rows and columns span the minimal bond space. Consequently
the simultaneous determinant-balancing theorem supplies all cut metrics.

The final theorem assumes only unitarity, positive physical dimension, and
positive length. It chooses endpoint-compatible bases, so a bound on the
physical cut ranks yields the exact minimal open-boundary representation
using those same bases. No efficient classical computation of these choices
is asserted.

Source: the finite nonuniform operator definition in arXiv:2508.08160v2,
`references/2508.08160/main.tex`, lines 1337--1402, and Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

open Matrix
open scoped Matrix ComplexOrder

namespace MPUCircuit

/-- The operator prefix factor obtained by separating the paired
physical letters in the minimal cut-basis prefix matrix.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def minimalOperatorPrefixFactor {d N : ℕ}
    (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) k))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k)) (k : ℕ) :
    MPSPreparation.CutPrefixConfig d N k →
      Matrix (MPSPreparation.CutPrefixConfig d N k)
        (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) k)) ℂ :=
  fun x y q ↦ MPSPreparation.cutPrefixMatrix (operatorCoefficientTensor U) B k
    (pairPhysicalConfig x y) q

/-- The operator suffix factor obtained by separating the paired
physical letters in the minimal cut-basis suffix matrix.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def minimalOperatorSuffixFactor {d N : ℕ}
    (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) k))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k)) (k : ℕ) :
    MPSPreparation.CutSuffixConfig d N k →
      Matrix (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) k))
        (MPSPreparation.CutSuffixConfig d N k) ℂ :=
  fun x q y ↦ MPSPreparation.cutSuffixMatrix (operatorCoefficientTensor U) B k q
    (pairPhysicalConfig x y)

/-- The constructed operator factors reproduce the original finite operator
with its output and input configurations split at the physical cut.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem factorizedOperator_minimalOperatorFactors {d N : ℕ}
    (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) k))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k)) (k : ℕ) :
    MPUPrefixGram.factorizedOperator
      (minimalOperatorPrefixFactor U B k) (minimalOperatorSuffixFactor U B k) =
      Matrix.reindex (physicalCutConfigEquiv d N k) (physicalCutConfigEquiv d N k) U := by
  classical
  ext ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
  change (MPSPreparation.cutPrefixMatrix (operatorCoefficientTensor U) B k *
      MPSPreparation.cutSuffixMatrix (operatorCoefficientTensor U) B k)
      (pairPhysicalConfig x₁ y₁) (pairPhysicalConfig x₂ y₂) =
    U ((physicalCutConfigEquiv d N k).symm (x₁, x₂))
      ((physicalCutConfigEquiv d N k).symm (y₁, y₂))
  rw [← MPSPreparation.cutCoefficientMatrix_eq_prefix_mul_suffix]
  change operatorCoefficientTensor U ((physicalCutConfigEquiv (d * d) N k).symm
    (pairPhysicalConfig x₁ y₁, pairPhysicalConfig x₂ y₂)) = _
  rw [physicalCutConfigEquiv_pair]
  exact operatorCoefficientTensor_apply U _ _

/-- The constructed factors of a finite unitary are globally isometric.
Their isometry follows from an exact reindexing of the original unitary.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem minimalOperatorFactors_isIsometry {d N : ℕ}
    (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hU : U ∈ unitaryGroup (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) k))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k)) (k : ℕ) :
    (MPUPrefixGram.factorizedOperator
      (minimalOperatorPrefixFactor U B k) (minimalOperatorSuffixFactor U B k)).IsIsometry := by
  classical
  rw [factorizedOperator_minimalOperatorFactors]
  exact ((Matrix.isUnitaryBetween_iff_mem_unitaryGroup U).mpr hU).1.reindex U
    (physicalCutConfigEquiv d N k) (physicalCutConfigEquiv d N k)

/-- Both constructed bond-space spans follow from the physical cut rank
and the equivalence between paired configurations and separate output-input
configurations. No spanning hypothesis is supplied.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem minimalOperatorFactors_spans {d N : ℕ}
    (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) k))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k)) (k : ℕ) :
    Submodule.span ℂ (Set.range
      (fun xy : MPSPreparation.CutPrefixConfig d N k ×
          MPSPreparation.CutPrefixConfig d N k ↦
        fun q ↦ minimalOperatorPrefixFactor U B k xy.1 xy.2 q)) = ⊤ ∧
      Submodule.span ℂ (Set.range
        (fun xy : MPSPreparation.CutSuffixConfig d N k ×
            MPSPreparation.CutSuffixConfig d N k ↦
          fun q ↦ minimalOperatorSuffixFactor U B k xy.1 q xy.2)) = ⊤ := by
  have hF : Set.range
      (fun xy : MPSPreparation.CutPrefixConfig d N k ×
          MPSPreparation.CutPrefixConfig d N k ↦
        fun q ↦ minimalOperatorPrefixFactor U B k xy.1 xy.2 q) =
      Set.range (MPSPreparation.cutPrefixMatrix (operatorCoefficientTensor U) B k).row := by
    exact (physicalPairConfigEquiv {s : Fin N // s.val < k} d).symm.surjective.range_comp _
  have hG : Set.range
      (fun xy : MPSPreparation.CutSuffixConfig d N k ×
          MPSPreparation.CutSuffixConfig d N k ↦
        fun q ↦ minimalOperatorSuffixFactor U B k xy.1 q xy.2) =
      Set.range (MPSPreparation.cutSuffixMatrix (operatorCoefficientTensor U) B k).col := by
    change Set.range ((MPSPreparation.cutSuffixMatrix (operatorCoefficientTensor U) B k).col ∘
        (physicalPairConfigEquiv {s : Fin N // k ≤ s.val} d).symm) = _
    exact (physicalPairConfigEquiv {s : Fin N // k ≤ s.val} d).symm.surjective.range_comp _
  rw [hF, hG]
  exact MPSPreparation.cutPrefixMatrix_rows_and_cutSuffixMatrix_cols_span
    (operatorCoefficientTensor U) B k

/-- For any cut-basis family of an actual finite unitary, one can choose
balanced positive metrics simultaneously at every cut. Global factorization
isometry and both physical spans are derived from the unitary and the bases.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_simultaneous_balanced_minimalOperator_metrics {d N : ℕ}
    (hd : 0 < d) (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hU : U ∈ unitaryGroup (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) k))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k)) :
    ∃ P : ∀ j : Fin (N + 1),
        Matrix (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) j.val))
          (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) j.val)) ℂ,
      ∀ j, P j ∈ prefixGramAffineHull
          (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B j.val aa bb q) ∧
        (P j).PosDef ∧ (dualGramMetric (P j)).PosDef ∧
        (∀ X ∈ prefixGramAffineHull
            (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B j.val aa bb q),
          trace (X * dualGramMetric (P j)) = 1) ∧
        trace ((dualGramMetric (P j))⁻¹ * (P j)⁻¹) =
          (MPSPreparation.cutRank (operatorCoefficientTensor U) j.val : ℂ) ^ 2 := by
  classical
  have hψ := operatorCoefficientTensor_ne_zero hd U hU
  let : ∀ j : Fin (N + 1),
      Fintype (MPSPreparation.CutPrefixConfig d N j.val) := fun _ ↦ inferInstance
  let : ∀ j : Fin (N + 1),
      Fintype (MPSPreparation.CutSuffixConfig d N j.val) := fun _ ↦ inferInstance
  let : ∀ j : Fin (N + 1),
      Nonempty (MPSPreparation.CutPrefixConfig d N j.val) := fun _ ↦
    ⟨fun _ ↦ ⟨0, hd⟩⟩
  let : ∀ j : Fin (N + 1),
      Nonempty (MPSPreparation.CutSuffixConfig d N j.val) := fun _ ↦
    ⟨fun _ ↦ ⟨0, hd⟩⟩
  let : ∀ j : Fin (N + 1),
      DecidableEq (MPSPreparation.CutPrefixConfig d N j.val) := fun _ ↦ inferInstance
  let : ∀ j : Fin (N + 1),
      DecidableEq (MPSPreparation.CutSuffixConfig d N j.val) := fun _ ↦ inferInstance
  let : ∀ j : Fin (N + 1),
      Nonempty (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) j.val)) := fun j ↦
    ⟨⟨0, MPSPreparation.cutRank_pos (operatorCoefficientTensor U) hψ j.val⟩⟩
  exact exists_simultaneous_balanced_prefix_metrics_of_factorizedOperator_isometries
    (fun j : Fin (N + 1) ↦ minimalOperatorPrefixFactor U B j.val)
    (fun j : Fin (N + 1) ↦ minimalOperatorSuffixFactor U B j.val)
    (fun j ↦ minimalOperatorFactors_isIsometry U hU B j.val)
    (fun j ↦ (minimalOperatorFactors_spans U B j.val).1)
    (fun j ↦ (minimalOperatorFactors_spans U B j.val).2)

/-- A finite unitary on a positive physical alphabet and a positive-length
chain admits endpoint-compatible minimal cut bases and simultaneously chosen
balanced metrics. No factorization, spanning, isometry, or boundary metric
witness is supplied. For any bound on the cut ranks, these same bases give
the exact minimal open-boundary chain of `minimalCutChain`.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_cutBases_simultaneous_balanced_metrics_of_unitary {d N : ℕ}
    (hd : 0 < d) (hN : 0 < N)
    (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hU : U ∈ unitaryGroup (Fin N → Fin d) ℂ) :
    ∃ B : ∀ k, Module.Basis (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) k))
        ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k),
      (∀ q, (B 0 q).val = 1) ∧
      (∀ q, (B N q).val = MPSPreparation.fullCutVector (operatorCoefficientTensor U)) ∧
      ∃ P : ∀ j : Fin (N + 1),
          Matrix (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) j.val))
            (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) j.val)) ℂ,
        ∀ j, P j ∈ prefixGramAffineHull
            (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B j.val aa bb q) ∧
          (P j).PosDef ∧ (dualGramMetric (P j)).PosDef ∧
          (∀ X ∈ prefixGramAffineHull
              (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B j.val aa bb q),
            trace (X * dualGramMetric (P j)) = 1) ∧
          trace ((dualGramMetric (P j))⁻¹ * (P j)⁻¹) =
            (MPSPreparation.cutRank (operatorCoefficientTensor U) j.val : ℂ) ^ 2 := by
  obtain ⟨B, hB0, hBN⟩ := MPSPreparation.exists_cutBasisFamily_with_endpoints
    (operatorCoefficientTensor U) (operatorCoefficientTensor_ne_zero hd U hU) hN
  obtain ⟨P, hP⟩ := exists_simultaneous_balanced_minimalOperator_metrics hd U hU B
  exact ⟨B, hB0, hBN, P, hP⟩

end MPUCircuit
