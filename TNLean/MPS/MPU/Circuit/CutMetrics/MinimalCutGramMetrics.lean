/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.VaryingBond.MinimalPhysicalCuts
import TNLean.MPS.MPU.Circuit.CutMetrics.PhysicalCutConfigurations
import TNLean.MPS.MPU.Circuit.CutMetrics.SimultaneousGramMetrics
import TNLean.MPS.Tensor.VaryingBond.MinimalCutRepresentationFactorization

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

open ManyBody (interval cutMatrix cutRank RegionConfig ComplConfig)

namespace MPUCircuit

/-- The operator prefix factor obtained by separating the paired
physical letters in the minimal cut-basis prefix matrix.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def minimalOperatorPrefixFactor {d N : ℕ}
    (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (cutRank (interval N 0 k) (operatorCoefficientTensor U)))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k)) (k : ℕ) :
    RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k) →
      Matrix (RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k))
        (Fin (cutRank (interval N 0 k) (operatorCoefficientTensor U))) ℂ :=
  fun x y q ↦ MPSPreparation.cutPrefixMatrix (operatorCoefficientTensor U) B k
    (pairPhysicalConfig x y) q

/-- The operator suffix factor obtained by separating the paired
physical letters in the minimal cut-basis suffix matrix.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def minimalOperatorSuffixFactor {d N : ℕ}
    (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (cutRank (interval N 0 k) (operatorCoefficientTensor U)))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k)) (k : ℕ) :
    ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k) →
      Matrix (Fin (cutRank (interval N 0 k) (operatorCoefficientTensor U)))
        (ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k)) ℂ :=
  fun x q y ↦ MPSPreparation.cutSuffixMatrix (operatorCoefficientTensor U) B k q
    (pairPhysicalConfig x y)

/-- The constructed operator factors reproduce the original finite operator
with its output and input configurations split at the physical cut.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem factorizedOperator_minimalOperatorFactors {d N : ℕ}
    (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (cutRank (interval N 0 k) (operatorCoefficientTensor U)))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k)) (k : ℕ) :
    MPUPrefixGram.factorizedOperator
      (minimalOperatorPrefixFactor U B k) (minimalOperatorSuffixFactor U B k) =
      Matrix.reindex (ManyBody.cutEquiv (fun _ : Fin N ↦ Fin d) (interval N 0 k)) (ManyBody.cutEquiv (fun _ : Fin N ↦ Fin d) (interval N 0 k)) U := by
  classical
  ext ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
  change (MPSPreparation.cutPrefixMatrix (operatorCoefficientTensor U) B k *
      MPSPreparation.cutSuffixMatrix (operatorCoefficientTensor U) B k)
      (pairPhysicalConfig x₁ y₁) (pairPhysicalConfig x₂ y₂) =
    U ((ManyBody.cutEquiv (fun _ : Fin N ↦ Fin d) (interval N 0 k)).symm (x₁, x₂))
      ((ManyBody.cutEquiv (fun _ : Fin N ↦ Fin d) (interval N 0 k)).symm (y₁, y₂))
  rw [← MPSPreparation.cutMatrix_eq_prefix_mul_suffix]
  change operatorCoefficientTensor U ((ManyBody.cutEquiv (fun _ : Fin N ↦ Fin (d * d)) (interval N 0 k)).symm
    (pairPhysicalConfig x₁ y₁, pairPhysicalConfig x₂ y₂)) = _
  rw [cutEquiv_symm_pairPhysicalConfig]
  exact operatorCoefficientTensor_apply U _ _

/-- The constructed factors of a finite unitary are globally isometric.
Their isometry follows from an exact reindexing of the original unitary.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem minimalOperatorFactors_isIsometry {d N : ℕ}
    (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hU : U ∈ unitaryGroup (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (cutRank (interval N 0 k) (operatorCoefficientTensor U)))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k)) (k : ℕ) :
    (MPUPrefixGram.factorizedOperator
      (minimalOperatorPrefixFactor U B k) (minimalOperatorSuffixFactor U B k)).IsIsometry := by
  classical
  rw [factorizedOperator_minimalOperatorFactors]
  exact ((Matrix.isUnitaryBetween_iff_mem_unitaryGroup U).mpr hU).1.reindex U
    (ManyBody.cutEquiv (fun _ : Fin N ↦ Fin d) (interval N 0 k)) (ManyBody.cutEquiv (fun _ : Fin N ↦ Fin d) (interval N 0 k))

/-- Both constructed bond-space spans follow from the physical cut rank
and the equivalence between paired configurations and separate output-input
configurations. No spanning hypothesis is supplied.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem minimalOperatorFactors_spans {d N : ℕ}
    (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (cutRank (interval N 0 k) (operatorCoefficientTensor U)))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k)) (k : ℕ) :
    Submodule.span ℂ (Set.range
      (fun xy : RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k) ×
          RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k) ↦
        fun q ↦ minimalOperatorPrefixFactor U B k xy.1 xy.2 q)) = ⊤ ∧
      Submodule.span ℂ (Set.range
        (fun xy : ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k) ×
            ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k) ↦
          fun q ↦ minimalOperatorSuffixFactor U B k xy.1 q xy.2)) = ⊤ := by
  have hF : Set.range
      (fun xy : RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k) ×
          RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k) ↦
        fun q ↦ minimalOperatorPrefixFactor U B k xy.1 xy.2 q) =
      Set.range (MPSPreparation.cutPrefixMatrix (operatorCoefficientTensor U) B k).row := by
    exact (physicalPairConfigEquiv {s : Fin N // s ∈ interval N 0 k} d).symm.surjective.range_comp _
  have hG : Set.range
      (fun xy : ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k) ×
          ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k) ↦
        fun q ↦ minimalOperatorSuffixFactor U B k xy.1 q xy.2) =
      Set.range (MPSPreparation.cutSuffixMatrix (operatorCoefficientTensor U) B k).col := by
    change Set.range ((MPSPreparation.cutSuffixMatrix (operatorCoefficientTensor U) B k).col ∘
        (physicalPairConfigEquiv {s : Fin N // s ∉ interval N 0 k} d).symm) = _
    exact (physicalPairConfigEquiv {s : Fin N // s ∉ interval N 0 k} d).symm.surjective.range_comp _
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
    (B : ∀ k, Module.Basis (Fin (cutRank (interval N 0 k) (operatorCoefficientTensor U)))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k)) :
    ∃ P : ∀ j : Fin (N + 1),
        Matrix (Fin (cutRank (interval N 0 j.val) (operatorCoefficientTensor U)))
          (Fin (cutRank (interval N 0 j.val) (operatorCoefficientTensor U))) ℂ,
      ∀ j, P j ∈ prefixGramAffineHull
          (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B j.val aa bb q) ∧
        (P j).PosDef ∧ (dualGramMetric (P j)).PosDef ∧
        (∀ X ∈ prefixGramAffineHull
            (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B j.val aa bb q),
          trace (X * dualGramMetric (P j)) = 1) ∧
        trace ((dualGramMetric (P j))⁻¹ * (P j)⁻¹) =
          (cutRank (interval N 0 j.val) (operatorCoefficientTensor U) : ℂ) ^ 2 := by
  classical
  have hψ := operatorCoefficientTensor_ne_zero hd U hU
  let : ∀ j : Fin (N + 1),
      Fintype (RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 j.val)) := fun _ ↦ inferInstance
  let : ∀ j : Fin (N + 1),
      Fintype (ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 j.val)) := fun _ ↦ inferInstance
  let : ∀ j : Fin (N + 1),
      Nonempty (RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 j.val)) := fun _ ↦
    ⟨fun _ ↦ ⟨0, hd⟩⟩
  let : ∀ j : Fin (N + 1),
      Nonempty (ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 j.val)) := fun _ ↦
    ⟨fun _ ↦ ⟨0, hd⟩⟩
  let : ∀ j : Fin (N + 1),
      DecidableEq (RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 j.val)) := fun _ ↦ inferInstance
  let : ∀ j : Fin (N + 1),
      DecidableEq (ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 j.val)) := fun _ ↦ inferInstance
  let : ∀ j : Fin (N + 1),
      Nonempty (Fin (cutRank (interval N 0 j.val) (operatorCoefficientTensor U)))
          := fun j ↦
    ⟨⟨0, (ManyBody.cutRank_pos (D := interval N 0 j.val) hψ)⟩⟩
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
    ∃ B : ∀ k, Module.Basis (Fin (cutRank (interval N 0 k) (operatorCoefficientTensor U)))
        ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k),
      (∀ q, (B 0 q).val = 1) ∧
      (∀ q, (B N q).val = MPSPreparation.fullCutVector (operatorCoefficientTensor U)) ∧
      ∃ P : ∀ j : Fin (N + 1),
          Matrix (Fin (cutRank (interval N 0 j.val) (operatorCoefficientTensor U)))
            (Fin (cutRank (interval N 0 j.val) (operatorCoefficientTensor U))) ℂ,
        ∀ j, P j ∈ prefixGramAffineHull
            (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B j.val aa bb q) ∧
          (P j).PosDef ∧ (dualGramMetric (P j)).PosDef ∧
          (∀ X ∈ prefixGramAffineHull
              (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B j.val aa bb q),
            trace (X * dualGramMetric (P j)) = 1) ∧
          trace ((dualGramMetric (P j))⁻¹ * (P j)⁻¹) =
            (cutRank (interval N 0 j.val) (operatorCoefficientTensor U) : ℂ) ^ 2 := by
  obtain ⟨B, hB0, hBN⟩ := MPSPreparation.exists_cutBasisFamily_with_endpoints
    (operatorCoefficientTensor U) (operatorCoefficientTensor_ne_zero hd U hU) hN
  obtain ⟨P, hP⟩ := exists_simultaneous_balanced_minimalOperator_metrics hd U hU B
  exact ⟨B, hB0, hBN, P, hP⟩

end MPUCircuit
