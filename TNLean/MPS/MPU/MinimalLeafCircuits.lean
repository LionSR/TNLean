/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.MinimalCutEndpointMetrics
import TNLean.MPS.MPU.EndpointBondEncoding
import TNLean.MPS.MPU.LeafIntervalCircuit

/-!
# Exact clean leaf circuits from a finite unitary

The selected weighted one-site intervals are reindexed to the physical
alphabet and their two endpoint-aware bond registers. The circuit existence
is then derived from the unitary and its physical cut-rank bound, with the
same balanced metrics and interval isometries at every cut. No leaf
isometry or endpoint rank is supplied as a hypothesis.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open Matrix MPSTensor MPSPreparation QuantumCircuit
open scoped Matrix ComplexOrder MatrixOrder

namespace MPUCircuit

/-- The physical configurations on a one-site interval are exactly the local physical alphabet.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def singleSiteIntervalConfigEquiv (d N : ℕ) (i : Fin N) :
    Fin d ≃ CutIntervalConfig d N i.val (i.val + 1) where
  toFun a := fun _ ↦ a
  invFun x := x ⟨i, by omega⟩
  left_inv _ := rfl
  right_inv x := by
    funext s
    apply congrArg x
    apply Subtype.ext
    apply Fin.ext
    change i.val = s.val.val
    have hs := s.2
    omega

/-- The selected weighted one-site interval, reindexed to one physical output, its right and left
bond labels, and one physical input.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def minimalLeafInterval {d N : ℕ}
    (U : Matrix (Cfg d N) (Cfg d N) ℂ)
    (B : ∀ k, Module.Basis (Fin (cutCoefficientRank (operatorCoefficientTensor U) k))
      ℂ (cutColumnSpace (operatorCoefficientTensor U) k))
    (P : ∀ j : Fin (N + 1), Matrix (Fin (cutCoefficientRank (operatorCoefficientTensor U) j.val))
      (Fin (cutCoefficientRank (operatorCoefficientTensor U) j.val)) ℂ) (i : Fin N) :
    Matrix (Fin d × (Fin (cutCoefficientRank (operatorCoefficientTensor U) (i.val + 1)) ×
      Fin (cutCoefficientRank (operatorCoefficientTensor U) i.val))) (Fin d) ℂ :=
  Matrix.reindex
    (Equiv.prodCongr (singleSiteIntervalConfigEquiv d N i).symm (Equiv.refl _))
    (singleSiteIntervalConfigEquiv d N i).symm
    (vectorizedWeightedInterval (minimalOperatorInterval U B (Nat.le_succ i.val))
      (CFC.sqrt (P i.castSucc)) (CFC.sqrt (dualGramMetric (P i.succ))))

/-- Reindexing the physical coordinates of a one-site interval preserves its isometry identity.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem minimalLeafInterval_isometry_of_interval_isometry {d N : ℕ}
    (U : Matrix (Cfg d N) (Cfg d N) ℂ)
    (B : ∀ k, Module.Basis (Fin (cutCoefficientRank (operatorCoefficientTensor U) k))
      ℂ (cutColumnSpace (operatorCoefficientTensor U) k))
    (P : ∀ j : Fin (N + 1), Matrix (Fin (cutCoefficientRank (operatorCoefficientTensor U) j.val))
      (Fin (cutCoefficientRank (operatorCoefficientTensor U) j.val)) ℂ) (i : Fin N)
    (hV : (vectorizedWeightedInterval (minimalOperatorInterval U B (Nat.le_succ i.val))
      (CFC.sqrt (P i.castSucc)) (CFC.sqrt (dualGramMetric (P i.succ)))).IsIsometry) :
    (minimalLeafInterval U B P i).IsIsometry := by
  unfold minimalLeafInterval
  exact hV.reindex _
    (Equiv.prodCongr (singleSiteIntervalConfigEquiv d N i).symm (Equiv.refl _))
    (singleSiteIntervalConfigEquiv d N i).symm


open scoped Classical in
/-- A finite unitary with bounded physical cut ranks admits one normalized balanced interval
family and actual exact clean circuits for all leaves. The endpoint encodings have width zero, all
interval isometries are derived, and the full interval retains the exact complex phase of the
original unitary.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem exists_normalized_minimalInterval_family_with_leaf_circuits_of_unitary
    {d D N : ℕ} [NeZero d]
    (hd : 2 ≤ d) (hN : 0 < N)
    (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hU : U ∈ unitaryGroup (Fin N → Fin d) ℂ)
    (hbound : ∀ j : Fin (N + 1), cutCoefficientRank (operatorCoefficientTensor U) j.val ≤ D) :
    ∃ B : ∀ k, Module.Basis (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) k))
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
        (∀ (j k : Fin (N + 1)) (hjk : j.val ≤ k.val),
          (vectorizedWeightedInterval (minimalOperatorInterval U B hjk)
              (CFC.sqrt (P j)) (CFC.sqrt (dualGramMetric (P k))))ᴴ *
            vectorizedWeightedInterval (minimalOperatorInterval U B hjk)
              (CFC.sqrt (P j)) (CFC.sqrt (dualGramMetric (P k))) = 1) ∧
        P 0 = 1 ∧ P (Fin.last N) = 1 ∧
        (∀ (α : Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) 0))
          (β : Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) N)),
          (vectorizedWeightedInterval (minimalOperatorInterval U B (Nat.zero_le N))
            (CFC.sqrt (P 0)) (CFC.sqrt (dualGramMetric (P (Fin.last N))))).submatrix
            (fun x ↦ (fullCutIntervalConfigEquiv d N x, (β, α)))
            (fullCutIntervalConfigEquiv d N) = U) ∧
        ∀ i : Fin N,
          ∃ Z : Matrix
              (Cfg d (1 + (cutBondRegisterWidth d D N i.succ +
                cutBondRegisterWidth d D N i.castSucc)))
              (Cfg d (1 + (cutBondRegisterWidth d D N i.succ +
                cutBondRegisterWidth d D N i.castSucc))) ℂ,
          ∃ C : Matrix
              (Cfg d ((1 + (cutBondRegisterWidth d D N i.succ +
                cutBondRegisterWidth d D N i.castSucc)) + 1))
              (Cfg d ((1 + (cutBondRegisterWidth d D N i.succ +
                cutBondRegisterWidth d D N i.castSucc)) + 1)) ℂ,
            Z ∈ unitary (Matrix
              (Cfg d (1 + (cutBondRegisterWidth d D N i.succ +
                cutBondRegisterWidth d D N i.castSucc)))
              (Cfg d (1 + (cutBondRegisterWidth d D N i.succ +
                cutBondRegisterWidth d D N i.castSucc))) ℂ) ∧
            Z * initializedBasisMatrix (leafInputEmbedding (d := d)
                (qρ := cutBondRegisterWidth d D N i.succ)
                (qσ := cutBondRegisterWidth d D N i.castSucc)) =
              initializedBasisMatrix
                (leafOutputEmbedding
                  (ρ := Fin (cutCoefficientRank (operatorCoefficientTensor U) (i.val + 1)))
                  (σ := Fin (cutCoefficientRank (operatorCoefficientTensor U) i.val))
                  (minimalCutBondRegisterEncoding hd U hU hbound i.succ)
                  (minimalCutBondRegisterEncoding hd U hU hbound i.castSucc)) *
                minimalLeafInterval U B P i ∧
            IsPairProduct d ((1 + (cutBondRegisterWidth d D N i.succ +
                cutBondRegisterWidth d D N i.castSucc)) + 1)
              (38 * (d ^ ((1 + (cutBondRegisterWidth d D N i.succ +
                cutBondRegisterWidth d D N i.castSucc)) + 1)) ^ 6) C ∧
            IsCleanImplementation
              (initializedBasisMatrix (zeroWorkspaceEmbedding (d := d)
                (n := 1 + (cutBondRegisterWidth d D N i.succ +
                  cutBondRegisterWidth d D N i.castSucc)) (a := 1))) C Z := by
  obtain ⟨B, hB0, hBN, P, hP, hIntervals, h0, hlast, hfull⟩ :=
    exists_normalized_minimalInterval_family_of_unitary (by omega : 0 < d) hN U hU
  refine ⟨B, hB0, hBN, P, hP, hIntervals, h0, hlast, hfull, ?_⟩
  intro i
  have hV : (minimalLeafInterval U B P i).IsIsometry :=
    minimalLeafInterval_isometry_of_interval_isometry U B P i
      (hIntervals i.castSucc i.succ (Nat.le_succ i.val))
  exact exists_exact_clean_leaf_circuit hd
    (minimalCutBondRegisterEncoding hd U hU hbound i.succ)
    (minimalCutBondRegisterEncoding hd U hU hbound i.castSucc) hV

end MPUCircuit
