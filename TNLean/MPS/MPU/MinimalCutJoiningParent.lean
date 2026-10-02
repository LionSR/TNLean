/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixUnitaryBetween
import TNLean.MPS.MPU.EncodedUniformMergingCircuit
import TNLean.MPS.MPU.BalancedIntervalDilation
import TNLean.MPS.MPU.MinimalCutEndpointMetrics

/-!
# The actual weighted parent of a minimal interval merger

Two adjacent intervals are taken from one coherent minimal cut representation.
Their normalized joining contraction equals the weighted longer interval after
splitting its physical coordinates at the joining cut. The joining bond pair
is reset to its zero basis vector. This equality retains every complex phase.

The actual prefix Gram affine hulls and their balanced metrics determine the
parent Gram. Consequently the parent isometry required by an encoded merger
is derived from the finite unitary and its cut metrics. It is not supplied as
an independent hypothesis. The final existence theorem chooses one normalized
basis and metric family for all cuts simultaneously.

The physical circuit encodings and the recursive circuit assembly are separate
arguments. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

open Matrix
open scoped Matrix Kronecker ComplexOrder MatrixOrder

namespace MPUCircuit

/-- The computed normalized joining contraction is the weighted product interval,
with the joining bond pair reset to the designated zero basis vector.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem normalizedJoiningParent_balancedIntervalChildren
    {r : ℕ} {o i o' i' l n : Type*}
    [Fintype o] [Fintype o'] [Fintype l] [Fintype n]
    [DecidableEq o] [DecidableEq o'] [DecidableEq l] [DecidableEq n]
    (hr : 0 < r) (A : o → i → Matrix l (Fin r) ℂ)
    (B : o' → i' → Matrix (Fin r) n ℂ)
    (L : Matrix l l ℂ) (R : Matrix n n ℂ)
    {P : Matrix (Fin r) (Fin r) ℂ} (hP : P.PosDef) :
    normalizedJoiningParent hr P (balancedIntervalChildren A B L R P) =
      basisResetOutput
        (vectorizedWeightedInterval
          (fun (a : o × o') (b : i × i') ↦ A a.1 b.1 * B a.2 b.2) L R)
        (⟨0, hr⟩, ⟨0, hr⟩) := by
  let : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  rw [normalizedJoiningParent]
  change (r : ℂ) • (liftedNormalizedBondReset P (⟨0, hr⟩, ⟨0, hr⟩) *
    balancedIntervalChildren A B L R P) = _
  rw [balancedIntervalChildren, liftedNormalizedBondReset_mul_children,
    contractedWeightedIntervals_balanced A B L R hP]
  have hc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  ext p b
  simp [basisResetOutput, Matrix.smul_apply, Fintype.card_fin, ← mul_assoc, hc]

/-- Splitting a physical interval at an intermediate cut is a bijection.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def cutIntervalSplitEquiv (d N j m k : ℕ) (hjm : j ≤ m) (hmk : m ≤ k) :
    MPSPreparation.CutIntervalConfig d N j k ≃
      (MPSPreparation.CutIntervalConfig d N j m ×
        MPSPreparation.CutIntervalConfig d N m k) where
  toFun w := (fun s ↦ w ⟨s.1, s.2.1, s.2.2.trans_le hmk⟩,
    fun s ↦ w ⟨s.1, hjm.trans s.2.1, s.2.2⟩)
  invFun w := MPSPreparation.joinCutInterval j m k w.1 w.2
  left_inv w := by
    funext s
    change (if _h : s.val < m then w s else w s) = w s
    split_ifs <;> rfl
  right_inv w := by
    apply Prod.ext
    · funext s
      simp [MPSPreparation.joinCutInterval, s.2.2]
    · funext s
      simp [MPSPreparation.joinCutInterval, Nat.not_lt_of_ge s.2.1]

/-- The product of adjacent minimal intervals is the actual longer weighted
interval with its physical coordinates split at the joining cut.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem weightedMinimalOperatorInterval_comp_eq_reindex {d N : ℕ}
    (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) k))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k))
    {j m k : ℕ} (hjm : j ≤ m) (hmk : m ≤ k)
    (L : Matrix (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) j))
      (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) j)) ℂ)
    (R : Matrix (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) k))
      (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) k)) ℂ) :
    vectorizedWeightedInterval
      (fun (a : MPSPreparation.CutIntervalConfig d N j m ×
            MPSPreparation.CutIntervalConfig d N m k)
          (b : MPSPreparation.CutIntervalConfig d N j m ×
            MPSPreparation.CutIntervalConfig d N m k) ↦
        minimalOperatorInterval U B hjm a.1 b.1 *
          minimalOperatorInterval U B hmk a.2 b.2) L R =
      reindexLinearEquiv ℂ ℂ
        (Equiv.prodCongr (cutIntervalSplitEquiv d N j m k hjm hmk) (Equiv.refl _))
        (cutIntervalSplitEquiv d N j m k hjm hmk)
        (vectorizedWeightedInterval (minimalOperatorInterval U B (hjm.trans hmk)) L R) := by
  classical
  ext ⟨⟨x, z⟩, β, α⟩ ⟨y, w⟩
  change vec (L * (minimalOperatorInterval U B hjm x y *
      minimalOperatorInterval U B hmk z w) * R) (β, α) =
    vec (L * minimalOperatorInterval U B (hjm.trans hmk)
      (MPSPreparation.joinCutInterval j m k x z)
      (MPSPreparation.joinCutInterval j m k y w) * R) (β, α)
  rw [minimalOperatorInterval_comp]

open scoped Classical in
/-- The actual adjacent minimal intervals contract to the actual weighted parent,
with split physical coordinates and the joining pair reset to zero.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem normalizedJoiningParent_minimalOperatorIntervals {d N : ℕ}
    (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) k))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k))
    {j m k : ℕ} (hjm : j ≤ m) (hmk : m ≤ k)
    (hr : 0 < MPSPreparation.cutRank (operatorCoefficientTensor U) m)
    (L : Matrix (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) j))
      (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) j)) ℂ)
    (R : Matrix (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) k))
      (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) k)) ℂ)
    {P : Matrix (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) m))
      (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) m)) ℂ}
    (hP : P.PosDef) :
    normalizedJoiningParent hr P
      (balancedIntervalChildren (minimalOperatorInterval U B hjm)
        (minimalOperatorInterval U B hmk) L R P) =
      basisResetOutput
        (reindexLinearEquiv ℂ ℂ
          (Equiv.prodCongr (cutIntervalSplitEquiv d N j m k hjm hmk) (Equiv.refl _))
          (cutIntervalSplitEquiv d N j m k hjm hmk)
          (vectorizedWeightedInterval (minimalOperatorInterval U B (hjm.trans hmk)) L R))
        (⟨0, hr⟩, ⟨0, hr⟩) := by
  classical
  rw [normalizedJoiningParent_balancedIntervalChildren hr _ _ L R hP,
    weightedMinimalOperatorInterval_comp_eq_reindex U B hjm hmk L R]

open scoped Classical in
/-- The actual cut metrics make the computed normalized parent an isometry.
Its Gram is derived from the actual longer interval, rather than assumed as
an induction hypothesis.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem normalizedJoiningParent_minimalOperatorIntervals_isIsometry {d N : ℕ}
    (hd : 0 < d) (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hU : U ∈ unitaryGroup (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) k))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k))
    {j m k : ℕ} (hjm : j ≤ m) (hmk : m ≤ k)
    {Pj : Matrix (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) j))
      (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) j)) ℂ}
    {Pm : Matrix (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) m))
      (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) m)) ℂ}
    {Pk : Matrix (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) k))
      (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) k)) ℂ}
    (hPj : Pj ∈ prefixGramAffineHull
      (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B j aa bb q))
    (hPjpos : Pj.PosDef) (hPmpos : Pm.PosDef) (hPkpos : Pk.PosDef)
    (hnorm : ∀ X ∈ prefixGramAffineHull
      (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B k aa bb q),
      trace (X * dualGramMetric Pk) = 1) :
    (normalizedJoiningParent
      (MPSPreparation.cutRank_pos _ (operatorCoefficientTensor_ne_zero hd U hU) m)
      Pm (balancedIntervalChildren (minimalOperatorInterval U B hjm)
        (minimalOperatorInterval U B hmk) (CFC.sqrt Pj)
        (CFC.sqrt (dualGramMetric Pk)) Pm)).IsIsometry := by
  classical
  let : Nonempty (Fin (MPSPreparation.cutRank (operatorCoefficientTensor U) k)) :=
    ⟨⟨0, MPSPreparation.cutRank_pos _ (operatorCoefficientTensor_ne_zero hd U hU) k⟩⟩
  have hparent : (vectorizedWeightedInterval (minimalOperatorInterval U B (hjm.trans hmk))
      (CFC.sqrt Pj) (CFC.sqrt (dualGramMetric Pk))).IsIsometry :=
    minimalOperatorInterval_isometry_of_cut_metrics U B (hjm.trans hmk)
      hPj hPjpos.posSemidef (dualGramMetric_posDef hPkpos).posSemidef hnorm
  rw [normalizedJoiningParent_minimalOperatorIntervals U B hjm hmk _ _ _ hPmpos]
  change (basisResetOutput _ _)ᴴ * basisResetOutput _ _ = 1
  rw [basisResetOutput_gram]
  exact hparent.reindex _
    (Equiv.prodCongr (cutIntervalSplitEquiv d N j m k hjm hmk) (Equiv.refl _))
    (cutIntervalSplitEquiv d N j m k hjm hmk)

open scoped Classical in
/-- A finite unitary admits one coherent minimal basis and balanced metric family
whose actual joining contractions are isometries at every intermediate cut.
The endpoint metrics and bases are normalized, and no interval Gram or joining
isometry is supplied as a hypothesis.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_normalized_joining_parent_isometries_of_unitary {d N : ℕ}
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
        (∀ j, P j ∈ prefixGramAffineHull
            (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B j.val aa bb q) ∧
          (P j).PosDef ∧
          ∀ X ∈ prefixGramAffineHull
            (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B j.val aa bb q),
            trace (X * dualGramMetric (P j)) = 1) ∧
        P 0 = 1 ∧ P (Fin.last N) = 1 ∧
        ∀ (j m k : Fin (N + 1)) (hjm : j.val ≤ m.val) (hmk : m.val ≤ k.val),
          (normalizedJoiningParent
            (MPSPreparation.cutRank_pos _ (operatorCoefficientTensor_ne_zero hd U hU) m.val)
            (P m) (balancedIntervalChildren (minimalOperatorInterval U B hjm)
              (minimalOperatorInterval U B hmk) (CFC.sqrt (P j))
              (CFC.sqrt (dualGramMetric (P k))) (P m))).IsIsometry := by
  classical
  obtain ⟨B, hB0, hBN, P, hP, _, hP0, hPN, _⟩ :=
    exists_normalized_minimalInterval_family_of_unitary hd hN U hU
  refine ⟨B, hB0, hBN, P, ?_, hP0, hPN, ?_⟩
  · intro j
    exact ⟨(hP j).1, (hP j).2.1, (hP j).2.2.2.1⟩
  · intro j m k hjm hmk
    exact normalizedJoiningParent_minimalOperatorIntervals_isIsometry hd U hU B hjm hmk
      (hP j).1 (hP j).2.1 (hP m).2.1 (hP k).2.1 (hP k).2.2.2.1

end MPUCircuit
