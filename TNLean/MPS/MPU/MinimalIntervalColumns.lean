/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SupportedChildColumns
import TNLean.MPS.MPU.IntervalColumnEncoding

/-!
# Actual minimal interval columns on the full logical register

The interval invariant uses the weighted interval selected from the given
finite unitary, the actual cut-label encodings, and the physical interval
input. Every interval auxiliary is initialized at the input; every strictly
interior auxiliary is zero at the output. All outside logical configurations
are retained by an identity factor.

The two child invariants and their disjoint supports imply the joint child
columns. No joint column identity, local child matrix, or parent Gram identity
is supplied as a hypothesis.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open Matrix MPSTensor MPSPreparation QuantumCircuit
open scoped Kronecker Matrix ComplexOrder MatrixOrder

namespace MPUCircuit

/-- The physical input and an arbitrary outside configuration, with all interval auxiliaries zero.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def minimalIntervalInputEmbedding {d D N : ℕ} [NeZero d] (j k : ℕ) :
    (CutIntervalConfig d N j k ×
      OutsidePlacedConfig d (intervalPacketSites d D N j k)) ↪
        Cfg d (logicalSiteCount d D N) :=
  placedBasisEmbedding (intervalPacketSites d D N j k)
    (intervalInputEmbedding j k) (Function.Embedding.refl _)

/-- The actual physical output and cut labels, together with the unchanged arbitrary outside
configuration.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def minimalIntervalOutputEmbedding {d D N : ℕ} [NeZero d]
    (hd : 2 ≤ d) (U : Matrix (Cfg d N) (Cfg d N) ℂ)
    (hU : U ∈ unitaryGroup (Cfg d N) ℂ)
    (hbound : ∀ j : Fin (N + 1), cutCoefficientRank (operatorCoefficientTensor U) j.val ≤ D)
    (j k : Fin (N + 1)) :
    ((CutIntervalConfig d N j.val k.val ×
      (Fin (cutCoefficientRank (operatorCoefficientTensor U) k.val) ×
        Fin (cutCoefficientRank (operatorCoefficientTensor U) j.val))) ×
      OutsidePlacedConfig d (intervalPacketSites d D N j.val k.val)) ↪
        Cfg d (logicalSiteCount d D N) :=
  placedBasisEmbedding (intervalPacketSites d D N j.val k.val)
    (intervalOutputEmbedding j k (minimalCutBondRegisterEncoding hd U hU hbound k)
      (minimalCutBondRegisterEncoding hd U hU hbound j)) (Function.Embedding.refl _)

open scoped Classical in
/-- The initialized columns of the logical operator are the actual weighted interval, with
identity action on every outside logical configuration.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def IsMinimalIntervalColumnImplementation {d D N : ℕ} [NeZero d]
    (hd : 2 ≤ d) (U : Matrix (Cfg d N) (Cfg d N) ℂ)
    (hU : U ∈ unitaryGroup (Cfg d N) ℂ)
    (hbound : ∀ j : Fin (N + 1), cutCoefficientRank (operatorCoefficientTensor U) j.val ≤ D)
    (B : ∀ k, Module.Basis (Fin (cutCoefficientRank (operatorCoefficientTensor U) k))
      ℂ (cutColumnSpace (operatorCoefficientTensor U) k))
    (P : ∀ j : Fin (N + 1), Matrix (Fin (cutCoefficientRank (operatorCoefficientTensor U) j.val))
      (Fin (cutCoefficientRank (operatorCoefficientTensor U) j.val)) ℂ)
    (j k : Fin (N + 1)) (hjk : j.val ≤ k.val)
    (X : Matrix (Cfg d (logicalSiteCount d D N)) (Cfg d (logicalSiteCount d D N)) ℂ) : Prop :=
  X * initializedBasisMatrix (minimalIntervalInputEmbedding (D := D) j.val k.val) =
    initializedBasisMatrix (minimalIntervalOutputEmbedding hd U hU hbound j k) *
      (vectorizedWeightedInterval (minimalOperatorInterval U B hjk)
        (CFC.sqrt (P j)) (CFC.sqrt (dualGramMetric (P k))) ⊗ₖ
          (1 : Matrix (OutsidePlacedConfig d (intervalPacketSites d D N j.val k.val))
            (OutsidePlacedConfig d (intervalPacketSites d D N j.val k.val)) ℂ))

open scoped Classical in
/-- The two actual interval column identities and disjoint child supports determine their joint
columns, including arbitrary outside configurations.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem minimalIntervalChildColumns_of_supported_individual {d D N : ℕ} [NeZero d]
    (hd : 2 ≤ d) (U : Matrix (Cfg d N) (Cfg d N) ℂ)
    (hU : U ∈ unitaryGroup (Cfg d N) ℂ)
    (hbound : ∀ j : Fin (N + 1), cutCoefficientRank (operatorCoefficientTensor U) j.val ≤ D)
    (B : ∀ k, Module.Basis (Fin (cutCoefficientRank (operatorCoefficientTensor U) k))
      ℂ (cutColumnSpace (operatorCoefficientTensor U) k))
    (P : ∀ j : Fin (N + 1), Matrix (Fin (cutCoefficientRank (operatorCoefficientTensor U) j.val))
      (Fin (cutCoefficientRank (operatorCoefficientTensor U) j.val)) ℂ)
    (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val)
    (X Y : Matrix (Cfg d (logicalSiteCount d D N)) (Cfg d (logicalSiteCount d D N)) ℂ)
    (hSX : X ∈ supportedOperators d (intervalConsecutiveSupport d D N j.val m.val))
    (hSY : Y ∈ supportedOperators d (intervalConsecutiveSupport d D N m.val k.val))
    (hX : IsMinimalIntervalColumnImplementation hd U hU hbound B P j m (Nat.le_of_lt hjm) X)
    (hY : IsMinimalIntervalColumnImplementation hd U hU hbound B P m k (Nat.le_of_lt hmk) Y) :
    (X * Y) * initializedBasisMatrix
      (jointPlacedBasisEmbedding (intervalPacketSites d D N j.val m.val)
        (intervalPacketSites d D N m.val k.val)
          (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk)
        (intervalInputEmbedding j.val m.val) (intervalInputEmbedding m.val k.val)
        (Function.Embedding.refl _)) =
      initializedBasisMatrix
        (jointPlacedBasisEmbedding (intervalPacketSites d D N j.val m.val)
          (intervalPacketSites d D N m.val k.val)
          (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk)
          (intervalOutputEmbedding j m (minimalCutBondRegisterEncoding hd U hU hbound m)
            (minimalCutBondRegisterEncoding hd U hU hbound j))
          (intervalOutputEmbedding m k (minimalCutBondRegisterEncoding hd U hU hbound k)
            (minimalCutBondRegisterEncoding hd U hU hbound m))
          (Function.Embedding.refl _)) *
        ((vectorizedWeightedInterval (minimalOperatorInterval U B (Nat.le_of_lt hjm))
          (CFC.sqrt (P j)) (CFC.sqrt (dualGramMetric (P m))) ⊗ₖ
          vectorizedWeightedInterval (minimalOperatorInterval U B (Nat.le_of_lt hmk))
            (CFC.sqrt (P m)) (CFC.sqrt (dualGramMetric (P k)))) ⊗ₖ 1) := by
  unfold IsMinimalIntervalColumnImplementation minimalIntervalInputEmbedding
    minimalIntervalOutputEmbedding at hX hY
  convert jointPlacedColumns_of_supported_individual
    (α := CutIntervalConfig d N j.val m.val)
    (β := CutIntervalConfig d N m.val k.val)
    (γ := CutIntervalConfig d N j.val m.val ×
      (Fin (cutCoefficientRank (operatorCoefficientTensor U) m.val) ×
        Fin (cutCoefficientRank (operatorCoefficientTensor U) j.val)))
    (δ := CutIntervalConfig d N m.val k.val ×
      (Fin (cutCoefficientRank (operatorCoefficientTensor U) k.val) ×
        Fin (cutCoefficientRank (operatorCoefficientTensor U) m.val)))
    (τ := OutsidePlacedConfig d (Fin.Embedding.append
      (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk)))
    (intervalPacketSites d D N j.val m.val) (intervalPacketSites d D N m.val k.val)
    (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk)
    (intervalInputEmbedding j.val m.val) (intervalInputEmbedding m.val k.val)
    (intervalOutputEmbedding j m (minimalCutBondRegisterEncoding hd U hU hbound m)
      (minimalCutBondRegisterEncoding hd U hU hbound j))
    (intervalOutputEmbedding m k (minimalCutBondRegisterEncoding hd U hU hbound k)
      (minimalCutBondRegisterEncoding hd U hU hbound m))
    (Function.Embedding.refl _) X Y
    (vectorizedWeightedInterval (minimalOperatorInterval U B (Nat.le_of_lt hjm))
      (CFC.sqrt (P j)) (CFC.sqrt (dualGramMetric (P m))))
    (vectorizedWeightedInterval (minimalOperatorInterval U B (Nat.le_of_lt hmk))
      (CFC.sqrt (P m)) (CFC.sqrt (dualGramMetric (P k))))
    (by rwa [intervalPacketSites_range]) (by rwa [intervalPacketSites_range]) hX hY using 1
  all_goals congr!

end MPUCircuit
