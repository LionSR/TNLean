/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.IntervalInputRegrouping

/-!
# Parent interval columns from the initialized joint input

The concrete joint child input covers exactly the parent initialized input,
with a derived coordinate bijection. An operator satisfying the parent
columns on the joint input therefore satisfies the full parent interval
invariant. All outside logical configurations remain unrestricted.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open Matrix MPSPreparation MPSTensor
open scoped Kronecker Matrix ComplexOrder MatrixOrder

namespace MPUCircuit

open scoped Classical in
/-- The actual joint input identity determines every parent initialized column.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem isMinimalIntervalColumnImplementation_of_joint_initialized_columns
    {d D N : ℕ} [NeZero d]
    (hd : 2 ≤ d) (U : Matrix (Cfg d N) (Cfg d N) ℂ)
    (hU : U ∈ unitaryGroup (Cfg d N) ℂ)
    (hbound : ∀ j : Fin (N + 1), cutRank (operatorCoefficientTensor U) j.val ≤ D)
    (B : ∀ t, Module.Basis (Fin (cutRank (operatorCoefficientTensor U) t))
      ℂ (cutColumnSpace (operatorCoefficientTensor U) t))
    (P : ∀ t : Fin (N + 1), Matrix (Fin (cutRank (operatorCoefficientTensor U) t.val))
      (Fin (cutRank (operatorCoefficientTensor U) t.val)) ℂ)
    (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val)
    (Z : Matrix (Cfg d (logicalSiteCount d D N)) (Cfg d (logicalSiteCount d D N)) ℂ)
    (h : Z * initializedBasisMatrix
        (intervalJointInputEmbedding (d := d) (D := D) j m k hjm hmk) =
      (initializedBasisMatrix (minimalIntervalOutputEmbedding hd U hU hbound j k) *
        (vectorizedWeightedInterval (minimalOperatorInterval U B (hjm.le.trans hmk.le))
          (CFC.sqrt (P j)) (CFC.sqrt (dualGramMetric (P k))) ⊗ₖ
            (1 : Matrix (OutsidePlacedConfig d (intervalPacketSites d D N j.val k.val))
              (OutsidePlacedConfig d (intervalPacketSites d D N j.val k.val)) ℂ))).submatrix id
        (intervalJointInputConfigEquiv j m k hjm hmk)) :
    IsMinimalIntervalColumnImplementation hd U hU hbound B P j k (hjm.le.trans hmk.le) Z := by
  unfold IsMinimalIntervalColumnImplementation
  rw [mul_initializedBasisMatrix]
  rw [mul_initializedBasisMatrix] at h
  ext x p
  have hh := congrFun (congrFun h x) ((intervalJointInputConfigEquiv j m k hjm hmk).symm p)
  simpa only [Matrix.submatrix_apply, id_eq, intervalJointInputEmbedding_eq_parent_input,
    Equiv.apply_symm_apply] using hh

end MPUCircuit
