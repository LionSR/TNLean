/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.MinimalIntervalColumns
import TNLean.Circuit.CleanUnitaryImplementation

/-!
# Circuit implementations of the actual minimal intervals

An interval implementation consists of a full logical unitary with the
prescribed interval support, an actual neighboring-pair circuit, its
all-input clean-workspace identity, and the actual weighted interval columns.
These are the induction data in the balanced interval construction. The
operator and circuit are matrices, and every identity includes its phase.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open Matrix MPSTensor MPSPreparation QuantumCircuit
open scoped Kronecker Matrix ComplexOrder MatrixOrder

namespace MPUCircuit

open scoped Classical in
/-- The complete circuit conditions for the actual weighted interval, with an
explicit gate budget and one reusable initialized workspace.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def IsMinimalIntervalCircuitImplementation {d D N : ℕ} [NeZero d]
    (hd : 2 ≤ d) (U : Matrix (Cfg d N) (Cfg d N) ℂ)
    (hU : U ∈ unitaryGroup (Cfg d N) ℂ)
    (hbound : ∀ j : Fin (N + 1), cutCoefficientRank (operatorCoefficientTensor U) j.val ≤ D)
    (B : ∀ k, Module.Basis (Fin (cutCoefficientRank (operatorCoefficientTensor U) k))
      ℂ (cutColumnSpace (operatorCoefficientTensor U) k))
    (P : ∀ j : Fin (N + 1), Matrix (Fin (cutCoefficientRank (operatorCoefficientTensor U) j.val))
      (Fin (cutCoefficientRank (operatorCoefficientTensor U) j.val)) ℂ)
    (j k : Fin (N + 1)) (hjk : j.val ≤ k.val) (K : ℕ)
    (Z : Matrix (Cfg d (logicalSiteCount d D N)) (Cfg d (logicalSiteCount d D N)) ℂ)
    (C : Matrix (Cfg d (globalSiteCount d D N)) (Cfg d (globalSiteCount d D N)) ℂ) :
    Prop :=
  Z ∈ unitary (Matrix (Cfg d (logicalSiteCount d D N))
      (Cfg d (logicalSiteCount d D N)) ℂ) ∧
    Z ∈ supportedOperators d (intervalConsecutiveSupport d D N j.val k.val) ∧
    IsPairProduct d (globalSiteCount d D N) K C ∧
    IsCleanImplementation
      (initializedBasisMatrix (zeroWorkspaceEmbedding (d := d)
        (n := logicalSiteCount d D N) (a := auxiliarySiteCount d D N))) C Z ∧
    IsMinimalIntervalColumnImplementation hd U hU hbound B P j k hjk Z

namespace IsMinimalIntervalCircuitImplementation

open scoped Classical in
/-- Increasing the gate budget preserves all actual interval and cleanup identities.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem mono {d D N K L : ℕ} [NeZero d]
    {hd : 2 ≤ d} {U : Matrix (Cfg d N) (Cfg d N) ℂ}
    {hU : U ∈ unitaryGroup (Cfg d N) ℂ}
    {hbound : ∀ j : Fin (N + 1), cutCoefficientRank (operatorCoefficientTensor U) j.val ≤ D}
    {B : ∀ k, Module.Basis (Fin (cutCoefficientRank (operatorCoefficientTensor U) k))
      ℂ (cutColumnSpace (operatorCoefficientTensor U) k)}
    {P : ∀ j : Fin (N + 1), Matrix (Fin (cutCoefficientRank (operatorCoefficientTensor U) j.val))
      (Fin (cutCoefficientRank (operatorCoefficientTensor U) j.val)) ℂ}
    {j k : Fin (N + 1)} {hjk : j.val ≤ k.val}
    {Z : Matrix (Cfg d (logicalSiteCount d D N)) (Cfg d (logicalSiteCount d D N)) ℂ}
    {C : Matrix (Cfg d (globalSiteCount d D N)) (Cfg d (globalSiteCount d D N)) ℂ}
    (h : IsMinimalIntervalCircuitImplementation hd U hU hbound B P j k hjk K Z C)
    (hKL : K ≤ L) :
    IsMinimalIntervalCircuitImplementation hd U hU hbound B P j k hjk L Z C :=
  ⟨h.1, h.2.1, h.2.2.1.mono hKL, h.2.2.2.1, h.2.2.2.2⟩

end IsMinimalIntervalCircuitImplementation

end MPUCircuit
