/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.MinimalIntervalCircuit
import TNLean.MPS.MPU.TreeAmplificationGateBounds

/-!
# Recursion for actual interval circuit implementations

Once single-site implementations and an adjacent-interval merging rule are
established for one fixed minimal basis and metric family, induction on an
actual consecutive interval partition gives its circuit. The induction retains
the full logical support, all-input workspace cleanup, and weighted interval
columns. Its gate count is the numerical count on that very partition.

This is a conditional recursion lemma. The leaf and merging constructions,
and their derivation from a finite unitary, are separate results. It does not
assert the general MPU circuit theorem without those constructions.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open Matrix MPSTensor MPSPreparation
open scoped Kronecker Matrix ComplexOrder MatrixOrder

namespace MPUCircuit

open scoped Classical in
/-- Actual leaf circuits and an actual adjacent-interval merging rule extend to
every consecutive interval partition, with precisely its recursively counted
gate budget. The same basis and metric family is used throughout.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem exists_minimalInterval_circuit_of_partition
    {d D N : ℕ} [NeZero d]
    (hd : 2 ≤ d) (U : Matrix (Cfg d N) (Cfg d N) ℂ)
    (hU : U ∈ unitaryGroup (Cfg d N) ℂ)
    (hbound : ∀ j : Fin (N + 1), cutCoefficientRank (operatorCoefficientTensor U) j.val ≤ D)
    (B : ∀ k, Module.Basis (Fin (cutCoefficientRank (operatorCoefficientTensor U) k))
      ℂ (cutColumnSpace (operatorCoefficientTensor U) k))
    (P : ∀ j : Fin (N + 1), Matrix (Fin (cutCoefficientRank (operatorCoefficientTensor U) j.val))
      (Fin (cutCoefficientRank (operatorCoefficientTensor U) j.val)) ℂ)
    (K b M : ℕ)
    (hLeaves : ∀ i : Fin N,
      ∃ Z : Matrix (Cfg d (logicalSiteCount d D N))
          (Cfg d (logicalSiteCount d D N)) ℂ,
      ∃ C : Matrix (Cfg d (globalSiteCount d D N))
          (Cfg d (globalSiteCount d D N)) ℂ,
        IsMinimalIntervalCircuitImplementation hd U hU hbound B P i.castSucc i.succ
          (Nat.le_succ i.val) K Z C)
    (hMerge : ∀ (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val)
        (K₁ K₂ : ℕ)
        (Z₁ Z₂ : Matrix (Cfg d (logicalSiteCount d D N))
          (Cfg d (logicalSiteCount d D N)) ℂ)
        (C₁ C₂ : Matrix (Cfg d (globalSiteCount d D N))
          (Cfg d (globalSiteCount d D N)) ℂ),
      IsMinimalIntervalCircuitImplementation hd U hU hbound B P j m
        (Nat.le_of_lt hjm) K₁ Z₁ C₁ →
      IsMinimalIntervalCircuitImplementation hd U hU hbound B P m k
        (Nat.le_of_lt hmk) K₂ Z₂ C₂ →
      ∃ Z : Matrix (Cfg d (logicalSiteCount d D N))
          (Cfg d (logicalSiteCount d D N)) ℂ,
      ∃ C : Matrix (Cfg d (globalSiteCount d D N))
          (Cfg d (globalSiteCount d D N)) ℂ,
        IsMinimalIntervalCircuitImplementation hd U hU hbound B P j k
          ((Nat.le_of_lt hjm).trans (Nat.le_of_lt hmk)) (b * (K₁ + K₂) + M) Z C)
    {start len : ℕ} {t : BinaryTree ℕ}
    (hpartition : IsIntervalPartition start len t) :
    ∀ hlimit : start + len ≤ N,
      ∃ Z : Matrix (Cfg d (logicalSiteCount d D N))
          (Cfg d (logicalSiteCount d D N)) ℂ,
      ∃ C : Matrix (Cfg d (globalSiteCount d D N))
          (Cfg d (globalSiteCount d D N)) ℂ,
        IsMinimalIntervalCircuitImplementation hd U hU hbound B P
          ⟨start, by omega⟩ ⟨start + len, by omega⟩
          (by change start ≤ start + len; omega)
          (treeGateCount K b M t) Z C := by
  induction hpartition with
  | leaf start =>
    intro hlimit
    obtain ⟨Z, C, hC⟩ := hLeaves ⟨start, by omega⟩
    exact ⟨Z, C, hC⟩
  | @node start l r left right hl hr hleft hright ihleft ihright =>
    intro hlimit
    obtain ⟨Z₁, C₁, hC₁⟩ := ihleft (by omega)
    obtain ⟨Z₂, C₂, hC₂⟩ := ihright (by omega)
    let j : Fin (N + 1) := ⟨start, by omega⟩
    let m : Fin (N + 1) := ⟨start + l, by omega⟩
    let k : Fin (N + 1) := ⟨start + (l + r), by omega⟩
    have hjm : j.val < m.val := by dsimp [j, m]; omega
    have hmk : m.val < k.val := by dsimp [m, k]; omega
    have hleftCircuit : IsMinimalIntervalCircuitImplementation hd U hU hbound B P
        j m (Nat.le_of_lt hjm) (treeGateCount K b M left) Z₁ C₁ := hC₁
    have hrightCircuit : IsMinimalIntervalCircuitImplementation hd U hU hbound B P
        m k (Nat.le_of_lt hmk) (treeGateCount K b M right) Z₂ C₂ := by
      simpa only [j, m, k, Nat.add_assoc] using hC₂
    obtain ⟨Z, C, hC⟩ := hMerge j m k hjm hmk
      (treeGateCount K b M left) (treeGateCount K b M right) Z₁ Z₂ C₁ C₂
      hleftCircuit hrightCircuit
    exact ⟨Z, C, hC⟩

end MPUCircuit
