/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.MinimalIntervalLeafColumns
import TNLean.MPS.MPU.MinimalIntervalRootColumns
import TNLean.MPS.MPU.MinimalIntervalRecursion
import TNLean.MPS.MPU.MinimalIntervalMergingCircuit
import TNLean.MPS.MPU.UniformCircuitResourceBounds
import TNLean.MPS.MPU.SingleSiteCompleteCircuit
import TNLean.MPS.MPU.PeriodicOperatorCutRank
/-!
# Exact neighboring-pair circuits for bounded operator cut ranks

The minimal interval family is obtained from the given finite unitary.
Its actual leaf implementations and actual joining construction are assembled
on the constructed midpoint tree. The full interval then gives the original
physical unitary, with every logical auxiliary and scratch qudit returned to
zero. The gate bound depends only on the local dimension, the bond bound,
and the physical length.

The gate parameters may be arbitrary complex numbers. This is a nonuniform
existence result; it does not claim efficient computation of these parameters.
Source: §5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex` and the arbitrary
neighboring two-qudit gate model of arXiv:2508.08160, local `main.tex`, line 820.
-/

open Matrix MPSTensor MPSPreparation
open scoped Kronecker Matrix ComplexOrder MatrixOrder

namespace MPUCircuit

open scoped Classical in
/-- A finite unitary whose consecutive operator cut ranks are bounded admits
an exact neighboring-pair circuit on the allocated global register. Every
auxiliary is initialized and returned to zero, and the physical action includes
the exact scalar phase. The coefficient is polynomial in the bond bound and
the length exponent grows logarithmically in that bound.

See §5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_clean_exact_circuit_of_bounded_cutRank_of_two_le
    {d D N : ℕ} [NeZero d] (hd : 2 ≤ d) (hN : 2 ≤ N)
    (U : Matrix (Cfg d N) (Cfg d N) ℂ)
    (hU : U ∈ unitaryGroup (Cfg d N) ℂ)
    (hbound : ∀ j : Fin (N + 1), cutRank (operatorCoefficientTensor U) j.val ≤ D) :
    ∃ C : Matrix (Cfg d (globalSiteCount d D N))
        (Cfg d (globalSiteCount d D N)) ℂ,
      IsPairProduct d (globalSiteCount d D N)
        (uniformCircuitResourceCoefficient d D * (D + 1) ^ 3 *
          (2 * N) ^ (Nat.clog 2 D + 6)) C ∧
      C * initializedBasisMatrix (physicalGlobalConfigEmbedding (d := d) (D := D) (N := N)) =
        initializedBasisMatrix (physicalGlobalConfigEmbedding (d := d) (D := D) (N := N)) * U := by
  obtain ⟨B, hB0, hBN, P, hP, hIntervals, hP0, hPN, hfull, hLeaves⟩ :=
    exists_normalized_minimalInterval_family_with_placed_leaf_columns_of_unitary
      hd hN U hU hbound
  have hD : 0 < D := (cutRank_pos (operatorCoefficientTensor U)
    (operatorCoefficientTensor_ne_zero (by omega : 0 < d) U hU) 0).trans_le (hbound 0)
  let K := uniformNodeGateCount d D N
  let F := uniformReflectionGateCount d D N
  let M := amplificationTreeOverhead D K F F
  have hleaf : ∀ i : Fin N,
      ∃ Z : Matrix (Cfg d (logicalSiteCount d D N))
          (Cfg d (logicalSiteCount d D N)) ℂ,
      ∃ C : Matrix (Cfg d (globalSiteCount d D N))
          (Cfg d (globalSiteCount d D N)) ℂ,
        IsMinimalIntervalCircuitImplementation hd U hU hbound B P i.castSucc i.succ
          (Nat.le_succ i.val) K Z C := by
    intro i
    obtain ⟨Z, C, _, _, hpair, _, hclean, hlogical, hsupport, hcolumns⟩ := hLeaves i
    refine ⟨embedOp (leafConsecutiveSites d D N i) Z, C,
      hlogical, hsupport, hpair.mono ?_, hclean, hcolumns⟩
    exact (placedLeafGateCount_le_uniform d D N).trans
      (Nat.le_add_right _ _)
  have hmerge : ∀ (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val)
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
          ((Nat.le_of_lt hjm).trans (Nat.le_of_lt hmk))
          ((2 * D + 1) * (K₁ + K₂) + M) Z C := by
    intro j m k hjm hmk K₁ K₂ Z₁ Z₂ C₁ C₂ h₁ h₂
    exact exists_minimalInterval_merging_circuit hd U hU hbound B P
      (fun t ↦ (hP t).1) (fun t ↦ (hP t).2.1)
      (fun t ↦ (hP t).2.2.2.1) j m k hjm hmk K₁ K₂ Z₁ Z₂ C₁ C₂ h₁ h₂
  obtain ⟨Z, C, hC⟩ := exists_minimalInterval_circuit_of_partition hd U hU hbound B P
    K (2 * D + 1) M hleaf hmerge (balancedIntervalTree_isIntervalPartition 0 N (by omega))
    (by omega : 0 + N ≤ N)
  have hroot : IsMinimalIntervalCircuitImplementation hd U hU hbound B P 0 (Fin.last N)
      (Nat.zero_le N) (treeGateCount K (2 * D + 1) M (balancedIntervalTree 0 N)) Z C := by
    simpa only [Nat.zero_add, Fin.mk_zero, Fin.last] using hC
  have hcost := uniformCircuitTreeGateCount_le_polynomial_bond hd hD (by omega : 0 < N)
    (fun _ ↦ D) (fun _ ↦ le_rfl)
  rw [uniformCircuitTreeGateCount, amplificationTreeGateCount_const_eq_treeGateCount]
    at hcost
  refine ⟨C, hroot.2.2.1.mono hcost, ?_⟩
  exact minimalIntervalRootColumns_eq_physical_global hd U hU hbound B hB0 hBN P
    (hP 0).1 (hP (Fin.last N)).1 Z hroot.2.2.2.2 C hroot.2.2.2.1

open scoped Classical in
/-- Every positive-length finite unitary of bounded consecutive operator cut
ranks admits an exact neighboring-pair circuit with uniformly bounded gate
count. All allocated auxiliaries begin and end at zero. The dimension
instance needed to name that zero is derived from `2 ≤ d`, rather than
assumed separately. Gate parameters are arbitrary complex numbers.

See §5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`; the gate model
is arXiv:2508.08160, local `main.tex`, line 820. -/
theorem exists_clean_exact_circuit_of_bounded_cutRank
    {d D N : ℕ} (hd : 2 ≤ d) (hN : 0 < N)
    (U : Matrix (Cfg d N) (Cfg d N) ℂ)
    (hU : U ∈ unitaryGroup (Cfg d N) ℂ)
    (hbound : ∀ j : Fin (N + 1), cutRank (operatorCoefficientTensor U) j.val ≤ D) :
    let : NeZero d := ⟨by omega⟩
    ∃ C : Matrix (Cfg d (completeCircuitSiteCount d D N))
        (Cfg d (completeCircuitSiteCount d D N)) ℂ,
      IsPairProduct d (completeCircuitSiteCount d D N)
        (uniformCircuitResourceCoefficient d D * (D + 1) ^ 3 *
          (2 * N) ^ (Nat.clog 2 D + 6)) C ∧
      C * initializedBasisMatrix (completePhysicalConfigEmbedding (d := d) (D := D) (N := N)) =
        initializedBasisMatrix
          (completePhysicalConfigEmbedding (d := d) (D := D) (N := N)) * U := by
  let : NeZero d := ⟨by omega⟩
  by_cases hN1 : N = 1
  · subst N
    obtain ⟨C, hC, hcolumns⟩ := exists_singleSite_complete_clean_pair_circuit (D := D) hU
    refine ⟨C, hC.mono ?_, hcolumns⟩
    have hcoeff : 1 ≤ uniformCircuitResourceCoefficient d D := by
      unfold uniformCircuitResourceCoefficient
      have hfirst : 1 ≤ 2 * D + 2 := by omega
      have hsecond : 1 ≤ 5 * (76 * (d ^ 4 * D ^ 2) ^ 6 + 8 * (D + 1)) + 400 := by omega
      have hprod : 1 ≤ (2 * D + 2) *
          (5 * (76 * (d ^ 4 * D ^ 2) ^ 6 + 8 * (D + 1)) + 400) := by
        simpa only [Nat.one_mul] using Nat.mul_le_mul hfirst hsecond
      exact hprod.trans (Nat.le_add_right _ _)
    have hpowerD : 1 ≤ (D + 1) ^ 3 := one_le_pow₀ (by omega)
    have hpowerN : 1 ≤ (2 * 1) ^ (Nat.clog 2 D + 6) := one_le_pow₀ (by omega)
    simpa only [Nat.one_mul] using
      Nat.mul_le_mul (Nat.mul_le_mul hcoeff hpowerD) hpowerN
  · have hN2 : 2 ≤ N := by omega
    obtain ⟨C, hC, hcolumns⟩ := exists_clean_exact_circuit_of_bounded_cutRank_of_two_le
      hd hN2 U hU hbound
    exact exists_complete_clean_pair_circuit_of_global hN2 U C hC hcolumns

open scoped Classical in
/-- The exact circuit theorem applied to an ordinary periodic MPU, with the
cut-rank bound derived by opening its two virtual bonds. Only unitarity at
this physical length is required; no Schmidt-value condition, canonical form,
or supplied decomposition is assumed.

See §5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`; the periodic
operator convention is arXiv:2508.08160, `eq:U_N_hom`. -/
theorem exists_clean_exact_circuit_of_periodic_mpo_unitary
    {d χ N : ℕ} (hd : 2 ≤ d) (hN : 0 < N) (M : MPOTensor d χ)
    (hU : M.mpo N ∈ unitaryGroup (Cfg d N) ℂ) :
    let : NeZero d := ⟨by omega⟩
    ∃ C : Matrix (Cfg d (completeCircuitSiteCount d (χ * χ) N))
        (Cfg d (completeCircuitSiteCount d (χ * χ) N)) ℂ,
      IsPairProduct d (completeCircuitSiteCount d (χ * χ) N)
        (uniformCircuitResourceCoefficient d (χ * χ) * (χ * χ + 1) ^ 3 *
          (2 * N) ^ (Nat.clog 2 (χ * χ) + 6)) C ∧
      C * initializedBasisMatrix
          (completePhysicalConfigEmbedding (d := d) (D := χ * χ) (N := N)) =
        initializedBasisMatrix
          (completePhysicalConfigEmbedding (d := d) (D := χ * χ) (N := N)) * M.mpo N :=
  exists_clean_exact_circuit_of_bounded_cutRank hd hN (M.mpo N) hU
    (cutRank_operatorCoefficientTensor_mpo_le_all M)

end MPUCircuit
