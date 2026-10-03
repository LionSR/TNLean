/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.ExactBoundedCutRankCircuit
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Operator-norm approximations with exact auxiliary cleanup

The exact bounded-cut-rank circuit also satisfies every nonnegative error
threshold in the Euclidean operator norm. Its physical phase and cleanup
identity are retained. Ordinary periodic MPUs inherit the same result from
the derived two-virtual-bond cut-rank bound.

The gates are arbitrary neighboring two-qudit unitaries. There is no finite
alphabet or efficient classical parameter-computation assertion. Source:
§5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

open Matrix MPSTensor MPSPreparation QuantumCircuit
open scoped Matrix

namespace MPUCircuit

open scoped Matrix.Norms.L2Operator

open scoped Classical in
/-- The same circuit realizes every prescribed nonnegative operator-norm
accuracy, with exact auxiliary cleanup. In fact its initialized operator-norm
error is zero. The norm here is the Euclidean operator norm on the rectangular
map from physical inputs to the complete physical and auxiliary register.

See §5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_clean_operatorNorm_approximate_circuit_of_bounded_cutRank
    {d D N : ℕ} (hd : 2 ≤ d) (hN : 0 < N)
    (U : Matrix (Cfg d N) (Cfg d N) ℂ)
    (hU : U ∈ unitaryGroup (Cfg d N) ℂ)
    (hbound : ∀ j : Fin (N + 1), cutRank (operatorCoefficientTensor U) j.val ≤ D)
    (ε : ℝ) (hε : 0 ≤ ε) :
    letI : NeZero d := ⟨by omega⟩
    ∃ C : Matrix (Cfg d (completeCircuitSiteCount d D N))
        (Cfg d (completeCircuitSiteCount d D N)) ℂ,
      IsPairProduct d (completeCircuitSiteCount d D N)
        (uniformCircuitResourceCoefficient d D * (D + 1) ^ 3 *
          (2 * N) ^ (Nat.clog 2 D + 6)) C ∧
      C * initializedBasisMatrix
          (completePhysicalConfigEmbedding (d := d) (D := D) (N := N)) =
        initializedBasisMatrix
          (completePhysicalConfigEmbedding (d := d) (D := D) (N := N)) * U ∧
      ‖C * initializedBasisMatrix
          (completePhysicalConfigEmbedding (d := d) (D := D) (N := N)) -
        initializedBasisMatrix
          (completePhysicalConfigEmbedding (d := d) (D := D) (N := N)) * U‖ ≤ ε := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hcolumns⟩ :=
    exists_clean_exact_circuit_of_bounded_cutRank hd hN U hU hbound
  refine ⟨C, hC, hcolumns, ?_⟩
  rw [hcolumns, sub_self, norm_zero]
  exact hε

open scoped Classical in
/-- Every periodic MPU at the given positive length admits arbitrary
operator-norm accuracy with the same neighboring-pair gate bound and exact
auxiliary cleanup. Its actual operator cut bound is derived from the periodic
MPO coefficients, with no spectral or canonical-form hypothesis.

See §5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex` and
arXiv:2508.08160, `eq:U_N_hom`. -/
theorem exists_clean_operatorNorm_approximate_circuit_of_periodic_mpo_unitary
    {d χ N : ℕ} (hd : 2 ≤ d) (hN : 0 < N) (M : MPOTensor d χ)
    (hU : M.mpo N ∈ unitaryGroup (Cfg d N) ℂ) (ε : ℝ) (hε : 0 ≤ ε) :
    letI : NeZero d := ⟨by omega⟩
    ∃ C : Matrix (Cfg d (completeCircuitSiteCount d (χ * χ) N))
        (Cfg d (completeCircuitSiteCount d (χ * χ) N)) ℂ,
      IsPairProduct d (completeCircuitSiteCount d (χ * χ) N)
        (uniformCircuitResourceCoefficient d (χ * χ) * (χ * χ + 1) ^ 3 *
          (2 * N) ^ (Nat.clog 2 (χ * χ) + 6)) C ∧
      C * initializedBasisMatrix
          (completePhysicalConfigEmbedding (d := d) (D := χ * χ) (N := N)) =
        initializedBasisMatrix
          (completePhysicalConfigEmbedding (d := d) (D := χ * χ) (N := N)) * M.mpo N ∧
      ‖C * initializedBasisMatrix
          (completePhysicalConfigEmbedding (d := d) (D := χ * χ) (N := N)) -
        initializedBasisMatrix
          (completePhysicalConfigEmbedding (d := d) (D := χ * χ) (N := N)) * M.mpo N‖ ≤ ε :=
  exists_clean_operatorNorm_approximate_circuit_of_bounded_cutRank hd hN (M.mpo N) hU
    (cutRank_operatorCoefficientTensor_mpo_le_all M) ε hε

end MPUCircuit
