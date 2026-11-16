/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.EntropySupport
import TNLean.MPS.AreaLaw.SoftTruncatedHamiltonianMPO
import TNLean.MPS.MPDO.TraceChainHermitian

/-!
# A finite family of actual regional soft replacements

The same original nearest-neighbour interactions determine every regional sum. Each soft
replacement is approximated directly, its Hermitian part is represented by actual tensors,
and finite diagonal blocks assemble one Hermitian approximation. The number of regions may
be zero. An arbitrary real scalar shift is represented exactly.
This is an operator-representation auxiliary to ALVV, arXiv:1602.08828v2,
`t:aisefficient` and `t:aisgaplessefficient`, lines 1373–1392 and 1435–1442.

**Local fix (cluster estimate and parameters):** the construction uses the corrected
interaction-label estimate and independent scale at least three times order. It does not
assert multi-region spectral comparisons, GEN or a running-time bound; see
`docs/paper-gaps/alvv16_cluster_approximation.tex`.
-/

open Matrix Finset
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.MPS.AreaLaw

/-- A finite family of regional soft replacements has one actual Hermitian approximating MPO.
All tensors come from the original local interactions. No regional representation or cut rank
is supplied. This supports the corrected operator construction for ALVV,
arXiv:1602.08828v2, `t:aisefficient` and `t:aisgaplessefficient`, lines 1373–1392 and 1435–1442. -/
theorem exists_regional_softTruncations_hermitian_mpo_of_accuracy {N q m s : ℕ}
    (hq : 1 ≤ q) (hm : 0 < m)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (h i) {i.castSucc, i.succ})
    (hh : ∀ i, (h i).IsHermitian) (hnorm : ∀ i, ‖h i‖ ≤ 1)
    (I : Fin s → Finset (Fin N)) (eps : Fin s → ℝ) (t xi z : ℝ)
    (hlo : ∀ j, (eps j : ℂ) • 1 ≤ ∑ i ∈ I j, h i)
    (hscale : 3 * (m : ℝ) ≤ t) (hxi : 0 < xi) :
    let H := ∑ i, h i
    let R := fun j ↦ ∑ i ∈ I j, h i
    let G := H + (z : ℂ) • 1 + ∑ j, ((eps j : ℂ) • 1 +
      cfc (Real.softTruncation t m) (R j - (eps j : ℂ) • 1) - R j)
    let delta := xi / (max 1 s : ℕ)
    let W := t * (2 : ℝ) ^ (m + 1)
    let b := 2 * (Real.exp (1 / 3 : ℝ) - 1)
    let r := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
      Real.log (Real.log (1 + delta / W))) / (-Real.log b)⌉₊
    let D0 := 1 + N * q ^ 2
    let D := D0 + ((D0 + (r ^ 2 * q ^ r) * (m + 1)) * 2) * s
    ∃ T : Fin (N + 1) → MPOTensor q D,
      G.IsHermitian ∧ (MPOTensor.traceChainOperator T 1).IsHermitian ∧
      ‖G - MPOTensor.traceChainOperator T 1‖ ≤ xi := by
  classical
  intro H R G delta W b r D0 D
  let F := fun j : Fin s ↦ H - R j + (eps j : ℂ) • 1 +
    cfc (Real.softTruncation t m) (R j - (eps j : ℂ) • 1)
  let c : ℂ := 1 - (s : ℂ)
  have hspos : 0 < ((max 1 s : ℕ) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 s))
  have hdelta : 0 < delta := div_pos hxi hspos
  have hherm : H.IsHermitian ∧ ∀ j, (R j).IsHermitian :=
    ⟨isHermitian_sum _ (fun i _ ↦ hh i), fun j ↦ isHermitian_sum _ (fun i _ ↦ hh i)⟩
  have hF (j : Fin s) : (F j).IsHermitian :=
    (((hherm.1.sub (hherm.2 j)).add
      (isHermitian_one.smul (by simp [isSelfAdjoint_iff]))).add
      (cfc_predicate (Real.softTruncation t m) (R j - (eps j : ℂ) • 1)))
  have hconstruct (j : Fin s) :
      ∃ A : Fin (N + 1) → MPOTensor q ((D0 + (r ^ 2 * q ^ r) * (m + 1)) * 2),
        (MPOTensor.traceChainOperator A 1).IsHermitian ∧
          ‖F j - MPOTensor.traceChainOperator A 1‖ ≤ delta := by
    obtain ⟨A, hA⟩ := exists_softTruncatedHamiltonian_mpo_of_accuracy
      hq hm h hs hh hnorm (I j) (eps j) t delta (hlo j) hscale hdelta
    exact MPOTensor.exists_hermitian_traceChainOperator_approximation (by omega) (hF j) A hA
  choose A hA using hconstruct
  obtain ⟨B, hB⟩ := MPOTensor.exists_traceChainOperator_linearCombination
    (by omega) A (fun _ ↦ (1 : ℂ))
  simp only [one_smul] at hB
  let f := fun i : Fin N ↦ c • h i
  have hf (i : Fin N) : Entropy.IsSupportedOn (f i) {i.castSucc, i.succ} :=
    QuantumCircuit.isSupportedOn_of_mem_supportedOperators
      (Submodule.smul_mem _ c (QuantumCircuit.mem_supportedOperators_of_isSupportedOn (hs i)))
  obtain ⟨C, hC⟩ := exists_local_sum_add_scalar_mpo hq f hf (z : ℂ)
  have hC0 : c • H + (z : ℂ) • 1 = MPOTensor.traceChainOperator C 1 := by
    simpa only [f, ← Finset.smul_sum] using hC
  have hG : G = c • H + (z : ℂ) • 1 + ∑ j, F j := by
    dsimp only [G, F, c]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]
    module
  have hcore : (c • H + (z : ℂ) • 1).IsHermitian :=
    (hherm.1.smul (by simp [c, isSelfAdjoint_iff])).add
      (isHermitian_one.smul (by simp [isSelfAdjoint_iff]))
  obtain ⟨T, hT⟩ := MPOTensor.exists_traceChainOperator_add (by omega) C B
  refine ⟨T, ?_, ?_, ?_⟩
  · rw [hG]
    exact hcore.add (isHermitian_sum _ (fun j _ ↦ hF j))
  · rw [← hT, ← hC0, ← hB]
    exact hcore.add (isHermitian_sum _ (fun j _ ↦ (hA j).1))
  · have hdiff : G - MPOTensor.traceChainOperator T 1 =
        ∑ j, (F j - MPOTensor.traceChainOperator (A j) 1) := by
      rw [hG, ← hT, ← hC0, ← hB, Finset.sum_sub_distrib]
      abel
    rw [hdiff]
    calc
      _ ≤ ∑ j, ‖F j - MPOTensor.traceChainOperator (A j) 1‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin s, delta := Finset.sum_le_sum (fun j _ ↦ (hA j).2)
      _ = (s : ℝ) * delta := by simp [nsmul_eq_mul]
      _ ≤ ((max 1 s : ℕ) : ℝ) * delta :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (le_max_right 1 s)) hdelta.le
      _ = xi := mul_div_cancel₀ xi hspos.ne'

end TNLean.MPS.AreaLaw
