/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.MPO.OperatorMPOFromCutRank
import QICLean.Analysis.Real.GeometricOrderPolynomialBound
import QICLean.ManyBody.Sites.PlacedConfiguration
import QICLean.ManyBody.Sites.Product.ProductVector
import QICLean.ManyBody.Entropy.Filter.Optimizer
import TNLean.MPS.Operator.Periodic.TraceChainHermitian
import Mathlib.Data.Fintype.EquivFin
import QICLean.Spectral.Perturbation.ClusterNormPerturbation
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.SoftTruncation.PhysicalScaledSoftTruncationResidual

/-!
# A logarithmic cluster order for the actual soft-truncation MPO

A logarithmic ceiling chooses the actual cluster order from the error budget, for any base
dominating every heat-time base. Taking scale at least three times the positive order puts every
required heat time in the strict small-time regime. Supporting a corrected ALVV, arXiv:1602.08828v2,
`lem:exp-approx-eff`, lines 1262–1268.

**Local fix (cutoff and normalization):** this is the corrected interaction-label construction, not
the printed physical-support estimate or a computational runtime result; see
`docs/paper-gaps/alvv16_cluster_approximation.tex`.

**Scope restriction (scale at least three times the order):** ALVV `lem:exp-approx-eff`, lines
1262–1268, allows any scale with `t′ < (ln 2/2) t`; `softHeat_base_bounds` and
`exists_softTruncation_mpo_of_accuracy` take `t ≥ 3m`, a sub-case of that range, while
`exists_softTruncation_mpo_of_accuracy_of_base` carries no such restriction. See
`docs/paper-gaps/alvv16_cluster_approximation.tex`.

## The actual soft-truncated Hamiltonian as an approximated operator chain

The selected regional terms are masked from the original nearest-neighbour family. The exterior sum
and scalar are represented exactly, and added to the directly constructed heat sum. Supporting a
corrected ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268.

**Local fix (cutoff and normalization):** this is the corrected interaction-label construction, with
the original local terms and scalar shift kept separate. It asserts no computational running time;
see `docs/paper-gaps/alvv16_cluster_approximation.tex`.

**Scope restriction (scale at least three times the order):** ALVV `lem:exp-approx-eff`, lines
1262–1268, allows any scale with `t′ < (ln 2/2) t`;
`exists_softTruncatedHamiltonian_mpo_of_accuracy` takes `t ≥ 3m`, a sub-case of that range, while
`exists_softTruncatedHamiltonian_mpo_of_accuracy_of_base` carries no such restriction. See
`docs/paper-gaps/alvv16_cluster_approximation.tex`.

## A finite family of actual regional soft replacements

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

## An actual MPO for selected regional soft replacements

Only the selected regional sums are replaced. Reindexing the selected finite set preserves
the same actual matrix and makes the represented bond depend on the number of replacements.
This operator-construction auxiliary supports ALVV, arXiv:1602.08828v2,
`t:aisefficient`, lines 1373–1392. It uses the corrected cluster construction and retains
independent scale at least three times order; no efficient-GEN or running-time bound follows.
See `docs/paper-gaps/alvv16_cluster_approximation.tex`.

It also contains the following results.

* `TNLean.MPS.AreaLaw.exists_regional_softTruncations_mpo_buffered_spectral_comparison`: buffered
  spectral comparison for actual regional soft approximations.
* `TNLean.MPS.AreaLaw.exists_interval_physical_soft_closeness_and_mpo`: physical spectral windows
  and an actual soft-truncation MPO at one parameter choice.
-/

section SoftTruncationMPOAccuracy

section

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.MPS.AreaLaw

/-- The common heat-time ceiling is strictly inside the cluster-expansion
regime. Numerical auxiliary to ALVV, arXiv:1602.08828v2,
`lem:exp-approx-eff`, lines 1262–1268. -/
theorem softHeat_base_bounds :
    0 < 2 * (Real.exp (1 / 3 : ℝ) - 1) ∧ 2 * (Real.exp (1 / 3 : ℝ) - 1) < 1 := by
  have hl : (1 / 3 : ℝ) < Real.log (3 / 2) := by
    have h := Real.log_lt_sub_one_of_pos (x := (3 / 2 : ℝ)⁻¹)
      (by norm_num) (by norm_num)
    rw [Real.log_inv] at h
    norm_num at h
    linarith
  have he : Real.exp (1 / 3 : ℝ) < 3 / 2 :=
    (Real.exp_lt_exp.mpr hl).trans_eq (Real.exp_log (by norm_num))
  have h1 : 1 < Real.exp (1 / 3 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
  constructor <;> linarith

/-- A logarithmic cluster order built from any base `b` dominating the largest heat-time base
`2 (e^{m/t} - 1)` gives actual soft-truncation tensors at any prescribed accuracy. Supporting a
corrected ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268. -/
theorem exists_softTruncation_mpo_of_accuracy_of_base {N q m : ℕ} (hq : 1 ≤ q)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
      (h i) {i.castSucc, i.succ})
    (hh : ∀ i, (h i).IsHermitian) (hnorm : ∀ i, ‖h i‖ ≤ 1)
    (eps t xi b : ℝ) (hlo : (eps : ℂ) • 1 ≤ ∑ i, h i) (ht : 0 < t) (hxi : 0 < xi)
    (hb0 : 0 < b) (hb1 : b < 1) (hbase : 2 * (Real.exp ((m : ℝ) / t) - 1) ≤ b) :
    let W := t * (2 : ℝ) ^ (m + 1)
    let r := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
      Real.log (Real.log (1 + xi / W))) / (-Real.log b)⌉₊
    ∃ A : Fin (N + 1) → MPOTensor q ((r ^ 2 * q ^ r) * (m + 1)),
      ‖cfc (Real.softTruncation t m) ((∑ i, h i) - (eps : ℂ) • 1) -
        MPOTensor.traceChainOperator A 1‖ ≤ xi := by
  intro W r
  have hbudget := Real.exponential_geometric_tail_order (N : ℝ) W b xi
    (by dsimp only [W]; positivity) hb0 hb1 hxi
  change 0 < r ∧ W * (Real.exp ((N : ℝ) ^ 2 * b ^ r) - 1) ≤ xi at hbudget
  obtain ⟨A, hA⟩ := exists_softTruncation_mpo_of_cluster_order (m := m) hq hbudget.1 h hs hh
    hnorm eps t hlo ht (hbase.trans hb1.le)
  refine ⟨A, hA.trans ?_⟩
  calc
    (t * (2 : ℝ) ^ (m + 1)) *
        (Real.exp ((N : ℝ) ^ 2 * (2 * (Real.exp ((m : ℝ) / t) - 1)) ^ r) - 1)
        ≤ W * (Real.exp ((N : ℝ) ^ 2 * b ^ r) - 1) := by
          dsimp only [W]
          gcongr
          exact mul_nonneg (by norm_num)
            (sub_nonneg.mpr (Real.one_le_exp (by positivity)))
    _ ≤ xi := hbudget.2

/-- A completely specified logarithmic cluster order gives actual soft-truncation tensors at
any prescribed accuracy, using any scale at least three times the positive order. All heat
approximants and tensors are constructed from the original local interactions.
Supporting a corrected ALVV,
arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268. -/
theorem exists_softTruncation_mpo_of_accuracy {N q m : ℕ} (hq : 1 ≤ q) (hm : 0 < m)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
      (h i) {i.castSucc, i.succ})
    (hh : ∀ i, (h i).IsHermitian) (hnorm : ∀ i, ‖h i‖ ≤ 1)
    (eps t xi : ℝ) (hlo : (eps : ℂ) • 1 ≤ ∑ i, h i)
    (hscale : 3 * (m : ℝ) ≤ t) (hxi : 0 < xi) :
    let W := t * (2 : ℝ) ^ (m + 1)
    let b := 2 * (Real.exp (1 / 3 : ℝ) - 1)
    let r := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
      Real.log (Real.log (1 + xi / W))) / (-Real.log b)⌉₊
    ∃ A : Fin (N + 1) → MPOTensor q ((r ^ 2 * q ^ r) * (m + 1)),
      ‖cfc (Real.softTruncation t m) ((∑ i, h i) - (eps : ℂ) • 1) -
        MPOTensor.traceChainOperator A 1‖ ≤ xi := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have ht : 0 < t := lt_of_lt_of_le (by positivity) hscale
  have hratio : (m : ℝ) / t ≤ 1 / 3 := (div_le_iff₀ ht).mpr (by linarith only [hscale])
  have hb := softHeat_base_bounds
  exact exists_softTruncation_mpo_of_accuracy_of_base hq h hs hh hnorm eps t xi _ hlo ht hxi
    hb.1 hb.2 (mul_le_mul_of_nonneg_left
      (sub_le_sub_right (Real.exp_le_exp.mpr hratio) 1) (by norm_num))

end TNLean.MPS.AreaLaw

end

section

open Matrix Finset
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.MPS.AreaLaw

/-- A selected regional soft replacement and its exact exterior have actual operator tensors
at every prescribed accuracy, with the logarithmic cluster order built from any base `b`
dominating the largest heat-time base `2 (e^{m/t} - 1)`. Supporting a corrected ALVV,
arXiv:1602.08828v2, `def:soft-trunc` and `lem:exp-approx-eff`, lines 1178–1185 and 1262–1268. -/
theorem exists_softTruncatedHamiltonian_mpo_of_accuracy_of_base {N q m : ℕ}
    (hq : 1 ≤ q)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
      (h i) {i.castSucc, i.succ})
    (hh : ∀ i, (h i).IsHermitian) (hnorm : ∀ i, ‖h i‖ ≤ 1)
    (I : Finset (Fin N)) (eps t xi : ℝ) (hlo : (eps : ℂ) • 1 ≤ ∑ i ∈ I, h i)
    (b : ℝ) (ht : 0 < t) (hxi : 0 < xi) (hb0 : 0 < b) (hb1 : b < 1)
    (hbase : 2 * (Real.exp ((m : ℝ) / t) - 1) ≤ b) :
    let W := t * (2 : ℝ) ^ (m + 1)
    let r := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
      Real.log (Real.log (1 + xi / W))) / (-Real.log b)⌉₊
    ∃ A : Fin (N + 1) → MPOTensor q
        ((1 + N * q ^ 2) + (r ^ 2 * q ^ r) * (m + 1)),
      ‖((∑ i, h i) - (∑ i ∈ I, h i) + (eps : ℂ) • 1 +
          cfc (Real.softTruncation t m)
            ((∑ i ∈ I, h i) - (eps : ℂ) • 1)) -
        MPOTensor.traceChainOperator A 1‖ ≤ xi := by
  classical
  intro W r
  let g : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ :=
    fun i ↦ if i ∈ I then h i else 0
  have hgs (i : Fin N) : ManyBody.IsSupportedOn (g i) {i.castSucc, i.succ} := by
    by_cases hi : i ∈ I
    · simpa only [g, ite_eq_left hi] using hs i
    · simp [g, hi, ManyBody.IsSupportedOn, ManyBody.IsSupportedOn]
  have hgh (i : Fin N) : (g i).IsHermitian := by
    by_cases hi : i ∈ I <;> simp [g, hi, hh i]
  have hgn (i : Fin N) : ‖g i‖ ≤ 1 := by
    by_cases hi : i ∈ I <;> simp [g, hi, hnorm i]
  have hgsum : (∑ i, g i) = ∑ i ∈ I, h i := by simp [g]
  obtain ⟨A, hA⟩ := exists_softTruncation_mpo_of_accuracy_of_base hq g hgs hgh hgn eps t xi b
    (by simpa only [hgsum] using hlo) ht hxi hb0 hb1 hbase
  rw [hgsum] at hA
  let f : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ :=
    fun i ↦ if i ∈ Iᶜ then h i else 0
  have hfs (i : Fin N) : ManyBody.IsSupportedOn (f i) {i.castSucc, i.succ} := by
    by_cases hi : i ∈ Iᶜ
    · simpa only [f, ite_eq_left hi] using hs i
    · have hiI : i ∈ I := by simpa using hi
      simp [f, hiI, ManyBody.IsSupportedOn, ManyBody.IsSupportedOn]
  have hfsum : (∑ i, f i) = ∑ i ∈ Iᶜ, h i := by
    simp only [f, Finset.sum_ite_mem, Finset.univ_inter]
  have hcomp : (∑ i ∈ Iᶜ, h i) = (∑ i, h i) - ∑ i ∈ I, h i :=
    eq_sub_iff_add_eq.mpr (Finset.sum_compl_add_sum I h)
  obtain ⟨B, hB⟩ := exists_local_sum_add_scalar_mpo hq f hfs (eps : ℂ)
  rw [hfsum, hcomp] at hB
  obtain ⟨C, hC⟩ := MPOTensor.exists_traceChainOperator_add (by omega) B A
  refine ⟨C, ?_⟩
  rw [← hC, ← hB]
  convert hA using 1
  congr 1
  abel

/-- A selected regional soft replacement and its exact exterior have actual operator tensors
at every prescribed accuracy. The cluster order is an explicit logarithmic ceiling, and no
heat approximation or representation is supplied. Supporting a corrected ALVV,
arXiv:1602.08828v2, `def:soft-trunc` and `lem:exp-approx-eff`, lines 1178–1185 and 1262–1268. -/
theorem exists_softTruncatedHamiltonian_mpo_of_accuracy {N q m : ℕ}
    (hq : 1 ≤ q) (hm : 0 < m)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
      (h i) {i.castSucc, i.succ})
    (hh : ∀ i, (h i).IsHermitian) (hnorm : ∀ i, ‖h i‖ ≤ 1)
    (I : Finset (Fin N)) (eps t xi : ℝ) (hlo : (eps : ℂ) • 1 ≤ ∑ i ∈ I, h i)
    (hscale : 3 * (m : ℝ) ≤ t) (hxi : 0 < xi) :
    let W := t * (2 : ℝ) ^ (m + 1)
    let b := 2 * (Real.exp (1 / 3 : ℝ) - 1)
    let r := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
      Real.log (Real.log (1 + xi / W))) / (-Real.log b)⌉₊
    ∃ A : Fin (N + 1) → MPOTensor q
        ((1 + N * q ^ 2) + (r ^ 2 * q ^ r) * (m + 1)),
      ‖((∑ i, h i) - (∑ i ∈ I, h i) + (eps : ℂ) • 1 +
          cfc (Real.softTruncation t m)
            ((∑ i ∈ I, h i) - (eps : ℂ) • 1)) -
        MPOTensor.traceChainOperator A 1‖ ≤ xi := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have ht : 0 < t := lt_of_lt_of_le (by positivity) hscale
  have hratio : (m : ℝ) / t ≤ 1 / 3 := (div_le_iff₀ ht).mpr (by linarith only [hscale])
  have hb := softHeat_base_bounds
  exact exists_softTruncatedHamiltonian_mpo_of_accuracy_of_base hq h hs hh hnorm I eps t xi hlo _
    ht hxi hb.1 hb.2 (mul_le_mul_of_nonneg_left
      (sub_le_sub_right (Real.exp_le_exp.mpr hratio) 1) (by norm_num))

end TNLean.MPS.AreaLaw

end

section

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
    (hs : ∀ i, ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
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
  have hf (i : Fin N) : ManyBody.IsSupportedOn (f i) {i.castSucc, i.succ} := by
    change _ ∈ ManyBody.supportedOperators _ _
    exact (SMulMemClass.smul_mem c (hs i))
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

end

section

open Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.MPS.AreaLaw

/-- A selected family of the original regional sums has an actual Hermitian MPO
approximation. The same finite partial-replacement sum is represented; no regional MPO or
rank estimate is supplied. Auxiliary to ALVV, arXiv:1602.08828v2, `t:aisefficient`,
lines 1373–1392. -/
theorem exists_selected_regional_softTruncations_hermitian_mpo_of_accuracy
    {N q m v : ℕ} (hq : 1 ≤ q) (hm : 0 < m)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
      (h i) {i.castSucc, i.succ})
    (hh : ∀ i, (h i).IsHermitian) (hnorm : ∀ i, ‖h i‖ ≤ 1)
    (I : Fin v → Finset (Fin N)) (p : Fin v → ℝ) (S : Finset (Fin v))
    (t xi z : ℝ) (hlo : ∀ j ∈ S, (p j : ℂ) • 1 ≤ ∑ i ∈ I j, h i)
    (hscale : 3 * (m : ℝ) ≤ t) (hxi : 0 < xi) :
    let R := fun j ↦ ∑ i ∈ I j, h i
    let G := (∑ i, h i) + (z : ℂ) • 1 + ∑ j ∈ S, ((p j : ℂ) • 1 +
      cfc (Real.softTruncation t m) (R j - (p j : ℂ) • 1) - R j)
    let delta := xi / (max 1 S.card : ℕ)
    let W := t * (2 : ℝ) ^ (m + 1)
    let b := 2 * (Real.exp (1 / 3 : ℝ) - 1)
    let r := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
      Real.log (Real.log (1 + delta / W))) / (-Real.log b)⌉₊
    let D0 := 1 + N * q ^ 2
    let D := D0 + ((D0 + (r ^ 2 * q ^ r) * (m + 1)) * 2) * S.card
    ∃ T : Fin (N + 1) → MPOTensor q D,
      G.IsHermitian ∧ (MPOTensor.traceChainOperator T 1).IsHermitian ∧
      ‖G - MPOTensor.traceChainOperator T 1‖ ≤ xi := by
  classical
  intro R G delta W b r D0 D
  let sel := S.equivFin.symm
  let I' := fun j : Fin S.card ↦ I (sel j).val
  let p' := fun j : Fin S.card ↦ p (sel j).val
  obtain ⟨T, hG, hT, herr⟩ := exists_regional_softTruncations_hermitian_mpo_of_accuracy
    hq hm h hs hh hnorm I' p' t xi z (fun j ↦ hlo (sel j).val (sel j).property)
      hscale hxi
  let F := fun j : Fin v ↦ (p j : ℂ) • 1 +
    cfc (Real.softTruncation t m) (R j - (p j : ℂ) • 1) - R j
  have hsum : (∑ j : Fin S.card, F (sel j).val) = ∑ j ∈ S, F j := by
    rw [← S.sum_attach]
    simpa only [Finset.attach_eq_univ] using
      (S.equivFin.symm.sum_comp (fun j : S ↦ F j.val))
  have hmatrix : (∑ i, h i) + (z : ℂ) • 1 + ∑ j : Fin S.card,
      ((p' j : ℂ) • 1 + cfc (Real.softTruncation t m)
        ((∑ i ∈ I' j, h i) - (p' j : ℂ) • 1) - ∑ i ∈ I' j, h i) = G := by
    change (∑ i, h i) + (z : ℂ) • 1 + (∑ j : Fin S.card, F (sel j).val) = G
    rw [hsum]
  refine ⟨T, ?_, hT, ?_⟩
  · rw [← hmatrix]
    exact hG
  · rw [← hmatrix]
    exact herr

end TNLean.MPS.AreaLaw

end

end SoftTruncationMPOAccuracy

section RegionalSoftSpectralApproximation

/-!
## Buffered spectral comparison for actual regional soft approximations

One Hermitian matrix product operator is constructed before every energy cutoff and buffer.
Its global operator-norm approximation gives both directed low-energy comparisons, with
no assumption on the intervening spectrum. This is an auxiliary for ALVV,
arXiv:1602.08828v2, `t:aisefficient` and `t:aisgaplessefficient`, lines 1412–1420 and 1446–1457.

**Local fix (cluster estimate and parameters):** the representation uses the corrected
interaction-label cluster estimate and independent scale at least three times order.
The comparison concerns the actual regional soft sum and its represented approximant;
it does not establish the paper's final GEN bounds or its comparison with the original
Hamiltonian. See `docs/paper-gaps/alvv16_cluster_approximation.tex`.
-/

open Matrix Finset
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.MPS.AreaLaw

/-- Actual regional soft replacements have one Hermitian approximating MPO whose buffered
spectral comparisons hold simultaneously for all cutoffs and positive buffers. The tensors
are chosen before those cutoffs, buffers and vectors. Auxiliary to ALVV,
arXiv:1602.08828v2, `t:aisefficient` and `t:aisgaplessefficient`, lines 1412–1420 and 1446–1457. -/
theorem exists_regional_softTruncations_mpo_buffered_spectral_comparison {N q m s : ℕ}
    (hq : 1 ≤ q) (hm : 0 < m)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
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
      ∃ hG : G.IsHermitian, ∃ hT : (MPOTensor.traceChainOperator T 1).IsHermitian,
        ‖G - MPOTensor.traceChainOperator T 1‖ ≤ xi ∧
        ∀ c w : ℝ, 0 < w →
          let U := ‖G‖ + xi
          let a := min (c - 1) (-U)
          let n := ⌈(c - a) / (2 * xi)⌉₊
          let loss := (n : ℝ) * (2 * xi) ^ 2 / (w + xi) ^ 2
          Submodule.IsCloseTo loss
            (Submodule.spectralSpanLE hT.eigenvectorBasis hT.eigenvalues (c + w))
            (Submodule.spectralSpanLE hG.eigenvectorBasis hG.eigenvalues c) ∧
          Submodule.IsCloseTo loss
            (Submodule.spectralSpanLE hG.eigenvectorBasis hG.eigenvalues (c + w))
            (Submodule.spectralSpanLE hT.eigenvectorBasis hT.eigenvalues c) := by
  classical
  intro H R G delta W b r D0 D
  obtain ⟨T, hG, hT, herr⟩ :=
    exists_regional_softTruncations_hermitian_mpo_of_accuracy
      hq hm h hs hh hnorm I eps t xi z hlo hscale hxi
  refine ⟨T, hG, hT, herr, ?_⟩
  intro c w hw
  exact hG.isCloseTo_spectralSpanLE_pair_of_norm_sub_le hT c xi w hxi hw herr

end TNLean.MPS.AreaLaw

end RegionalSoftSpectralApproximation

section PhysicalSoftTruncationMPOApproximation

/-!
## Physical spectral windows and an actual soft-truncation MPO at one parameter choice

The order is chosen before every physical Hamiltonian. The actual soft replacement has both
proved spectral-window comparisons and constructed operator tensors at any requested norm
accuracy, with a logarithmic cluster order. Supporting the corrected moment and label routes to
ALVV, arXiv:1602.08828v2, `lem:exp-approx` and `lem:exp-approx-eff`, lines 1195–1268.

**Local fix (parameters and corrected estimates):** scale is three times order. The proof uses
the corrected exponential-moment residual and interaction-label cluster estimate. Neither
false printed estimate nor a computational running time is asserted; see
`docs/paper-gaps/alvv16_soft_truncation_energy_estimate.tex` and
`docs/paper-gaps/alvv16_cluster_approximation.tex`.

**Scope restriction (scale three times the order):** ALVV `lem:exp-approx-eff`, lines
1262–1268, allows any scale with `t′ < (ln 2/2) t`; this module takes `t = 3m`, a sub-case of
that range. See `docs/paper-gaps/alvv16_cluster_approximation.tex`.
-/

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- One physical soft Hamiltonian has the two directed spectral comparisons and an actual
operator-chain approximation at every norm accuracy. The regional and ground data, order and
cluster budget are constructed; no heat, residual, closeness or MPO family is supplied.
Supporting the corrected ALVV route, arXiv:1602.08828v2, `lem:exp-approx` and
`lem:exp-approx-eff`, lines 1195–1268. -/
theorem exists_interval_physical_soft_closeness_and_mpo
    (eta w delta : ℝ) (heta : 0 < eta) (hw : 0 < w) (hdelta : 0 < delta) :
    let rho := min 1 (min (w / 2) (delta * w ^ 2 / (2 * (eta + 2))))
    ∃ m : ℕ, m = ⌈12 + (2 / 3 : ℝ) * eta + (16 / 3 : ℝ) * Real.log (80 / rho)⌉₊ ∧ 0 < m ∧
      ∀ (N q p v : ℕ) (hq : 0 < q) (_hpr : p ≤ v) (_hrL : v ≤ (N + 1))
        (Φ : ManyBody.BondInteraction (N + 1) q),
        (∀ i, 0 ≤ Φ.term i) → (∀ i, Φ.term i ≤ 1) →
        let : Nonempty (Fin (N + 1) → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
        let k : Fin 6 → ℕ := ![0, p, v, v, v, (N + 1)]
        let A : Fin 5 → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ := fun j ↦
          ∑ i ∈ Finset.univ.filter
            (fun i : Fin N ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), Φ.term i
        ∃ (e : Fin 5 → ℝ) (E0 : ℝ) (x : (Fin (N + 1) → Fin q) → ℂ),
          let H := Φ.hamiltonian
          let Hc := H - (((∑ j, e j) : ℝ) : ℂ) • 1
          ∃ hHc : Hc.IsHermitian,
            star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
            (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
            E0 = minEigenvalue hHc ∧ 0 ≤ E0 ∧ E0 ≤ 2 ∧
            ∀ eps : ℝ, e 1 - 10 ≤ eps → eps ≤ e 1 →
              let Hsoft := H - A 1 + (eps : ℂ) • 1 +
                cfc (Real.softTruncation (3 * (m : ℝ)) m) (A 1 - (eps : ℂ) • 1)
              let Hsc := Hsoft - (((∑ j, e j) : ℝ) : ℂ) • 1
              ∃ (Es : ℝ) (hHsc : Hsc.IsHermitian),
                Es = minEigenvalue hHsc ∧ Hsoft ≤ H ∧
                0 ≤ E0 - Es ∧ E0 - Es ≤ rho ∧
                Submodule.IsCloseTo delta
                  (Submodule.spectralSpanLE hHsc.eigenvectorBasis hHsc.eigenvalues
                    (Es + eta + w))
                  (Submodule.spectralSpanLE hHc.eigenvectorBasis hHc.eigenvalues
                    (E0 + eta)) ∧
                Submodule.IsCloseTo delta
                  (Submodule.spectralSpanLE hHc.eigenvectorBasis hHc.eigenvalues
                    (E0 + eta + w))
                  (Submodule.spectralSpanLE hHsc.eigenvectorBasis hHsc.eigenvalues
                    (Es + eta)) ∧
                ∀ (xi : ℝ), 0 < xi →
                  let W := 3 * (m : ℝ) * (2 : ℝ) ^ (m + 1)
                  let b := 2 * (Real.exp (1 / 3 : ℝ) - 1)
                  let ell := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
                    Real.log (Real.log (1 + xi / W))) / (-Real.log b)⌉₊
                  ∃ T : Fin (N + 1) → MPOTensor q
                      ((1 + N * q ^ 2) + (ell ^ 2 * q ^ ell) * (m + 1)),
                    ‖Hsoft - MPOTensor.traceChainOperator T 1‖ ≤ xi := by
  intro rho
  obtain ⟨m, hmformula, hm, hphysical⟩ :=
    exists_interval_physical_scaled_soft_low_energy_closeness eta w delta heta hw hdelta
  refine ⟨m, hmformula, hm, ?_⟩
  intro N q p v hq hpv hvL Φ h0 h1 _inst k A
  obtain ⟨e, E0, x, hO, hxunit, hx, he, hEcan, hE0, hE2, hclose⟩ :=
    hphysical (N + 1) q p v hq hpv hvL Φ h0 h1
  refine ⟨e, E0, x, hO, hxunit, hx, he, hEcan, hE0, hE2, ?_⟩
  intro eps hepslo hepshi Hsoft Hsc
  obtain ⟨Es, hS, hEscan, hsoftH, hshift0, hshift, hforward, hreverse⟩ :=
    hclose eps hepslo hepshi
  refine ⟨Es, hS, hEscan, hsoftH, hshift0, hshift, hforward, hreverse, ?_⟩
  intro xi hxi W b ell
  classical
  let I : Finset (Fin N) := Finset.univ.filter
    (fun i ↦ p ≤ i.val ∧ i.val + 1 < v)
  have hI : (∑ i ∈ I, Φ.term i) = A 1 := by rfl
  have hs' (i : Fin N) : ManyBody.IsSupportedOn (Φ.term i) {i.castSucc, i.succ} :=
    Φ.term_mem_supportedOperators_chainBond i
  have hh (i : Fin N) : (Φ.term i).IsHermitian := (IsSelfAdjoint.of_nonneg (h0 i)).isHermitian
  have hn (i : Fin N) : ‖Φ.term i‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (h0 i)).mpr (h1 i)
  have heps : (eps : ℂ) • (1 : Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ) ≤ A 1 := by
    have heA : (A 1 - (e 1 : ℂ) • 1).PosSemidef := he 1
    have hmin : (e 1 : ℂ) • 1 ≤ A 1 := Matrix.le_iff.mpr heA
    have hlower : eps • (1 : Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ) ≤
        (e 1 : ℝ) • 1 :=
      smul_le_smul_of_nonneg_right hepshi zero_le_one
    have hlowerC : (eps : ℂ) • (1 : Matrix (Fin (N + 1) → Fin q)
        (Fin (N + 1) → Fin q) ℂ) ≤ (e 1 : ℂ) • 1 := by
      simpa only [Complex.coe_smul] using hlower
    exact hlowerC.trans hmin
  obtain ⟨T, hT⟩ := exists_softTruncatedHamiltonian_mpo_of_accuracy (N := N) hq hm Φ.term hs'
    hh hn I eps
    (3 * (m : ℝ)) xi (by simpa only [hI] using heps) le_rfl hxi
  refine ⟨T, ?_⟩
  rw [hI] at hT
  exact hT

end TNLean.MPS.AreaLaw

end PhysicalSoftTruncationMPOApproximation
