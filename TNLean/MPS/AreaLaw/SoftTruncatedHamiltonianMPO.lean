/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SoftTruncationMPOAccuracy
import TNLean.MPS.AreaLaw.LocalSumMPO

/-!
# The actual soft-truncated Hamiltonian as an approximated operator chain

The selected regional terms are masked from the original nearest-neighbour family. The exterior
sum and scalar are represented exactly, and added to the directly constructed heat sum.
Supporting a corrected ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268.

**Local fix (cutoff and parameter choice):** this is the corrected interaction-label construction
at scale at least three times the order, with the original local terms and scalar shift kept
separate. It asserts no computational running time; see
`docs/paper-gaps/alvv16_cluster_approximation.tex`.

**Scope restriction (scale at least three times the order):** ALVV `lem:exp-approx-eff`, lines
1262–1268, allows any scale with `t′ < (ln 2/2) t`; this module takes `t ≥ 3m`, a sub-case of
that range. See `docs/paper-gaps/alvv16_cluster_approximation.tex`.
-/

open Matrix Finset
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.MPS.AreaLaw

/-- A selected regional soft replacement and its exact exterior have actual operator tensors
at every prescribed accuracy. The cluster order is an explicit logarithmic ceiling, and no
heat approximation or representation is supplied. Supporting a corrected ALVV,
arXiv:1602.08828v2, `def:soft-trunc` and `lem:exp-approx-eff`, lines 1178–1185 and 1262–1268. -/
theorem exists_softTruncatedHamiltonian_mpo_of_accuracy {N q m : ℕ}
    (hq : 1 ≤ q) (hm : 0 < m)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
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
  classical
  intro W b r
  let g : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ :=
    fun i ↦ if i ∈ I then h i else 0
  have hgs (i : Fin N) : Entropy.IsSupportedOn (g i) {i.castSucc, i.succ} := by
    by_cases hi : i ∈ I
    · simpa only [g, ite_eq_left hi] using hs i
    · simp [g, hi, Entropy.IsSupportedOn]
  have hgh (i : Fin N) : (g i).IsHermitian := by
    by_cases hi : i ∈ I <;> simp [g, hi, hh i]
  have hgn (i : Fin N) : ‖g i‖ ≤ 1 := by
    by_cases hi : i ∈ I <;> simp [g, hi, hnorm i]
  have hgsum : (∑ i, g i) = ∑ i ∈ I, h i := by simp [g]
  obtain ⟨A, hA⟩ := exists_softTruncation_mpo_of_accuracy hq hm g hgs hgh hgn eps t xi
    (by simpa only [hgsum] using hlo) hscale hxi
  rw [hgsum] at hA
  let f : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ :=
    fun i ↦ if i ∈ Iᶜ then h i else 0
  have hfs (i : Fin N) : Entropy.IsSupportedOn (f i) {i.castSucc, i.succ} := by
    by_cases hi : i ∈ Iᶜ
    · simpa only [f, ite_eq_left hi] using hs i
    · have hiI : i ∈ I := by simpa using hi
      simp [f, hiI, Entropy.IsSupportedOn]
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

end TNLean.MPS.AreaLaw
