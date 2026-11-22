/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.EmbeddedC2
import TNLean.MPS.ParentHamiltonian.Martingale.FixedAmbientMartingaleBound
import QICLean.ManyBody.Hamiltonian.Martingale.NachtergaeleFullRangeEstimate

/-!
# Uniform gap for the nonwrapping open MPS parent Hamiltonian

This file specializes the full-range C1--C3 martingale estimate to the canonical
nonwrapping open parent Hamiltonian.  For interaction length \(L=l+1\), the
source constants are
\[
  d_{l+1}=1,\qquad \gamma_{l+1}=1,
\]
while condition C3 keeps the same coefficient \(\epsilon_l\).  Hence the gap
coefficient is exactly
\[
  (1-\epsilon_l\sqrt{l+1})^2.
\]

**Scope restriction (full-range martingale hypotheses):** The abstract
full-range theorem assumes C1--C3 at every index \(n=0,\ldots,N-1\), which is
stronger than the lower-threshold hypotheses in the source.  Here the extra
early indices are harmless: before a complete length-\(l+1\) interaction fits,
the suffix Hamiltonian vanishes, its kernel projection is the identity, and
the fixed-ambient martingale difference vanishes.  At the first complete
window, the fixed-volume C3 product vanishes by the endpoint projector
identity.  The distinction between the abstract restriction and this physical
discharge is recorded in
`docs/paper-gaps/cpgsv21_martingale_overlap.tex`.

## References

* Nachtergaele, arXiv:cond-mat/9410110, conditions C1--C3, lines 1030--1094.
* Nachtergaele, arXiv:cond-mat/9410110, Theorem 2.1(i), lines 1119--1130,
  and proof lines 1195--1259.
-/

open scoped BigOperators ComplexOrder InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

/-- The Hamiltonian of an interval of exactly the interaction length vanishes before its window
fits. This supplies the early-index part of the full-range C1 and C2 hypotheses. -/
theorem hamiltonian_restrict_parentChainInteraction_eq_zero_of_lt
    (A : MPSTensor d D) {L N n : ℕ} (hnL : n < L) :
    ((parentChainInteraction A L N).restrict
      fun i ↦ n - L ≤ i.val ∧ i.val + L ≤ n).hamiltonian = 0 := by
  rw [ManyBody.Interaction.hamiltonian_restrict,
    Finset.filter_false_of_mem fun i _ ↦ by omega, ManyBody.Interaction.partialHamiltonian_empty]

/-- Shifting the full filtration range by one gives the C1 sum over intervals. Terms
before the first complete length-\(L\) window are zero. -/
theorem sum_range_hamiltonian_restrict_parentChainInteraction_succ_eq_Icc
    (A : MPSTensor d D) {L N : ℕ} (hL : 0 < L) :
    ∑ n ∈ Finset.range N, ((parentChainInteraction A L N).restrict
        fun i ↦ n + 1 - L ≤ i.val ∧ i.val + L ≤ n + 1).hamiltonian =
      ∑ n ∈ Finset.Icc L N, ((parentChainInteraction A L N).restrict
        fun i ↦ n - L ≤ i.val ∧ i.val + L ≤ n).hamiltonian := by
  let f := fun n ↦ ((parentChainInteraction A L N).restrict
    fun i ↦ n - L ≤ i.val ∧ i.val + L ≤ n).hamiltonian
  have hshift :
      ∑ n ∈ Finset.range N, f (n + 1) = ∑ n ∈ Finset.Icc 1 N, f n := by
    apply Finset.sum_bij (fun n _ ↦ n + 1)
    · intro n hn
      simp only [Finset.mem_range] at hn
      simp only [Finset.mem_Icc]
      omega
    · intro n₁ hn₁ n₂ hn₂ h
      omega
    · intro m hm
      simp only [Finset.mem_Icc] at hm
      refine ⟨m - 1, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · omega
    · intro n hn
      rfl
  have htrim :
      ∑ n ∈ Finset.Icc L N, f n = ∑ n ∈ Finset.Icc 1 N, f n := by
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_Icc] at hn ⊢
      omega
    · intro n hn hnL
      simp only [Finset.mem_Icc] at hn hnL
      exact hamiltonian_restrict_parentChainInteraction_eq_zero_of_lt A (by omega)
  exact hshift.trans htrim.symm

/-- Full-range C1 for intervals of exactly the interaction length \(L\), with the source
counting constant \(d_L=1\). The range indices are shifted because the local Hamiltonian at
martingale index \(n\) acts on \([n+1-L,n+1)\). Nachtergaele, arXiv:cond-mat/9410110, condition
C1, lines 1030--1041. -/
theorem parentChainInteraction_C1_full_range_quadratic_form
    (A : MPSTensor d D) {L N : ℕ} (hL : 0 < L) (x : EuclideanSpace ℂ (Cfg d N)) :
    0 ≤ ∑ n ∈ Finset.range N,
        (⟪Matrix.toEuclideanLin ((parentChainInteraction A L N).restrict
          fun i ↦ n + 1 - L ≤ i.val ∧ i.val + L ≤ n + 1).hamiltonian x, x⟫_ℂ).re ∧
      (∑ n ∈ Finset.range N,
        (⟪Matrix.toEuclideanLin ((parentChainInteraction A L N).restrict
          fun i ↦ n + 1 - L ≤ i.val ∧ i.val + L ≤ n + 1).hamiltonian x, x⟫_ℂ).re) ≤
        (⟪Matrix.toEuclideanLin (parentChainInteraction A L N).hamiltonian x, x⟫_ℂ).re := by
  have hC1 := (parentChainInteraction_C1 A (le_refl L) N).2
  rw [Nat.sub_self, zero_add, Nat.cast_one, one_smul,
    ← sum_range_hamiltonian_restrict_parentChainInteraction_succ_eq_Icc A hL,
    ← Matrix.toEuclideanLin_le_toEuclideanLin_iff, map_sum] at hC1
  refine ⟨Finset.sum_nonneg fun n _ ↦ (Matrix.isPositive_toEuclideanLin_iff.mpr
    (posSemidef_hamiltonian_restrict_parentChainInteraction A L N _)).2 x, ?_⟩
  have hx := ((LinearMap.le_def ..).mp hC1).2 x
  rw [LinearMap.sub_apply, inner_sub_left, map_sub, LinearMap.sum_apply, sum_inner,
    map_sum] at hx
  exact sub_nonneg.mp hx

/-- Full-range norm-square form of C2 with \(\gamma_L=1\) for an interval of exactly the
interaction length. Before the window fits both sides vanish; once it fits, the interval
Hamiltonian is the orthogonal projection \(I-Q\) onto the complement of its kernel.
Nachtergaele, arXiv:cond-mat/9410110, condition C2, lines 1045--1056. -/
theorem parentChainInteraction_C2_full_range_norm_sq
    (A : MPSTensor d D) {L N n : ℕ} (hnN : n ≤ N) (x : EuclideanSpace ℂ (Cfg d N)) :
    ‖((LinearMap.id : EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N)) -
        (LinearMap.ker (Matrix.toEuclideanLin ((parentChainInteraction A L N).restrict
          fun i ↦ n - L ≤ i.val ∧ i.val + L ≤ n).hamiltonian)).starProjection.toLinearMap)
          x‖ ^ 2 ≤
      (⟪Matrix.toEuclideanLin ((parentChainInteraction A L N).restrict
        fun i ↦ n - L ≤ i.val ∧ i.val + L ≤ n).hamiltonian x, x⟫_ℂ).re := by
  by_cases hnL : n < L
  · rw [hamiltonian_restrict_parentChainInteraction_eq_zero_of_lt A hnL, map_zero,
      LinearMap.ker_zero, Submodule.starProjection_top']
    norm_num
  · have hLn : L ≤ n := by omega
    have hH := Matrix.isSymmetricProjection_toEuclideanLin_iff.mpr
      (isStarProjection_hamiltonian_restrict_parentChainInteraction A hLn hnN)
    rw [← toEuclideanLin_hamiltonian_restrict_parentChainInteraction_eq_id_sub_starProjection
      A hLn hnN]
    generalize Matrix.toEuclideanLin ((parentChainInteraction A L N).restrict
      fun i ↦ n - L ≤ i.val ∧ i.val + L ≤ n).hamiltonian = H at hH ⊢
    have hIdem : H (H x) = H x := LinearMap.congr_fun hH.isIdempotentElem.eq x
    calc ‖H x‖ ^ 2 = (⟪H x, H x⟫_ℂ).re := (inner_self_eq_norm_sq (𝕜 := ℂ) (H x)).symm
      _ = (⟪H (H x), x⟫_ℂ).re := by rw [hH.isSymmetric (H x) x]
      _ ≤ (⟪H x, x⟫_ℂ).re := by rw [hIdem]

/-- Fixed-parameter open-chain gap obtained from the fixed-ambient C3 bound: every eigenvalue
of the open-chain parent Hamiltonian is `0` or at least \((1-\epsilon_l\sqrt{l+1})^2\). For
\(L=l+1\), conditions C1 and C2 have constants one. Nachtergaele, arXiv:cond-mat/9410110,
Theorem 2.1(i), lines 1119--1130. -/
theorem hamiltonian_parentChainInteraction_gap_of_fixedAmbient_c3
    (A : MPSTensor d D) {l N : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hεlt : ε < 1 / Real.sqrt ((l + 1 : ℕ) : ℝ))
    (hC3 : ∀ n ∈ Finset.range N,
      ‖LinearMap.toContinuousLinearMap
        ((openIntervalGroundProjectionES A (l + 1) l N n).comp
          ((fixedAmbientNestedGroundProjectionsES A (l + 1) N).martingaleDifference n))‖ ≤ ε) :
    ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction A (l + 1) N).hamiltonian) μ →
        μ = 0 ∨ (((1 - ε * Real.sqrt ((l + 1 : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ) ≤ μ := by
  let G := fixedAmbientNestedGroundProjectionsES A (l + 1) N
  let Q := fun n ↦ openIntervalGroundProjectionES A (l + 1) l N n
  let localHamiltonian := fun n ↦ Matrix.toEuclideanLin
    ((parentChainInteraction A (l + 1) N).restrict
      fun i ↦ n + 1 - (l + 1) ≤ i.val ∧ i.val + (l + 1) ≤ n + 1).hamiltonian
  let H := Matrix.toEuclideanLin (parentChainInteraction A (l + 1) N).hamiltonian
  have hzero : G.projection 0 = LinearMap.id := by
    change openPrefixGroundProjectionES A (l + 1) N 0 =
      (1 : EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N))
    exact openPrefixGroundProjectionES_eq_one_of_lt A (N := N) (by omega)
  have hQ : ∀ n ∈ Finset.range N, (Q n).IsSymmetricProjection := by
    intro n hn
    exact Submodule.isSymmetricProjection_starProjection _
  have hcomm : ∀ n ∈ Finset.range N, ∀ m,
      m < n - l ∨ n < m →
        (G.martingaleDifference m).comp (Q n) =
          (Q n).comp (G.martingaleDifference m) := by
    intro n hn m hout
    exact fixedAmbient_martingaleDifference_commute_openIntervalGroundProjectionES
      A hout
  have hground : LinearMap.range (G.projection N) = LinearMap.ker H := by
    change LinearMap.range (openPrefixGroundProjectionES A (l + 1) N N) = LinearMap.ker H
    simp only [openPrefixGroundProjectionES, Submodule.range_starProjection]
    rw [hamiltonian_prefix_parentChainInteraction_self_eq_hamiltonian_parentChainInteraction]
  have hgap :=
    FrustrationFree.NestedGroundProjections.norm_lower_bound_of_nachtergaele_c1_c3_full_range
      G Q localHamiltonian H N l hzero
      (γ := (1 : ℝ)) (d := (1 : ℝ)) (ε := ε)
      (by norm_num) (by norm_num) hε hεlt hQ hcomm
      (fun x ↦ by
        simpa only [localHamiltonian, H, one_mul] using
          parentChainInteraction_C1_full_range_quadratic_form A (Nat.succ_pos l) x)
      (fun n hn x ↦ by
        simpa only [localHamiltonian, Q, one_mul, openIntervalGroundProjectionES] using
          parentChainInteraction_C2_full_range_norm_sq A
            (Nat.succ_le_of_lt (Finset.mem_range.mp hn)) x)
      hC3 (Matrix.isPositive_toEuclideanLin_iff.mpr
        (posSemidef_hamiltonian_parentChainInteraction A (l + 1) N)) hground
  refine (ManyBody.forall_hasEigenvalue_iff_norm
    (posSemidef_hamiltonian_parentChainInteraction A (l + 1) N)).mpr ?_
  simpa only [H, div_one, one_mul] using hgap

/-- A primitive MPS has a uniform gap of its open-chain parent Hamiltonians: every eigenvalue
is `0` or at least \((1-\epsilon_l\sqrt{l+1})^2\). The witnesses use the same \(l\) and
\(\epsilon_l\) as the physical C3 estimate, uniformly for every \(N\) with \(l+1\leq N\).
Nachtergaele, arXiv:cond-mat/9410110, Theorem 2.1(i), lines 1119--1130. -/
theorem _root_.Kraus.HasComplementaryFixedPointGap.exists_hamiltonian_parentChainInteraction_gap
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : Kraus.HasComplementaryFixedPointGap A ρ) (hρ : ρ.PosDef) :
    ∃ l : ℕ, ∃ ε : ℝ, ∃ _hl : 1 < l, ∃ _hInj : Kraus.IsNBlkInjective A l,
      0 ≤ ε ∧ ε < 1 / Real.sqrt ((l + 1 : ℕ) : ℝ) ∧
      ∀ N : ℕ, l + 1 ≤ N → ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentChainInteraction A (l + 1) N).hamiltonian) μ →
          μ = 0 ∨ (((1 - ε * Real.sqrt ((l + 1 : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ) ≤ μ := by
  obtain ⟨l, ε, hl, hInj, hε, hεlt, hC3⟩ :=
    hP.exists_fixedAmbient_martingaleDifference_norm_lt_c3_threshold hρ
  exact ⟨l, ε, hl, hInj, hε, hεlt, fun N _ ↦
    hamiltonian_parentChainInteraction_gap_of_fixedAmbient_c3 A hε hεlt
      fun n hn ↦ hC3 N n (Finset.mem_range.mp hn)⟩

end MPSTensor
