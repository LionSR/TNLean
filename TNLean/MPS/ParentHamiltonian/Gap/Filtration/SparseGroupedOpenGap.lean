/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Gap.Filtration.GroupedProjectorEstimate
import TNLean.MPS.ParentHamiltonian.ParentInteraction.EmbeddedC2

/-!
# Sparse grouped open-chain energy bounds

Sampling the range-\(2p\) interactions at starts \(0,p,2p,\ldots\)
retains the grouped martingale energy estimate with coefficient
\((1-\epsilon\sqrt2)^2\). The estimate controls the orthogonal
complement of the full prefix ground space. One additional terminal
interaction covers a residual interval without counting any local term twice.

These are quantitative consequences of Nachtergaele,
arXiv:cond-mat/9410110, Theorem 2.1(ii), lines 1131--1136, and the
three-interval projector estimate of Section 6, Lemma `commutation` (ii).
-/

open scoped BigOperators ComplexOrder InnerProductSpace MatrixOrder


private theorem smul_orthogonal_projection_le_of_energy_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (U : Submodule ℂ E) {H : E →ₗ[ℂ] E}
    (hH : H.IsPositive) (hU : U ≤ LinearMap.ker H) {γ : ℝ}
    (hEnergy : ∀ v ∈ Uᗮ, γ * ‖v‖ ^ 2 ≤ (⟪H v, v⟫_ℂ).re) :
    (γ : ℂ) • Uᗮ.starProjection.toLinearMap ≤ H := by
  refine ⟨hH.isSymmetric.sub (Uᗮ.starProjection_isSymmetric.smul (by simp)), ?_⟩
  intro v
  have hproj : H (U.starProjection v) = 0 :=
    LinearMap.mem_ker.mp (hU (Submodule.starProjection_apply_mem _ _))
  have hform : ⟪H v, v⟫_ℂ = ⟪H (Uᗮ.starProjection v), Uᗮ.starProjection v⟫_ℂ := by
    simp only [Submodule.starProjection_orthogonal_val, map_sub, hproj, sub_zero,
      hH.isSymmetric v]
  have hnorm : (⟪Uᗮ.starProjection v, v⟫_ℂ).re = ‖Uᗮ.starProjection v‖ ^ 2 :=
    Uᗮ.re_inner_starProjection_eq_normSq v
  have h := hEnergy (Uᗮ.starProjection v) (Submodule.starProjection_apply_mem _ _)
  change 0 ≤ (⟪H v - (γ : ℂ) • Uᗮ.starProjection v, v⟫_ℂ).re
  simpa only [inner_sub_left, inner_smul_left, Complex.sub_re, Complex.conj_ofReal,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    hnorm, hform, sub_nonneg] using h

namespace MPSTensor

variable {d D : ℕ}

private theorem grouped_window_iff {p M n i : ℕ} (hp : 0 < p) (hn : n < M) :
    (p * (n + 1) - 2 * p ≤ i ∧ i + 2 * p ≤ p * (n + 1)) ↔
      (p ∣ i ∧ i + 2 * p ≤ p * M) ∧ n = i / p + 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := by
      rcases n with _ | k
      · rw [zero_add, mul_one] at h2
        omega
      · exact ⟨k, rfl⟩
    have hk : p * (k + 1 + 1) = p * k + 2 * p := by ring
    obtain rfl : i = p * k := by omega
    exact ⟨⟨dvd_mul_right p k, hk ▸ Nat.mul_le_mul_left p hn⟩,
      by rw [Nat.mul_div_cancel_left k hp]⟩
  · rintro ⟨⟨⟨k, rfl⟩, -⟩, rfl⟩
    have hk : p * (k + 1 + 1) = p * k + 2 * p := by ring
    rw [Nat.mul_div_cancel_left k hp]
    omega

/-- The Hamiltonians of the grouped windows of \(2p\) sites ending at \(p, 2p, \ldots, pM\) add
up to the Hamiltonian of the range-\(2p\) parent interaction restricted to the starts
\(0,p,\ldots,p(M-2)\); the initial window, ending at \(p\), contributes zero.
Source: Nachtergaele, arXiv:cond-mat/9410110, conditions C1-prime and C2. -/
theorem sum_range_hamiltonian_restrict_parentChainInteraction_grouped (A : MPSTensor d D)
    {p : ℕ} (hp : 0 < p) (N M : ℕ) :
    ∑ n ∈ Finset.range M, ((parentChainInteraction A (2 * p) N).restrict
        fun i ↦ p * (n + 1) - 2 * p ≤ i.val ∧ i.val + 2 * p ≤ p * (n + 1)).hamiltonian =
      ((parentChainInteraction A (2 * p) N).restrict
        fun i ↦ p ∣ i.val ∧ i.val + 2 * p ≤ p * M).hamiltonian :=
  ManyBody.Interaction.sum_hamiltonian_restrict_eq_hamiltonian_restrict _ _ _
    (fun i ↦ i.val / p + 1)
    (fun i hi ↦ by
      obtain ⟨⟨k, hk⟩, h⟩ := hi
      have h' : p * (k + 2) ≤ p * M := by
        rw [Nat.mul_add, ← hk]
        omega
      have := Nat.le_of_mul_le_mul_left h' hp
      rw [Finset.mem_range, hk, Nat.mul_div_cancel_left k hp]
      omega)
    fun _ _ hn ↦ grouped_window_iff hp (Finset.mem_range.mp hn)

/-- Adding right spectator sites preserves the grouped C3 estimate uniformly
in the number of sampled windows. Source: Nachtergaele,
arXiv:cond-mat/9410110, condition C3-prime, lines 1095--1107. -/
theorem grouped_martingaleDifference_norm_le_of_projector_defect_of_le
    (A : MPSTensor d D) {p N M : ℕ} (hp : 0 < p) (hMN : p * M ≤ N)
    (hKernel : ∀ n, 2 * p ≤ n →
      LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A (2 * p) n).hamiltonian) =
          groundSpaceES A n)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hDefect : ∀ K : ℕ,
      ‖(groundSpaceES A (K + p + p)).starProjection -
        (leftBoundaryMapES A (K + p) p).range.starProjection.comp
          (reassocTailBoundaryMapES A K p p).range.starProjection‖ ≤ ε) :
    ∀ n ∈ Finset.range M,
      ‖LinearMap.toContinuousLinearMap
        ((groupedIntervalGroundProjectionES A p N n).comp
          ((groupedNestedGroundProjectionsES A p N).martingaleDifference n))‖ ≤ ε := by
  apply grouped_martingaleDifference_norm_le_of_two_le A hp hε
  intro n hn2 hnM
  have hlocal := grouped_martingaleDifference_norm_le_of_projector_defect A hp
    (M := n + 1) hKernel hε hDefect n (by simp)
  have hend : p * (n + 1) ≤ N :=
    (Nat.mul_le_mul_left p (by omega : n + 1 ≤ M)).trans hMN
  have hspec := norm_suffixGroundProjection_comp_prefixDifference_le_active A
    (R := 2 * p) (l := 2 * p) (n := p * (n + 1))
    (r := N - p * (n + 1)) (p := p * n) (by nlinarith)
  simp only [groupedIntervalGroundProjectionES,
    FrustrationFree.NestedGroundProjections.martingaleDifference,
    groupedNestedGroundProjectionsES] at hlocal ⊢
  let F (N a b : ℕ) : ℝ :=
    ‖LinearMap.toContinuousLinearMap
      ((LinearMap.ker
        (Matrix.toEuclideanLin
            ((parentChainInteraction A (2 * p) N).restrict fun i ↦ b - 2 * p ≤ i.val ∧ i.val + 2 *
                p ≤ b).hamiltonian)).starProjection.toLinearMap.comp
          (openPrefixGroundProjectionES A (2 * p) N a -
            openPrefixGroundProjectionES A (2 * p) N b))‖
  change F (p * (n + 1) + (N - p * (n + 1))) (p * n) (p * (n + 1)) ≤
    F (p * (n + 1)) (p * n) (p * (n + 1)) at hspec
  change F N (p * n) (p * (n + 1)) ≤ ε
  have hbound := hspec.trans hlocal
  change F (p * (n + 1) + (N - p * (n + 1))) (p * n) (p * (n + 1)) ≤ ε
    at hbound
  rwa [Nat.add_sub_of_le hend] at hbound

/-- The range-\(2p\) parent interaction restricted to the starts \(0,p,\ldots,p(M-2)\) has the
full grouped energy lower bound on the orthogonal complement of the prefix ground space. The C1
sum is exactly the Hamiltonian of this restriction, so its comparison constant is one.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 2.1(ii), lines 1131--1136. -/
theorem sparseGrouped_energy_bound_of_grouped_c3
    (A : MPSTensor d D) {p N M : ℕ} (hp : 0 < p) (hMN : p * M ≤ N)
    {ε : ℝ} (hε : 0 ≤ ε) (hεlt : ε < 1 / Real.sqrt 2)
    (hC3 : ∀ n ∈ Finset.range M,
      ‖LinearMap.toContinuousLinearMap
        ((groupedIntervalGroundProjectionES A p N n).comp
          ((groupedNestedGroundProjectionsES A p N).martingaleDifference n))‖ ≤ ε)
    (v : EuclideanSpace ℂ (Cfg d N))
    (hv : v ∈ (LinearMap.ker (Matrix.toEuclideanLin ((parentChainInteraction A (2 * p) N).restrict
      fun i ↦ i.val + 2 * p ≤ p * M).hamiltonian))ᗮ) :
    (1 - ε * Real.sqrt 2) ^ 2 * ‖v‖ ^ 2 ≤
      (⟪Matrix.toEuclideanLin ((parentChainInteraction A (2 * p) N).restrict
        fun i ↦ p ∣ i.val ∧ i.val + 2 * p ≤ p * M).hamiltonian v, v⟫_ℂ).re := by
  have hgap :=
    FrustrationFree.NestedGroundProjections.energy_lower_bound_of_nachtergaele_c1_c3_full_range
      (groupedNestedGroundProjectionsES A p N)
      (groupedIntervalGroundProjectionES A p N)
      (fun n => Matrix.toEuclideanLin ((parentChainInteraction A (2 * p) N).restrict
        fun i ↦ p * (n + 1) - 2 * p ≤ i.val ∧ i.val + 2 * p ≤ p * (n + 1)).hamiltonian)
      (Matrix.toEuclideanLin ((parentChainInteraction A (2 * p) N).restrict
        fun i ↦ p ∣ i.val ∧ i.val + 2 * p ≤ p * M).hamiltonian) M 1 v
      (show openPrefixGroundProjectionES A (2 * p) N 0 = 1 from
        openPrefixGroundProjectionES_eq_one_of_lt A (by omega))
      (by simpa only [groupedNestedGroundProjectionsES, openPrefixGroundProjectionES,
        Submodule.range_starProjection] using hv)
      (γ := (1 : ℝ)) (d := (1 : ℝ)) (ε := ε)
      (by norm_num) (by norm_num) hε (by simpa using hεlt)
      (fun _ _ => Submodule.isSymmetricProjection_starProjection _)
      (fun _ _ _ hout => grouped_martingaleDifference_commute A hp hout)
      (fun x => by
        refine ⟨Finset.sum_nonneg fun n _ => (Matrix.isPositive_toEuclideanLin_iff.mpr
          (posSemidef_hamiltonian_restrict_parentChainInteraction A (2 * p) N _)).2 x, ?_⟩
        rw [← sum_range_hamiltonian_restrict_parentChainInteraction_grouped A hp N M, map_sum,
          LinearMap.sum_apply, sum_inner, Complex.re_sum, one_mul])
      (fun n hn x => by
        simpa only [groupedIntervalGroundProjectionES, one_mul] using
          parentChainInteraction_C2_full_range_norm_sq A (L := 2 * p)
            ((Nat.mul_le_mul_left p (Finset.mem_range.mp hn)).trans hMN) x)
      hC3
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, div_one, one_mul] using hgap

/-- The Hamiltonian of the range-\(2p\) parent interaction restricted to the starts
\(0,p,\ldots,p(M-2)\) dominates the full prefix excitation projection with the sharp grouped
martingale coefficient. Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 2.1(ii),
lines 1131--1136. -/
theorem sparseGrouped_projection_bound_of_grouped_c3
    (A : MPSTensor d D) {p N M : ℕ} (hp : 0 < p) (hMN : p * M ≤ N)
    {ε : ℝ} (hε : 0 ≤ ε) (hεlt : ε < 1 / Real.sqrt 2)
    (hC3 : ∀ n ∈ Finset.range M,
      ‖LinearMap.toContinuousLinearMap
        ((groupedIntervalGroundProjectionES A p N n).comp
          ((groupedNestedGroundProjectionsES A p N).martingaleDifference n))‖ ≤ ε) :
    (((1 - ε * Real.sqrt 2) ^ 2 : ℝ) : ℂ) •
      ((LinearMap.ker (Matrix.toEuclideanLin ((parentChainInteraction A (2 * p) N).restrict
        fun i ↦ i.val + 2 * p ≤ p * M).hamiltonian))ᗮ).starProjection.toLinearMap ≤
      Matrix.toEuclideanLin ((parentChainInteraction A (2 * p) N).restrict
        fun i ↦ p ∣ i.val ∧ i.val + 2 * p ≤ p * M).hamiltonian := by
  apply smul_orthogonal_projection_le_of_energy_bound _ (Matrix.isPositive_toEuclideanLin_iff.mpr
    (posSemidef_hamiltonian_restrict_parentChainInteraction A (2 * p) N _))
  · intro v hv
    rw [ManyBody.Interaction.mem_ker_toEuclideanLin_hamiltonian_restrict_iff
      (posSemidef_parentChainInteraction_term A (2 * p) N)] at hv ⊢
    exact fun i hi ↦ hv i hi.2
  · exact sparseGrouped_energy_bound_of_grouped_c3 A hp hMN hε hεlt hC3

/-- A positive residual interval permits one additional terminal interaction without repeating
any sampled local term: the Hamiltonians of the restriction to the starts \(0,p,\ldots,p(M-2)\)
and of the terminal window add up to at most the open-chain Hamiltonian. -/
theorem sparseGrouped_add_terminal_le (A : MPSTensor d D) (p M : ℕ) {q : ℕ} (hq : 0 < q) :
    ((parentChainInteraction A (2 * p) (p * M + q)).restrict
        fun i ↦ p ∣ i.val ∧ i.val + 2 * p ≤ p * M).hamiltonian +
      ((parentChainInteraction A (2 * p) (p * M + q)).restrict
        fun i ↦ p * M + q - 2 * p ≤ i.val ∧ i.val + 2 * p ≤ p * M + q).hamiltonian ≤
      (parentChainInteraction A (2 * p) (p * M + q)).hamiltonian :=
  ManyBody.Interaction.hamiltonian_restrict_add_hamiltonian_restrict_le
    (fun i ↦ Matrix.nonneg_iff_posSemidef.mpr
      (posSemidef_parentChainInteraction_term A (2 * p) (p * M + q) i)) _ _
    fun i hi hi' ↦ by omega

end MPSTensor
