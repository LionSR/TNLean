/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.GroupedProjectorEstimate
import TNLean.MPS.ParentHamiltonian.Martingale.EmbeddedC2

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

open scoped BigOperators ComplexOrder InnerProductSpace


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

/-- The range-\(2p\) local interactions sampled at starts
\(0,p,\ldots,p(M-2)\), acting in one ambient open chain. The initial
window, ending at \(p\), is zero.
Source: Nachtergaele, arXiv:cond-mat/9410110, conditions C1-prime and C2. -/
noncomputable def sparseGroupedOpenParentHamiltonianES (A : MPSTensor d D)
    (p N M : ℕ) : EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  ∑ n ∈ Finset.range M,
    openSuffixParentHamiltonianES A (2 * p) (2 * p) N (p * (n + 1))

/-- Adding right spectator sites preserves the grouped C3 estimate uniformly
in the number of sampled windows. Source: Nachtergaele,
arXiv:cond-mat/9410110, condition C3-prime, lines 1095--1107. -/
theorem grouped_martingaleDifference_norm_le_of_projector_defect_of_le
    (A : MPSTensor d D) {p N M : ℕ} (hp : 0 < p) (hM : 2 ≤ M) (hMN : p * M ≤ N)
    (hKernel : ∀ n, 2 * p ≤ n →
      LinearMap.ker (openParentHamiltonianES A (2 * p) n) = groundSpaceES A n)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hDefect : ∀ K : ℕ,
      ‖(groundSpaceES A (K + p + p)).starProjection -
        (leftBoundaryMapES A (K + p) p).range.starProjection.comp
          (reassocTailBoundaryMapES A K p p).range.starProjection‖ ≤ ε) :
    ∀ n ∈ Finset.range M,
      ‖LinearMap.toContinuousLinearMap
        ((groupedIntervalGroundProjectionES A p N n).comp
          ((groupedNestedGroundProjectionsES A p N).martingaleDifference n))‖ ≤ ε := by
  apply grouped_martingaleDifference_norm_le_of_two_le A hp (by nlinarith) hε
  intro n hn2 hnM
  have hlocal := grouped_martingaleDifference_norm_le_of_projector_defect A hp
    (M := n + 1) (by omega) hKernel hε hDefect n (by simp)
  have hend : p * (n + 1) ≤ N :=
    (Nat.mul_le_mul_left p (by omega : n + 1 ≤ M)).trans hMN
  have hspec := norm_suffixGroundProjection_comp_prefixDifference_le_active A
    (R := 2 * p) (l := 2 * p) (n := p * (n + 1))
    (r := N - p * (n + 1)) (p := p * n) (by omega) (by nlinarith)
  simp only [groupedIntervalGroundProjectionES,
    FrustrationFree.NestedGroundProjections.martingaleDifference,
    groupedNestedGroundProjectionsES] at hlocal ⊢
  let F (N a b : ℕ) : ℝ :=
    ‖LinearMap.toContinuousLinearMap
      ((LinearMap.ker
        (openSuffixParentHamiltonianES A (2 * p) (2 * p) N b)).starProjection.toLinearMap.comp
          (openPrefixGroundProjectionES A (2 * p) N a -
            openPrefixGroundProjectionES A (2 * p) N b))‖
  change F (p * (n + 1) + (N - p * (n + 1))) (p * n) (p * (n + 1)) ≤
    F (p * (n + 1)) (p * n) (p * (n + 1)) at hspec
  change F N (p * n) (p * (n + 1)) ≤ ε
  have hbound := hspec.trans hlocal
  change F (p * (n + 1) + (N - p * (n + 1))) (p * n) (p * (n + 1)) ≤ ε
    at hbound
  rwa [Nat.add_sub_of_le hend] at hbound

/-- The sparse sampled interaction has the full grouped energy lower bound
on the orthogonal complement of the prefix ground space. The C1 sum is now
exactly the sparse interaction, so its comparison constant is one.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 2.1(ii), lines 1131--1136. -/
theorem sparseGroupedOpenParentHamiltonianES_energy_bound_of_grouped_c3
    (A : MPSTensor d D) {p N M : ℕ} (hp : 0 < p) (hM : 2 ≤ M) (hMN : p * M ≤ N)
    {ε : ℝ} (hε : 0 ≤ ε) (hεlt : ε < 1 / Real.sqrt 2)
    (hC3 : ∀ n ∈ Finset.range M,
      ‖LinearMap.toContinuousLinearMap
        ((groupedIntervalGroundProjectionES A p N n).comp
          ((groupedNestedGroundProjectionsES A p N).martingaleDifference n))‖ ≤ ε)
    (v : EuclideanSpace ℂ (Cfg d N))
    (hv : v ∈ (LinearMap.ker (openPrefixParentHamiltonianES A (2 * p) N (p * M)))ᗮ) :
    (1 - ε * Real.sqrt 2) ^ 2 * ‖v‖ ^ 2 ≤
      (⟪sparseGroupedOpenParentHamiltonianES A p N M v, v⟫_ℂ).re := by
  have hgap :=
    FrustrationFree.NestedGroundProjections.energy_lower_bound_of_nachtergaele_c1_c3_full_range
      (groupedNestedGroundProjectionsES A p N)
      (groupedIntervalGroundProjectionES A p N)
      (fun n => openSuffixParentHamiltonianES A (2 * p) (2 * p) N (p * (n + 1)))
      (sparseGroupedOpenParentHamiltonianES A p N M) M 1 v
      (show openPrefixGroundProjectionES A (2 * p) N 0 = 1 from
        openPrefixGroundProjectionES_eq_one_of_lt A (by omega))
      (by simpa only [groupedNestedGroundProjectionsES, openPrefixGroundProjectionES,
        Submodule.range_starProjection] using hv)
      (γ := (1 : ℝ)) (d := (1 : ℝ)) (ε := ε)
      (by norm_num) (by norm_num) hε (by simpa using hεlt)
      (fun _ _ => Submodule.isSymmetricProjection_starProjection _)
      (fun _ _ _ hout => grouped_martingaleDifference_commute A hp (by nlinarith) hout)
      (fun x => by
        refine ⟨Finset.sum_nonneg fun n _ =>
          (openSuffixParentHamiltonianES_isPositive A (2 * p) (2 * p) N (p * (n + 1))).2 x,
          ?_⟩
        simp only [sparseGroupedOpenParentHamiltonianES, LinearMap.sum_apply,
          sum_inner, Complex.re_sum, one_mul]
        exact le_rfl)
      (fun n hn x => by
        have hn' : p * (n + 1) - 1 < N := by
          have hnM := Finset.mem_range.mp hn
          have hend := Nat.mul_le_mul_left p
            (by omega : n + 1 ≤ M)
          have hpos : 0 < p * (n + 1) := Nat.mul_pos hp (by omega)
          omega
        simpa only [groupedIntervalGroundProjectionES, openIntervalGroundProjectionES,
          Nat.sub_add_cancel (by omega : 1 ≤ 2 * p),
          Nat.sub_add_cancel (by nlinarith : 1 ≤ p * (n + 1)), one_mul] using
          openSuffixParentHamiltonianES_C2_full_range_norm_sq A (l := 2 * p - 1) hn' x)
      hC3
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, div_one, one_mul] using hgap

/-- The sparse grouped Hamiltonian is positive. -/
theorem sparseGroupedOpenParentHamiltonianES_isPositive
    (A : MPSTensor d D) (p N M : ℕ) :
    (sparseGroupedOpenParentHamiltonianES A p N M).IsPositive := by
  unfold sparseGroupedOpenParentHamiltonianES
  exact LinearMap.isPositive_sum _ fun n _ =>
    openSuffixParentHamiltonianES_isPositive A (2 * p) (2 * p) N (p * (n + 1))

/-- The sparse grouped sum dominates the full prefix excitation projection
with the sharp grouped martingale coefficient. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorem 2.1(ii), lines 1131--1136. -/
theorem sparseGroupedOpenParentHamiltonianES_projection_bound_of_grouped_c3
    (A : MPSTensor d D) {p N M : ℕ} (hp : 0 < p) (hM : 2 ≤ M) (hMN : p * M ≤ N)
    {ε : ℝ} (hε : 0 ≤ ε) (hεlt : ε < 1 / Real.sqrt 2)
    (hC3 : ∀ n ∈ Finset.range M,
      ‖LinearMap.toContinuousLinearMap
        ((groupedIntervalGroundProjectionES A p N n).comp
          ((groupedNestedGroundProjectionsES A p N).martingaleDifference n))‖ ≤ ε) :
    (((1 - ε * Real.sqrt 2) ^ 2 : ℝ) : ℂ) •
      ((LinearMap.ker
        (openPrefixParentHamiltonianES A (2 * p) N (p * M)))ᗮ).starProjection.toLinearMap ≤
          sparseGroupedOpenParentHamiltonianES A p N M := by
  apply smul_orthogonal_projection_le_of_energy_bound _
    (sparseGroupedOpenParentHamiltonianES_isPositive A p N M)
  · intro v hv
    rw [LinearMap.mem_ker, sparseGroupedOpenParentHamiltonianES, LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro n hn
    have hnM := Finset.mem_range.mp hn
    have hend : p * (n + 1) ≤ p * M := Nat.mul_le_mul_left p (by omega)
    have hpos : 0 < p * (n + 1) := Nat.mul_pos hp (by omega)
    have hker := ker_openPrefixParentHamiltonianES_le_ker_openSuffixParentHamiltonianES
      A (L := 2 * p) (l := 2 * p - 1) (N := N) (m := p * M)
      (n := p * (n + 1) - 1) (by omega)
    have hv' := hker hv
    rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * p), Nat.sub_add_cancel hpos] at hv'
    exact LinearMap.mem_ker.mp hv'
  · exact sparseGroupedOpenParentHamiltonianES_energy_bound_of_grouped_c3
      A hp hM hMN hε hεlt hC3

/-- A positive residual interval permits one additional terminal interaction
without repeating any sampled local term. Their sum is bounded by the full
open Hamiltonian with coefficient one. -/
theorem sparseGroupedOpenParentHamiltonianES_add_terminal_le
    (A : MPSTensor d D) {p M q : ℕ} (hp : 0 < p) (hM : 2 ≤ M) (hq : 0 < q) :
    sparseGroupedOpenParentHamiltonianES A p (p * M + q) M +
      openSuffixParentHamiltonianES A (2 * p) (2 * p) (p * M + q) (p * M + q) ≤
        openParentHamiltonianES A (2 * p) (p * M + q) := by
  classical
  let N := p * M + q
  have hRN : 2 * p ≤ N := by dsimp [N]; nlinarith
  have hlast : p * (M - 2) + 2 * p = p * M := by
    calc
      _ = p * (M - 2 + 2) := by ring
      _ = _ := by rw [Nat.sub_add_cancel hM]
  have hterm : N - 2 * p = p * (M - 2) + q := by dsimp [N]; omega
  have hmul (n : Fin M) (hn : n.val ≠ 0) : p * (n.val - 1) + 2 * p = p * (n.val + 1) := by
    have h := congrArg (p * ·) (Nat.sub_add_cancel (by omega : 1 ≤ n.val))
    simp only [Nat.mul_add, Nat.mul_one] at h ⊢
    omega
  let I (n : Fin M) : NonwrappingStart (2 * p) N :=
    ⟨⟨if n.val = 0 then N - 2 * p else p * (n.val - 1), by
      split_ifs with hn
      · omega
      · have hend := (Nat.mul_le_mul_left p (by omega : n.val + 1 ≤ M))
        have := hmul n hn
        dsimp [N]
        omega⟩, by
      change (if n.val = 0 then N - 2 * p else p * (n.val - 1)) + 2 * p ≤ N
      split_ifs with hn
      · omega
      · have hend := Nat.mul_le_mul_left p (by omega : n.val + 1 ≤ M)
        have := hmul n hn
        dsimp [N]
        omega⟩
  have hI : Function.Injective I := by
    intro n n' heq
    have he := congrArg (fun i : NonwrappingStart (2 * p) N => i.1.val) heq
    dsimp [I] at he
    by_cases hn : n.val = 0
    · by_cases hn' : n'.val = 0
      · exact Fin.ext (hn.trans hn'.symm)
      · have hbound := Nat.mul_le_mul_left p (by omega : n'.val - 1 ≤ M - 2)
        simp only [hn, hn', ite_true, ite_false] at he
        omega
    · by_cases hn' : n'.val = 0
      · have hbound := Nat.mul_le_mul_left p (by omega : n.val - 1 ≤ M - 2)
        simp only [hn, hn', ite_true, ite_false] at he
        omega
      · simp only [hn, hn', ite_false] at he
        have hcancel := Nat.mul_left_cancel hp he
        apply Fin.ext
        omega
  let f (n : Fin M) := openSuffixParentHamiltonianES A (2 * p) (2 * p) N (p * (n.val + 1))
  let z : Fin M := ⟨0, by omega⟩
  let T := openSuffixParentHamiltonianES A (2 * p) (2 * p) N N
  have hupdate (n : Fin M) : localTermES A (2 * p) (I n).1 = Function.update f z T n := by
    by_cases hn : n = z
    · subst n
      rw [Function.update_self]
      dsimp only [T]
      rw [openSuffixParentHamiltonianES_eq_localTermES A (by omega) hRN le_rfl]
      congr 1
    · have hn0 : n.val ≠ 0 := by intro h; apply hn; exact Fin.ext h
      rw [Function.update_of_ne hn]
      dsimp only [f]
      rw [openSuffixParentHamiltonianES_eq_localTermES A (by omega)
        (by have := hmul n hn0; nlinarith)
        (by have := Nat.mul_le_mul_left p (by omega : n.val + 1 ≤ M); dsimp [N]; omega)]
      congr 1
      apply Fin.ext
      change (if n.val = 0 then N - 2 * p else p * (n.val - 1)) =
        p * (n.val + 1) - 2 * p
      rw [ite_eq_right hn0]
      have := hmul n hn0
      omega
  have hfzero : f z = 0 := by
    exact openSuffixParentHamiltonianES_eq_zero_of_lt A (by dsimp [z]; omega)
  have hsum : (∑ n : Fin M, localTermES A (2 * p) (I n).1) =
      sparseGroupedOpenParentHamiltonianES A p N M + T := by
    simp_rw [hupdate]
    rw [Finset.sum_update_of_mem (Finset.mem_univ z)]
    have hremove : (∑ n ∈ Finset.univ \ {z}, f n) = ∑ n : Fin M, f n := by
      apply Finset.sum_subset (Finset.sdiff_subset)
      intro n _ hn
      have hnz : n = z := by simpa using hn
      simpa [hnz] using hfzero
    rw [hremove, add_comm]
    congr 1
    exact Fin.sum_univ_eq_sum_range
      (fun n => openSuffixParentHamiltonianES A (2 * p) (2 * p) N (p * (n + 1))) M
  rw [← hsum, openParentHamiltonianES]
  have himage :
      (∑ i ∈ Finset.univ.image I, localTermES A (2 * p) i.1) =
        ∑ n : Fin M, localTermES A (2 * p) (I n).1 := Finset.sum_image hI.injOn
  rw [← himage]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ => LinearMap.nonneg_iff_isPositive.mpr (localTermES_isPositive A (2 * p) i.1))

end MPSTensor
