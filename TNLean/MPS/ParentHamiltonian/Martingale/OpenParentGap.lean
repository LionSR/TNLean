/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.EmbeddedC2
import TNLean.MPS.ParentHamiltonian.Martingale.FixedAmbientMartingaleBound
import TNLean.MPS.ParentHamiltonian.Martingale.NachtergaeleFullRangeEstimate

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

/-- A fixed-window suffix Hamiltonian vanishes before its full interaction
window fits.  This supplies the early-index part of the full-range C1 and C2
hypotheses. -/
theorem openSuffixParentHamiltonianES_eq_zero_of_lt
    (A : MPSTensor d D) {L N n : ℕ} (hnL : n < L) :
    openSuffixParentHamiltonianES A L L N n = 0 := by
  rw [openSuffixParentHamiltonianES]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_filter] at hi
  exfalso
  omega

/-- Shifting the full filtration range by one gives the C1 suffix sum.  Terms
before the first complete length-\(L\) window are zero. -/
theorem sum_range_openSuffixParentHamiltonianES_succ_eq_Icc
    (A : MPSTensor d D) {L N : ℕ} (hL : 0 < L) :
    ∑ n ∈ Finset.range N, openSuffixParentHamiltonianES A L L N (n + 1) =
      ∑ n ∈ Finset.Icc L N, openSuffixParentHamiltonianES A L L N n := by
  let f := fun n ↦ openSuffixParentHamiltonianES A L L N n
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
      exact openSuffixParentHamiltonianES_eq_zero_of_lt A (by omega)
  exact hshift.trans htrim.symm

/-- Full-range C1 for interaction length \(l+1\), with the source counting
constant \(d_{l+1}=1\).  The range indices are shifted because the local
Hamiltonian at martingale index \(n\) acts on \([n-l,n+1)\). -/
theorem openParentHamiltonianES_C1_full_range_quadratic_form
    (A : MPSTensor d D) {l N : ℕ} (x : EuclideanSpace ℂ (Cfg d N)) :
    0 ≤ ∑ n ∈ Finset.range N,
        (⟪openSuffixParentHamiltonianES A (l + 1) (l + 1) N (n + 1) x, x⟫_ℂ).re ∧
      (∑ n ∈ Finset.range N,
        (⟪openSuffixParentHamiltonianES A (l + 1) (l + 1) N (n + 1) x, x⟫_ℂ).re) ≤
        (⟪openParentHamiltonianES A (l + 1) N x, x⟫_ℂ).re := by
  have hsum := sum_range_openSuffixParentHamiltonianES_succ_eq_Icc
    A (L := l + 1) (N := N) (by omega)
  have hC1 := openParentHamiltonianES_C1 A
    (L := l + 1) (l := l + 1) (N := N) (le_refl _)
  simp only [Nat.sub_self, zero_add, Nat.cast_one, one_smul] at hC1
  rw [← hsum] at hC1
  let S := ∑ n ∈ Finset.range N,
    openSuffixParentHamiltonianES A (l + 1) (l + 1) N (n + 1)
  constructor
  · exact Finset.sum_nonneg fun n hn ↦
      (openSuffixParentHamiltonianES_isPositive A (l + 1) (l + 1) N (n + 1)).2 x
  · have hpos := (LinearMap.le_def S (openParentHamiltonianES A (l + 1) N)).mp hC1.2
    have hx := hpos.2 x
    have hSform :
        RCLike.re ⟪S x, x⟫_ℂ =
          ∑ n ∈ Finset.range N,
            (⟪openSuffixParentHamiltonianES A (l + 1) (l + 1) N (n + 1) x,
              x⟫_ℂ).re := by
      simp only [S, LinearMap.sum_apply, sum_inner, map_sum, RCLike.re_to_complex]
    change 0 ≤ RCLike.re ⟪(openParentHamiltonianES A (l + 1) N - S) x, x⟫_ℂ at hx
    rw [LinearMap.sub_apply, inner_sub_left, map_sub, hSform] at hx
    exact sub_nonneg.mp hx

/-- Full-range norm-square form of C2 with \(\gamma_{l+1}=1\).  At early
indices both sides vanish.  Once the window fits, the suffix Hamiltonian is the
orthogonal projection \(I-Q_n\). -/
theorem openSuffixParentHamiltonianES_C2_full_range_norm_sq
    (A : MPSTensor d D) {l N n : ℕ} (hnN : n < N)
    (x : EuclideanSpace ℂ (Cfg d N)) :
    ‖((LinearMap.id : EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ]
          EuclideanSpace ℂ (Cfg d N)) -
        openIntervalGroundProjectionES A (l + 1) l N n) x‖ ^ 2 ≤
      (⟪openSuffixParentHamiltonianES A (l + 1) (l + 1) N (n + 1) x, x⟫_ℂ).re := by
  by_cases hnl : n < l
  · have hzero := openSuffixParentHamiltonianES_eq_zero_of_lt
      A (L := l + 1) (N := N) (n := n + 1) (by omega)
    simp only [openIntervalGroundProjectionES, hzero, LinearMap.ker_zero,
      Submodule.starProjection_top']
    norm_num
  · have hln : l + 1 ≤ n + 1 := by omega
    have hnN' : n + 1 ≤ N := by omega
    let H := openSuffixParentHamiltonianES A (l + 1) (l + 1) N (n + 1)
    have hH : H.IsSymmetricProjection :=
      openSuffixParentHamiltonianES_isSymmetricProjection A (by omega) hln hnN'
    have hEq :
        H = (LinearMap.id : EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ]
          EuclideanSpace ℂ (Cfg d N)) -
          openIntervalGroundProjectionES A (l + 1) l N n := by
      simpa only [H, openIntervalGroundProjectionES] using
        openSuffixParentHamiltonianES_eq_id_sub_starProjection_ker
          A (by omega) hln hnN'
    rw [← hEq]
    have hIdem : H (H x) = H x := by
      have h := congrArg (fun T : EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ]
        EuclideanSpace ℂ (Cfg d N) ↦ T x) hH.isIdempotentElem.eq
      simpa [Module.End.mul_apply] using h
    calc
      ‖H x‖ ^ 2 = (⟪H x, H x⟫_ℂ).re :=
        (inner_self_eq_norm_sq (𝕜 := ℂ) (H x)).symm
      _ = (⟪H (H x), x⟫_ℂ).re := by rw [hH.isSymmetric (H x) x]
      _ = (⟪H x, x⟫_ℂ).re := by rw [hIdem]
      _ ≤ (⟪openSuffixParentHamiltonianES A (l + 1) (l + 1) N (n + 1) x,
          x⟫_ℂ).re := le_rfl

/-- Fixed-parameter open-chain gap obtained from the fixed-ambient C3 bound.
For \(L=l+1\), conditions C1 and C2 have constants one, so the coefficient is
\((1-\epsilon_l\sqrt{l+1})^2\). -/
theorem openParentHamiltonianES_norm_gap_of_fixedAmbient_c3
    [NeZero D] (A : MPSTensor d D) {l N : ℕ}
    (hl : 0 < l) (hInj : Kraus.IsNBlkInjective A l) (hlN : l + 1 ≤ N)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hεlt : ε < 1 / Real.sqrt ((l + 1 : ℕ) : ℝ))
    (hC3 : ∀ n ∈ Finset.range N,
      ‖LinearMap.toContinuousLinearMap
        ((openIntervalGroundProjectionES A (l + 1) l N n).comp
          ((fixedAmbientNestedGroundProjectionsES A (l + 1) N).martingaleDifference n))‖ ≤ ε) :
    ∀ v ∈ (groundSpaceES A N)ᗮ,
      (1 - ε * Real.sqrt ((l + 1 : ℕ) : ℝ)) ^ 2 * ‖v‖ ≤
        ‖openParentHamiltonianES A (l + 1) N v‖ := by
  let G := fixedAmbientNestedGroundProjectionsES A (l + 1) N
  let Q := fun n ↦ openIntervalGroundProjectionES A (l + 1) l N n
  let localHamiltonian := fun n ↦
    openSuffixParentHamiltonianES A (l + 1) (l + 1) N (n + 1)
  let H := openParentHamiltonianES A (l + 1) N
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
      A hlN hout
  have hground : LinearMap.range (G.projection N) = LinearMap.ker H := by
    change LinearMap.range (openPrefixGroundProjectionES A (l + 1) N N) =
      LinearMap.ker (openParentHamiltonianES A (l + 1) N)
    simp only [openPrefixGroundProjectionES, Submodule.range_starProjection]
    rw [openPrefixParentHamiltonianES_self_eq_openParentHamiltonianES]
  have hgap :=
    FrustrationFree.NestedGroundProjections.norm_lower_bound_of_nachtergaele_c1_c3_full_range
      G Q localHamiltonian H N l hzero
      (γ := (1 : ℝ)) (d := (1 : ℝ)) (ε := ε)
      (by norm_num) (by norm_num) hε hεlt hQ hcomm
      (fun x ↦ by
        simpa only [localHamiltonian, H, one_mul] using
          openParentHamiltonianES_C1_full_range_quadratic_form A x)
      (fun n hn x ↦ by
        simpa only [localHamiltonian, Q, one_mul] using
          openSuffixParentHamiltonianES_C2_full_range_norm_sq A
            (Finset.mem_range.mp hn) x)
      hC3 (openParentHamiltonianES_isPositive A (l + 1) N) hground
  rw [ker_openParentHamiltonianES_eq_groundSpaceES_of_isNBlkInjective
    hInj hl hlN] at hgap
  simpa only [H, div_one, one_mul] using hgap

/-- A primitive MPS has a uniform nonwrapping open-parent-Hamiltonian gap.
The witnesses use the same \(l\) and \(\epsilon_l\) as the physical C3
estimate, uniformly for every \(N\) with \(l+1\leq N\). -/
theorem IsPrimitiveMPS.exists_openParentHamiltonianES_gap
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) :
    ∃ l : ℕ, ∃ ε : ℝ, ∃ _hl : 1 < l, ∃ _hInj : Kraus.IsNBlkInjective A l,
      0 ≤ ε ∧ ε < 1 / Real.sqrt ((l + 1 : ℕ) : ℝ) ∧
      ∀ N : ℕ, l + 1 ≤ N → ∀ v ∈ (groundSpaceES A N)ᗮ,
        (1 - ε * Real.sqrt ((l + 1 : ℕ) : ℝ)) ^ 2 * ‖v‖ ≤
          ‖openParentHamiltonianES A (l + 1) N v‖ := by
  obtain ⟨l, ε, hl, hInj, hε, hεlt, hC3⟩ :=
    hP.exists_fixedAmbient_martingaleDifference_norm_lt_c3_threshold hρ
  refine ⟨l, ε, hl, hInj, hε, hεlt, fun N hlN ↦ ?_⟩
  exact openParentHamiltonianES_norm_gap_of_fixedAmbient_c3
    A hl.le hInj hlN hε hεlt (fun n hn ↦ hC3 N n (Finset.mem_range.mp hn))

end MPSTensor
