/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.OverlappingIntervalGap
import TNLean.MPS.ParentHamiltonian.Martingale.IntervalGapTransport
import TNLean.MPS.ParentHamiltonian.Martingale.IntervalKernelTransport
import TNLean.MPS.ParentHamiltonian.BlockedFiniteGapTransport
import TNLean.MPS.ParentHamiltonian.CanonicalParentInteractionMatrix

/-!
# Extending an aligned open gap to all residues

For N=(K+M)m+r, the prefix has length (K+M)m and the terminal interval
has length Mm+r. Their overlap is Mm. The aligned prefix inherits its
finite open gap; the finitely many terminal volumes have a positive common
gap on their actual kernel complements. Their energies sum to at most twice
the full-chain energy. The existing two-interval comparison then gives a
common gap once the three-interval ground-projection defect is at most 1/2.
The kernel intersection is exact whenever the two intervals cover every
interaction window.

This is an auxiliary criterion. Its projection-defect hypothesis is explicit;
no quantitative decay estimate for periodic tensors is asserted here.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma commutation (ii), and equations (3.12)--(3.16).
-/

open scoped Matrix BigOperators ComplexOrder InnerProductSpace
namespace MPSTensor
variable {d D : ℕ}
/-- The full open-chain kernel is contained in every prefix kernel.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma commutation (ii), and equations (3.12)--(3.16). -/
theorem ker_openParentHamiltonianES_le_ker_openPrefix
    (A : MPSTensor d D) {R N n : ℕ} (hn : n ≤ N) :
    LinearMap.ker (openParentHamiltonianES A R N) ≤
      LinearMap.ker (openPrefixParentHamiltonianES A R N n) := by
  rw [← openPrefixParentHamiltonianES_self_eq_openParentHamiltonianES A R N]
  exact ker_openPrefixParentHamiltonianES_antitone A R N hn
/-- The finitely many terminal volumes W+r, with r<m, have a common positive norm gap
on their actual kernel complements.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma commutation (ii), and equations (3.12)--(3.16). -/
theorem exists_pos_openParentHamiltonianES_gap_over_residues
    (A : MPSTensor d D) (R W m : ℕ) (hm : 0 < m) :
    ∃ η : ℝ, 0 < η ∧ ∀ r < m, ∀ v ∈
      (LinearMap.ker (openParentHamiltonianES A R (W + r)))ᗮ,
      η * ‖v‖ ≤ ‖openParentHamiltonianES A R (W + r) v‖ := by
  classical
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  choose δ hδ hGap using fun r : Fin m =>
    LinearMap.exists_pos_mul_norm_le_of_mem_orthogonal_ker
      (openParentHamiltonianES A R (W + r.val))
  let η := Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin m)).Nonempty) δ
  have hη : 0 < η := by
    simp only [η, Finset.lt_inf'_iff, Finset.mem_univ, forall_const]
    exact hδ
  refine ⟨η, hη, fun r hr v hv => ?_⟩
  exact (mul_le_mul_of_nonneg_right
    (Finset.inf'_le δ (Finset.mem_univ (⟨r, hr⟩ : Fin m))) (norm_nonneg v)).trans
    (hGap ⟨r, hr⟩ v hv)
/-- An aligned prefix gap and an explicit three-interval projection defect give a
common positive gap in every residue. The terminal gap is derived by finite
dimensionality.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma commutation (ii), and equations (3.12)--(3.16). -/
theorem exists_pos_openParentHamiltonianES_gap_of_aligned_cover_defect
    (A : MPSTensor d D) {R m M K₀ : ℕ} (hR : 0 < R) (hm : 0 < m)
    (hRW : R ≤ M * m)
    (hKernel : ∀ N, R ≤ N →
      LinearMap.ker (openParentHamiltonianES A R N) = groundSpaceES A N)
    {γ : ℝ} (hγ : 0 < γ)
    (hLeft : ∀ K ≥ K₀, ∀ v ∈
      (LinearMap.ker (openParentHamiltonianES A R (K * m + M * m)))ᗮ,
      γ * ‖v‖ ≤ ‖openParentHamiltonianES A R (K * m + M * m) v‖)
    (hDefect : ∀ K ≥ K₀, ∀ r < m,
      ‖(groundSpaceES A (K * m + M * m + r)).starProjection -
        (leftBoundaryMapES A (K * m + M * m) r).range.starProjection.comp
          (reassocTailBoundaryMapES A (K * m) (M * m) r).range.starProjection‖ ≤
        (1 / 2 : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ K ≥ K₀, ∀ r < m, ∀ v ∈
      (LinearMap.ker (openParentHamiltonianES A R (K * m + M * m + r)))ᗮ,
      δ * ‖v‖ ≤ ‖openParentHamiltonianES A R (K * m + M * m + r) v‖ := by
  obtain ⟨η, hη, hRight⟩ :=
    exists_pos_openParentHamiltonianES_gap_over_residues A R (M * m) m hm
  refine ⟨min γ η / 16, div_pos (lt_min hγ hη) (by norm_num),
    fun K hK r hr => ?_⟩
  apply openParentHamiltonianES_norm_gap_of_overlapping_interval_gaps
    A R (K * m + M * m + r) (K * m + M * m) (M * m + r) (lt_min hγ hη).le
  · intro v hv
    exact (mul_le_mul_of_nonneg_right (min_le_left γ η) (norm_nonneg v)).trans
      (openPrefixParentHamiltonianES_norm_gap_of_local_gap A hR hγ (hLeft K hK) v hv)
  · intro v hv
    exact (mul_le_mul_of_nonneg_right (min_le_right γ η) (norm_nonneg v)).trans
      (openSuffixParentHamiltonianES_norm_gap_of_local_gap A hR (by omega)
        (by omega) le_rfl hη (hRight r hr) v hv)
  · rw [hKernel _ (by omega),
      ker_openPrefixParentHamiltonianES_eq_range_leftBoundaryMapES A hR
        (hKernel _ (by omega)),
      ker_openSuffixParentHamiltonianES_eq_range_reassocTailBoundaryMapES A hR
        (by omega) (hKernel _ (by omega))]
    exact hDefect K hK r hr
/-- Vanishing of an interval parent sum forces every contained local projection to
vanish.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma commutation (ii), and equations (3.12)--(3.16). -/
theorem localTermES_eq_zero_of_openSuffixParentHamiltonianES_eq_zero
    (A : MPSTensor d D) (R W N n : ℕ) {v : EuclideanSpace ℂ (Cfg d N)}
    (hv : openSuffixParentHamiltonianES A R W N n v = 0)
    (i : NonwrappingStart R N)
    (hi : n - W ≤ i.1.val ∧ i.1.val + R ≤ n) : localTermES A R i.1 v = 0 := by
  classical
  let I := {j : NonwrappingStart R N // n - W ≤ j.1.val ∧ j.1.val + R ≤ n}
  have hsum : (∑ j : I, localTermES A R j.1.1) v = 0 := by
    rw [openSuffixParentHamiltonianES] at hv
    rw [Finset.sum_subtype (p := fun j : NonwrappingStart R N =>
      n - W ≤ j.1.val ∧ j.1.val + R ≤ n)
      (Finset.univ.filter fun j : NonwrappingStart R N =>
        n - W ≤ j.1.val ∧ j.1.val + R ≤ n) (fun _ => by simp)
      (fun j => localTermES A R j.1)] at hv
    exact hv
  exact ProjectionGeometry.apply_eq_zero_of_sum_apply_eq_zero
    (fun j : I => localTermES A R j.1.1)
    (fun j => localTermES_isSymmetricProjection A R j.1.1) hsum ⟨i, hi⟩
/-- Two covering intervals have exactly the full open-chain kernel in common, provided
every local interaction window is contained in one of them.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma commutation (ii), and equations (3.12)--(3.16). -/
theorem ker_openPrefix_inf_ker_openSuffix_eq_ker_openParentHamiltonianES
    (A : MPSTensor d D) {R N n W : ℕ} (hn : n ≤ N)
    (hcover : N + R ≤ n + W + 1) :
    LinearMap.ker (openPrefixParentHamiltonianES A R N n) ⊓
      LinearMap.ker (openSuffixParentHamiltonianES A R W N N) =
      LinearMap.ker (openParentHamiltonianES A R N) := by
  classical
  apply le_antisymm
  · rintro v ⟨hleft, hright⟩
    rw [LinearMap.mem_ker, openParentHamiltonianES, LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i.1.val + R ≤ n
    · exact localTermES_eq_zero_of_openPrefixParentHamiltonianES_eq_zero
        A R N n (LinearMap.mem_ker.mp hleft) ⟨i, hi⟩
    · exact localTermES_eq_zero_of_openSuffixParentHamiltonianES_eq_zero
        A R W N N (LinearMap.mem_ker.mp hright) i ⟨by omega, i.2⟩
  · refine le_inf (ker_openParentHamiltonianES_le_ker_openPrefix A hn) ?_
    intro v hv
    rw [LinearMap.mem_ker, openSuffixParentHamiltonianES, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun i _ =>
      localTermES_eq_zero_of_openParentHamiltonianES_eq_zero A R N
        (LinearMap.mem_ker.mp hv) i
/-- The sum of two interval Hamiltonians is at most twice the full open Hamiltonian.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma commutation (ii), and equations (3.12)--(3.16). -/
theorem openPrefix_add_openSuffix_le_two_openParentHamiltonianES
    (A : MPSTensor d D) (R N n W : ℕ) :
    openPrefixParentHamiltonianES A R N n + openSuffixParentHamiltonianES A R W N N ≤
      (2 : ℂ) • openParentHamiltonianES A R N := by
  simpa only [two_smul] using add_le_add
    (openPrefixParentHamiltonianES_le_openParentHamiltonianES A R N n)
    (openSuffixParentHamiltonianES_le_openParentHamiltonianES A R W N N)
/-- Residue bounds beyond a common quotient threshold give the same gap at every
sufficiently large original length.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma commutation (ii), and equations (3.12)--(3.16). -/
theorem openParentHamiltonianES_gap_all_large_of_residue_gaps
    (A : MPSTensor d D) {R m M K₀ : ℕ} (hm : 0 < m) {δ : ℝ}
    (hGap : ∀ K ≥ K₀, ∀ r < m, ∀ v ∈
      (LinearMap.ker (openParentHamiltonianES A R (K * m + M * m + r)))ᗮ,
      δ * ‖v‖ ≤ ‖openParentHamiltonianES A R (K * m + M * m + r) v‖) :
    ∀ N, (K₀ + M) * m ≤ N → ∀ v ∈
      (LinearMap.ker (openParentHamiltonianES A R N))ᗮ,
      δ * ‖v‖ ≤ ‖openParentHamiltonianES A R N v‖ := by
  intro N hN
  have hquot : K₀ + M ≤ N / m := (Nat.le_div_iff_mul_le hm).mpr hN
  have hEq : (N / m - M) * m + M * m + N % m = N := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
    simpa only [Nat.mul_comm] using Nat.div_add_mod N m
  rw [← hEq]
  exact hGap (N / m - M) (by omega) (N % m) (Nat.mod_lt N hm)
/-- The extended prefix and terminal boundary spaces intersect exactly in
G_N whenever the original canonical open kernels are the boundary spaces.
Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.10)--(3.16)
and Section 6, Lemma commutation (ii). -/
theorem leftBoundary_inf_reassocTail_range_eq_groundSpaceES_of_open_kernel
    (A : MPSTensor d D) {R K L r : ℕ} (hR : 0 < R) (hRL : R ≤ L)
    (hKernel : ∀ N, R ≤ N →
      LinearMap.ker (openParentHamiltonianES A R N) = groundSpaceES A N) :
    (leftBoundaryMapES A (K + L) r).range ⊓
      (reassocTailBoundaryMapES A K L r).range = groundSpaceES A (K + L + r) := by
  rw [← ker_openPrefixParentHamiltonianES_eq_range_leftBoundaryMapES A hR
      (hKernel (K + L) (by omega)),
    ← ker_openSuffixParentHamiltonianES_eq_range_reassocTailBoundaryMapES A hR
      (by omega) (hKernel (L + r) (by omega)),
    ker_openPrefix_inf_ker_openSuffix_eq_ker_openParentHamiltonianES A (by omega)
      (by omega), hKernel _ (by omega)]
/-- A periodic tensor with exact canonical open kernels has a common gap
at every sufficiently large original length if the stated residual cover
projection defect is at most 1/2. The aligned gap and the finitely many
terminal gaps are derived, not supplied.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma commutation (ii). This remains an auxiliary angle criterion. -/
theorem IsPeriodic.exists_pos_openParentHamiltonianES_gap_all_of_residue_cover_defect
    [NeZero d] {m R M K₀ : ℕ} {A : MPSTensor d D} (hA : IsPeriodic m A)
    (hR : 0 < R) (hRW : R ≤ M * m)
    (hKernel : ∀ N, R ≤ N →
      LinearMap.ker (openParentHamiltonianES A R N) = groundSpaceES A N)
    (hDefect : ∀ K ≥ K₀, ∀ r < m,
      ‖(groundSpaceES A (K * m + M * m + r)).starProjection -
        (leftBoundaryMapES A (K * m + M * m) r).range.starProjection.comp
          (reassocTailBoundaryMapES A (K * m) (M * m) r).range.starProjection‖ ≤
        (1 / 2 : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N, (K₀ + M) * m ≤ N → ∀ v ∈
      (LinearMap.ker (openParentHamiltonianES A R N))ᗮ,
      δ * ‖v‖ ≤ ‖openParentHamiltonianES A R N v‖ := by
  let : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
  have hker : ∀ᶠ n in Filter.atTop, LinearMap.ker
      (openInteractionHamiltonianES
        (Matrix.toEuclideanLin (canonicalParentInteractionMatrix A R)) n) =
        groundSpaceES A n := by
    filter_upwards [Filter.eventually_ge_atTop R] with n hn
    rw [toEuclideanLin_canonicalParentInteractionMatrix,
      openInteractionHamiltonianES_parentInteractionES A hR]
    exact hKernel n hn
  obtain ⟨γ, hγ, hGap⟩ := hA.exists_aligned_openInteractionMatrix_gap_of_eventual_kernel
    (canonicalParentInteractionMatrix A R) (canonicalParentInteractionMatrix_posSemidef A R)
    hR hker
  have hLeft : ∀ K ≥ K₀, ∀ v ∈
      (LinearMap.ker (openParentHamiltonianES A R (K * m + M * m)))ᗮ,
      γ * ‖v‖ ≤ ‖openParentHamiltonianES A R (K * m + M * m) v‖ := by
    intro K _
    have h := hGap (K + M)
    rw [← openInteractionHamiltonianES_eq_toEuclideanLin_openInteractionMatrix
        (canonicalParentInteractionMatrix A R) hR (by rw [Nat.add_mul]; omega),
      toEuclideanLin_canonicalParentInteractionMatrix,
      openInteractionHamiltonianES_parentInteractionES A hR] at h
    rw [← Nat.add_mul]
    exact h
  obtain ⟨δ, hδ, hResidue⟩ := exists_pos_openParentHamiltonianES_gap_of_aligned_cover_defect
    A hR hA.period_pos hRW hKernel hγ hLeft hDefect
  exact ⟨δ, hδ, openParentHamiltonianES_gap_all_large_of_residue_gaps A hA.period_pos hResidue⟩

end MPSTensor
