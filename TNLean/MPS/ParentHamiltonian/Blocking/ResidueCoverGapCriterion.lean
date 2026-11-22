/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Gap.Filtration.OverlappingIntervalGap
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.IntervalGapTransport
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.IntervalKernelTransport
import TNLean.MPS.ParentHamiltonian.Blocking.BlockedFiniteGapTransport
import TNLean.MPS.ParentHamiltonian.ParentInteraction.CanonicalParentInteractionMatrix
import QICLean.Analysis.Topology.UniformSelectionBounds
import QICLean.Spectral.Gap.OrthogonalKernelGap
import TNLean.MPS.ParentHamiltonian.Interaction.PeriodicOriginalIntersection

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

## A uniform open gap from aligned gaps and residual covers

For an arbitrary tensor, an eventual gap at lengths divisible by a fixed
positive integer extends to all original lengths once the canonical kernels
are exact and the residual cover projection defects vanish uniformly along
every choice of the exterior lengths. The finitely many remaining volumes
are included by taking a positive finite minimum above their actual kernels.

The aligned gap, exact kernels, and projection limits are explicit hypotheses.
This is an auxiliary criterion, rather than a tensor-specific gap theorem.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6, Lemma commutation
(ii), and equations (3.12)--(3.16).

## From residual cover projection limits to an open-chain gap

Suppose a periodic tensor has a vanishing three-interval projection defect
along every choice of the prefix and tail lengths, as the overlap length
in periods tends to infinity. An elementary selection argument gives one
overlap length for which the defect is at most one half for every prefix
and tail. Periodicity supplies a canonical range with exact open kernels;
the residue cover criterion then supplies one positive norm gap at all
sufficiently large original lengths.

This is a limit criterion: the stated projection-defect convergence is an
explicit hypothesis. No tensor-specific proof of that convergence is made
in this module. The result is not an unconditional periodic tensor gap
theorem.

Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma commutation (ii), and equations (3.12)--(3.16).
-/

section

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

end

section

open Filter
open scoped InnerProductSpace
namespace MPSTensor
variable {d D R L N₀ : ℕ}

/-- An eventual aligned norm gap, exact canonical open kernels, and residual
cover projection limits imply a single norm gap at every original length.
The gap is above the actual kernel at each length. Source: Nachtergaele,
arXiv:cond-mat/9410110, Section 6, Lemma commutation (ii).
The three supplied estimates are explicit hypotheses of this criterion. -/
theorem exists_pos_openParentHamiltonianES_gap_of_aligned_gap_of_residue_cover_limit
    (A : MPSTensor d D) (hR : 0 < R) (hL : 0 < L)
    (hKernel : ∀ N, R ≤ N →
      LinearMap.ker (openParentHamiltonianES A R N) = groundSpaceES A N)
    {γ : ℝ} (hγ : 0 < γ)
    (hAligned : ∀ n ≥ N₀, ∀ v ∈
      (LinearMap.ker (openParentHamiltonianES A R (n * L)))ᗮ,
      γ * ‖v‖ ≤ ‖openParentHamiltonianES A R (n * L) v‖)
    (hDefect : ∀ K r : ℕ → ℕ, Tendsto (fun M =>
      ‖(groundSpaceES A (K M * L + M * L + r M)).starProjection -
        (leftBoundaryMapES A (K M * L + M * L) (r M)).range.starProjection.comp
          (reassocTailBoundaryMapES A (K M * L) (M * L) (r M)).range.starProjection‖)
      atTop (nhds 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N,
      ∀ v ∈ (LinearMap.ker (openParentHamiltonianES A R N))ᗮ,
        δ * ‖v‖ ≤ ‖openParentHamiltonianES A R N v‖ := by
  let e (M : ℕ) (z : ℕ × ℕ) : ℝ :=
    ‖(groundSpaceES A (z.1 * L + M * L + z.2)).starProjection -
      (leftBoundaryMapES A (z.1 * L + M * L) z.2).range.starProjection.comp
        (reassocTailBoundaryMapES A (z.1 * L) (M * L) z.2).range.starProjection‖
  have hUniform : ∀ᶠ M in atTop, ∀ z, e M z ≤ (1 / 2 : ℝ) :=
    eventually_forall_le_of_tendsto_all_selections e
      (fun z => hDefect (fun M => (z M).1) (fun M => (z M).2)) (by norm_num)
  obtain ⟨M, hM, hRM⟩ := (hUniform.and (eventually_ge_atTop (max R N₀))).exists
  have hRW : R ≤ M * L :=
    (le_max_left R N₀).trans (hRM.trans (Nat.le_mul_of_pos_right M hL))
  have hLeft : ∀ K ≥ 0, ∀ v ∈
      (LinearMap.ker (openParentHamiltonianES A R (K * L + M * L)))ᗮ,
      γ * ‖v‖ ≤ ‖openParentHamiltonianES A R (K * L + M * L) v‖ := by
    intro K _
    rw [← Nat.add_mul]
    exact hAligned (K + M) (by omega)
  obtain ⟨δ, hδ, hResidue⟩ :=
    exists_pos_openParentHamiltonianES_gap_of_aligned_cover_defect
      A hR hL hRW hKernel hγ hLeft (fun K _ r _ => hM (K, r))
  have hTail := openParentHamiltonianES_gap_all_large_of_residue_gaps A hL hResidue
  exact Nat.exists_pos_forall_of_eventually
    (P := fun N δ => ∀ v ∈ (LinearMap.ker (openParentHamiltonianES A R N))ᗮ,
      δ * ‖v‖ ≤ ‖openParentHamiltonianES A R N v‖)
    (fun N δ η hle hgap v hv =>
      (mul_le_mul_of_nonneg_right hle (norm_nonneg v)).trans (hgap v hv))
    (fun N => LinearMap.exists_pos_mul_norm_le_of_mem_orthogonal_ker
      (openParentHamiltonianES A R N)) hδ hTail

end MPSTensor

end

section

open scoped InnerProductSpace
namespace MPSTensor
variable {d D m : ℕ}

/-- Vanishing physical cover defects along every prefix and tail selection
imply a common canonical open-parent gap at every sufficiently large original
length. The range and exact open kernels are derived from periodicity.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma commutation (ii), and equations (3.12)--(3.16). The projection limit
remains an explicit hypothesis of this auxiliary criterion. -/
theorem IsPeriodic.exists_pos_openParentHamiltonianES_gap_of_residue_cover_limit
    [NeZero d] {A : MPSTensor d D} (hA : IsPeriodic m A)
    (hDefect : ∀ K r : ℕ → ℕ, Filter.Tendsto (fun M =>
      ‖(groundSpaceES A (K M * m + M * m + r M)).starProjection -
        (leftBoundaryMapES A (K M * m + M * m) (r M)).range.starProjection.comp
          (reassocTailBoundaryMapES A (K M * m) (M * m) (r M)).range.starProjection‖)
      Filter.atTop (nhds 0)) :
    ∃ R : ℕ, 0 < R ∧
      (∀ N, R ≤ N → LinearMap.ker (openParentHamiltonianES A R N) = groundSpaceES A N) ∧
      ∃ N₀ : ℕ, R ≤ N₀ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ N, N₀ ≤ N → ∀ v ∈ (LinearMap.ker (openParentHamiltonianES A R N))ᗮ,
        δ * ‖v‖ ≤ ‖openParentHamiltonianES A R N v‖ := by
  obtain ⟨R, hR, hKernel⟩ := hA.exists_ker_openParentHamiltonianES_eq_groundSpaceES
  let e (M : ℕ) (z : ℕ × ℕ) : ℝ :=
    ‖(groundSpaceES A (z.1 * m + M * m + z.2)).starProjection -
      (leftBoundaryMapES A (z.1 * m + M * m) z.2).range.starProjection.comp
        (reassocTailBoundaryMapES A (z.1 * m) (M * m) z.2).range.starProjection‖
  have hUniform : ∀ᶠ M in Filter.atTop, ∀ z, e M z ≤ (1 / 2 : ℝ) :=
    Filter.eventually_forall_le_of_tendsto_all_selections e
      (fun x => hDefect (fun M => (x M).1) (fun M => (x M).2)) (by norm_num)
  obtain ⟨M, hM, hRM⟩ := (hUniform.and (Filter.eventually_ge_atTop R)).exists
  have hRW : R ≤ M * m := hRM.trans (Nat.le_mul_of_pos_right M hA.period_pos)
  obtain ⟨δ, hδ, hGap⟩ :=
    hA.exists_pos_openParentHamiltonianES_gap_all_of_residue_cover_defect (K₀ := 0)
      hR hRW (fun N => hKernel R N le_rfl) (fun K _ r _ => hM (K, r))
  exact ⟨R, hR, (fun N hN => hKernel R N le_rfl hN), M * m, hRW, δ, hδ,
    by simpa only [Nat.zero_add] using hGap⟩

end MPSTensor

end
