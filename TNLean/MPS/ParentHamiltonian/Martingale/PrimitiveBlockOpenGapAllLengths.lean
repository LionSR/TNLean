/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.IntervalGapTransport
import TNLean.MPS.ParentHamiltonian.Martingale.IntervalKernelTransport
import TNLean.MPS.ParentHamiltonian.Martingale.OverlappingIntervalGap
import TNLean.MPS.ParentHamiltonian.Martingale.PrimitiveBlockGap

/-!
# Uniform open-chain gaps at every length for primitive block sums

Write an arbitrary large chain length as \(N=pM+q\), with \(0\leq q<p\).
The grouped theorem controls the prefix of length \(pM\). A terminal interval
of length \(2p+q\) overlaps this prefix in \(2p\) sites, so the three-interval
projector estimate combines their gaps. There are only finitely many terminal
lengths. The remaining finitely many full-chain lengths are handled by their
finite-dimensional positive gaps on the complements of their kernels.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2, Theorem 2.1(ii),
and the three-interval estimate of Section 6, Lemma `commutation` (ii).
-/

open scoped Topology ComplexOrder

namespace MPSTensor
variable {d D : ℕ}
/-- An overlapping terminal interval removes the divisibility restriction
from the grouped open-chain gap. -/
private theorem open_gap_at_all_large_lengths (A : MPSTensor d D) {p : ℕ} (hp : 0 < p)
    {γ η : ℝ} (hγ : 0 < γ) (hη : 0 < η)
    (hKernel : ∀ N, 2 * p ≤ N →
      LinearMap.ker (openParentHamiltonianES A (2 * p) N) = groundSpaceES A N)
    (hLong : ∀ M, 2 ≤ M → ∀ v ∈
      (LinearMap.ker (openParentHamiltonianES A (2 * p) (p * M)))ᗮ,
      γ * ‖v‖ ≤ ‖openParentHamiltonianES A (2 * p) (p * M) v‖)
    (hShort : ∀ W, W < 3 * p → ∀ v ∈
      (LinearMap.ker (openParentHamiltonianES A (2 * p) W))ᗮ,
      η * ‖v‖ ≤ ‖openParentHamiltonianES A (2 * p) W v‖)
    (hDefect : ∀ (K Q : ℕ), 0 < Q → Q < p →
      ‖((groundSpaceES A (K + 2 * p + Q)).starProjection :
        EuclideanSpace ℂ (Cfg d (K + 2 * p + Q)) →L[ℂ]
          EuclideanSpace ℂ (Cfg d (K + 2 * p + Q))) -
        ((leftBoundaryMapES A (K + 2 * p) Q).range.starProjection :
          EuclideanSpace ℂ (Cfg d (K + 2 * p + Q)) →L[ℂ]
            EuclideanSpace ℂ (Cfg d (K + 2 * p + Q))).comp
          (reassocTailBoundaryMapES A K (2 * p) Q).range.starProjection‖ ≤ (1 / 2 : ℝ)) :
    ∀ N, 3 * p ≤ N → ∀ v ∈
      (LinearMap.ker (openParentHamiltonianES A (2 * p) N))ᗮ,
      (min γ η / 16) * ‖v‖ ≤ ‖openParentHamiltonianES A (2 * p) N v‖ := by
  intro N hN
  have hM : 3 ≤ N / p := (Nat.le_div_iff_mul_le hp).mpr hN
  rw [← Nat.div_add_mod N p] at hN ⊢
  have hq : N % p < p := Nat.mod_lt N hp
  have hn : 3 * p ≤ p * (N / p) := by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left p hM
  by_cases hq0 : N % p = 0
  · rw [hq0, Nat.add_zero]
    exact fun v hv ↦ (mul_le_mul_of_nonneg_right
      (show min γ η / 16 ≤ γ by linarith [min_le_left γ η]) (norm_nonneg v)).trans
        (hLong (N / p) (by omega) v hv)
  · refine openParentHamiltonianES_norm_gap_of_overlapping_interval_gaps A
      (2 * p) (p * (N / p) + N % p) (p * (N / p)) (2 * p + N % p)
      (lt_min hγ hη).le ?_ ?_ ?_
    · exact fun v hv ↦ (mul_le_mul_of_nonneg_right (min_le_left γ η) (norm_nonneg v)).trans
        (openPrefixParentHamiltonianES_norm_gap_of_local_gap A (by omega) hγ
          (hLong (N / p) (by omega)) v hv)
    · exact fun v hv ↦ (mul_le_mul_of_nonneg_right (min_le_right γ η) (norm_nonneg v)).trans
        (openSuffixParentHamiltonianES_norm_gap_of_local_gap A
          (by omega) (by omega) (by omega) le_rfl hη
          (hShort (2 * p + N % p) (by omega)) v hv)
    · have hlen : p * (N / p) - 2 * p + 2 * p = p * (N / p) := by omega
      rw [← hlen]
      rw [hKernel _ (by omega),
        ker_openPrefixParentHamiltonianES_eq_range_leftBoundaryMapES A (by omega)
          (hKernel _ (by omega)),
        ker_openSuffixParentHamiltonianES_eq_range_reassocTailBoundaryMapES A
          (by omega) (by omega) (hKernel _ (by omega))]
      exact hDefect _ _ (by omega) hq

private theorem exists_pos_finite_open_gap (A : MPSTensor d D) (R M : ℕ) :
    ∃ η : ℝ, 0 < η ∧ ∀ W, W < M → ∀ v ∈
      (LinearMap.ker (openParentHamiltonianES A R W))ᗮ,
      η * ‖v‖ ≤ ‖openParentHamiltonianES A R W v‖ := by
  refine Nat.exists_pos_forall_of_eventually
    (P := fun W η ↦ W < M → ∀ v ∈ (LinearMap.ker (openParentHamiltonianES A R W))ᗮ,
      η * ‖v‖ ≤ ‖openParentHamiltonianES A R W v‖)
    ?_ ?_ (M := M) zero_lt_one ?_
  · exact fun N γ δ hle hgap hN v hv ↦
      (mul_le_mul_of_nonneg_right hle (norm_nonneg v)).trans (hgap hN v hv)
  · exact fun N ↦ (LinearMap.exists_pos_mul_norm_le_of_mem_orthogonal_ker
      (openParentHamiltonianES A R N)).imp fun η h ↦ ⟨h.1, fun _ ↦ h.2⟩
  · exact fun N hMN hNM ↦ False.elim (by omega)

variable {r : ℕ} {dim : Fin r → ℕ} [NeZero d] [∀ j, NeZero (dim j)]
/-- Inequivalent normalized primitive blocks admit an open parent interaction
with a positive gap uniform over every chain length. Its range can be chosen
above any prescribed lower bound. At lengths below the interaction range,
the operator is zero and the assertion on its kernel complement is vacuous.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2 and Section 6,
Lemma `commutation` (ii). The grouped estimate is extended to other lengths
by a terminal interval overlapping the prefix in twice the grouping length. -/
theorem exists_ge_openParentHamiltonianES_toTensorFromBlocks_gap_all_of_isPrimitiveMPS
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i)) (Rmin : ℕ) :
    ∃ p : ℕ, Rmin ≤ p ∧ 0 < p ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ N : ℕ, ∀ v ∈
        (LinearMap.ker (openParentHamiltonianES
          (toTensorFromBlocks (d := d) (μ := μ) A) (2 * p) N))ᗮ,
        δ * ‖v‖ ≤ ‖openParentHamiltonianES
          (toTensorFromBlocks (d := d) (μ := μ) A) (2 * p) N v‖ := by
  obtain ⟨L₀, hL₀, hKernel⟩ :=
    exists_ker_openParentHamiltonianES_toTensorFromBlocks_eq_groundSpaceES_of_isPrimitiveMPS
      μ A hμ ρ hP hρ hDistinct
  obtain ⟨L₁, hDefect⟩ := Filter.eventually_atTop.1
    (eventually_toTensorFromBlocks_projector_defect_le μ A hμ ρ hP hρ hDistinct
      (η := (1 / 2 : ℝ)) (by norm_num))
  obtain ⟨p, hpBound, hp, γ, hγ, hLong⟩ :=
    exists_ge_openParentHamiltonianES_toTensorFromBlocks_gap_of_isPrimitiveMPS
      μ A hμ ρ hP hρ hDistinct (max Rmin (max L₀ L₁))
  let T := toTensorFromBlocks (d := d) (μ := μ) A
  obtain ⟨η, hη, hShort⟩ := exists_pos_finite_open_gap T (2 * p) (3 * p)
  have hAllLarge := open_gap_at_all_large_lengths T hp hγ hη
    (fun N hN ↦ hKernel (2 * p) N (by omega) hN) hLong hShort
    (fun K Q hQ _ ↦ hDefect (2 * p) (by omega) K Q hQ)
  obtain ⟨δ, hδ, hGap⟩ := Nat.exists_pos_forall_of_eventually
    (P := fun N δ ↦ ∀ v ∈ (LinearMap.ker (openParentHamiltonianES T (2 * p) N))ᗮ,
      δ * ‖v‖ ≤ ‖openParentHamiltonianES T (2 * p) N v‖)
    (fun N γ δ hle hgap v hv ↦
      (mul_le_mul_of_nonneg_right hle (norm_nonneg v)).trans (hgap v hv))
    (fun N ↦ LinearMap.exists_pos_mul_norm_le_of_mem_orthogonal_ker
      (openParentHamiltonianES T (2 * p) N))
    (div_pos (lt_min hγ hη) (by norm_num)) hAllLarge
  exact ⟨p, by omega, hp, δ, hδ, hGap⟩
end MPSTensor
