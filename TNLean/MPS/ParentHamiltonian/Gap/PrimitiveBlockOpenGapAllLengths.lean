/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.OpenFiniteRangeKnabeGap
import TNLean.MPS.ParentHamiltonian.Gap.Filtration.OverlappingIntervalGap
import TNLean.MPS.ParentHamiltonian.Gap.PrimitiveBlockGap
import TNLean.MPS.ParentHamiltonian.Gap.BlockOpenGroundSpaceAtSimultaneousInjectivity
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.BlockWordSpanNormalization
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.OpenRangeComparison
import TNLean.MPS.CanonicalForm.BlockSeparation.SharpBlocking

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

## Open-chain gaps at every length at simultaneous injectivity

A simultaneous word span at a positive length \(S\) gives a uniform positive
open-chain gap at each interaction range \(R\geq S+1\), for every chain
length \(N\geq R\). The tensor is a weighted direct sum with nonzero
coefficients. No primitive normalization or separation hypothesis is imposed
on the supplied blocks: these properties are derived from simultaneous
injectivity, with all local ground spaces preserved.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2 and Section 6;
arXiv:2011.12127, Section IV.C, lines 2114--2129.

**Scope restriction (sufficient interaction range):** The result assumes
\(R\geq S+1\). This is the sufficient range of the intersection argument,
not a restriction of the source definition of a parent interaction. The
shorter-range assertion is recorded in
`docs/paper-gaps/cpgsv21_block_parent_interaction_range.tex` and
`docs/paper-gaps/cpgsv21_short_range_parent_gap.tex`.

## Open-chain gaps for normal blocks at a dimension bound

Pairwise inequivalent normal blocks of total bond dimension \(D\) have a
simultaneous injectivity length \(S\) with \(S+1\leq3\max(D,1)^5\).
The all-length open-chain theorem therefore applies at every interaction
range above this dimension bound, without a supplied injectivity length.

Source: arXiv:1606.00608, lines 317--345; Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2 and Section 6.

**Scope restriction (sufficient interaction range):** The dimension bound is
sufficient and need not be optimal. The sharper theorem assumes
\(R\geq S+1\) at an actual simultaneous injectivity length. The restriction
is documented in `docs/paper-gaps/cpgsv21_block_parent_interaction_range.tex`.
-/

open MPTensor

section

open scoped Topology ComplexOrder

namespace MPSTensor
variable {d D : ℕ}
/-- An overlapping terminal interval removes the divisibility restriction
from the grouped open-chain gap. -/
private theorem open_gap_at_all_large_lengths (A : MPSTensor d D) {p : ℕ} (hp : 0 < p)
    {γ η : ℝ} (hγ : 0 < γ) (hη : 0 < η)
    (hKernel : ∀ N, 2 * p ≤ N →
      LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A (2 * p) N).hamiltonian) =
          ((groundSpace A N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap))
    (hLong : ∀ M, 2 ≤ M → ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
      (parentChainInteraction A (2 * p) (p * M)).hamiltonian) μ → μ = 0 ∨ (γ : ℂ) ≤ μ)
    (hShort : ∀ W, W < 3 * p → ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
      (parentChainInteraction A (2 * p) W).hamiltonian) μ → μ = 0 ∨ (η : ℂ) ≤ μ)
    (hDefect : ∀ (K Q : ℕ), 0 < Q → Q < p →
      ‖(((groundSpace A (K + 2 * p + Q)).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).starProjection :
        EuclideanSpace ℂ (Cfg d (K + 2 * p + Q)) →L[ℂ]
          EuclideanSpace ℂ (Cfg d (K + 2 * p + Q))) -
        ((leftBoundaryMapES A (K + 2 * p) Q).range.starProjection :
          EuclideanSpace ℂ (Cfg d (K + 2 * p + Q)) →L[ℂ]
            EuclideanSpace ℂ (Cfg d (K + 2 * p + Q))).comp
          (reassocTailBoundaryMapES A K (2 * p) Q).range.starProjection‖ ≤ (1 / 2 : ℝ)) :
    ∀ N, 3 * p ≤ N → ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
      (parentChainInteraction A (2 * p) N).hamiltonian) μ →
        μ = 0 ∨ ((min γ η / 16 : ℝ) : ℂ) ≤ μ := by
  intro N hN
  have hM : 3 ≤ N / p := (Nat.le_div_iff_mul_le hp).mpr hN
  rw [← Nat.div_add_mod N p] at hN ⊢
  have hq : N % p < p := Nat.mod_lt N hp
  have hn : 3 * p ≤ p * (N / p) := by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left p hM
  by_cases hq0 : N % p = 0
  · rw [hq0, Nat.add_zero]
    exact ManyBody.forall_hasEigenvalue_mono (by linarith [min_le_left γ η])
      (hLong (N / p) (by omega))
  · refine hamiltonian_parentChainInteraction_gap_of_overlapping_interval_gaps A
      (2 * p) (p * (N / p) + N % p) (p * (N / p)) (2 * p + N % p)
      (lt_min hγ hη).le ?_ ?_ ?_
    · exact ManyBody.forall_hasEigenvalue_mono (min_le_left γ η)
        (hamiltonian_prefix_parentChainInteraction_gap_of_local_gap A hγ
          (hLong (N / p) (by omega)))
    · exact ManyBody.forall_hasEigenvalue_mono (min_le_right γ η)
        (hamiltonian_restrict_parentChainInteraction_gap_of_local_gap A
          (by omega) (by omega) (by omega) le_rfl hη (hShort (2 * p + N % p) (by omega)))
    · have hlen : p * (N / p) - 2 * p + 2 * p = p * (N / p) := by omega
      rw [← hlen]
      rw [hKernel _ (by omega),
        ker_hamiltonian_prefix_parentChainInteraction_eq_range_leftBoundaryMapES A
          (hKernel _ (by omega)),
        ker_hamiltonian_restrict_parentChainInteraction_eq_range_reassocTailBoundaryMapES A
          (by omega) (by omega) (hKernel _ (by omega))]
      exact hDefect _ _ (by omega) hq

private theorem exists_pos_finite_open_gap (A : MPSTensor d D) (R M : ℕ) :
    ∃ η : ℝ, 0 < η ∧ ∀ W, W < M → ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction A R W).hamiltonian) μ →
        μ = 0 ∨ (η : ℂ) ≤ μ := by
  refine Nat.exists_pos_forall_of_eventually
    (P := fun W η ↦ W < M → ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction A R W).hamiltonian) μ →
        μ = 0 ∨ (η : ℂ) ≤ μ)
    ?_ ?_ (M := M) zero_lt_one ?_
  · exact fun N γ δ hle hgap hN ↦ ManyBody.forall_hasEigenvalue_mono hle (hgap hN)
  · exact fun N ↦ (ManyBody.exists_pos_forall_hasEigenvalue
      (posSemidef_hamiltonian_parentChainInteraction A R N)).imp fun η h ↦ ⟨h.1, fun _ ↦ h.2⟩
  · exact fun N hMN hNM ↦ False.elim (by omega)

variable {r : ℕ} {dim : Fin r → ℕ} [NeZero d] [∀ j, NeZero (dim j)]

/-- Inequivalent normalized primitive blocks admit an open parent interaction
with a positive gap uniform over every chain length: every eigenvalue of the open-chain parent
Hamiltonian is `0` or at least the gap. Its range can be chosen above any prescribed lower
bound. Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2 and Section 6,
Lemma `commutation` (ii). The grouped estimate is extended to other lengths
by a terminal interval overlapping the prefix in twice the grouping length. -/
theorem exists_ge_hamiltonian_parentChainInteraction_toTensorFromBlocks_gap_all_of_fixedPointGap
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i)) (Rmin : ℕ) :
    ∃ p : ℕ, Rmin ≤ p ∧ 0 < p ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ N : ℕ, ∀ z : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
        (parentChainInteraction (toTensorFromBlocks (α := Fin d) (μ := μ) A) (2 * p) N).hamiltonian)
          z → z = 0 ∨ (δ : ℂ) ≤ z := by
  obtain ⟨L₀, hL₀, hKernel⟩ :=
    exists_ker_hamiltonian_parentChainInteraction_toTensorFromBlocks_eq_map_groundSpace
      μ A hμ ρ hP hρ hDistinct
  obtain ⟨L₁, hDefect⟩ := Filter.eventually_atTop.1
    (eventually_toTensorFromBlocks_projector_defect_le μ A hμ ρ hP hρ hDistinct
      (η := (1 / 2 : ℝ)) (by norm_num))
  obtain ⟨p, hpBound, hp, γ, hγ, hLong⟩ :=
    exists_ge_hamiltonian_parentChainInteraction_toTensorFromBlocks_gap_of_fixedPointGap
      μ A hμ ρ hP hρ hDistinct (max Rmin (max L₀ L₁))
  let T := toTensorFromBlocks (α := Fin d) (μ := μ) A
  obtain ⟨η, hη, hShort⟩ := exists_pos_finite_open_gap T (2 * p) (3 * p)
  have hAllLarge := open_gap_at_all_large_lengths T hp hγ hη
    (fun N hN ↦ hKernel (2 * p) N (by omega) hN) hLong hShort
    (fun K Q hQ _ ↦ hDefect (2 * p) (by omega) K Q hQ)
  obtain ⟨δ, hδ, hGap⟩ := Nat.exists_pos_forall_of_eventually
    (P := fun N δ ↦ ∀ z : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction T (2 * p) N).hamiltonian) z →
        z = 0 ∨ (δ : ℂ) ≤ z)
    (fun N γ δ hle hgap ↦ ManyBody.forall_hasEigenvalue_mono hle hgap)
    (fun N ↦ ManyBody.exists_pos_forall_hasEigenvalue
      (posSemidef_hamiltonian_parentChainInteraction T (2 * p) N))
    (div_pos (lt_min hγ hη) (by norm_num)) hAllLarge
  exact ⟨p, by omega, hp, δ, hδ, hGap⟩

end MPSTensor

end

section

open scoped ComplexOrder

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ} [NeZero d] [∀ j, NeZero (dim j)]

/-- Simultaneous injectivity at a positive length \(S\) gives a positive
open-chain parent gap at every range \(R\geq S+1\), uniform over all
chain lengths \(N\geq R\). Primitive normalization, separation of blocks,
and equality of the open-chain kernel with the boundary-condition space are
derived internally. Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2
and Section 6; arXiv:2011.12127, Section IV.C, lines 2114--2129. -/
theorem exists_hamiltonian_parentChainInteraction_toTensorFromBlocks_gap_of_wordTupleSpanTop
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) {S R : ℕ} (hS : 0 < S)
    (hSpan : WordTupleSpanTop A S) (hR : S + 1 ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, R ≤ N → ∀ z : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
      (parentChainInteraction (toTensorFromBlocks (α := Fin d) (μ := μ) A) R N).hamiltonian) z →
        z = 0 ∨ (δ : ℂ) ≤ z := by
  obtain ⟨B, ρ, hP, hρ, hSpanB, hGS, _⟩ :=
    exists_hasComplementaryFixedPointGap_family_of_wordTupleSpanTop A hS hSpan
  let T := toTensorFromBlocks (α := Fin d) (μ := μ) B
  have hKernel : ∀ L N : ℕ, S + 1 ≤ L → L ≤ N →
      LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction T L N).hamiltonian) =
          ((groundSpace T N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) :=
    fun L N hSL hLN ↦
      ker_hamiltonian_parentChainInteraction_toTensorFromBlocks_eq_of_wordTupleSpanTop
        μ B hμ hS hSpanB hSL hLN
  obtain ⟨p, hRp, hp, γ, hγ, hLong⟩ :=
    exists_ge_hamiltonian_parentChainInteraction_toTensorFromBlocks_gap_all_of_fixedPointGap
      μ B hμ ρ hP hρ (fun i j hij h ↦ by
        simpa only [eqRec_eq_cast] using
          not_gaugePhaseEquiv_of_wordTupleSpanTop B hSpanB i j hij h) R
  obtain ⟨κ, C, hκ, _hC, hLocal, _hUpper⟩ :=
    exists_pos_toMatrix'_parentInteraction_hamiltonian_parentChainInteraction_comparison
      T (hKernel R (2 * p) hR (by omega))
  obtain ⟨δ, hδ, hGapB⟩ := Nat.exists_pos_forall_of_eventually
    (P := fun N δ ↦ ∀ z : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction T R N).hamiltonian) z →
        z = 0 ∨ (δ : ℂ) ≤ z)
    (fun N γ η hle hgap ↦ ManyBody.forall_hasEigenvalue_mono hle hgap)
    (fun N ↦ ManyBody.exists_pos_forall_hasEigenvalue
      (posSemidef_hamiltonian_parentChainInteraction T R N))
    (div_pos (mul_pos hκ hγ) (Nat.cast_pos.mpr (Nat.succ_pos (2 * p - R))))
    (fun N hN ↦ toEuclideanLin_hamiltonian_chainTranslates_gap_of_long_gap_at_length T _
      (posSemidef_toMatrix'_parentInteraction T R) (by omega) hκ hLocal
      (hKernel R N hR (by omega)) (hKernel (2 * p) N (by omega) hN) (hLong N))
  have hLocalGS : groundSpace (toTensorFromBlocks (α := Fin d) (μ := μ) A) R = groundSpace T R :=
    groundSpace_toTensorFromBlocks_eq_of_block_groundSpace_eq μ μ A B hμ hμ (fun j ↦ hGS j R)
  refine ⟨δ, hδ, fun N _ ↦ ?_⟩
  rw [parentChainInteraction_eq_of_groundSpace_eq hLocalGS N]
  exact hGapB N

end MPSTensor

end

section

open scoped ComplexOrder

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ} [NeZero d]

/-- Pairwise inequivalent normal blocks have a uniform open-chain gap at
range at least \(3\max(\sum_jD_j,1)^5\), for every chain containing an
interaction. Normalization and an injectivity length are derived internally.
Source: arXiv:1606.00608, lines 317--345; Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2 and Section 6. -/
theorem exists_hamiltonian_parentChainInteraction_toTensorFromBlocks_gap_of_isNormalTensor
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) (hNormal : ∀ j, IsNormalTensor (A j))
    (hDistinct : BlocksNotGaugePhaseEquiv A) {R : ℕ}
    (hR : 3 * (max (∑ j, dim j) 1) ^ 5 ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, R ≤ N → ∀ z : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin
          (parentChainInteraction (toTensorFromBlocks (α := Fin d) (μ := μ) A) R N).hamiltonian) z →
        z = 0 ∨ (δ : ℂ) ≤ z := by
  let : ∀ j, NeZero (dim j) := fun j ↦ ⟨(hNormal j).bondDim_ne_zero⟩
  obtain ⟨S, hS, hBound, hSpan⟩ :=
    exists_positive_wordTupleSpanTop_succ_le_three_cap_pow_five_of_isNormalTensor A
      (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) (le_max_left _ _) hNormal hDistinct
  exact exists_hamiltonian_parentChainInteraction_toTensorFromBlocks_gap_of_wordTupleSpanTop
    μ A hμ hS hSpan (hBound.trans hR)

end MPSTensor

end
