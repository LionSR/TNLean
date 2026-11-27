/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Gap.Filtration.OverlappingIntervalGap
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.OpenFiniteRangeKnabeGap
import TNLean.MPS.ParentHamiltonian.Blocking.BlockedFiniteGapTransport
import TNLean.MPS.ParentHamiltonian.ParentInteraction.Transport
import QICLean.Analysis.Topology.UniformSelectionBounds
import QICLean.Spectral.Gap.EigenvalueGap
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

/-- The finitely many terminal volumes W+r, with r<m, of the Hamiltonian of the parent
interaction on the open chain have a common positive gap above their actual kernels: every
eigenvalue is `0` or at least the gap. Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma commutation (ii), and equations (3.12)--(3.16). -/
theorem exists_pos_hamiltonian_parentChainInteraction_gap_over_residues
    (A : MPSTensor d D) (R W m : ℕ) (hm : 0 < m) :
    ∃ η : ℝ, 0 < η ∧ ∀ r < m, ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction A R (W + r)).hamiltonian) μ →
        μ = 0 ∨ (η : ℂ) ≤ μ := by
  classical
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  choose δ hδ hGap using fun r : Fin m =>
    ManyBody.exists_pos_forall_hasEigenvalue
      (posSemidef_hamiltonian_parentChainInteraction A R (W + r.val))
  let η := Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin m)).Nonempty) δ
  have hη : 0 < η := by
    simp only [η, Finset.lt_inf'_iff, Finset.mem_univ, forall_const]
    exact hδ
  exact ⟨η, hη, fun r hr μ hμ => (hGap ⟨r, hr⟩ μ hμ).imp_right
    (Complex.real_le_real.mpr (Finset.inf'_le δ (Finset.mem_univ (⟨r, hr⟩ : Fin m)))).trans⟩

/-- Residue bounds of the Hamiltonian of the parent interaction on the open chain beyond a
common quotient threshold give the same gap at every sufficiently large original length.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6, Lemma commutation (ii), and equations
(3.12)--(3.16). -/
theorem hamiltonian_parentChainInteraction_gap_all_large_of_residue_gaps
    (A : MPSTensor d D) {R m M K₀ : ℕ} (hm : 0 < m) {δ : ℝ}
    (hGap : ∀ K ≥ K₀, ∀ r < m, ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
        (parentChainInteraction A R (K * m + M * m + r)).hamiltonian) μ → μ = 0 ∨ (δ : ℂ) ≤ μ) :
    ∀ N, (K₀ + M) * m ≤ N → ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) μ →
        μ = 0 ∨ (δ : ℂ) ≤ μ := by
  intro N hN
  have hquot : K₀ + M ≤ N / m := (Nat.le_div_iff_mul_le hm).mpr hN
  have hEq : (N / m - M) * m + M * m + N % m = N := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
    simpa only [Nat.mul_comm] using Nat.div_add_mod N m
  rw [← hEq]
  exact hGap (N / m - M) (by omega) (N % m) (Nat.mod_lt N hm)

/-- The full open-chain kernel is contained in every prefix kernel.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma commutation (ii), and equations (3.12)--(3.16). -/
theorem ker_hamiltonian_parentChainInteraction_le_ker_hamiltonian_prefix
    (A : MPSTensor d D) (R N n : ℕ) :
    LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) ≤
      LinearMap.ker (Matrix.toEuclideanLin
        ((parentChainInteraction A R N).restrict fun i ↦ i.val + R ≤ n).hamiltonian) := by
  intro v hv
  rw [ManyBody.Interaction.mem_ker_toEuclideanLin_hamiltonian_iff
    (posSemidef_parentChainInteraction_term A R N)] at hv
  rw [ManyBody.Interaction.mem_ker_toEuclideanLin_hamiltonian_restrict_iff
    (posSemidef_parentChainInteraction_term A R N)]
  exact fun i _ ↦ hv i
/-- An aligned prefix gap and an explicit three-interval projection defect give a
common positive gap in every residue. The terminal gap is derived by finite
dimensionality.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma commutation (ii), and equations (3.12)--(3.16). -/
theorem exists_pos_hamiltonian_parentChainInteraction_gap_of_aligned_cover_defect
    (A : MPSTensor d D) {R m M K₀ : ℕ} (hR : 0 < R) (hm : 0 < m)
    (hRW : R ≤ M * m)
    (hKernel : ∀ N, R ≤ N →
      LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) =
          ((groundSpace A N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap))
    {γ : ℝ} (hγ : 0 < γ)
    (hLeft : ∀ K ≥ K₀, ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
      (parentChainInteraction A R (K * m + M * m)).hamiltonian) μ → μ = 0 ∨ (γ : ℂ) ≤ μ)
    (hDefect : ∀ K ≥ K₀, ∀ r < m,
      ‖((groundSpace A (K * m + M * m + r)).map (WithLp.linearEquiv 2 ℂ
          _).symm.toLinearMap).starProjection -
        (leftBoundaryMapES A (K * m + M * m) r).range.starProjection.comp
          (reassocTailBoundaryMapES A (K * m) (M * m) r).range.starProjection‖ ≤
        (1 / 2 : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ K ≥ K₀, ∀ r < m, ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction A R (K * m + M * m + r)).hamiltonian) μ →
        μ = 0 ∨ (δ : ℂ) ≤ μ := by
  obtain ⟨η, hη, hRight⟩ :=
    exists_pos_hamiltonian_parentChainInteraction_gap_over_residues A R (M * m) m hm
  refine ⟨min γ η / 16, div_pos (lt_min hγ hη) (by norm_num),
    fun K hK r hr => ?_⟩
  apply hamiltonian_parentChainInteraction_gap_of_overlapping_interval_gaps
    A R (K * m + M * m + r) (K * m + M * m) (M * m + r) (lt_min hγ hη).le
  · exact ManyBody.forall_hasEigenvalue_mono (min_le_left γ η)
      (hamiltonian_prefix_parentChainInteraction_gap_of_local_gap A hγ (hLeft K hK))
  · exact ManyBody.forall_hasEigenvalue_mono (min_le_right γ η)
      (hamiltonian_restrict_parentChainInteraction_gap_of_local_gap A hR (by omega)
        (by omega) le_rfl hη (hRight r hr))
  · rw [hKernel _ (by omega),
      ker_hamiltonian_prefix_parentChainInteraction_eq_range_leftBoundaryMapES A
        (hKernel _ (by omega)),
      ker_hamiltonian_restrict_parentChainInteraction_eq_range_reassocTailBoundaryMapES A hR
        (by omega) (hKernel _ (by omega))]
    exact hDefect K hK r hr
/-- Two covering intervals have exactly the full open-chain kernel in common, provided
every local interaction window is contained in one of them.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma commutation (ii), and equations (3.12)--(3.16). -/
theorem ker_hamiltonian_prefix_inf_ker_hamiltonian_restrict_parentChainInteraction
    (A : MPSTensor d D) {R N n W : ℕ}
    (hcover : N + R ≤ n + W + 1) :
    LinearMap.ker
        (Matrix.toEuclideanLin
            ((parentChainInteraction A R N).restrict fun i ↦ i.val + R ≤ n).hamiltonian) ⊓
      LinearMap.ker
          (Matrix.toEuclideanLin
              ((parentChainInteraction A R N).restrict fun i ↦ N - W ≤ i.val ∧ i.val + R ≤
                  N).hamiltonian) =
      LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) := by
  have hpos := posSemidef_parentChainInteraction_term A R N
  ext v
  rw [Submodule.mem_inf, ManyBody.Interaction.mem_ker_toEuclideanLin_hamiltonian_restrict_iff hpos,
    ManyBody.Interaction.mem_ker_toEuclideanLin_hamiltonian_restrict_iff hpos,
    ManyBody.Interaction.mem_ker_toEuclideanLin_hamiltonian_iff hpos]
  exact ⟨fun ⟨hl, hr⟩ i ↦ if hi : i.val + R ≤ n then hl i hi else hr i (by omega),
    fun h ↦ ⟨fun i _ ↦ h i, fun i _ ↦ h i⟩⟩
/-- The extended prefix and terminal boundary spaces intersect exactly in
G_N whenever the original canonical open kernels are the boundary spaces.
Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.10)--(3.16)
and Section 6, Lemma commutation (ii). -/
theorem leftBoundary_inf_reassocTail_range_eq_map_groundSpace_of_open_kernel
    (A : MPSTensor d D) {R K L r : ℕ} (hR : 0 < R) (hRL : R ≤ L)
    (hKernel : ∀ N, R ≤ N →
      LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) =
          ((groundSpace A N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) :
    (leftBoundaryMapES A (K + L) r).range ⊓
      (reassocTailBoundaryMapES A K L r).range = ((groundSpace A (K + L + r)).map
          (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) := by
  rw [← ker_hamiltonian_prefix_parentChainInteraction_eq_range_leftBoundaryMapES A
      (hKernel (K + L) (by omega)),
    ← ker_hamiltonian_restrict_parentChainInteraction_eq_range_reassocTailBoundaryMapES A hR
      (by omega) (hKernel (L + r) (by omega)),
    ker_hamiltonian_prefix_inf_ker_hamiltonian_restrict_parentChainInteraction A
      (by omega), hKernel _ (by omega)]
/-- A periodic tensor with exact canonical open kernels has a common gap
at every sufficiently large original length if the stated residual cover
projection defect is at most 1/2. The aligned gap and the finitely many
terminal gaps are derived, not supplied.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma commutation (ii). This remains an auxiliary angle criterion. -/
theorem IsPeriodic.exists_pos_hamiltonian_parentChainInteraction_gap_all_of_residue_cover_defect
    [NeZero d] {m R M K₀ : ℕ} {A : MPSTensor d D} (hA : IsPeriodic m A)
    (hR : 0 < R) (hRW : R ≤ M * m)
    (hKernel : ∀ N, R ≤ N →
      LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) =
          ((groundSpace A N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap))
    (hDefect : ∀ K ≥ K₀, ∀ r < m,
      ‖((groundSpace A (K * m + M * m + r)).map (WithLp.linearEquiv 2 ℂ
          _).symm.toLinearMap).starProjection -
        (leftBoundaryMapES A (K * m + M * m) r).range.starProjection.comp
          (reassocTailBoundaryMapES A (K * m) (M * m) r).range.starProjection‖ ≤
        (1 / 2 : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N, (K₀ + M) * m ≤ N → ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) μ →
        μ = 0 ∨ (δ : ℂ) ≤ μ := by
  let : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
  have hker : ∀ᶠ n in Filter.atTop, LinearMap.ker
      (Matrix.toEuclideanLin (parentChainInteraction A R n).hamiltonian) =
        ((groundSpace A n).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) := by
    filter_upwards [Filter.eventually_ge_atTop R] with n hn using hKernel n hn
  obtain ⟨γ, hγ, hGap⟩ := hA.exists_aligned_hamiltonian_chainTranslates_gap_of_eventual_kernel
    (LinearMap.toMatrix' (parentInteraction A R)) (posSemidef_toMatrix'_parentInteraction A R)
    hker
  have hLeft : ∀ K ≥ K₀, ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
      (parentChainInteraction A R (K * m + M * m)).hamiltonian) μ → μ = 0 ∨ (γ : ℂ) ≤ μ := by
    intro K _
    have h := hGap (K + M)
    rw [Nat.add_mul] at h
    exact h
  obtain ⟨δ, hδ, hResidue⟩ :=
      exists_pos_hamiltonian_parentChainInteraction_gap_of_aligned_cover_defect
    A hR hA.period_pos hRW hKernel hγ hLeft hDefect
  exact ⟨δ, hδ, hamiltonian_parentChainInteraction_gap_all_large_of_residue_gaps A hA.period_pos
      hResidue⟩

end MPSTensor

end

section

open Filter
open scoped InnerProductSpace ComplexOrder
namespace MPSTensor
variable {d D R L N₀ : ℕ}

/-- An eventual aligned gap, exact canonical open kernels, and residual
cover projection limits imply a single gap at every original length: every eigenvalue of the
open-chain parent Hamiltonian is `0` or at least the gap. Source: Nachtergaele,
arXiv:cond-mat/9410110, Section 6, Lemma commutation (ii).
The three supplied estimates are explicit hypotheses of this criterion. -/
theorem exists_pos_hamiltonian_parentChainInteraction_gap_of_aligned_gap_of_residue_cover_limit
    (A : MPSTensor d D) (hR : 0 < R) (hL : 0 < L)
    (hKernel : ∀ N, R ≤ N →
      LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) =
          ((groundSpace A N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap))
    {γ : ℝ} (hγ : 0 < γ)
    (hAligned : ∀ n ≥ N₀, ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction A R (n * L)).hamiltonian) μ →
        μ = 0 ∨ (γ : ℂ) ≤ μ)
    (hDefect : ∀ K r : ℕ → ℕ, Tendsto (fun M =>
      ‖((groundSpace A (K M * L + M * L + r M)).map (WithLp.linearEquiv 2 ℂ
          _).symm.toLinearMap).starProjection -
        (leftBoundaryMapES A (K M * L + M * L) (r M)).range.starProjection.comp
          (reassocTailBoundaryMapES A (K M * L) (M * L) (r M)).range.starProjection‖)
      atTop (nhds 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N,
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ := by
  let e (M : ℕ) (z : ℕ × ℕ) : ℝ :=
    ‖((groundSpace A (z.1 * L + M * L + z.2)).map (WithLp.linearEquiv 2 ℂ
        _).symm.toLinearMap).starProjection -
      (leftBoundaryMapES A (z.1 * L + M * L) z.2).range.starProjection.comp
        (reassocTailBoundaryMapES A (z.1 * L) (M * L) z.2).range.starProjection‖
  have hUniform : ∀ᶠ M in atTop, ∀ z, e M z ≤ (1 / 2 : ℝ) :=
    eventually_forall_le_of_tendsto_all_selections e
      (fun z => hDefect (fun M => (z M).1) (fun M => (z M).2)) (by norm_num)
  obtain ⟨M, hM, hRM⟩ := (hUniform.and (eventually_ge_atTop (max R N₀))).exists
  have hRW : R ≤ M * L :=
    (le_max_left R N₀).trans (hRM.trans (Nat.le_mul_of_pos_right M hL))
  have hLeft : ∀ K ≥ 0, ∀ μ : ℂ, Module.End.HasEigenvalue
    (Matrix.toEuclideanLin (parentChainInteraction A R (K * L + M * L)).hamiltonian) μ →
      μ = 0 ∨ (γ : ℂ) ≤ μ := by
    intro K _
    rw [← Nat.add_mul]
    exact hAligned (K + M) (by omega)
  obtain ⟨δ, hδ, hResidue⟩ :=
    exists_pos_hamiltonian_parentChainInteraction_gap_of_aligned_cover_defect
      A hR hL hRW hKernel hγ hLeft (fun K _ r _ => hM (K, r))
  have hTail := hamiltonian_parentChainInteraction_gap_all_large_of_residue_gaps A hL hResidue
  exact Nat.exists_pos_forall_of_eventually
    (P := fun N δ => ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) μ →
        μ = 0 ∨ (δ : ℂ) ≤ μ)
    (fun N δ η hle hgap => ManyBody.forall_hasEigenvalue_mono hle hgap)
    (fun N => ManyBody.exists_pos_forall_hasEigenvalue
      (posSemidef_hamiltonian_parentChainInteraction A R N)) hδ hTail

end MPSTensor

end

section

open scoped InnerProductSpace ComplexOrder
namespace MPSTensor
variable {d D m : ℕ}

/-- Vanishing physical cover defects along every prefix and tail selection
imply a common canonical open-parent gap at every sufficiently large original
length. The range and exact open kernels are derived from periodicity.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma commutation (ii), and equations (3.12)--(3.16). The projection limit
remains an explicit hypothesis of this auxiliary criterion. -/
theorem IsPeriodic.exists_pos_hamiltonian_parentChainInteraction_gap_of_residue_cover_limit
    [NeZero d] {A : MPSTensor d D} (hA : IsPeriodic m A)
    (hDefect : ∀ K r : ℕ → ℕ, Filter.Tendsto (fun M =>
      ‖((groundSpace A (K M * m + M * m + r M)).map (WithLp.linearEquiv 2 ℂ
          _).symm.toLinearMap).starProjection -
        (leftBoundaryMapES A (K M * m + M * m) (r M)).range.starProjection.comp
          (reassocTailBoundaryMapES A (K M * m) (M * m) (r M)).range.starProjection‖)
      Filter.atTop (nhds 0)) :
    ∃ R : ℕ, 0 < R ∧
      (∀ N, R ≤ N → LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian)
          = ((groundSpace A N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) ∧
      ∃ N₀ : ℕ, R ≤ N₀ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ N, N₀ ≤ N → ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ := by
  obtain ⟨R, hR, hKernel⟩ := hA.exists_ker_hamiltonian_parentChainInteraction_eq_map_groundSpace
  let e (M : ℕ) (z : ℕ × ℕ) : ℝ :=
    ‖((groundSpace A (z.1 * m + M * m + z.2)).map (WithLp.linearEquiv 2 ℂ
        _).symm.toLinearMap).starProjection -
      (leftBoundaryMapES A (z.1 * m + M * m) z.2).range.starProjection.comp
        (reassocTailBoundaryMapES A (z.1 * m) (M * m) z.2).range.starProjection‖
  have hUniform : ∀ᶠ M in Filter.atTop, ∀ z, e M z ≤ (1 / 2 : ℝ) :=
    Filter.eventually_forall_le_of_tendsto_all_selections e
      (fun x => hDefect (fun M => (x M).1) (fun M => (x M).2)) (by norm_num)
  obtain ⟨M, hM, hRM⟩ := (hUniform.and (Filter.eventually_ge_atTop R)).exists
  have hRW : R ≤ M * m := hRM.trans (Nat.le_mul_of_pos_right M hA.period_pos)
  obtain ⟨δ, hδ, hGap⟩ :=
    hA.exists_pos_hamiltonian_parentChainInteraction_gap_all_of_residue_cover_defect (K₀ := 0)
      hR hRW (fun N => hKernel R N le_rfl) (fun K _ r _ => hM (K, r))
  exact ⟨R, hR, (fun N hN => hKernel R N le_rfl hN), M * m, hRW, δ, hδ,
    by simpa only [Nat.zero_add] using hGap⟩

end MPSTensor

end
