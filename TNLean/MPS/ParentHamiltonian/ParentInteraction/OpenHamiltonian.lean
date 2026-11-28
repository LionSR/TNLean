/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ParentInteraction.Transport
import TNLean.MPS.Tensor.GroundSpace.UniqueGroundState
import QICLean.Algebra.Combinatorics.FinSum
import QICLean.ManyBody.Hamiltonian.FrustrationFree
import QICLean.ManyBody.Dynamics.InteractionOperations
import QICLean.ManyBody.Hamiltonian.LocalTermTranslates
import QICLean.Spectral.Gap.EigenvalueGap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TNLean.MPS.ParentHamiltonian.ParentInteraction.PhysicalDeformation

/-!
# The nonwrapping open-chain parent Hamiltonian

For a chain of length `N`, this file sums the canonical local parent interactions
only over starts whose length-`L` windows stay inside the linear interval.  Thus
no local term crosses the cut between the last and first sites.

When the tensor has virtual dimension \(D \ge 1\) and is block-injective at
length \(L₀\), with \(0 < L₀\) and \(L₀ + 1 \le N\), the kernel of the
length-\(L₀ + 1\) open Hamiltonian is the open MPS boundary-condition space
`((groundSpace A N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)`. This is the finite-volume
ground-space input for
Nachtergaele's C1--C3 martingale theorem.

It also contains the following results.

* `MPSTensor.exists_pos_toMatrix'_parentInteraction_hamiltonian_parentChainInteraction_comparison`,
  `MPSTensor.IsParentInteraction.exists_pos_comparison_toEuclideanLin_toMatrix'_parentInteraction`:
  finite-interval comparison with the parent projection.

## References

* Nachtergaele, arXiv:cond-mat/9410110, equations (3.12)--(3.16).
* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:2011.12127, Section IV.C.

## Exact canonical open kernels from one-step intersections

The one-step intersection identities determine every larger boundary space
from contiguous local constraints. A canonical open kernel vector satisfies
all such constraints, so the intersection identities imply exact open
kernels. The intersection property is supplied explicitly in these two
criteria; no injectivity or tensor normalization is assumed.

Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.10)--(3.13),
Lemma existenceinteraction; PGVWC07, arXiv:quant-ph/0608197, Theorem 12.
-/

section OpenHamiltonian

section

open scoped BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- A start site whose length-`L` window does not cross the right endpoint of an
`N`-site open chain.

This is the index set in Nachtergaele, arXiv:cond-mat/9410110, equation (3.12). -/
abbrev NonwrappingStart (L N : ℕ) :=
  {i : Fin N // i.val + L ≤ N}

/-! ### Dimension of the open-boundary ground space -/

/-- The canonical \(\ell^2\) realization of the local ground space has dimension
\(D^2\) under block injectivity at length \(L\). -/
theorem map_groundSpace_finrank_eq_of_isNBlkInjective {A : MPSTensor d D} {L : ℕ}
    (hInj : Kraus.IsNBlkInjective A L) :
    Module.finrank ℂ ((groundSpace A L).map (WithLp.linearEquiv 2 ℂ
        _).symm.toLinearMap) = D ^ 2 := by
  rw [LinearEquiv.finrank_map_eq]
  exact groundSpace_finrank_eq_of_isNBlkInjective hInj

/-! ### The open-chain parent Hamiltonian as the Hamiltonian of `parentChainInteraction`

The same facts for the Hamiltonian of the parent interaction on the open chain
(`parentChainInteraction`), the matrix of the open-chain parent Hamiltonian; statements about
vectors take its operator `Matrix.toEuclideanLin`. -/

section ChainInteraction

open scoped Matrix MatrixOrder

private theorem contiguousCfg_chainWindow {L N a : ℕ} (h : a + L ≤ N) (ω : Cfg d L)
    (σ : Cfg d N) (u : Fin L) : contiguousCfg a L ω σ (ManyBody.chainWindow a h u) = ω u := by
  unfold contiguousCfg
  rw [dite_eq_left (show a ≤ (ManyBody.chainWindow a h u).val ∧
    (ManyBody.chainWindow a h u).val < a + L by simp)]
  exact congrArg ω (Fin.ext (by simp))

private theorem contiguousCfg_of_forall_chainWindow_ne {L N a : ℕ} (h : a + L ≤ N)
    (ω : Cfg d L) (σ : Cfg d N) {v : Fin N} (hv : ∀ u, ManyBody.chainWindow a h u ≠ v) :
    contiguousCfg a L ω σ v = σ v := by
  unfold contiguousCfg
  rw [dite_eq_right]
  rintro ⟨h₁, h₂⟩
  exact hv ⟨v.val - a, by omega⟩ (Fin.ext (by simp only [ManyBody.val_chainWindow]; omega))

private theorem contiguousCfg_contiguousCfg {L N a : ℕ} (ω ω' : Cfg d L) (τ : Cfg d N) :
    contiguousCfg a L ω' (contiguousCfg a L ω τ) = contiguousCfg a L ω' τ := by
  funext k
  unfold contiguousCfg
  split_ifs <;> rfl

/-- A matrix placed on the window of `L` sites starting at `a` acts at a configuration `σ` as
the matrix on the restriction of the vector to that window, the other sites fixed by `σ`, read
at the window of `σ`. -/
theorem placeAlong_chainWindow_mulVec_apply {L N a : ℕ} (h : a + L ≤ N)
    (K : Matrix (Cfg d L) (Cfg d L) ℂ) (ψ : Cfg d N → ℂ) (σ : Cfg d N) :
    (ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.chainWindow a h) K *ᵥ ψ) σ =
      (K *ᵥ contiguousRestrictₗ a L h σ ψ) (fun u ↦ σ (ManyBody.chainWindow a h u)) := by
  rw [ManyBody.placeAlong_mulVec_apply_of _ _ ψ σ (fun ω ↦ contiguousCfg a L ω σ)
    (contiguousCfg_chainWindow h · σ)
    (fun ω _ hv ↦ contiguousCfg_of_forall_chainWindow_ne h ω σ hv)]
  rfl

private theorem toMatrix'_parentInteraction_mulVec_eq_zero_iff (A : MPSTensor d D) {L : ℕ}
    (f : Cfg d L → ℂ) :
    LinearMap.toMatrix' (parentInteraction A L) *ᵥ f = 0 ↔ f ∈ groundSpace A L := by
  have hf : f ∈ groundSpace A L ↔ WithLp.toLp 2 f ∈ ((groundSpace A L).map (WithLp.linearEquiv 2 ℂ
      _).symm.toLinearMap) :=
    (mem_map_groundSpace_iff A L _).symm
  rw [hf, ← toEuclideanLin_toMatrix'_parentInteraction_apply_eq_zero_iff, Matrix.toLpLin_apply,
    WithLp.ofLp_toLp, WithLp.toLp_eq_zero]

/-- **Kernel of a term.** The term of the parent interaction on the open chain at the start `i`
annihilates a vector exactly when every restriction of the vector to the window of the term,
the other sites fixed, lies in the local ground space \(G_L(A)\). Nachtergaele,
arXiv:cond-mat/9410110, equation (3.12). -/
theorem parentChainInteraction_term_mulVec_eq_zero_iff (A : MPSTensor d D) {L N : ℕ}
    (i : Fin (N + 1 - L)) (ψ : Cfg d N → ℂ) :
    (parentChainInteraction A L N).term i *ᵥ ψ = 0 ↔
      ∀ τ : Cfg d N, contiguousRestrictₗ i.val L (by omega) τ ψ ∈ groundSpace A L := by
  have hi : i.val + L ≤ N := by omega
  rw [ManyBody.Interaction.ofPlaceAlong_term]
  constructor
  · intro hψ τ
    rw [← toMatrix'_parentInteraction_mulVec_eq_zero_iff]
    funext ω
    have h := congrFun hψ (contiguousCfg i.val L ω τ)
    rw [placeAlong_chainWindow_mulVec_apply hi] at h
    have hr : contiguousRestrictₗ i.val L hi (contiguousCfg i.val L ω τ) ψ =
        contiguousRestrictₗ i.val L hi τ ψ := by
      funext ω'
      exact congrArg ψ (contiguousCfg_contiguousCfg ω ω' τ)
    have hw : (fun u ↦ contiguousCfg i.val L ω τ (ManyBody.chainWindow i.val hi u)) = ω :=
      funext (contiguousCfg_chainWindow hi ω τ)
    rw [hr, hw] at h
    exact h
  · intro hψ
    funext σ
    rw [placeAlong_chainWindow_mulVec_apply hi,
      (toMatrix'_parentInteraction_mulVec_eq_zero_iff A _).mpr (hψ σ)]
    rfl

/-- Every term of the parent interaction on the open chain is positive semidefinite. -/
theorem posSemidef_parentChainInteraction_term (A : MPSTensor d D) (L N : ℕ)
    (i : Fin (N + 1 - L)) : ((parentChainInteraction A L N).term i).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (ManyBody.Interaction.ofPlaceAlong_term_nonneg _
    (fun _ ↦ Matrix.nonneg_iff_posSemidef.mpr (posSemidef_toMatrix'_parentInteraction A L)) i)

/-- Every term of the parent interaction on the open chain is an orthogonal projection. -/
theorem isStarProjection_parentChainInteraction_term (A : MPSTensor d D) (L N : ℕ)
    (i : Fin (N + 1 - L)) : IsStarProjection ((parentChainInteraction A L N).term i) := by
  have hP := isStarProjection_toMatrix'_parentInteraction A L
  rw [ManyBody.Interaction.ofPlaceAlong_term]
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, ← ManyBody.placeAlong_mul, hP.isIdempotentElem.eq]
  · rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, ← ManyBody.placeAlong_conjTranspose,
      ← Matrix.star_eq_conjTranspose, hP.isSelfAdjoint.star_eq]

/-- Two terms of the parent interaction on the open chain whose windows are ordered and do not
meet commute. -/
theorem commute_parentChainInteraction_term_of_add_le (A : MPSTensor d D) {L N : ℕ}
    {i j : Fin (N + 1 - L)} (hij : i.val + L ≤ j.val) :
    Commute ((parentChainInteraction A L N).term i) ((parentChainInteraction A L N).term j) := by
  refine ManyBody.commute_placeAlong_of_disjoint (X := fun _ ↦ Fin d) _
    (Finset.disjoint_left.mpr fun k hki hkj ↦ ?_) _ _
  rw [ManyBody.map_chainWindow, ManyBody.mem_interval] at hki hkj
  omega

/-- The Hamiltonian of a restriction of the parent interaction on the open chain to a set of
windows is positive semidefinite. -/
theorem posSemidef_hamiltonian_restrict_parentChainInteraction (A : MPSTensor d D) (L N : ℕ)
    (p : Fin (N + 1 - L) → Prop) [DecidablePred p] :
    ((parentChainInteraction A L N).restrict p).hamiltonian.PosSemidef :=
  ManyBody.Interaction.posSemidef_hamiltonian fun i ↦
    ManyBody.Interaction.forall_restrict_term Matrix.PosSemidef.zero
      (posSemidef_parentChainInteraction_term A L N i)

/-- The Hamiltonian of the parent interaction on the open chain is positive semidefinite. -/
theorem posSemidef_hamiltonian_parentChainInteraction (A : MPSTensor d D) (L N : ℕ) :
    (parentChainInteraction A L N).hamiltonian.PosSemidef :=
  ManyBody.Interaction.posSemidef_hamiltonian (posSemidef_parentChainInteraction_term A L N)

/-- **Frustration-free extraction.** A vector annihilated by the Hamiltonian of the parent
interaction on the open chain has every restriction to a window of `L` sites in the local
ground space. Nachtergaele, arXiv:cond-mat/9410110, equation (3.12). -/
theorem contiguousRestrictₗ_mem_groundSpace_of_mem_ker_hamiltonian_parentChainInteraction
    (A : MPSTensor d D) {L N : ℕ} {v : EuclideanSpace ℂ (Cfg d N)}
    (hv : v ∈ LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A L N).hamiltonian))
    (s : ℕ) (hs : s + L ≤ N) (τ : Cfg d N) :
    contiguousRestrictₗ s L hs τ (WithLp.ofLp v) ∈ groundSpace A L := by
  have hH : (parentChainInteraction A L N).hamiltonian *ᵥ WithLp.ofLp v = 0 := by
    rw [LinearMap.mem_ker, Matrix.toLpLin_apply, WithLp.toLp_eq_zero] at hv
    exact hv
  have hterm := (ManyBody.Interaction.hamiltonian_mulVec_eq_zero_iff
    (posSemidef_parentChainInteraction_term A L N)).mp hH ⟨s, by omega⟩
  exact (parentChainInteraction_term_mulVec_eq_zero_iff A ⟨s, by omega⟩ _).mp hterm τ

/-- The cyclic form of the frustration-free extraction: for a window that does not cross the
right endpoint, the cyclic restriction is the contiguous one. -/
theorem cyclicRestrictₗ_mem_groundSpace_of_mem_ker_hamiltonian_parentChainInteraction
    (A : MPSTensor d D) {L N : ℕ} (hLN : L ≤ N) {v : EuclideanSpace ℂ (Cfg d N)}
    (hv : v ∈ LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A L N).hamiltonian))
    (i : Fin N) (hi : i.val + L ≤ N) (τ : Fin N → Fin d) :
    cyclicRestrictₗ (Fin.pos i) L i τ (WithLp.linearEquiv 2 ℂ (NSiteSpace (Fin d) N) v) ∈
      groundSpace A L := by
  rw [cyclicRestrictₗ_eq_contiguousRestrictₗ (Fin.pos i) hLN hi]
  exact contiguousRestrictₗ_mem_groundSpace_of_mem_ker_hamiltonian_parentChainInteraction A hv
    i.val hi τ

/-- The open MPS boundary-condition space lies in the kernel of the Hamiltonian of the parent
interaction on the open chain: every window restriction of an open-boundary MPS vector is an
open-boundary MPS vector. Nachtergaele, arXiv:cond-mat/9410110, equation (3.12). -/
theorem map_groundSpace_le_ker_hamiltonian_parentChainInteraction (A : MPSTensor d D)
    (L N : ℕ) :
    ((groundSpace A N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) ≤
      LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A L N).hamiltonian) := by
  intro v hv
  rw [mem_map_groundSpace_iff, groundSpace, LinearMap.mem_range] at hv
  obtain ⟨X, hX⟩ := hv
  rw [LinearMap.mem_ker, Matrix.toLpLin_apply, WithLp.toLp_eq_zero,
    ManyBody.Interaction.hamiltonian, Matrix.sum_mulVec]
  refine Finset.sum_eq_zero fun i _ ↦ (parentChainInteraction_term_mulVec_eq_zero_iff A i _).mpr
    fun τ ↦ ?_
  have := contiguousRestrictₗ_groundSpaceMap_mem_groundSpace (A := A)
    (show i.val + L ≤ N by omega) τ X
  rwa [hX] at this

/-- Under block injectivity at length \(L_0 > 0\), the kernel of the Hamiltonian of the
length-\((L_0+1)\) parent interaction on the open chain lies in the open MPS boundary-condition
space. Nachtergaele, arXiv:cond-mat/9410110, equations (3.12)--(3.16). -/
theorem ker_hamiltonian_parentChainInteraction_le_map_groundSpace_of_isNBlkInjective
    {A : MPSTensor d D} [NeZero D] {L₀ N : ℕ}
    (hInj : Kraus.IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hL₀N : L₀ + 1 ≤ N) :
    LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A (L₀ + 1) N).hamiltonian) ≤
      ((groundSpace A N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) := by
  intro v hv
  rw [mem_map_groundSpace_iff]
  exact contiguous_mem_groundSpace_of_isNBlkInjective hInj hL₀ hL₀N fun s hs τ ↦
    contiguousRestrictₗ_mem_groundSpace_of_mem_ker_hamiltonian_parentChainInteraction A hv s hs τ

/-- For a block-injective tensor, the kernel of the Hamiltonian of the parent interaction on the
open chain is exactly the open MPS boundary-condition space. Nachtergaele,
arXiv:cond-mat/9410110, equations (3.12)--(3.16). -/
theorem ker_hamiltonian_parentChainInteraction_eq_map_groundSpace_of_isNBlkInjective
    {A : MPSTensor d D} [NeZero D] {L₀ N : ℕ}
    (hInj : Kraus.IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hL₀N : L₀ + 1 ≤ N) :
    LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A (L₀ + 1) N).hamiltonian) =
      ((groundSpace A N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) :=
  le_antisymm (ker_hamiltonian_parentChainInteraction_le_map_groundSpace_of_isNBlkInjective
    hInj hL₀ hL₀N) (map_groundSpace_le_ker_hamiltonian_parentChainInteraction A (L₀ + 1) N)

/-- Project result: **boundary degeneracy of the open-chain parent Hamiltonian.** For a tensor
block-injective at length \(L_0 > 0\), the kernel of the Hamiltonian of the length-\((L_0+1)\)
parent interaction on \(N \ge L_0 + 1\) sites has dimension exactly \(D^2\). Sources: Nachtergaele,
arXiv:cond-mat/9410110, lines 1484--1486, 1505--1510, 1545--1558; Pérez-García--Verstraete--
Wolf--Cirac, arXiv:quant-ph/0608197, lines 1211--1233; arXiv:2011.12127, line 1174 (a lower
bound; the theorem is sharper than the review's statement). -/
theorem finrank_ker_hamiltonian_parentChainInteraction_of_isNBlkInjective
    {A : MPSTensor d D} [NeZero D] {L₀ N : ℕ}
    (hInj : Kraus.IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hL₀N : L₀ + 1 ≤ N) :
    Module.finrank ℂ (LinearMap.ker
      (Matrix.toEuclideanLin (parentChainInteraction A (L₀ + 1) N).hamiltonian)) = D ^ 2 := by
  rw [ker_hamiltonian_parentChainInteraction_eq_map_groundSpace_of_isNBlkInjective hInj hL₀ hL₀N]
  exact map_groundSpace_finrank_eq_of_isNBlkInjective
    (Kraus.isNBlkInjective_of_le hL₀ hInj (by omega))

/-- At volume \(N = L\) the Hamiltonian of the parent interaction on the open chain is the local
parent interaction itself: the only window is the whole chain. -/
theorem hamiltonian_parentChainInteraction_self (A : MPSTensor d D) (L : ℕ) :
    (parentChainInteraction A L L).hamiltonian = LinearMap.toMatrix' (parentInteraction A L) := by
  rw [ManyBody.Interaction.hamiltonian_chainTranslates_eq_sum_range, Nat.add_sub_cancel_left,
    Finset.sum_range_one, dite_eq_left (by omega)]
  have hw : ManyBody.chainWindow (N := L) (k := L) 0 (by omega) = Function.Embedding.refl _ :=
    Function.Embedding.ext fun j ↦ Fin.ext (by simp)
  rw [hw, ManyBody.placeAlong_refl]

/-- At the first full-window volume the operator of the open-chain parent Hamiltonian preserves
the norm on the orthogonal complement of its kernel. -/
theorem norm_toEuclideanLin_hamiltonian_parentChainInteraction_self_of_mem_orthogonal_ker
    (A : MPSTensor d D) (L : ℕ) (v : EuclideanSpace ℂ (Cfg d L))
    (hv : v ∈ (LinearMap.ker
      (Matrix.toEuclideanLin (parentChainInteraction A L L).hamiltonian))ᗮ) :
    ‖Matrix.toEuclideanLin (parentChainInteraction A L L).hamiltonian v‖ = ‖v‖ := by
  rw [hamiltonian_parentChainInteraction_self, toEuclideanLin_toMatrix'_parentInteraction] at hv ⊢
  change ‖((groundSpace A L).map (WithLp.linearEquiv 2 ℂ
      _).symm.toLinearMap)ᗮ.starProjection v‖ = ‖v‖
  apply Submodule.norm_starProjection_apply
  have hker : LinearMap.ker (((groundSpace A L).map (WithLp.linearEquiv 2 ℂ
      _).symm.toLinearMap)ᗮ.starProjection.toLinearMap) =
      ((groundSpace A L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) := by
    ext w
    rw [LinearMap.mem_ker, ← toEuclideanLin_toMatrix'_parentInteraction,
      toEuclideanLin_toMatrix'_parentInteraction_apply_eq_zero_iff]
  rwa [hker] at hv

/-- The open-chain parent Hamiltonian has unit gap at the first full-window volume: every
eigenvalue is `0` or at least `1`. This is \(γ_{l+1} = 1\) in Nachtergaele,
arXiv:cond-mat/9410110, Theorem 2.1(i), for \(L = l + 1\).

**Scope restriction (single-window volume):** This proves only the volume \(N=L\). It does not
establish the general-volume C1--C3 martingale gap; see
`docs/paper-gaps/cpgsv21_martingale_overlap.tex`. -/
theorem unit_gap_hamiltonian_parentChainInteraction_self (A : MPSTensor d D) (L : ℕ) :
    ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction A L L).hamiltonian) μ →
        μ = 0 ∨ (1 : ℂ) ≤ μ := by
  rw [hamiltonian_parentChainInteraction_self]
  exact ManyBody.forall_hasEigenvalue_one_of_isStarProjection
    (isStarProjection_toMatrix'_parentInteraction A L)

/-- **Condition C1.** For the prefixes \(\Lambda_n=[0,n)\) of the open chain, each term of the
range-\(L\) parent interaction lies in at most \(l-L+1\) of the intervals
\(\Lambda_n\setminus\Lambda_{n-l}\), \(l\le n\le N\); the Hamiltonian of such an interval is the
Hamiltonian of the interaction restricted to the windows inside it. Therefore
\[
0\leq\sum_{n=l}^N H_{\Lambda_n\setminus\Lambda_{n-l}}\leq (l-L+1)H_{\Lambda_N}.
\]
The source gives \(d_l=pl-r+1\) for \(\Lambda_n=[1,pn]\); here \(p=1\) and \(r=L\). Nachtergaele,
arXiv:cond-mat/9410110, condition C1, lines 1030--1041. -/
theorem parentChainInteraction_C1 (A : MPSTensor d D) {L l : ℕ} (hLl : L ≤ l) (N : ℕ) :
    0 ≤ ∑ n ∈ Finset.Icc l N, ((parentChainInteraction A L N).restrict
        fun i ↦ n - l ≤ i.val ∧ i.val + L ≤ n).hamiltonian ∧
      ∑ n ∈ Finset.Icc l N, ((parentChainInteraction A L N).restrict
        fun i ↦ n - l ≤ i.val ∧ i.val + L ≤ n).hamiltonian ≤
        ((l - L + 1 : ℕ) : ℂ) • (parentChainInteraction A L N).hamiltonian :=
  ⟨Finset.sum_nonneg fun _ _ ↦ Matrix.nonneg_iff_posSemidef.mpr
      (ManyBody.Interaction.posSemidef_hamiltonian fun i ↦
        ManyBody.Interaction.forall_restrict_term Matrix.PosSemidef.zero
          (posSemidef_parentChainInteraction_term A L N i)),
    ManyBody.Interaction.sum_hamiltonian_restrict_chainTranslates_le hLl
      (Matrix.nonneg_iff_posSemidef.mpr (posSemidef_toMatrix'_parentInteraction A L)) N⟩

end ChainInteraction

end MPSTensor

end

section

open Filter
open scoped BigOperators
namespace MPSTensor
variable {d D : ℕ}

/-- Iterating one-step intersections identifies the kernel of the Hamiltonian of the parent
interaction on the open chain at every volume at least the interaction range. The intersection
assumption is explicit; no injectivity is assumed. Source: Nachtergaele, arXiv:cond-mat/9410110,
equations (3.10)--(3.13), Lemma existenceinteraction; PGVWC07, arXiv:quant-ph/0608197,
Theorem 12. -/
theorem ker_hamiltonian_parentChainInteraction_eq_map_groundSpace_of_restriction_intersection
    [NeZero d] (A : MPSTensor d D) {R N : ℕ} (hR : 0 < R) (hRN : R ≤ N)
    (hStep : ∀ M, R ≤ M →
      ((⨅ b, (groundSpace A M).comap (restrictLastₗ b)) ⊓
        ⨅ a, (groundSpace A M).comap (restrictFirstₗ a)) = groundSpace A (M + 1)) :
    LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) =
      ((groundSpace A N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) := by
  apply le_antisymm ?_ (map_groundSpace_le_ker_hamiltonian_parentChainInteraction A R N)
  intro v hv
  exact (mem_map_groundSpace_iff A N v).mpr
    (contiguous_mem_of_restriction_intersection_submodules (fun M => groundSpace A M) hR hRN
      hStep fun s hs τ ↦
        contiguousRestrictₗ_mem_groundSpace_of_mem_ker_hamiltonian_parentChainInteraction A hv
          s hs τ)

/-- An eventual one-step intersection property gives one positive threshold beyond which the
Hamiltonian of the parent interaction on the open chain has, for every range, the open MPS
boundary-condition space as its kernel. Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma
existenceinteraction and equations (3.10)--(3.13). -/
theorem exists_ker_hamiltonian_parentChainInteraction_eq_map_groundSpace_of_eventually_intersection
    [NeZero d] (A : MPSTensor d D)
    (hStep : ∀ᶠ n in atTop,
      ((⨅ b, (groundSpace A (n + 1)).comap (restrictLastₗ b)) ⊓
        ⨅ a, (groundSpace A (n + 1)).comap (restrictFirstₗ a)) = groundSpace A (n + 2)) :
    ∃ R₀, 0 < R₀ ∧ ∀ R N, R₀ ≤ R → R ≤ N →
      LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) =
        ((groundSpace A N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) := by
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hStep
  refine ⟨n₀ + 1, Nat.succ_pos _, fun R N hR hRN => ?_⟩
  apply ker_hamiltonian_parentChainInteraction_eq_map_groundSpace_of_restriction_intersection
    A (by omega) hRN
  rintro (_ | n) hn
  · omega
  · simpa only [Nat.add_assoc] using hn₀ n (by omega)

end MPSTensor

end

end OpenHamiltonian

section FiniteIntervalGapComparison

/-!
## Finite-interval comparison with the parent projection

If the kernel of an open parent Hamiltonian is the full local MPS space,
finite dimensionality bounds its excitation projection by a positive multiple
of that Hamiltonian. This is the local comparison needed to transfer a
parent-Hamiltonian gap between admissible interaction ranges; see
`docs/paper-gaps/cpgsv21_block_parent_interaction_range.tex`.

The comparison is stated for the Hamiltonian of the parent interaction on the open chain
(`parentChainInteraction`) and the matrix of the local parent interaction.

### Comparison of parent interactions with the canonical projection

A positive local interaction with the prescribed MPS kernel bounds, and is
bounded by, positive multiples of the canonical parent projection. The constants
depend only on the local interaction. This finite-dimensional comparison is the
local step in extending the parent-Hamiltonian gap to arbitrary fixed parent
interactions, as defined in CPGSV21, arXiv:2011.12127, lines 1996--1999. It is
the remark at line 2170 that non-projector interactions are bounded above and
below by projectors up to a constant, which reduces the gap theorem at lines
2183--2187 to the canonical projection interaction.
-/

section

open scoped InnerProductSpace ComplexOrder

namespace MPSTensor

/-! ### The Hamiltonian of the parent interaction on the open chain -/

section ChainInteraction

open scoped MatrixOrder

/-- If the kernel of the operator of the Hamiltonian of the parent interaction on the open chain
is the local MPS space, that Hamiltonian and the local parent interaction bound one another, in
the Loewner order, by positive constants. -/
theorem exists_pos_toMatrix'_parentInteraction_hamiltonian_parentChainInteraction_comparison
    {d D R W : ℕ} (A : MPSTensor d D)
    (hker : LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A R W).hamiltonian) =
      ((groundSpace A W).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧
      (κ : ℂ) • LinearMap.toMatrix' (parentInteraction A W) ≤
        (parentChainInteraction A R W).hamiltonian ∧
      (parentChainInteraction A R W).hamiltonian ≤
        (C : ℂ) • LinearMap.toMatrix' (parentInteraction A W) := by
  have hH := Matrix.isPositive_toEuclideanLin_iff.mpr
    (posSemidef_hamiltonian_parentChainInteraction A R W)
  obtain ⟨κ, hκ, hLower⟩ := LinearMap.IsPositive.exists_pos_smul_orthogonal_ker_projection_le hH
  obtain ⟨C, hC, hUpper⟩ := LinearMap.IsPositive.exists_pos_le_smul_orthogonal_ker_projection hH
  rw [hker, ← toEuclideanLin_toMatrix'_parentInteraction, ← map_smul] at hLower hUpper
  exact ⟨κ, C, hκ, hC, Matrix.toEuclideanLin_le_toEuclideanLin_iff.mp hLower,
    Matrix.toEuclideanLin_le_toEuclideanLin_iff.mp hUpper⟩

end ChainInteraction

end MPSTensor

end

section

open scoped ComplexOrder

namespace MPSTensor

/-- Every positive parent interaction is comparable in both directions to the operator of the
matrix of the canonical parent interaction. The constants are strictly positive, including
when both operators vanish.

Source: CPGSV21, arXiv:2011.12127, lines 1996--1999 and line 2170. -/
theorem IsParentInteraction.exists_pos_comparison_toEuclideanLin_toMatrix'_parentInteraction
    {d D R : ℕ} {A : MPSTensor d D}
    {h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)}
    (hh : IsParentInteraction A R h) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧
      (κ : ℂ) • Matrix.toEuclideanLin (LinearMap.toMatrix' (parentInteraction A R)) ≤ h ∧
      h ≤ (C : ℂ) • Matrix.toEuclideanLin (LinearMap.toMatrix' (parentInteraction A R)) := by
  obtain ⟨κ, hκ, hLower⟩ :=
    hh.isPositive.exists_pos_smul_orthogonal_ker_projection_le
  obtain ⟨C, hC, hUpper⟩ :=
    hh.isPositive.exists_pos_le_smul_orthogonal_ker_projection
  rw [toEuclideanLin_toMatrix'_parentInteraction]
  exact ⟨κ, C, hκ, hC, by simpa only [hh.ker_eq] using hLower,
    by simpa only [hh.ker_eq] using hUpper⟩

end MPSTensor

end

end FiniteIntervalGapComparison
