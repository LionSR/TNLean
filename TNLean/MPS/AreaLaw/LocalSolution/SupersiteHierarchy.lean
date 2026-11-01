/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SupportedFunctionalCalculus
import TNLean.Circuit.LocalCircuit
import TNLean.MPS.AreaLaw.LocalSolution.HierarchyLevels

/-!
# The hierarchy on supersites

Hastings, *Solving gapped Hamiltonians locally*, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 609–628, groups the sites of the chain into supersites of `2 l_proj` sites, so that each
operator `M_i` acts on at most two neighbouring supersites, and lets `M_{k,k+1}` be the sum of
the `M_i` acting on supersites `k` and `k + 1`. The hierarchy of lines 668–707 then pairs
blocks of `2^m` consecutive supersites. This file supplies the two facts about this grouping
that the bound over all levels (`norm_sub_hierarchy_le`) takes as hypotheses.

* **Commutation.** Spectral windows keep the support of the operator they are taken of, so
  every projection of level `m` acts on its block of `2^m` supersites. The two halves of a block
  act on disjoint sets of sites and therefore commute.
* **Residuals of sums.** If each `M_i` has residual `‖(M_i - c_i) Ψ‖` and `M = ∑ M_i`, then
  `‖(M - ∑ c_i) Ψ‖ ≤ ∑ ‖(M_i - c_i) Ψ‖`. With `c_i = ⟨Ψ_a, M_i Ψ_a⟩`, the centre `∑ c_i` is
  `⟨Ψ_a, M Ψ_a⟩`, and eq. `low` for the `M_i` gives the residual of the pair operators.

The supersite of a site is given by a map `blk : ι → ℕ`; the level-`m` block `k` consists of
the sites whose supersite has quotient `k` by `2^m`. The source's chain is periodic, but the
binary tree of blocks never pairs supersite `N` with supersite `1`, so the map need not be
periodic.

## Main statements

* `windowProjection_mem_supportedOperators`,
  `compressedWindowProjection_mem_supportedOperators`: support of spectral windows,
  from the shared `QuantumCircuit.cfc_mem_supportedOperators`.
* `mem_supportedOperators_hierarchy`: the level-`m` projection acts on its block.
* `commute_supersiteHierarchy`: the projections of the two halves of a block commute.
* `norm_sub_supersiteHierarchy_le`: the bound over all levels, with the commutation of the
  halves derived from the supports of the pair operators.
* `norm_toEuclideanLin_sum_sub_le`: the residual of a sum.
-/

open Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.MPS.AreaLaw.LocalSolution

section Support

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The window projection of an operator acting on `S` acts on `S`. -/
theorem windowProjection_mem_supportedOperators {S : Set ι}
    {M : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hM : M ∈ supportedOperators d S) (c x : ℝ) :
    windowProjection M c x ∈ supportedOperators d S :=
  cfc_mem_supportedOperators _ (Submodule.sub_mem _ hM
    (Submodule.smul_mem _ _ (one_mem_supportedOperators S)))

/-- The window projection inside the range of `Q` acts on `S` when `Q` and `M` do. -/
theorem compressedWindowProjection_mem_supportedOperators {S : Set ι}
    {Q M : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hQ : Q ∈ supportedOperators d S)
    (hM : M ∈ supportedOperators d S) (c x : ℝ) :
    compressedWindowProjection Q M c x ∈ supportedOperators d S :=
  mul_mem_supportedOperators hQ (windowProjection_mem_supportedOperators
    (mul_mem_supportedOperators (mul_mem_supportedOperators hQ hM) hQ) c x)

end Support

section Supersites

variable {ι : Type*}

/-- The sites of block `k` at level `m`: those whose supersite has quotient `k` by `2^m`. -/
def levelBlock (blk : ι → ℕ) (m k : ℕ) : Set ι :=
  {i | blk i / 2 ^ m = k}

theorem levelBlock_two_mul_subset (blk : ι → ℕ) (m k : ℕ) :
    levelBlock blk m (2 * k) ⊆ levelBlock blk (m + 1) k := fun i hi ↦ by
  change blk i / 2 ^ m = _ at hi
  change blk i / 2 ^ (m + 1) = k
  rw [pow_succ, ← Nat.div_div_eq_div_mul, hi]
  omega

theorem levelBlock_two_mul_add_one_subset (blk : ι → ℕ) (m k : ℕ) :
    levelBlock blk m (2 * k + 1) ⊆ levelBlock blk (m + 1) k := fun i hi ↦ by
  change blk i / 2 ^ m = _ at hi
  change blk i / 2 ^ (m + 1) = k
  rw [pow_succ, ← Nat.div_div_eq_div_mul, hi]
  omega

theorem disjoint_levelBlock_two_mul (blk : ι → ℕ) (m k : ℕ) :
    Disjoint (levelBlock blk m (2 * k)) (levelBlock blk m (2 * k + 1)) :=
  Set.disjoint_left.mpr fun i h₁ h₂ ↦ by
    change blk i / 2 ^ m = 2 * k at h₁
    change blk i / 2 ^ m = 2 * k + 1 at h₂
    omega

variable {d : ℕ} [Fintype ι] [DecidableEq ι]

/-- **Each projection acts on its block.** If `P 0 k = 1`, `P (m + 1) k` is the window of
`M m k` inside the range of `P m (2k) P m (2k + 1)`, and the pair operator `M m k` acts on the
block `k` of level `m + 1`, then `P m k` acts on the block `k` of level `m`. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 609–628 and 668–685. -/
theorem mem_supportedOperators_hierarchy (blk : ι → ℕ)
    (P M : ℕ → ℕ → Matrix (ι → Fin d) (ι → Fin d) ℂ) (c : ℕ → ℕ → ℝ) (x : ℕ → ℝ)
    (hP0 : ∀ k, P 0 k = 1)
    (hstep : ∀ m k, P (m + 1) k =
      compressedWindowProjection (P m (2 * k) * P m (2 * k + 1)) (M m k) (c m k) (x m))
    (hMsupp : ∀ m k, M m k ∈ supportedOperators d (levelBlock blk (m + 1) k)) :
    ∀ m k, P m k ∈ supportedOperators d (levelBlock blk m k) := by
  intro m
  induction m with
  | zero =>
    intro k
    rw [hP0]
    exact one_mem_supportedOperators _
  | succ m ih =>
    intro k
    rw [hstep]
    exact compressedWindowProjection_mem_supportedOperators
      (mul_mem_supportedOperators
        (supportedOperators_mono (levelBlock_two_mul_subset blk m k) (ih (2 * k)))
        (supportedOperators_mono (levelBlock_two_mul_add_one_subset blk m k)
          (ih (2 * k + 1))))
      (hMsupp m k) _ _

/-- **The halves of a block commute.** In the hierarchy of `mem_supportedOperators_hierarchy`,
the projections of the two halves of each block act on the disjoint blocks `2k` and `2k + 1` of
their level, so they commute. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 609–628 and 668–685. -/
theorem commute_supersiteHierarchy (blk : ι → ℕ)
    (P M : ℕ → ℕ → Matrix (ι → Fin d) (ι → Fin d) ℂ) (c : ℕ → ℕ → ℝ) (x : ℕ → ℝ)
    (hP0 : ∀ k, P 0 k = 1)
    (hstep : ∀ m k, P (m + 1) k =
      compressedWindowProjection (P m (2 * k) * P m (2 * k + 1)) (M m k) (c m k) (x m))
    (hMsupp : ∀ m k, M m k ∈ supportedOperators d (levelBlock blk (m + 1) k)) :
    ∀ m k, Commute (P m (2 * k)) (P m (2 * k + 1)) := by
  have hsupp := mem_supportedOperators_hierarchy blk P M c x hP0 hstep hMsupp
  exact fun m k ↦ commute_of_mem_supportedOperators (disjoint_levelBlock_two_mul blk m k)
    (hsupp m (2 * k)) (hsupp m (2 * k + 1))

/-- **All levels on supersites.** The bound of `norm_sub_hierarchy_le`, with the commutation of
the two halves of each block derived from the supports: each pair operator `M m k` acts on the
block `k` of level `m + 1`, as the operators `M_{k,k+1}` joining two neighbouring supersites
do. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 609–707. -/
theorem norm_sub_supersiteHierarchy_le (blk : ι → ℕ)
    (P M : ℕ → ℕ → Matrix (ι → Fin d) (ι → Fin d) ℂ) (c : ℕ → ℕ → ℝ) (x : ℕ → ℝ)
    (hP0 : ∀ k, P 0 k = 1)
    (hstep : ∀ m k, P (m + 1) k =
      compressedWindowProjection (P m (2 * k) * P m (2 * k + 1)) (M m k) (c m k) (x m))
    (hMsupp : ∀ m k, M m k ∈ supportedOperators d (levelBlock blk (m + 1) k))
    (hM : ∀ m k, (M m k).IsHermitian) (hx : ∀ m, 0 < x m)
    {ψ : EuclideanSpace ℂ (ι → Fin d)} (hψ : ‖ψ‖ = 1) {ε K : ℝ}
    (hres : ∀ m k, ‖toEuclideanLin (M m k - (c m k : ℂ) • 1) ψ‖ ≤ ε)
    (hK : ∀ m k, ‖M m k - (c m k : ℂ) • 1‖ ≤ K) :
    ∀ m k, IsStarProjection (P m k) ∧
      ‖ψ - toEuclideanLin (P m k) ψ‖ ≤ hierarchyDeficiency ε K x m :=
  norm_sub_hierarchy_le P M c x hP0 hstep
    (commute_supersiteHierarchy blk P M c x hP0 hstep hMsupp) hM hx hψ hres hK

end Supersites

section Residual

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The residual of a sum.** For operators `Mᵢ` and reals `cᵢ`,
`‖(∑ Mᵢ - ∑ cᵢ) ψ‖ ≤ ∑ ‖(Mᵢ - cᵢ) ψ‖`. With `Mᵢ` the operators `M_i` acting on two
neighbouring supersites and `cᵢ = ⟨Ψ_a, M_i Ψ_a⟩`, this bounds the residual of `M_{k,k+1}` by
eq. `low` for its summands, Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 628–639. -/
theorem norm_toEuclideanLin_sum_sub_le {α : Type*} (s : Finset α) (Mi : α → Matrix ι ι ℂ)
    (ci : α → ℝ) (ψ : EuclideanSpace ℂ ι) :
    ‖toEuclideanLin (∑ a ∈ s, Mi a - ((∑ a ∈ s, ci a : ℝ) : ℂ) • 1) ψ‖ ≤
      ∑ a ∈ s, ‖toEuclideanLin (Mi a - (ci a : ℂ) • 1) ψ‖ := by
  have e : ∑ a ∈ s, Mi a - ((∑ a ∈ s, ci a : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) =
      ∑ a ∈ s, (Mi a - (ci a : ℂ) • 1) := by
    rw [Finset.sum_sub_distrib, Complex.ofReal_sum, Finset.sum_smul]
  rw [e, map_sum, LinearMap.sum_apply]
  exact norm_sum_le _ _

end Residual

end TNLean.MPS.AreaLaw.LocalSolution
