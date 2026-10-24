/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.FinalStateCount
import TNLean.MPS.AreaLaw.LocalSolution.HierarchyLevels

/-!
# The energy of every final state of Hastings' hierarchical construction

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 609–730), builds the final states `α^h` in
`h` levels. At level `m` the operator `M_{k,k+1}` joining the two halves of a block is
compressed to the states kept on the halves, and the window projection keeps its eigenvectors
with eigenvalue within `x_m` of `c = ⟨Ψ_a, M_{k,k+1} Ψ_a⟩` (lines 640–642 and 671–685). Eq.
`hchy` (lines 709–720) asserts that a final state has energy at most
`⟨Ψ_a, ∑_i M_i Ψ_a⟩ + N J O(·)`, and lines 722–730 count the final states, which needs this for
every `α^h`.

Every unit vector `φ` in the range of the final projection satisfies the bound. Such a `φ` is
kept at every level, so for each joining operator `M` it lies in the range of the window
projection of `Q M Q`, where `Q` is the projection of the level below and `Q φ = φ`. On that
range `‖(Q M Q - c) φ‖ ≤ x ‖φ‖`, so `|⟨φ, M φ⟩ - c| = |⟨φ, (Q M Q - c) φ⟩| ≤ x`. Summing over
the joining operators of the tree gives
`|⟨φ, ∑ M φ⟩ - ⟨Ψ_a, ∑ M Ψ_a⟩| ≤ ∑_m 2^{h-1-m} x_m`, with one window radius `x_m` for each
joining operator of level `m`. In particular every `α^h` satisfies eq. `hchy`, and the count of
at most `2n` final states follows once this error and the energy of `Ψ_a` lie within `ΔE/2` of
the ground energy.

The blocks of one level act on disjoint sets of supersites, so the projections of the two halves
of a block commute. As in `HierarchyLevels.lean`, that commutation is a hypothesis here;
`mem_supportedOperators_hierarchy` and `disjoint_levelBlock_two_mul` derive it from the
supersite grouping of lines 609–628.

**Scope restriction (open chain):** the source's chain of supersites is periodic (lines 626–628).
The tree of joining operators covers the `N - 1` links `(k, k+1)` of the open chain, and the
link `(N, 1)` is the joining operator of no level, so no window controls its energy. The sum
of the joining operators, `hierarchySum M h 0`, is therefore the open-chain part of
`∑_i M_i`, and the count of final states assumes the gap for this open-chain sum rather than
for the periodic `∑_i M_i` of the source. Documented in
`docs/paper-gaps/hastings05_hierarchical_energy.tex`.

## Main results

* `TNLean.MPS.AreaLaw.LocalSolution.abs_re_inner_sub_le_of_compressedWindowProjection`: a
  vector kept by a window has expectation of the joining operator within the radius of the
  centre.
* `TNLean.MPS.AreaLaw.LocalSolution.abs_re_inner_hierarchySum_sub_le`: the same for the sum of
  the joining operators of a block, with the sum of the radii.
* `TNLean.MPS.AreaLaw.LocalSolution.re_inner_hierarchySum_le_add`: eq. `hchy` for every unit
  vector kept by the final projection.
* `TNLean.MPS.AreaLaw.LocalSolution.card_le_two_mul_re_trace_of_hierarchy`: at most `2n`
  orthonormal final states.
-/

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace

namespace TNLean.MPS.AreaLaw.LocalSolution

open TNLean.MPS.AreaLaw.Hastings

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sum over the binary tree below the block `k` of level `m`: the value at a block of
level `m + 1` is its own term plus the sums of its two halves. With `f m k` the operator
joining the halves of block `k` of level `m + 1`, `hierarchySum f h 0` is the sum of the
`2^h - 1` links of an open chain of `2^h` supersites. -/
def hierarchySum {A : Type*} [AddCommMonoid A] (f : ℕ → ℕ → A) : ℕ → ℕ → A
  | 0, _ => 0
  | m + 1, k => f m k + hierarchySum f m (2 * k) + hierarchySum f m (2 * k + 1)

@[simp]
theorem hierarchySum_zero {A : Type*} [AddCommMonoid A] (f : ℕ → ℕ → A) (k : ℕ) :
    hierarchySum f 0 k = 0 := rfl

theorem hierarchySum_succ {A : Type*} [AddCommMonoid A] (f : ℕ → ℕ → A) (m k : ℕ) :
    hierarchySum f (m + 1) k =
      f m k + hierarchySum f m (2 * k) + hierarchySum f m (2 * k + 1) := rfl

/-- `hierarchySum` commutes with additive maps. -/
theorem map_hierarchySum {A B F : Type*} [AddCommMonoid A] [AddCommMonoid B]
    [FunLike F A B] [AddMonoidHomClass F A B] (g : F) (f : ℕ → ℕ → A) (m k : ℕ) :
    g (hierarchySum f m k) = hierarchySum (fun m k ↦ g (f m k)) m k := by
  induction m generalizing k with
  | zero => simp
  | succ m ih => simp [hierarchySum_succ, ih]

/-- The number of joining operators below a block of level `m` is `2^m - 1`. -/
theorem hierarchySum_one (m k : ℕ) : hierarchySum (fun _ _ ↦ (1 : ℕ)) m k = 2 ^ m - 1 := by
  induction m generalizing k with
  | zero => rfl
  | succ m ih =>
    rw [hierarchySum_succ, ih, ih, pow_succ]
    have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    omega

/-- **A vector kept by a window.** Let `A` be Hermitian, `x ≥ 0`, and let `φ` be kept by the
window projection of `A` at `c` and `x`. Then `|re⟨φ, A φ⟩ - c ‖φ‖²| ≤ x ‖φ‖²`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 640–642. -/
theorem abs_re_inner_sub_le_of_windowProjection {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (c : ℝ) {x : ℝ} (hx : 0 ≤ x) {φ : EuclideanSpace ℂ ι}
    (hφ : toEuclideanLin (windowProjection A c x) φ = φ) :
    |(⟪φ, toEuclideanLin A φ⟫_ℂ).re - c * ‖φ‖ ^ 2| ≤ x * ‖φ‖ ^ 2 := by
  have hAc := isHermitian_sub_ofReal_smul_one hA c
  have e : (⟪φ, toEuclideanLin A φ⟫_ℂ).re - c * ‖φ‖ ^ 2 =
      (⟪φ, toEuclideanLin ((A - (c : ℂ) • 1) * windowProjection A c x) φ⟫_ℂ).re := by
    rw [toEuclideanLin_mul_apply, hφ, map_sub, LinearMap.sub_apply, inner_sub_right,
      Complex.sub_re, map_smul, LinearMap.smul_apply, toEuclideanLin_one_apply,
      inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  rw [e]
  refine (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm (𝕜 := ℂ) _ _).trans ?_)
  have hn := Entropy.norm_toEuclideanLin_le ((A - (c : ℂ) • 1) * windowProjection A c x) φ
  have hW : ‖(A - (c : ℂ) • 1) * windowProjection A c x‖ ≤ x :=
    norm_mul_spectralCutoff_le hAc hx
  calc ‖φ‖ * ‖toEuclideanLin ((A - (c : ℂ) • 1) * windowProjection A c x) φ‖
      ≤ ‖φ‖ * (x * ‖φ‖) := by
        gcongr
        exact hn.trans (mul_le_mul_of_nonneg_right hW (norm_nonneg _))
    _ = x * ‖φ‖ ^ 2 := by ring

/-- **A vector kept by a later-level window.** Let `Q` be an orthogonal projection, `M`
Hermitian and `x ≥ 0`. If `φ` is kept by the window projection of `M` at `c` and `x` inside the
range of `Q`, then `Q φ = φ` and `|re⟨φ, M φ⟩ - c ‖φ‖²| ≤ x ‖φ‖²`. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 671–685, where `c = ⟨Ψ_a, M Ψ_a⟩`. -/
theorem abs_re_inner_sub_le_of_compressedWindowProjection {Q M : Matrix ι ι ℂ}
    (hQ : IsStarProjection Q) (hM : M.IsHermitian) (c : ℝ) {x : ℝ} (hx : 0 ≤ x)
    {φ : EuclideanSpace ℂ ι}
    (hφ : toEuclideanLin (compressedWindowProjection Q M c x) φ = φ) :
    toEuclideanLin Q φ = φ ∧ |(⟪φ, toEuclideanLin M φ⟫_ℂ).re - c * ‖φ‖ ^ 2| ≤ x * ‖φ‖ ^ 2 := by
  have hQφ : toEuclideanLin Q φ = φ := by
    conv_lhs => rw [← hφ]
    rw [← toEuclideanLin_mul_apply, compressedWindowProjection, ← mul_assoc,
      hQ.isIdempotentElem.eq]
    exact hφ
  refine ⟨hQφ, ?_⟩
  have hQM : (Q * M * Q).IsHermitian := by
    simpa only [hQ.isSelfAdjoint.isHermitian.eq] using isHermitian_mul_mul_conjTranspose Q hM
  have hW : toEuclideanLin (windowProjection (Q * M * Q) c x) φ = φ := by
    rw [← toEuclideanLin_compressedWindowProjection_of_mem hQ M c x hQφ, hφ]
  have hsym := isSymmetric_toEuclideanLin_iff.2 hQ.isSelfAdjoint.isHermitian
  have e : ⟪φ, toEuclideanLin (Q * M * Q) φ⟫_ℂ = ⟪φ, toEuclideanLin M φ⟫_ℂ := by
    rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply, hQφ, ← hsym, hQφ]
  rw [← e]
  exact abs_re_inner_sub_le_of_windowProjection hQM c hx hW

variable (P M : ℕ → ℕ → Matrix ι ι ℂ) (c : ℕ → ℕ → ℝ) (x : ℕ → ℝ)

/-- **eq. `hchy` below one block.** In the hierarchy of `norm_sub_hierarchy_le`, with radii
`x m ≥ 0`, every vector `φ` kept by the projection of block `k` of level `m` satisfies
`|re⟨φ, M_T φ⟩ - c_T ‖φ‖²| ≤ x_T ‖φ‖²`, where `M_T`, `c_T` and `x_T` sum the joining
operators, centres and radii of the tree below the block. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 668–720. -/
theorem abs_re_inner_hierarchySum_sub_le (hP0 : ∀ k, P 0 k = 1)
    (hstep : ∀ m k, P (m + 1) k =
      compressedWindowProjection (P m (2 * k) * P m (2 * k + 1)) (M m k) (c m k) (x m))
    (hcomm : ∀ m k, Commute (P m (2 * k)) (P m (2 * k + 1)))
    (hM : ∀ m k, (M m k).IsHermitian) (hx : ∀ m, 0 ≤ x m) :
    ∀ m k {φ : EuclideanSpace ℂ ι}, toEuclideanLin (P m k) φ = φ →
      |(⟪φ, toEuclideanLin (hierarchySum M m k) φ⟫_ℂ).re - hierarchySum c m k * ‖φ‖ ^ 2| ≤
        hierarchySum (fun m _ ↦ x m) m k * ‖φ‖ ^ 2 := by
  have hproj := isStarProjection_hierarchy P M c x hP0 hstep hcomm hM
  intro m
  induction m with
  | zero => intro k φ _; simp
  | succ m ih =>
    intro k φ hφ
    rw [hstep] at hφ
    have hQ := (hproj m (2 * k)).mul (hproj m (2 * k + 1)) (hcomm m k)
    obtain ⟨hQφ, h0⟩ :=
      abs_re_inner_sub_le_of_compressedWindowProjection hQ (hM m k) (c m k) (hx m) hφ
    -- The vector is kept by both halves.
    have hφ1 : toEuclideanLin (P m (2 * k)) φ = φ := by
      conv_lhs => rw [← hQφ]
      rw [← toEuclideanLin_mul_apply, ← mul_assoc, (hproj m (2 * k)).isIdempotentElem.eq, hQφ]
    have hφ2 : toEuclideanLin (P m (2 * k + 1)) φ = φ := by
      conv_lhs => rw [← hQφ]
      rw [← toEuclideanLin_mul_apply, (hcomm m k).eq, ← mul_assoc,
        (hproj m (2 * k + 1)).isIdempotentElem.eq, ← (hcomm m k).eq, hQφ]
    have h1 := ih (2 * k) hφ1
    have h2 := ih (2 * k + 1) hφ2
    simp only [hierarchySum_succ, map_add, LinearMap.add_apply, inner_add_right,
      Complex.add_re]
    calc _ = |((⟪φ, toEuclideanLin (M m k) φ⟫_ℂ).re - c m k * ‖φ‖ ^ 2) +
          ((⟪φ, toEuclideanLin (hierarchySum M m (2 * k)) φ⟫_ℂ).re -
            hierarchySum c m (2 * k) * ‖φ‖ ^ 2) +
          ((⟪φ, toEuclideanLin (hierarchySum M m (2 * k + 1)) φ⟫_ℂ).re -
            hierarchySum c m (2 * k + 1) * ‖φ‖ ^ 2)| := by ring_nf
      _ ≤ _ := (abs_add_three _ _ _).trans (by linarith)

/-- **eq. `hchy` for every final state.** In the hierarchy of `norm_sub_hierarchy_le`, take the
centres `c m k = re⟨Ψ, M m k Ψ⟩` of a unit vector `Ψ` and radii `x m ≥ 0`. Then every unit vector
`φ` kept by the projection of block `k` of level `m` has
`re⟨φ, M_T φ⟩ ≤ re⟨Ψ, M_T Ψ⟩ + x_T`, where `M_T` is the sum of the joining operators below the
block and `x_T` the sum of their radii. With `Ψ = Ψ_a` and the final projection, this is eq.
`hchy` of Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 709–720, for each final
state `α^h`, with the explicit error `∑_m 2^{h-1-m} x_m`, under the open-chain restriction of the
module docstring. -/
theorem re_inner_hierarchySum_le_add (hP0 : ∀ k, P 0 k = 1)
    {Ψ : EuclideanSpace ℂ ι}
    (hstep : ∀ m k, P (m + 1) k = compressedWindowProjection (P m (2 * k) * P m (2 * k + 1))
      (M m k) (⟪Ψ, toEuclideanLin (M m k) Ψ⟫_ℂ).re (x m))
    (hcomm : ∀ m k, Commute (P m (2 * k)) (P m (2 * k + 1)))
    (hM : ∀ m k, (M m k).IsHermitian) (hx : ∀ m, 0 ≤ x m) (m k : ℕ)
    {φ : EuclideanSpace ℂ ι} (hφ1 : ‖φ‖ = 1) (hφ : toEuclideanLin (P m k) φ = φ) :
    (⟪φ, toEuclideanLin (hierarchySum M m k) φ⟫_ℂ).re ≤
      (⟪Ψ, toEuclideanLin (hierarchySum M m k) Ψ⟫_ℂ).re + hierarchySum (fun m _ ↦ x m) m k := by
  have h := abs_re_inner_hierarchySum_sub_le P M _ x hP0 hstep hcomm hM hx m k hφ
  have hc : hierarchySum (fun m k ↦ (⟪Ψ, toEuclideanLin (M m k) Ψ⟫_ℂ).re) m k =
      (⟪Ψ, toEuclideanLin (hierarchySum M m k) Ψ⟫_ℂ).re := by
    let g : Matrix ι ι ℂ →+ ℝ :=
      { toFun := fun A ↦ (⟪Ψ, toEuclideanLin A Ψ⟫_ℂ).re
        map_zero' := by simp
        map_add' := fun A B ↦ by simp [inner_add_right] }
    exact (map_hierarchySum g M m k).symm
  rw [hc, hφ1] at h
  simp only [one_pow, mul_one] at h
  linarith [le_abs_self ((⟪φ, toEuclideanLin (hierarchySum M m k) φ⟫_ℂ).re -
    (⟪Ψ, toEuclideanLin (hierarchySum M m k) Ψ⟫_ℂ).re)]

/-- **At most `2n` final states.** In the hierarchy of `re_inner_hierarchySum_le_add`, let
`H = hierarchySum M h 0` have gap `ΔE` above `E₀` with ground projection `P₀` in the sense of
`card_le_two_mul_re_trace`. If `re⟨Ψ, H Ψ⟩ + ∑ x ≤ E₀ + ΔE/2`, then every orthonormal family
of vectors kept by the final projection `P h 0` has at most `2 re tr P₀` members. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 722–730, under the open-chain restriction of
the module docstring. -/
theorem card_le_two_mul_re_trace_of_hierarchy (hP0 : ∀ k, P 0 k = 1)
    {Ψ : EuclideanSpace ℂ ι}
    (hstep : ∀ m k, P (m + 1) k = compressedWindowProjection (P m (2 * k) * P m (2 * k + 1))
      (M m k) (⟪Ψ, toEuclideanLin (M m k) Ψ⟫_ℂ).re (x m))
    (hcomm : ∀ m k, Commute (P m (2 * k)) (P m (2 * k + 1)))
    (hM : ∀ m k, (M m k).IsHermitian) (hx : ∀ m, 0 ≤ x m) (h : ℕ)
    {P₀ : Matrix ι ι ℂ} (hP₀ : IsStarProjection P₀) {E₀ ΔE : ℝ} (hΔ : 0 < ΔE)
    (hgap : ∀ v : EuclideanSpace ℂ ι,
      ΔE * (‖v‖ ^ 2 - (⟪v, toEuclideanLin P₀ v⟫_ℂ).re) ≤
        (⟪v, toEuclideanLin (hierarchySum M h 0) v⟫_ℂ).re - E₀ * ‖v‖ ^ 2)
    (hE : (⟪Ψ, toEuclideanLin (hierarchySum M h 0) Ψ⟫_ℂ).re +
      hierarchySum (fun m _ ↦ x m) h 0 ≤ E₀ + ΔE / 2)
    {κ : Type*} {φ : κ → EuclideanSpace ℂ ι} (hφ : Orthonormal ℂ φ) (s : Finset κ)
    (hφP : ∀ j ∈ s, toEuclideanLin (P h 0) (φ j) = φ j) :
    (s.card : ℝ) ≤ 2 * (trace P₀).re :=
  card_le_two_mul_re_trace hP₀ hΔ hgap hφ s fun j hj ↦
    (re_inner_hierarchySum_le_add P M x hP0 hstep hcomm hM hx h 0 (hφ.1 j) (hφP j hj)).trans hE

end TNLean.MPS.AreaLaw.LocalSolution
