/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockSubspaceOverlap
import TNLean.MPS.ParentHamiltonian.BlockGroundSpaceOverlap

/-!
# Independence from small subspace overlaps

A finite family of subspaces is independent when a matrix of its pairwise
overlap bounds has norm less than one. Consequently a finite family whose
pairwise overlaps tend uniformly to zero is eventually independent. The
ambient Hilbert spaces may vary along an arbitrary filter.

These are consequences of the lower Gram estimate in Nachtergaele,
arXiv:cond-mat/9410110, Lemma overlapestimate, lines 2109--2175.
-/

open Filter
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator ComplexOrder

namespace Submodule

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Fintype ι] [DecidableEq ι]

/-- A matrix of pairwise overlap bounds with norm less than one gives an
independent family of subspaces. Source: Nachtergaele,
arXiv:cond-mat/9410110, Lemma overlapestimate, lines 2109--2175. -/
theorem iSupIndep_of_overlapMatrix (V : ι → Submodule ℂ E) (B : Matrix ι ι ℝ)
    (hdiag : ∀ i, B i i = 0) (hB : ‖B‖ < 1)
    (hpair : ∀ i j, i ≠ j → ∀ x ∈ V i, ∀ y ∈ V j,
      ‖⟪x, y⟫_ℂ‖ ≤ B i j * ‖x‖ * ‖y‖) :
    iSupIndep V := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hsum i hi
  let w : ι → E := fun j => if j ∈ s then v j else 0
  have hw (j : ι) : w j ∈ V j := by
    by_cases hj : j ∈ s
    · simpa [w, hj] using hv j hj
    · simp [w, hj]
  have hwSum : ∑ j, w j = 0 := by
    simpa [w] using hsum
  have hLower := norm_sum_sq_ge_of_overlapMatrix w B hdiag
    (fun j k hjk => hpair j k hjk _ (hw j) _ (hw k))
  rw [hwSum, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hLower
  have hSumNonneg : 0 ≤ ∑ j, ‖w j‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hSumZero : ∑ j, ‖w j‖ ^ 2 = 0 := by
    nlinarith [sub_pos.mpr hB]
  have hiBound : ‖w i‖ ^ 2 ≤ ∑ j, ‖w j‖ ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖w j‖) (Finset.mem_univ i)
  rw [hSumZero] at hiBound
  have hiZero : ‖w i‖ = 0 := by nlinarith [norm_nonneg (w i)]
  simpa [w, hi] using norm_eq_zero.mp hiZero

omit [Fintype ι] [DecidableEq ι] in
/-- Uniformly vanishing pairwise overlaps make a finite family of subspaces
eventually independent. Source: Nachtergaele, arXiv:cond-mat/9410110,
Lemma overlapestimate, lines 2109--2175. -/
theorem eventually_iSupIndep_of_pairwise_overlap
    [Finite ι]
    {κ : Type*} {l : Filter κ} {F : κ → Type*}
    [∀ n, NormedAddCommGroup (F n)] [∀ n, InnerProductSpace ℂ (F n)]
    (V : (n : κ) → ι → Submodule ℂ (F n))
    (hOverlap : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in l, ∀ i j, i ≠ j →
      ∀ x ∈ V n i, ∀ y ∈ V n j, ‖⟪x, y⟫_ℂ‖ ≤ ε * ‖x‖ * ‖y‖) :
    ∀ᶠ n in l, iSupIndep (V n) := by
  classical
  let _ := Fintype.ofFinite ι
  let C : Matrix ι ι ℝ := fun i j => if i = j then 0 else 1
  let ε : ℝ := 1 / (‖C‖ + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hSmall : ‖ε • C‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    dsimp [ε]
    rw [one_div_mul_eq_div]
    exact (div_lt_one (by positivity)).mpr (by linarith)
  have hEntry (i j : ι) : (ε • C) i j = ε * C i j := rfl
  filter_upwards [hOverlap ε hε] with n hn
  refine iSupIndep_of_overlapMatrix (V n) (ε • C) ?_ hSmall ?_
  · intro i
    simp [hEntry, C]
  · intro i j hij x hx y hy
    simpa [hEntry, C, hij] using hn i j hij x hx y hy

end Submodule

namespace MPSTensor

/-- Distinct primitive tensors with faithful invariant matrices have
independent boundary spaces at every sufficiently large length.
Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma disjoint,
lines 1744--1820, combined with Lemma overlapestimate, lines 2109--2175.
The primitive faithful generating data and their inequivalence are supplied. -/
theorem eventually_groundSpaceES_iSupIndep_of_primitive
    {d : ℕ} {ι : Type*} [Finite ι] {dim : ι → ℕ} [∀ j, NeZero (dim j)]
    (B : ∀ j, MPSTensor d (dim j))
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (B j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : dim j = dim i,
      ¬ GaugePhaseEquiv (e ▸ B j) (B i)) :
    ∀ᶠ N in atTop, iSupIndep (fun j => groundSpaceES (B j) N) := by
  apply Submodule.eventually_iSupIndep_of_pairwise_overlap
  intro ε hε
  filter_upwards [Filter.eventually_all.2 fun i =>
    Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun hij =>
      (hP i).eventually_norm_inner_groundSpaceES_le_of_inequivalent
        (hP j) (hρ i) (hρ j) (hDistinct i j hij) hε] with N hN
  exact fun i j hij => hN i j hij

end MPSTensor
