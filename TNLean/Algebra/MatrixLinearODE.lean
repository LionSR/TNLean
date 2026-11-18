/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixEntrywiseDeriv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Transport by a matrix linear differential equation

On a closed real interval, a solution of `g' = X g` starting at the identity
remains invertible. Every solution of the same equation is `g` times its
initial value. Existence of `g` is an explicit hypothesis; continuity of `X`
is used for uniqueness, via a bound on the compact interval.

This is the integration argument needed for the L-symbol gauge law in
Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, Section 5.2, line 1551.
-/

open Set
open scoped Matrix Matrix.Norms.L2Operator NNReal BigOperators Kronecker

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
  {X F G : ℝ → Matrix n n ℂ} {a b t₀ : ℝ}

omit [DecidableEq n] in
/-- Uniqueness for a continuous matrix coefficient on a closed interval,
with the initial point anywhere in the interval, including its endpoints. -/
theorem eqOn_of_hasDerivAt_mul (hX : ContinuousOn X (Icc a b))
    (hF : ∀ t ∈ Icc a b, HasDerivAt F (X t * F t) t)
    (hG : ∀ t ∈ Icc a b, HasDerivAt G (X t * G t) t)
    (ht₀ : t₀ ∈ Icc a b) (h₀ : F t₀ = G t₀) : EqOn F G (Icc a b) := by
  classical
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hX
  let K : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hLip (t : ℝ) (ht : t ∈ Icc a b) :
      LipschitzOnWith K (fun Y : Matrix n n ℂ ↦ X t * Y) univ := by
    apply LipschitzOnWith.of_dist_le_mul
    intro Y _ Z _
    simp only [dist_eq_norm, ← mul_sub]
    exact (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right ((hC t ht).trans (le_max_left _ _)) (norm_nonneg _))
  intro t ht
  rcases le_total t t₀ with h | h
  · have hs : Icc t t₀ ⊆ Icc a b := Icc_subset_Icc ht.1 ht₀.2
    exact ODE_solution_unique_of_mem_Icc_left
      (fun u hu ↦ hLip u (hs (Ioc_subset_Icc_self hu)))
      (HasDerivAt.continuousOn fun u hu ↦ hF u (hs hu))
      (fun u hu ↦ (hF u (hs (Ioc_subset_Icc_self hu))).hasDerivWithinAt)
      (fun _ _ ↦ mem_univ _)
      (HasDerivAt.continuousOn fun u hu ↦ hG u (hs hu))
      (fun u hu ↦ (hG u (hs (Ioc_subset_Icc_self hu))).hasDerivWithinAt)
      (fun _ _ ↦ mem_univ _) h₀ ⟨le_rfl, h⟩
  · have hs : Icc t₀ t ⊆ Icc a b := Icc_subset_Icc ht₀.1 ht.2
    exact ODE_solution_unique_of_mem_Icc_right
      (fun u hu ↦ hLip u (hs (Ico_subset_Icc_self hu)))
      (HasDerivAt.continuousOn fun u hu ↦ hF u (hs hu))
      (fun u hu ↦ (hF u (hs (Ico_subset_Icc_self hu))).hasDerivWithinAt)
      (fun _ _ ↦ mem_univ _)
      (HasDerivAt.continuousOn fun u hu ↦ hG u (hs hu))
      (fun u hu ↦ (hG u (hs (Ico_subset_Icc_self hu))).hasDerivWithinAt)
      (fun _ _ ↦ mem_univ _) h₀ ⟨h, le_rfl⟩

/-- A fundamental solution transports every other solution from its value
at the base point. No invertibility hypothesis is needed. -/
theorem eq_mul_initial_of_hasDerivAt_mul (hX : ContinuousOn X (Icc a b))
    (hF : ∀ t ∈ Icc a b, HasDerivAt F (X t * F t) t)
    (hG : ∀ t ∈ Icc a b, HasDerivAt G (X t * G t) t)
    (ht₀ : t₀ ∈ Icc a b) (h₀ : G t₀ = 1) {t : ℝ} (ht : t ∈ Icc a b) :
    F t = G t * F t₀ := by
  apply eqOn_of_hasDerivAt_mul hX hF (G := fun u ↦ G u * F t₀) _ ht₀ _ ht
  · intro u hu
    simpa only [mul_assoc] using (hG u hu).mul_const (F t₀)
  · simp [h₀]

/-- A fundamental solution remains invertible. Uniqueness, applied backwards
from any chosen time to the initial time, shows that left multiplication by
that solution is injective. This also covers the empty matrix index type. -/
theorem isUnit_of_hasDerivAt_mul (hX : ContinuousOn X (Icc a b))
    (hG : ∀ t ∈ Icc a b, HasDerivAt G (X t * G t) t)
    (ht₀ : t₀ ∈ Icc a b) (h₀ : G t₀ = 1) {t : ℝ} (ht : t ∈ Icc a b) :
    IsUnit (G t) := by
  apply isUnit_iff_exists_inv.mpr
  apply LinearMap.surjective_of_injective (f := LinearMap.mulLeft ℂ (G t))
  intro U V hUV
  have hprod (C : Matrix n n ℂ) (u : ℝ) (hu : u ∈ Icc a b) :
      HasDerivAt (fun v ↦ G v * C) (X u * (G u * C)) u := by
    simpa only [mul_assoc] using (hG u hu).mul_const C
  have heq := eqOn_of_hasDerivAt_mul hX (hprod U) (hprod V) ht hUV ht₀
  simpa only [h₀, one_mul] using heq

/-- Rectangular solutions are transported column by column by the same
fundamental matrix. The derivatives are stated entrywise. -/
theorem eq_mul_initial_of_hasDerivAt_mul_entries {m : Type*}
    {F : ℝ → Matrix n m ℂ} (hX : ContinuousOn X (Icc a b))
    (hF : ∀ t ∈ Icc a b, ∀ i j, HasDerivAt (fun u ↦ F u i j) ((X t * F t) i j) t)
    (hG : ∀ t ∈ Icc a b, HasDerivAt G (X t * G t) t)
    (ht₀ : t₀ ∈ Icc a b) (h₀ : G t₀ = 1) {t : ℝ} (ht : t ∈ Icc a b) :
    F t = G t * F t₀ := by
  ext i j
  let H : ℝ → Matrix n n ℂ := fun u k _ ↦ F u k j
  have hH (u : ℝ) (hu : u ∈ Icc a b) : HasDerivAt H (X u * H u) u := by
    apply hasDerivAt_pi.mpr
    intro k
    apply hasDerivAt_pi.mpr
    intro l
    exact hF u hu k j
  exact congrFun (congrFun
    (eq_mul_initial_of_hasDerivAt_mul hX hH hG ht₀ h₀ ht) i) i

/-- Integration of a two-sided matrix equation. If `F' = X F - F Y`,
`G' = X G` and `H' = Y H`, then `F = G F₀ H⁻¹`. Both fundamental
solutions start at the identity; their invertibility is a consequence. -/
theorem eq_mul_initial_mul_inv_of_hasDerivAt {m : Type*} [Fintype m] [DecidableEq m]
    {F : ℝ → Matrix n m ℂ} {Y H : ℝ → Matrix m m ℂ}
    (hX : ContinuousOn X (Icc a b)) (hY : ContinuousOn Y (Icc a b))
    (hF : ∀ t ∈ Icc a b, ∀ i j,
      HasDerivAt (fun u ↦ F u i j) ((X t * F t - F t * Y t) i j) t)
    (hG : ∀ t ∈ Icc a b, HasDerivAt G (X t * G t) t)
    (hH : ∀ t ∈ Icc a b, HasDerivAt H (Y t * H t) t)
    (ht₀ : t₀ ∈ Icc a b) (hG₀ : G t₀ = 1) (hH₀ : H t₀ = 1)
    {t : ℝ} (ht : t ∈ Icc a b) : F t = G t * F t₀ * (H t)⁻¹ := by
  have hFH (u : ℝ) (hu : u ∈ Icc a b) (i : n) (j : m) :
      HasDerivAt (fun v ↦ (F v * H v) i j) ((X u * (F u * H u)) i j) u := by
    have hd := hasDerivAt_mul_entries (hF u hu)
      (fun k l ↦ (hasDerivAt_pi.mp (hasDerivAt_pi.mp (hH u hu) k) l)) i j
    simpa only [Matrix.sub_mul, Matrix.mul_assoc, sub_add_cancel] using hd
  have heq := eq_mul_initial_of_hasDerivAt_mul_entries hX hFH hG ht₀ hG₀ ht
  rw [hH₀, Matrix.mul_one] at heq
  have hi := (Matrix.isUnit_iff_isUnit_det _).mp
    (isUnit_of_hasDerivAt_mul hY hH ht₀ hH₀ ht)
  rw [← heq, Matrix.mul_nonsing_inv_cancel_right _ _ hi]

/-- Integration of the three-factor infinitesimal gauge law. The first two
fundamental matrices act on the two row indices, and the inverse of the
third acts on the column index. -/
theorem eq_kronecker_mul_initial_mul_inv_of_hasDerivAt
    {m p : Type*} [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p]
    {Y H : ℝ → Matrix m m ℂ} {Z J : ℝ → Matrix p p ℂ}
    {L : ℝ → Matrix (n × m) p ℂ}
    (hX : ContinuousOn X (Icc a b)) (hY : ContinuousOn Y (Icc a b))
    (hZ : ContinuousOn Z (Icc a b))
    (hG : ∀ t ∈ Icc a b, HasDerivAt G (X t * G t) t)
    (hH : ∀ t ∈ Icc a b, HasDerivAt H (Y t * H t) t)
    (hJ : ∀ t ∈ Icc a b, HasDerivAt J (Z t * J t) t)
    (hL : ∀ t ∈ Icc a b, ∀ i j k, HasDerivAt (fun u ↦ L u (i, j) k)
      (∑ i', X t i i' * L t (i', j) k + ∑ j', Y t j j' * L t (i, j') k -
        ∑ k', L t (i, j) k' * Z t k' k) t)
    (ht₀ : t₀ ∈ Icc a b) (hG₀ : G t₀ = 1) (hH₀ : H t₀ = 1) (hJ₀ : J t₀ = 1)
    {t : ℝ} (ht : t ∈ Icc a b) :
    L t = (G t ⊗ₖ H t) * L t₀ * (J t)⁻¹ := by
  let A : ℝ → Matrix (n × m) (n × m) ℂ := fun u ↦ X u ⊗ₖ 1 + 1 ⊗ₖ Y u
  have hA : ContinuousOn A (Icc a b) := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact ((continuousOn_pi.mp (continuousOn_pi.mp hX i.1) j.1).mul continuousOn_const).add
      (continuousOn_const.mul (continuousOn_pi.mp (continuousOn_pi.mp hY i.2) j.2))
  have hGH (u : ℝ) (hu : u ∈ Icc a b) :
      HasDerivAt (fun v ↦ G v ⊗ₖ H v) (A u * (G u ⊗ₖ H u)) u := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    have hd := (hasDerivAt_pi.mp (hasDerivAt_pi.mp (hG u hu) i.1) j.1).fun_mul
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp (hH u hu) i.2) j.2)
    simpa only [A, Matrix.add_mul, ← mul_kronecker_mul, one_mul,
      Matrix.add_apply, kroneckerMap_apply] using hd
  have hLd (u : ℝ) (hu : u ∈ Icc a b) (i : n × m) (k : p) :
      HasDerivAt (fun v ↦ L v i k) ((A u * L u - L u * Z u) i k) u := by
    convert hL u hu i.1 i.2 k using 1
    simp [A, Matrix.sub_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.add_apply, Matrix.one_apply, add_mul,
      Finset.sum_add_distrib]
  exact eq_mul_initial_mul_inv_of_hasDerivAt hA hZ hLd hGH hJ ht₀
    (by simp [hG₀, hH₀]) hJ₀ ht

end Matrix
