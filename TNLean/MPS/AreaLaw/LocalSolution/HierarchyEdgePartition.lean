/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.FiniteHierarchyEdges

/-!
# Partitioning local terms into hierarchy edges

An assignment of each physical term to one coarse edge gives its edge operator by summing
that fibre. The total operator is unchanged. Norms and local residuals increase by at most
the number of physical terms. This permits the coarse bounds used for coordinate slices in
Hastings, arXiv:cond-mat/0508554v3, lines 609–639 and 745–756.
-/

open Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.MPS.AreaLaw.LocalSolution

/-- Sum the physical terms assigned to one coarse edge.
Hastings, arXiv:cond-mat/0508554v3, lines 609–639 and 745–756. -/
def edgePartition {α β A : Type*} [Fintype α] [DecidableEq β] [AddCommMonoid A]
    (f : α → β) (a : α → A) (j : β) : A := ∑ i with f i = j, a i

/-- Each physical term occurs exactly once in the coarse sum. -/
theorem sum_edgePartition {α β A : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [AddCommMonoid A] (f : α → β) (a : α → A) :
    ∑ j, edgePartition f a j = ∑ i, a i := Finset.sum_fiberwise Finset.univ f a

/-- A fibre sum has norm at most the total number of terms times their uniform bound. -/
theorem norm_edgePartition_le {α β E : Type*} [Fintype α] [DecidableEq β]
    [NormedAddCommGroup E] (f : α → β) (a : α → E) {J : ℝ} (hJ : 0 ≤ J)
    (ha : ∀ i, ‖a i‖ ≤ J) (j : β) : ‖edgePartition f a j‖ ≤ Fintype.card α * J := by
  unfold edgePartition
  calc
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i ↦ f i = j), ‖a i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i ↦ f i = j), J := Finset.sum_le_sum fun i _ ↦ ha i
    _ = ((Finset.univ.filter (fun i ↦ f i = j)).card : ℝ) * J := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ _) hJ

section Matrices

variable {α β n : Type*} [Fintype α] [DecidableEq β] [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- Hermiticity passes from local terms to every coarse edge. -/
theorem isHermitian_edgePartition (f : α → β) (a : α → Matrix n n ℂ)
    (ha : ∀ i, (a i).IsHermitian) (j : β) : (edgePartition f a j).IsHermitian := by
  change (edgePartition f a j).conjTranspose = edgePartition f a j
  simp only [edgePartition, Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun i _ ↦ (ha i).eq

/-- Centring at the expectation in one reference vector commutes with partition sums. -/
theorem centered_edgePartition (f : α → β) (a : α → Matrix n n ℂ)
    (ψ : EuclideanSpace ℂ n) (j : β) :
    edgePartition f a j - ((⟪ψ, toEuclideanLin (edgePartition f a j) ψ⟫_ℂ).re : ℂ) • 1 =
      edgePartition f
        (fun i ↦ a i - ((⟪ψ, toEuclideanLin (a i) ψ⟫_ℂ).re : ℂ) • 1) j := by
  simp only [edgePartition, map_sum, LinearMap.sum_apply, inner_sum, Complex.re_sum,
    Finset.sum_sub_distrib, Complex.ofReal_sum, Finset.sum_smul]

/-- The residual of a coarse edge follows from the local residuals, without an
assumption about a preassembled pair operator. Hastings, arXiv:cond-mat/0508554v3,
equation `low`, lines 628–639 and 745–756. -/
theorem residual_edgePartition_le (f : α → β) (a : α → Matrix n n ℂ)
    (ψ : EuclideanSpace ℂ n) {ε : ℝ} (hε : 0 ≤ ε)
    (ha : ∀ i, ‖toEuclideanLin
      (a i - ((⟪ψ, toEuclideanLin (a i) ψ⟫_ℂ).re : ℂ) • 1) ψ‖ ≤ ε) (j : β) :
    ‖toEuclideanLin
      (edgePartition f a j -
        ((⟪ψ, toEuclideanLin (edgePartition f a j) ψ⟫_ℂ).re : ℂ) • 1) ψ‖ ≤
      Fintype.card α * ε := by
  rw [centered_edgePartition]
  simp only [edgePartition, map_sum, LinearMap.sum_apply]
  exact norm_edgePartition_le f
    (fun i ↦ toEuclideanLin (a i - ((⟪ψ, toEuclideanLin (a i) ψ⟫_ℂ).re : ℂ) • 1) ψ) hε ha j

/-- Uniform local centred-norm bounds give the coarse centred-norm bound. -/
theorem centeredNorm_edgePartition_le (f : α → β) (a : α → Matrix n n ℂ)
    (ψ : EuclideanSpace ℂ n) {K : ℝ} (hK : 0 ≤ K)
    (ha : ∀ i, ‖a i - ((⟪ψ, toEuclideanLin (a i) ψ⟫_ℂ).re : ℂ) • 1‖ ≤ K) (j : β) :
    ‖edgePartition f a j -
      ((⟪ψ, toEuclideanLin (edgePartition f a j) ψ⟫_ℂ).re : ℂ) • 1‖ ≤
      Fintype.card α * K := by
  rw [centered_edgePartition]
  exact norm_edgePartition_le f _ hK ha j

/-- Local operator norms suffice for the coarse centred bound `2 N J`, in every dimension.
Hastings, arXiv:cond-mat/0508554v3, lines 676–695 and 745–756. -/
theorem centeredNorm_edgePartition_le_two_mul (f : α → β) (a : α → Matrix n n ℂ)
    {ψ : EuclideanSpace ℂ n} (hψ : ‖ψ‖ = 1) {J : ℝ} (hJ : 0 ≤ J)
    (ha : ∀ i, ‖a i‖ ≤ J) (j : β) :
    ‖edgePartition f a j -
      ((⟪ψ, toEuclideanLin (edgePartition f a j) ψ⟫_ℂ).re : ℂ) • 1‖ ≤
      2 * Fintype.card α * J := by
  refine (norm_sub_smul_one_le_two_mul
    (abs_re_inner_toEuclideanLin_le (edgePartition f a j) hψ)).trans ?_
  nlinarith [norm_edgePartition_le f a hJ ha j]

end Matrices

section Support

variable {α β ι : Type*} [Fintype α] [DecidableEq β] [Fintype ι] {d : ℕ}

/-- A coarse edge has the support shared by the terms assigned to it. -/
theorem edgePartition_mem_supportedOperators (f : α → β)
    (a : α → Matrix (ι → Fin d) (ι → Fin d) ℂ) (j : β) (S : Set ι)
    (ha : ∀ i, f i = j → a i ∈ supportedOperators d S) :
    edgePartition f a j ∈ supportedOperators d S := by
  apply Submodule.sum_mem
  intro i hi
  exact ha i (Finset.mem_filter.mp hi).2

end Support

end TNLean.MPS.AreaLaw.LocalSolution
