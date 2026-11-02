/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.CoordinateSliceHierarchy
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Sharp coarsening of a periodic one-dimensional chain

A periodic chain with `N` blocks of `2ℓ` physical sites is grouped into adjacent pairs.
A term centred in the first half of its block belongs to the preceding edge; a term
centred in the second half belongs to the following edge. Every edge receives exactly
`2ℓ` terms. Cyclic balls of radius `ℓ` lie in the assigned pair, including the closing
edge. Local norm and residual estimates consequently give centred pair norm `4ℓJ`
and residual `2ℓε`, independently of the number of physical sites.

This module treats a regular periodic chain. The estimates do not identify a periodic
chain with an open interval, and use the actual cyclic physical distance.

Source: Hastings, arXiv:cond-mat/0508554v3, lines 609–639 and 676–695.
-/

open Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.MPS.AreaLaw.LocalSolution

/-- The edge receiving a term on a regular periodic chain grouped into blocks of width `2ℓ`.
For the coarsening in Hastings, arXiv:cond-mat/0508554v3, lines 609–639. -/
def periodicCoarseEdge {N ℓ : ℕ} (i : Fin N × Fin (2 * ℓ)) : Fin N :=
  if (i.2 : ℕ) < ℓ then i.1 else finRotate N i.1

/-- A coarse edge receives exactly `2ℓ` local terms, uniformly in the chain length.
For the coarsening in Hastings, arXiv:cond-mat/0508554v3, lines 609–639. -/
theorem card_periodicCoarseEdge_fibre {N ℓ : ℕ} (j : Fin N) :
    (Finset.univ.filter (fun i : Fin N × Fin (2 * ℓ) ↦ periodicCoarseEdge i = j)).card =
      2 * ℓ := by
  have hinj : Set.InjOn Prod.snd
      (↑(Finset.univ.filter (fun i : Fin N × Fin (2 * ℓ) ↦ periodicCoarseEdge i = j)) :
        Set (Fin N × Fin (2 * ℓ))) := by
    intro a ha b hb hab
    have hea := (Finset.mem_filter.mp ha).2
    have heb := (Finset.mem_filter.mp hb).2
    apply Prod.ext _ hab
    unfold periodicCoarseEdge at hea heb
    rw [hab] at hea
    split_ifs at hea heb with hs
    · exact hea.trans heb.symm
    · exact (finRotate N).injective (hea.trans heb.symm)
  have hsurj : Set.SurjOn Prod.snd
      (↑(Finset.univ.filter (fun i : Fin N × Fin (2 * ℓ) ↦ periodicCoarseEdge i = j)) :
        Set (Fin N × Fin (2 * ℓ))) (↑(Finset.univ : Finset (Fin (2 * ℓ)))) := by
    intro s _
    by_cases hs : (s : ℕ) < ℓ
    · exact ⟨(j, s), by simp [periodicCoarseEdge, hs], rfl⟩
    · refine ⟨((finRotate N).symm j, s), ?_, rfl⟩
      change ((finRotate N).symm j, s) ∈
        Finset.univ.filter (fun i : Fin N × Fin (2 * ℓ) ↦ periodicCoarseEdge i = j)
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change (if (s : ℕ) < ℓ then (finRotate N).symm j else
        finRotate N ((finRotate N).symm j)) = j
      rw [ite_eq_right hs]
      exact (finRotate N).apply_symm_apply j
  have hc := Finset.card_nbij Prod.snd
    (s := Finset.univ.filter (fun i : Fin N × Fin (2 * ℓ) ↦ periodicCoarseEdge i = j))
    (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _) hinj hsurj
  simpa using hc

/-- Consecutive coarse sites have either consecutive natural labels or wrap to zero.
For the coarsening in Hastings, arXiv:cond-mat/0508554v3, lines 609–639. -/
theorem finRotate_val_eq_succ_or_zero {N : ℕ} (i : Fin N) :
    (finRotate N i : ℕ) = (i : ℕ) + 1 ∨
      ((i : ℕ) + 1 = N ∧ (finRotate N i : ℕ) = 0) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero i.pos.ne'
  rw [coe_finRotate]
  split_ifs with hi
  · right
    simp [hi]
  · exact Or.inl rfl

/-- The physical coordinate on a regular periodic chain.
For the coarsening in Hastings, arXiv:cond-mat/0508554v3, lines 609–639. -/
def periodicPhysicalCoordinate {N ℓ : ℕ} (i : Fin N × Fin (2 * ℓ)) : ℕ :=
  (i.1 : ℕ) * (2 * ℓ) + (i.2 : ℕ)

/-- The physical cyclic distance between two sites.
For the coarsening in Hastings, arXiv:cond-mat/0508554v3, lines 609–639. -/
def periodicPhysicalDistance {N ℓ : ℕ} (i v : Fin N × Fin (2 * ℓ)) : ℕ :=
  min (Nat.dist (periodicPhysicalCoordinate i) (periodicPhysicalCoordinate v))
    (N * (2 * ℓ) - Nat.dist (periodicPhysicalCoordinate i) (periodicPhysicalCoordinate v))

/-- The flattened coordinate is within the physical chain.
For the coarsening in Hastings, arXiv:cond-mat/0508554v3, lines 609–639. -/
theorem periodicPhysicalCoordinate_lt {N ℓ : ℕ} (i : Fin N × Fin (2 * ℓ)) :
    periodicPhysicalCoordinate i < N * (2 * ℓ) := by
  have hi := i.1.isLt
  have hs := i.2.isLt
  dsimp [periodicPhysicalCoordinate]
  nlinarith

/-- An internal assigned edge centres its terms within one locality radius of that edge.
For the coarsening in Hastings, arXiv:cond-mat/0508554v3, lines 609–639. -/
theorem periodicCoarseEdge_internal_centre {N ℓ : ℕ}
    (i : Fin N × Fin (2 * ℓ)) {j : Fin N} (hj : 0 < (j : ℕ))
    (he : periodicCoarseEdge i = j) :
    (j : ℕ) * (2 * ℓ) ≤ periodicPhysicalCoordinate i + ℓ ∧
      periodicPhysicalCoordinate i < (j : ℕ) * (2 * ℓ) + ℓ := by
  have hs := i.2.isLt
  have hrot := finRotate_val_eq_succ_or_zero i.1
  unfold periodicCoarseEdge at he
  split_ifs at he with hhead
  · have hval := congrArg Fin.val he
    dsimp [periodicPhysicalCoordinate]
    constructor <;> nlinarith
  · have hval := congrArg Fin.val he
    rcases hrot with hrot | ⟨_, hrot⟩
    · dsimp [periodicPhysicalCoordinate]
      constructor <;> nlinarith
    · omega

/-- A cyclic locality ball is contained in the two blocks of its assigned internal edge.
For the coarsening in Hastings, arXiv:cond-mat/0508554v3, lines 609–639. -/
theorem periodicCoarseEdge_support {N ℓ : ℕ} (hℓ : 0 < ℓ)
    (i v : Fin N × Fin (2 * ℓ)) {j : Fin N} (hj : 0 < (j : ℕ))
    (he : periodicCoarseEdge i = j) (hv : periodicPhysicalDistance i v ≤ ℓ) :
    (v.1 : ℕ) + 1 = (j : ℕ) ∨ (v.1 : ℕ) = (j : ℕ) := by
  obtain ⟨hlo, hhi⟩ := periodicCoarseEdge_internal_centre i hj he
  have hi := periodicPhysicalCoordinate_lt i
  have hx := periodicPhysicalCoordinate_lt v
  have hjN := j.isLt
  have hzlo : ℓ ≤ periodicPhysicalCoordinate i := by nlinarith
  have hzhi : periodicPhysicalCoordinate i + ℓ < N * (2 * ℓ) := by nlinarith
  have hd : Nat.dist (periodicPhysicalCoordinate i) (periodicPhysicalCoordinate v) ≤ ℓ := by
    unfold periodicPhysicalDistance at hv
    rw [min_le_iff] at hv
    rcases hv with hv | hv
    · exact hv
    · unfold Nat.dist at hv ⊢
      omega
  have hjw : (j : ℕ) * (2 * ℓ) = ((j : ℕ) - 1) * (2 * ℓ) + 2 * ℓ := by
    have : (j : ℕ) - 1 + 1 = (j : ℕ) := by omega
    nlinarith
  have hxlo : ((j : ℕ) - 1) * (2 * ℓ) ≤ periodicPhysicalCoordinate v := by
    have hd' := Nat.dist_tri_right' (periodicPhysicalCoordinate i) (periodicPhysicalCoordinate v)
    nlinarith
  have hxhi : periodicPhysicalCoordinate v < ((j : ℕ) + 1) * (2 * ℓ) := by
    have hd' := Nat.dist_tri_right (periodicPhysicalCoordinate i) (periodicPhysicalCoordinate v)
    nlinarith
  have hdiv : periodicPhysicalCoordinate v / (2 * ℓ) = (v.1 : ℕ) := by
    apply Nat.div_eq_of_lt_le
    · dsimp [periodicPhysicalCoordinate]
      omega
    · dsimp [periodicPhysicalCoordinate]
      nlinarith [v.2.isLt]
  have hblocklo := (Nat.le_div_iff_mul_le (by omega : 0 < 2 * ℓ)).mpr hxlo
  have hblockhi := (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * ℓ)).mpr hxhi
  rw [hdiv] at hblocklo hblockhi
  omega

private theorem cyclic_boundary_interval {L r x z : ℕ}
    (hr : 0 < r) (hx : x < L) (hz : z < L)
    (hc : z < r ∨ L ≤ z + r)
    (hd : min (Nat.dist z x) (L - Nat.dist z x) ≤ r) :
    x < 2 * r ∨ L ≤ x + 2 * r := by
  unfold Nat.dist at hd
  omega


private theorem periodicCoarseEdge_zero_centre {N ℓ : ℕ}
    (i : Fin N × Fin (2 * ℓ)) {j : Fin N} (hj : (j : ℕ) = 0)
    (he : periodicCoarseEdge i = j) :
    periodicPhysicalCoordinate i < ℓ ∨
      N * (2 * ℓ) ≤ periodicPhysicalCoordinate i + ℓ := by
  have hs := i.2.isLt
  have hrot := finRotate_val_eq_succ_or_zero i.1
  unfold periodicCoarseEdge at he
  split_ifs at he with hhead
  · have hval : (i.1 : ℕ) = 0 := (congrArg Fin.val he).trans hj
    left
    simpa only [periodicPhysicalCoordinate, hval, zero_mul, zero_add] using hhead
  · have hval : (finRotate N i.1 : ℕ) = 0 := (congrArg Fin.val he).trans hj
    rcases hrot with hrot | ⟨hwrap, _⟩
    · omega
    · right
      dsimp [periodicPhysicalCoordinate]
      nlinarith


/-- The closing cyclic locality ball meets only the first and last coarse blocks.
For the coarsening in Hastings, arXiv:cond-mat/0508554v3, lines 609–639. -/
theorem periodicCoarseEdge_zero_support {N ℓ : ℕ} (hℓ : 0 < ℓ)
    (i v : Fin N × Fin (2 * ℓ)) {j : Fin N} (hj : (j : ℕ) = 0)
    (he : periodicCoarseEdge i = j) (hv : periodicPhysicalDistance i v ≤ ℓ) :
    (v.1 : ℕ) = 0 ∨ (v.1 : ℕ) + 1 = N := by
  have hc := periodicCoarseEdge_zero_centre i hj he
  have hx := cyclic_boundary_interval hℓ (periodicPhysicalCoordinate_lt v)
    (periodicPhysicalCoordinate_lt i) hc hv
  rcases hx with hx | hx
  · left
    by_contra hn
    have hp : 1 ≤ (v.1 : ℕ) := by omega
    have hm := Nat.mul_le_mul_right (2 * ℓ) hp
    dsimp [periodicPhysicalCoordinate] at hx
    nlinarith [Nat.zero_le (v.2 : ℕ)]
  · right
    by_contra hn
    have hp : (v.1 : ℕ) + 2 ≤ N := by have := v.1.isLt; omega
    have hm := Nat.mul_le_mul_right (2 * ℓ) hp
    dsimp [periodicPhysicalCoordinate] at hx
    nlinarith [v.2.isLt]


/-- Every cyclic locality ball lies in the two blocks adjacent to its assigned edge,
including the edge joining the last and first blocks.
For the coarsening in Hastings, arXiv:cond-mat/0508554v3, lines 609–639. -/
theorem periodicCoarseEdge_support_all {N ℓ : ℕ} (hℓ : 0 < ℓ)
    (i v : Fin N × Fin (2 * ℓ)) {j : Fin N}
    (he : periodicCoarseEdge i = j) (hv : periodicPhysicalDistance i v ≤ ℓ) :
    v.1 = j ∨ finRotate N v.1 = j := by
  by_cases hj : (j : ℕ) = 0
  · rcases periodicCoarseEdge_zero_support hℓ i v hj he hv with hzero | hlast
    · exact Or.inl (Fin.ext (hzero.trans hj.symm))
    · right
      apply Fin.ext
      rcases finRotate_val_eq_succ_or_zero v.1 with hsucc | ⟨_, hzero⟩
      · have := (finRotate N v.1).isLt
        omega
      · exact hzero.trans hj.symm
  · have hjpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero hj
    rcases periodicCoarseEdge_support hℓ i v hjpos he hv with hprev | hsame
    · right
      apply Fin.ext
      rcases finRotate_val_eq_succ_or_zero v.1 with hsucc | ⟨hwrap, _⟩
      · exact hsucc.trans hprev
      · have := j.isLt
        omega
    · exact Or.inl (Fin.ext hsame)


/-- A partition sum is controlled by the size of its actual fibre.
For the coarsening in Hastings, arXiv:cond-mat/0508554v3, lines 609–639. -/
theorem norm_edgePartition_le_of_fibre_card {α β E : Type*} [Fintype α] [DecidableEq β]
    [NormedAddCommGroup E] (f : α → β) (a : α → E) {J : ℝ} (hJ : 0 ≤ J)
    (ha : ∀ i, ‖a i‖ ≤ J) (j : β) {M : ℕ}
    (hM : (Finset.univ.filter (fun i ↦ f i = j)).card ≤ M) :
    ‖edgePartition f a j‖ ≤ M * J := by
  unfold edgePartition
  calc
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i ↦ f i = j), ‖a i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i ↦ f i = j), J := Finset.sum_le_sum fun i _ ↦ ha i
    _ = ((Finset.univ.filter (fun i ↦ f i = j)).card : ℝ) * J := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hM) hJ

/-- The actual periodic pair operator.
For the coarsening in Hastings, arXiv:cond-mat/0508554v3, lines 609–639. -/
def periodicCoarseOperator {N ℓ d : ℕ}
    (a : (Fin N × Fin (2 * ℓ)) →
      Matrix ((Fin N × Fin (2 * ℓ)) → Fin d) ((Fin N × Fin (2 * ℓ)) → Fin d) ℂ) :=
  edgePartition periodicCoarseEdge a

/-- Grouping the periodic terms preserves their sum.
For the coarsening in Hastings, arXiv:cond-mat/0508554v3, lines 609–639. -/
theorem sum_periodicCoarseOperator {N ℓ d : ℕ}
    (a : (Fin N × Fin (2 * ℓ)) →
      Matrix ((Fin N × Fin (2 * ℓ)) → Fin d) ((Fin N × Fin (2 * ℓ)) → Fin d) ℂ) :
    ∑ j, periodicCoarseOperator a j = ∑ i, a i := sum_edgePartition _ _

/-- Physical cyclic locality gives the internal pair support.
For the coarsening in Hastings, arXiv:cond-mat/0508554v3, lines 609–639. -/
theorem periodicCoarseOperator_mem_supportedOperators {N ℓ d : ℕ} (hℓ : 0 < ℓ)
    (a : (Fin N × Fin (2 * ℓ)) →
      Matrix ((Fin N × Fin (2 * ℓ)) → Fin d) ((Fin N × Fin (2 * ℓ)) → Fin d) ℂ)
    (ha : ∀ i, a i ∈ supportedOperators d {v | periodicPhysicalDistance i v ≤ ℓ})
    (j : Fin N) (hj : 0 < (j : ℕ)) :
    periodicCoarseOperator a j ∈ supportedOperators d
      {v | (v.1 : ℕ) + 1 = (j : ℕ) ∨ (v.1 : ℕ) = (j : ℕ)} := by
  apply edgePartition_mem_supportedOperators
  intro i hi
  exact supportedOperators_mono (fun v hv ↦ periodicCoarseEdge_support hℓ i v hj hi hv) (ha i)

/-- Hermiticity is preserved by the periodic grouping.
For the coarsening in Hastings, arXiv:cond-mat/0508554v3, lines 609–639. -/
theorem isHermitian_periodicCoarseOperator {N ℓ d : ℕ}
    (a : (Fin N × Fin (2 * ℓ)) →
      Matrix ((Fin N × Fin (2 * ℓ)) → Fin d) ((Fin N × Fin (2 * ℓ)) → Fin d) ℂ)
    (ha : ∀ i, (a i).IsHermitian) (j : Fin N) :
    (periodicCoarseOperator a j).IsHermitian := isHermitian_edgePartition _ a ha j

/-- The pair residual costs `2ℓ` local residuals, independently of the chain length.
For the coarsening in Hastings, arXiv:cond-mat/0508554v3, lines 609–639. -/
theorem residual_periodicCoarseOperator_le {N ℓ d : ℕ}
    (a : (Fin N × Fin (2 * ℓ)) →
      Matrix ((Fin N × Fin (2 * ℓ)) → Fin d) ((Fin N × Fin (2 * ℓ)) → Fin d) ℂ)
    (ψ : EuclideanSpace ℂ ((Fin N × Fin (2 * ℓ)) → Fin d))
    {ε : ℝ} (hε : 0 ≤ ε)
    (ha : ∀ i, ‖toEuclideanLin
      (a i - ((⟪ψ, toEuclideanLin (a i) ψ⟫_ℂ).re : ℂ) • 1) ψ‖ ≤ ε) (j : Fin N) :
    ‖toEuclideanLin (periodicCoarseOperator a j -
      ((⟪ψ, toEuclideanLin (periodicCoarseOperator a j) ψ⟫_ℂ).re : ℂ) • 1) ψ‖ ≤
      (2 * ℓ : ℕ) * ε := by
  rw [periodicCoarseOperator, centered_edgePartition]
  simp only [edgePartition, map_sum, LinearMap.sum_apply]
  exact norm_edgePartition_le_of_fibre_card periodicCoarseEdge _ hε ha j
    (card_periodicCoarseEdge_fibre j).le

/-- The centred pair norm is at most `4ℓJ`, independently of the chain length.
For the coarsening in Hastings, arXiv:cond-mat/0508554v3, lines 609–639. -/
theorem centeredNorm_periodicCoarseOperator_le {N ℓ d : ℕ}
    (a : (Fin N × Fin (2 * ℓ)) →
      Matrix ((Fin N × Fin (2 * ℓ)) → Fin d) ((Fin N × Fin (2 * ℓ)) → Fin d) ℂ)
    {ψ : EuclideanSpace ℂ ((Fin N × Fin (2 * ℓ)) → Fin d)} (hψ : ‖ψ‖ = 1)
    {J : ℝ} (hJ : 0 ≤ J) (ha : ∀ i, ‖a i‖ ≤ J) (j : Fin N) :
    ‖periodicCoarseOperator a j -
      ((⟪ψ, toEuclideanLin (periodicCoarseOperator a j) ψ⟫_ℂ).re : ℂ) • 1‖ ≤
      4 * (ℓ : ℝ) * J := by
  refine (norm_sub_smul_one_le_two_mul
    (abs_re_inner_toEuclideanLin_le (periodicCoarseOperator a j) hψ)).trans ?_
  have hn := norm_edgePartition_le_of_fibre_card periodicCoarseEdge a hJ ha j
    (card_periodicCoarseEdge_fibre j).le
  change ‖periodicCoarseOperator a j‖ ≤ _ at hn
  push_cast at hn
  nlinarith


end TNLean.MPS.AreaLaw.LocalSolution
