/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.HierarchyEdgePartition
import Mathlib.Data.Nat.Dist
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Coordinate slices for the local hierarchy

Group sites into slices of width twice the locality radius. The support of a term lies
in the two slices determined by the lower end of its coordinate interval. Assigning the
term to their common coarse edge therefore constructs the pair operators from the actual
local terms, in any spatial dimension.

Source: Hastings, arXiv:cond-mat/0508554v3, lines 609–628 and 745–756.
-/

open Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.MPS.AreaLaw.LocalSolution

/-- The coarse slice of a site at coordinate `z`.
Hastings, arXiv:cond-mat/0508554v3, lines 609–628 and 745–756. -/
def coordinateSlice (ℓ z : ℕ) : ℕ := z / (2 * ℓ)

/-- The lower of the two coarse slices meeting a coordinate-local support. -/
def coordinateSliceLower (ℓ z : ℕ) : ℕ := (z - ℓ) / (2 * ℓ)

/-- A coordinate-local term meets only two consecutive coarse slices.
Hastings, arXiv:cond-mat/0508554v3, lines 609–628 and 745–756. -/
theorem coordinateSlice_eq_lower_or_succ {ℓ x z : ℕ} (hℓ : 0 < ℓ)
    (hx : Nat.dist x z ≤ ℓ) :
    coordinateSlice ℓ x = coordinateSliceLower ℓ z ∨
      coordinateSlice ℓ x = coordinateSliceLower ℓ z + 1 := by
  have hw : 0 < 2 * ℓ := by omega
  have hlow : z - ℓ ≤ x := by unfold Nat.dist at hx; omega
  have hhigh : x ≤ (z - ℓ) + 2 * ℓ := by unfold Nat.dist at hx; omega
  have hlo := Nat.div_le_div_right hlow (c := 2 * ℓ)
  have hhi := Nat.div_le_div_right hhigh (c := 2 * ℓ)
  have hdiv : ((z - ℓ) + 2 * ℓ) / (2 * ℓ) = (z - ℓ) / (2 * ℓ) + 1 := by
    exact Nat.add_div_right _ hw
  unfold coordinateSlice coordinateSliceLower
  omega

/-- The edge receiving a local term. The rightmost coarse edge is treated as the
closing edge zero. Hastings, arXiv:cond-mat/0508554v3, lines 626–628 and 745–756. -/
def coordinateSliceEdge {N : ℕ} (hN : 0 < N) (ℓ z : ℕ) : Fin N :=
  if hj : coordinateSliceLower ℓ z + 1 < N then
    ⟨coordinateSliceLower ℓ z + 1, hj⟩ else ⟨0, hN⟩

/-- Every internal assigned edge contains the whole coordinate-local support. -/
theorem coordinateSliceEdge_support {N ℓ z x : ℕ} (hN : 0 < N) (hℓ : 0 < ℓ)
    (hx : Nat.dist x z ≤ ℓ) {j : Fin N} (hj : 0 < (j : ℕ))
    (he : coordinateSliceEdge hN ℓ z = j) :
    coordinateSlice ℓ x + 1 = (j : ℕ) ∨ coordinateSlice ℓ x = (j : ℕ) := by
  have hchoice := coordinateSlice_eq_lower_or_succ hℓ hx
  unfold coordinateSliceEdge at he
  split_ifs at he with hlt
  · have hval := congrArg Fin.val he
    dsimp only at hval
    omega
  · have hval := congrArg Fin.val he
    dsimp only at hval
    omega

/-- A bound on the coordinate extent ensures all sites belong to the finite slice family. -/
theorem coordinateSlice_lt {N ℓ z : ℕ} (hℓ : 0 < ℓ) (hz : z < N * (2 * ℓ)) :
    coordinateSlice ℓ z < N := by
  unfold coordinateSlice
  exact (Nat.div_lt_iff_lt_mul (by omega)).mpr hz

/-- The closing edge receives the last slice; this is contained in the periodic
pair formed by the last and first slices. The coordinate extent is stated explicitly. -/
theorem coordinateSliceEdge_closing_support {N ℓ z x : ℕ} (hN : 0 < N) (hℓ : 0 < ℓ)
    (hz : z < N * (2 * ℓ)) (hxN : x < N * (2 * ℓ)) (hx : Nat.dist x z ≤ ℓ)
    (he : coordinateSliceEdge hN ℓ z = ⟨0, hN⟩) :
    coordinateSlice ℓ x + 1 = N ∨ coordinateSlice ℓ x = 0 := by
  have hchoice := coordinateSlice_eq_lower_or_succ hℓ hx
  have hlow : coordinateSliceLower ℓ z < N :=
    (Nat.div_le_div_right (Nat.sub_le z ℓ)).trans_lt (coordinateSlice_lt hℓ hz)
  have hhigh := coordinateSlice_lt hℓ hxN
  unfold coordinateSliceEdge at he
  split_ifs at he with hlt
  · have hval := congrArg Fin.val he
    dsimp only at hval
    omega
  · omega

private theorem natDist_cast_eq_dist (a b : ℕ) : (Nat.dist a b : ℝ) = dist a b := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab, Nat.cast_sub hab, Nat.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hab))]
    ring
  · rw [Nat.dist_eq_sub_of_le_right hba, Nat.cast_sub hba, Nat.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hba))]

/-- Projection to one coordinate does not enlarge distances in the coordinate maximum
metric. The same holds for any physical metric dominating that coordinate metric.
Hastings, arXiv:cond-mat/0508554v3, lines 745–756. -/
theorem natDist_coordinate_le_of_dist_le {σ : Type*} [PseudoMetricSpace σ] {D : ℕ}
    (coord : σ → (Fin D → ℕ))
    (hcoord : ∀ a b, dist (coord a) (coord b) ≤ dist a b) (axis : Fin D)
    {a b : σ} {ℓ : ℕ} (hab : dist a b ≤ ℓ) :
    Nat.dist (coord a axis) (coord b axis) ≤ ℓ := by
  have hmetric := (dist_le_pi_dist (coord a) (coord b) axis).trans ((hcoord a b).trans hab)
  rw [← natDist_cast_eq_dist] at hmetric
  exact_mod_cast hmetric

section Operators

variable {ι : Type*} [Fintype ι] {d N : ℕ}

/-- The actual pair operator is the sum of the local terms assigned to its coarse edge.
Hastings, arXiv:cond-mat/0508554v3, lines 628–639 and 745–756. -/
def coordinateSliceOperator (z : ι → ℕ) (ℓ : ℕ) (hN : 0 < N)
    (a : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ) : Fin N → Matrix (ι → Fin d) (ι → Fin d) ℂ :=
  edgePartition (fun i ↦ coordinateSliceEdge hN ℓ (z i)) a

/-- The coordinate grouping preserves the full sum of local terms. -/
theorem sum_coordinateSliceOperator (z : ι → ℕ) (ℓ : ℕ) (hN : 0 < N)
    (a : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ) :
    ∑ j, coordinateSliceOperator z ℓ hN a j = ∑ i, a i :=
  sum_edgePartition _ _

/-- Internal pair supports follow from the physical coordinate-local supports.
Hastings, arXiv:cond-mat/0508554v3, lines 609–639 and 745–756. -/
theorem coordinateSliceOperator_mem_supportedOperators (z : ι → ℕ)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (hN : 0 < N)
    (a : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (ha : ∀ i, a i ∈ supportedOperators d {v | Nat.dist (z v) (z i) ≤ ℓ})
    (j : Fin N) (hj : 0 < (j : ℕ)) :
    coordinateSliceOperator z ℓ hN a j ∈ supportedOperators d
      {v | coordinateSlice ℓ (z v) + 1 = (j : ℕ) ∨ coordinateSlice ℓ (z v) = (j : ℕ)} := by
  apply edgePartition_mem_supportedOperators
  intro i hi
  exact supportedOperators_mono (fun v hv ↦ coordinateSliceEdge_support hN hℓ hv hj hi) (ha i)

/-- Metric-ball support on an arbitrary finite coordinate box gives the actual adjacent
slice supports. Coordinate maximum distance may be replaced by any dominating physical
metric. Hastings, arXiv:cond-mat/0508554v3, lines 609–639 and 745–756. -/
theorem coordinateSliceOperator_mem_supportedOperators_of_metric [PseudoMetricSpace ι]
    {D : ℕ} (coord : ι → (Fin D → ℕ))
    (hcoord : ∀ a b, dist (coord a) (coord b) ≤ dist a b) (axis : Fin D)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (hN : 0 < N)
    (a : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (ha : ∀ i, a i ∈ supportedOperators d {v | dist v i ≤ ℓ})
    (j : Fin N) (hj : 0 < (j : ℕ)) :
    coordinateSliceOperator (fun i ↦ coord i axis) ℓ hN a j ∈ supportedOperators d
      {v | coordinateSlice ℓ (coord v axis) + 1 = (j : ℕ) ∨
        coordinateSlice ℓ (coord v axis) = (j : ℕ)} := by
  apply coordinateSliceOperator_mem_supportedOperators _ hℓ hN a _ j hj
  intro i
  exact supportedOperators_mono
    (fun v hv ↦ natDist_coordinate_le_of_dist_le coord hcoord axis hv) (ha i)

/-- The actual coordinate-slice edge operators are Hermitian. -/
theorem isHermitian_coordinateSliceOperator (z : ι → ℕ) (ℓ : ℕ) (hN : 0 < N)
    (a : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ) (ha : ∀ i, (a i).IsHermitian)
    (j : Fin N) : (coordinateSliceOperator z ℓ hN a j).IsHermitian :=
  isHermitian_edgePartition _ a ha j

variable [DecidableEq ι]

/-- The residual of an actual slice pair is at most the number of physical terms times
the local residual, in every dimension. Hastings, arXiv:cond-mat/0508554v3,
equation `low`, lines 628–639 and 745–756. -/
theorem residual_coordinateSliceOperator_le (z : ι → ℕ) (ℓ : ℕ) (hN : 0 < N)
    (a : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ) (ψ : EuclideanSpace ℂ (ι → Fin d))
    {ε : ℝ} (hε : 0 ≤ ε)
    (ha : ∀ i, ‖toEuclideanLin
      (a i - ((⟪ψ, toEuclideanLin (a i) ψ⟫_ℂ).re : ℂ) • 1) ψ‖ ≤ ε) (j : Fin N) :
    ‖toEuclideanLin (coordinateSliceOperator z ℓ hN a j -
      ((⟪ψ, toEuclideanLin (coordinateSliceOperator z ℓ hN a j) ψ⟫_ℂ).re : ℂ) • 1) ψ‖ ≤
      Fintype.card ι * ε :=
  residual_edgePartition_le _ a ψ hε ha j

/-- Local centred bounds give actual slice-pair bounds. -/
theorem centeredNorm_coordinateSliceOperator_le (z : ι → ℕ) (ℓ : ℕ) (hN : 0 < N)
    (a : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ) (ψ : EuclideanSpace ℂ (ι → Fin d))
    {K : ℝ} (hK : 0 ≤ K)
    (ha : ∀ i, ‖a i - ((⟪ψ, toEuclideanLin (a i) ψ⟫_ℂ).re : ℂ) • 1‖ ≤ K) (j : Fin N) :
    ‖coordinateSliceOperator z ℓ hN a j -
      ((⟪ψ, toEuclideanLin (coordinateSliceOperator z ℓ hN a j) ψ⟫_ℂ).re : ℂ) • 1‖ ≤
      Fintype.card ι * K :=
  centeredNorm_edgePartition_le _ a ψ hK ha j

/-- A coarse bound `2 N J` suffices for the centred norm of every actual slice pair.
Hastings, arXiv:cond-mat/0508554v3, lines 676–695 and 745–756. -/
theorem centeredNorm_coordinateSliceOperator_le_two_mul (z : ι → ℕ) (ℓ : ℕ) (hN : 0 < N)
    (a : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ) {ψ : EuclideanSpace ℂ (ι → Fin d)}
    (hψ : ‖ψ‖ = 1) {J : ℝ} (hJ : 0 ≤ J) (ha : ∀ i, ‖a i‖ ≤ J) (j : Fin N) :
    ‖coordinateSliceOperator z ℓ hN a j -
      ((⟪ψ, toEuclideanLin (coordinateSliceOperator z ℓ hN a j) ψ⟫_ℂ).re : ℂ) • 1‖ ≤
      2 * Fintype.card ι * J :=
  centeredNorm_edgePartition_le_two_mul _ a hψ hJ ha j

omit [DecidableEq ι] in
/-- The closing slice operator acts only on the two boundary slices of the finite box. -/
theorem coordinateSliceOperator_closing_mem_supportedOperators (z : ι → ℕ)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (hN : 0 < N) (hz : ∀ i, z i < N * (2 * ℓ))
    (a : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (ha : ∀ i, a i ∈ supportedOperators d {v | Nat.dist (z v) (z i) ≤ ℓ}) :
    coordinateSliceOperator z ℓ hN a ⟨0, hN⟩ ∈ supportedOperators d
      {v | coordinateSlice ℓ (z v) + 1 = N ∨ coordinateSlice ℓ (z v) = 0} := by
  apply edgePartition_mem_supportedOperators
  intro i hi
  exact supportedOperators_mono
    (fun v hv ↦ coordinateSliceEdge_closing_support hN hℓ (hz i) (hz v) hv hi) (ha i)

end Operators

end TNLean.MPS.AreaLaw.LocalSolution
