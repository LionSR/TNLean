/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.UnitInterval

/-!
# Closedness of bounded-rank matrices

The set of complex matrices of rank at most `k` is closed in the topology of entrywise
convergence, so matrix rank is lower semicontinuous.

## Main results

* `Matrix.isClosed_setOf_rank_le`: the set `{A | A.rank ≤ k}` of complex matrices is
  closed.
* `Matrix.lowerSemicontinuous_rank`: matrix rank over `ℂ` is lower semicontinuous.
* `isLocallyConstant_pair_of_lowerSemicontinuous_nat_mul_eq`: two lower-semicontinuous
  natural-valued functions with fixed positive product are locally constant.

The closedness result underlies the compactness of the set of states of Schmidt number
at most `r` (Wolf, *Quantum Channels & Operations*, Proposition 3.3). The final two
results isolate the topological argument in arXiv:1703.09188, lines 813–817.
-/

open Filter Matrix Module Submodule Set
open scoped Topology

namespace Matrix

variable {m n : Type*} [Finite m] [Fintype n]

/-- **Lower semicontinuity of rank.** The set of complex matrices of rank at most `k`
is closed in the topology of entrywise convergence. Equivalently, having rank greater
than `k` is an open condition. -/
theorem isClosed_setOf_rank_le (k : ℕ) :
    IsClosed {A : Matrix m n ℂ | A.rank ≤ k} := by
  classical
  let _ := Fintype.ofFinite m
  rw [← isOpen_compl_iff]
  let e : Matrix m n ℂ ≃L[ℂ] ((n → ℂ) →L[ℂ] (m → ℂ)) :=
    (Matrix.toLin' ≪≫ₗ LinearMap.toContinuousLinearMap).toContinuousLinearEquiv
  have hopen := (isOpen_setOfPred_nat_le_rank (𝕜 := ℂ)
    (E := n → ℂ) (F := m → ℂ) (k + 1)).preimage e.continuous
  convert hopen using 1
  ext A
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, Set.mem_preimage]
  change k < A.rank ↔ ↑(k + 1) ≤ Module.rank ℂ (Matrix.toLin' A).range
  rw [← Module.finrank_eq_rank]
  simp [Matrix.rank, Matrix.toLin'_apply']
  rfl

/-- Matrix rank over finite complex matrices is lower semicontinuous.

This packages `isClosed_setOf_rank_le` in Mathlib's semicontinuity API. -/
theorem lowerSemicontinuous_rank :
    LowerSemicontinuous fun A : Matrix m n ℂ => A.rank := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro k
  change IsClosed {A : Matrix m n ℂ | A.rank ≤ k}
  exact isClosed_setOf_rank_le (m := m) (n := n) k

end Matrix

/-- The rank along a continuous path of finite complex matrices is lower semicontinuous. -/
theorem Continuous.lowerSemicontinuous_matrix_rank
    {X m n : Type*} [TopologicalSpace X] [Finite m] [Fintype n]
    {A : X → Matrix m n ℂ} (hA : Continuous A) :
    LowerSemicontinuous fun x => (A x).rank := by
  simpa only [Function.comp_def] using
    (Matrix.lowerSemicontinuous_rank (m := m) (n := n)).comp hA

section FixedPositiveProduct

variable {X : Type*} [TopologicalSpace X]

/-- Two lower-semicontinuous natural-valued functions with a fixed positive product are
locally constant.

Indeed, lower semicontinuity makes both factors weakly increase near any point. Since
both factors are positive and their product is fixed, neither factor can increase.
This is the numerical topological step in arXiv:1703.09188, lines 813–817. -/
theorem isLocallyConstant_pair_of_lowerSemicontinuous_nat_mul_eq
    {r l : X → ℕ} {c : ℕ} (hr : LowerSemicontinuous r) (hl : LowerSemicontinuous l)
    (hc : 0 < c) (hmul : ∀ x, r x * l x = c) :
    IsLocallyConstant r ∧ IsLocallyConstant l := by
  have hpair : IsLocallyConstant fun x => (r x, l x) :=
    (IsLocallyConstant.iff_eventually_eq _).2 fun x => by
      have hr_pos : 0 < r x := Nat.pos_of_mul_pos_right (hmul x ▸ hc)
      have hl_pos : 0 < l x := Nat.pos_of_mul_pos_left (hmul x ▸ hc)
      have hr_ge : ∀ᶠ y in 𝓝 x, r x ≤ r y :=
        (hr x (r x - 1) (by omega)).mono fun y hy => by omega
      have hl_ge : ∀ᶠ y in 𝓝 x, l x ≤ l y :=
        (hl x (l x - 1) (by omega)).mono fun y hy => by omega
      filter_upwards [hr_ge, hl_ge] with y hry hly
      have hprod : r x * l x = r y * l y := (hmul x).trans (hmul y).symm
      have hle : r y * l x ≤ r x * l x := by
        calc
          r y * l x ≤ r y * l y := Nat.mul_le_mul_left _ hly
          _ = r x * l x := hprod.symm
      have hr_eq : r x = r y := Nat.eq_of_mul_eq_mul_right hl_pos <|
        le_antisymm (Nat.mul_le_mul_right _ hry) hle
      have hl_eq : l x = l y := Nat.eq_of_mul_eq_mul_left hr_pos <| by
        simpa only [hr_eq] using hprod
      exact Prod.ext hr_eq.symm hl_eq.symm
  exact ⟨hpair.comp Prod.fst, hpair.comp Prod.snd⟩

/-- On a preconnected set, lower-semicontinuous natural-valued functions with a fixed
positive product take the same pair of values at every two points of the set. -/
theorem eq_of_lowerSemicontinuous_nat_mul_eq_of_isPreconnected
    {r l : X → ℕ} {c : ℕ} (hr : LowerSemicontinuous r) (hl : LowerSemicontinuous l)
    (hc : 0 < c) (hmul : ∀ x, r x * l x = c) {s : Set X} (hs : IsPreconnected s)
    {x y : X} (hx : x ∈ s) (hy : y ∈ s) : r x = r y ∧ l x = l y := by
  obtain ⟨hr_local, hl_local⟩ :=
    isLocallyConstant_pair_of_lowerSemicontinuous_nat_mul_eq hr hl hc hmul
  exact ⟨hr_local.apply_eq_of_isPreconnected hs hx hy,
    hl_local.apply_eq_of_isPreconnected hs hx hy⟩

/-- On a preconnected space, lower-semicontinuous natural-valued functions with a fixed
positive product are constant. -/
theorem eq_of_lowerSemicontinuous_nat_mul_eq
    [PreconnectedSpace X] {r l : X → ℕ} {c : ℕ} (hr : LowerSemicontinuous r)
    (hl : LowerSemicontinuous l) (hc : 0 < c) (hmul : ∀ x, r x * l x = c)
    (x y : X) : r x = r y ∧ l x = l y :=
  eq_of_lowerSemicontinuous_nat_mul_eq_of_isPreconnected hr hl hc hmul
    isPreconnected_univ trivial trivial

/-- Lower-semicontinuous natural-valued functions with fixed positive product are
constant on the unit interval. -/
theorem unitInterval_eq_of_lowerSemicontinuous_nat_mul_eq
    {r l : unitInterval → ℕ} {c : ℕ} (hr : LowerSemicontinuous r)
    (hl : LowerSemicontinuous l) (hc : 0 < c) (hmul : ∀ x, r x * l x = c)
    (x y : unitInterval) : r x = r y ∧ l x = l y :=
  eq_of_lowerSemicontinuous_nat_mul_eq hr hl hc hmul x y

end FixedPositiveProduct
