/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.Complex.Basic

/-!
# Rank–minor characterization and closedness of bounded-rank matrices

This file proves the classical characterization of matrix rank by nonsingular minors:
a matrix has rank greater than `k` exactly when it possesses an invertible
`(k+1) × (k+1)` submatrix, indexed by injective row and column selections. As a
consequence, the set of matrices of rank at most `k` is closed in the topology of
entrywise convergence over `ℂ`, i.e. matrix rank is lower semicontinuous.

## Main results

* `Matrix.exists_injective_linearIndependent_cols_of_lt_rank`: from `k < A.rank` one
  extracts `k+1` columns at distinct indices that are linearly independent.
* `Matrix.lt_rank_iff_exists_isUnit_submatrix`: `k < A.rank` iff there exist injective
  index selections `f, g` of size `k+1` with `A.submatrix f g` invertible.
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

/-- **Index-aligned column extraction.** If `k < A.rank` then there is an injective
selection `g : Fin (k+1) → n` of columns whose associated column vectors are linearly
independent. This is the column-space half of the rank–minor characterization. -/
theorem exists_injective_linearIndependent_cols_of_lt_rank
    {K : Type*} [Field K] (A : Matrix m n K) {k : ℕ} (hk : k < A.rank) :
    ∃ g : Fin (k + 1) → n, Function.Injective g ∧
      LinearIndependent K (fun j : Fin (k + 1) => A.col (g j)) := by
  classical
  -- Extract a linearly independent sub-family of the columns spanning the same space.
  obtain ⟨κ, a, ha_inj, ha_span, ha_li⟩ := exists_linearIndependent' K A.col
  -- That sub-family lives in the finite-dimensional space `m → K`, hence is finite.
  have : Finite κ := ha_li.finite
  cases nonempty_fintype κ
  -- Its cardinality equals `finrank` of the column span, which is `A.rank`.
  have hcard : Fintype.card κ = A.rank := by
    have hli_card : Fintype.card κ = (Set.range (A.col ∘ a)).finrank K :=
      linearIndependent_iff_card_eq_finrank_span.mp ha_li
    rw [hli_card, Set.finrank, ha_span, ← rank_eq_finrank_span_cols]
  -- Since `A.rank > k`, there is an injection `Fin (k+1) ↪ κ`; compose with `a`.
  have hle : k + 1 ≤ Fintype.card κ := by rw [hcard]; exact hk
  obtain ⟨e⟩ : Nonempty (Fin (k + 1) ↪ κ) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hle)
  refine ⟨a ∘ e, ha_inj.comp e.injective, ?_⟩
  -- The selected columns are a sub-family of a linearly independent family.
  exact ha_li.comp e e.injective

/-- **Rank–minor characterization.** A matrix has rank greater than `k` if and only if
some `(k+1) × (k+1)` submatrix, selected by injective row and column index maps, is
invertible. -/
theorem lt_rank_iff_exists_isUnit_submatrix
    {K : Type*} [Field K] (A : Matrix m n K) (k : ℕ) :
    k < A.rank ↔ ∃ (f : Fin (k + 1) → m) (g : Fin (k + 1) → n),
      Function.Injective f ∧ Function.Injective g ∧ IsUnit (A.submatrix f g) := by
  classical
  cases nonempty_fintype m
  constructor
  · intro hk
    -- Stage A: extract `k+1` independent columns at distinct indices.
    obtain ⟨g, hg_inj, hg_li⟩ := exists_injective_linearIndependent_cols_of_lt_rank A hk
    -- The resulting strip `B = A.submatrix id g` has full column rank `k+1`.
    set B : Matrix m (Fin (k + 1)) K := A.submatrix id g with hB
    have hB_col : B.col = fun j : Fin (k + 1) => A.col (g j) := by
      ext j i; simp [hB, Matrix.col, Matrix.submatrix]
    -- For columns of a matrix `B`, `Bᵀ.row = B.col`, so the transpose has full row rank.
    have hBT_rank : Bᵀ.rank = k + 1 := by
      have hli_col : LinearIndependent K B.col := by rw [hB_col]; exact hg_li
      have hrow : Bᵀ.row = B.col := by ext j i; simp [Matrix.row, Matrix.col]
      have hli' : LinearIndependent K Bᵀ.row := by rw [hrow]; exact hli_col
      simpa using hli'.rank_matrix
    -- Stage B: apply Stage A to `Bᵀ` to extract `k+1` independent rows of `B`.
    have hkBT : k < Bᵀ.rank := by rw [hBT_rank]; exact Nat.lt_succ_self k
    obtain ⟨f, hf_inj, hf_li⟩ :=
      exists_injective_linearIndependent_cols_of_lt_rank Bᵀ hkBT
    -- `hf_li` exhibits the selected rows of `A.submatrix f g` as independent, since
    -- `Bᵀ.col (f j)` is the `(f j)`-th row of `B = A.submatrix id g`, i.e. the `j`-th
    -- row of `A.submatrix f g`. Independent rows of a square matrix mean it is a unit.
    refine ⟨f, g, hf_inj, hg_inj, ?_⟩
    rw [← linearIndependent_rows_iff_isUnit]
    have hC_row : (A.submatrix f g).row = fun j : Fin (k + 1) => Bᵀ.col (f j) := by
      ext j i
      simp [hB, Matrix.row, Matrix.col, Matrix.transpose, Matrix.submatrix]
    rw [hC_row]; exact hf_li
  · rintro ⟨f, g, _, _, hUnit⟩
    -- The submatrix is a `(k+1) × (k+1)` unit, so it has full rank `k+1 ≤ A.rank`.
    have hrank : (A.submatrix f g).rank = k + 1 := by
      rw [rank_of_isUnit _ hUnit, Fintype.card_fin]
    have hle : (A.submatrix f g).rank ≤ A.rank := rank_submatrix_le A f g
    omega

/-- **Lower semicontinuity of rank.** The set of complex matrices of rank at most `k`
is closed in the topology of entrywise convergence. Equivalently, having rank greater
than `k` is an open condition. -/
theorem isClosed_setOf_rank_le (k : ℕ) :
    IsClosed {A : Matrix m n ℂ | A.rank ≤ k} := by
  classical
  rw [← isOpen_compl_iff]
  -- The complement is `{A | k < A.rank}`, which the minor characterization writes as a
  -- finite union of the open sets where a chosen `(k+1) × (k+1)` minor is nonsingular.
  have hcompl :
      {A : Matrix m n ℂ | A.rank ≤ k}ᶜ =
        ⋃ (f : Fin (k + 1) → m) (g : Fin (k + 1) → n),
          {A : Matrix m n ℂ | (A.submatrix f g).det ≠ 0} := by
    ext A
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, Set.mem_iUnion]
    rw [lt_rank_iff_exists_isUnit_submatrix]
    constructor
    · rintro ⟨f, g, _, _, hUnit⟩
      exact ⟨f, g, isUnit_iff_ne_zero.mp ((A.submatrix f g).isUnit_iff_isUnit_det.mp hUnit)⟩
    · rintro ⟨f, g, hdet⟩
      -- A nonsingular minor need not come from injective `f, g`, but if `f` or `g`
      -- collapses two indices the minor has a repeated row/column and zero determinant.
      have hf : Function.Injective f := by
        by_contra h
        obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp h
        exact hdet (det_zero_of_row_eq hne (by ext c; simp [Matrix.submatrix, hij]))
      have hg : Function.Injective g := by
        by_contra h
        obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp h
        exact hdet (det_zero_of_column_eq hne (fun r => by simp [Matrix.submatrix, hij]))
      exact ⟨f, g, hf, hg,
        (A.submatrix f g).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdet)⟩
  rw [hcompl]
  refine isOpen_iUnion fun f => isOpen_iUnion fun g => ?_
  -- `A ↦ (A.submatrix f g).det` is continuous and `{x | x ≠ 0}` is open.
  have hcont : Continuous fun A : Matrix m n ℂ => (A.submatrix f g).det :=
    (continuous_id.matrix_submatrix f g).matrix_det
  exact isOpen_ne.preimage hcont

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
