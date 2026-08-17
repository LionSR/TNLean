/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Interval.Finset.Nat
import TNLean.Analysis.ProjectionGeometry

/-!
# Finite-range Knabe inequality for cyclic families of projections

This file develops the Knabe open-to-periodic gap transfer for an abstract
one-dimensional cyclic family of symmetric projections with a finite
interaction range `R`.

Let `h i` be symmetric projections indexed by the cyclic group `ZMod N`, and
write `H = ∑ i, h i` for the total term.  For `m ≥ R`, let
`cyclicWindowSum h m s = ∑ q : Fin m, h (s + q)` be the sum of `m` consecutive
terms starting at `s`, and suppose every window satisfies the quadratic-form
gap `γ • Re ⟪A s v, v⟫ ≤ Re ⟪A s v, A s v⟫` uniformly in `s` and `v`.  If terms
at cyclic separation at least `R` commute pointwise, then for `N ≥ 2 * m` the
total term satisfies, as a quadratic form,

`δ * Re ⟪H v, v⟫ ≤ Re ⟪H v, H v⟫,  δ = (m * γ - (R - 1) ^ 2) / (m - R + 1),`

whenever the numerator `(R - 1) ^ 2 < m * γ` is positive.

For `R = 2` this recovers Knabe's nearest-neighbor coefficient
`(m * γ - 1) / (m - 1)`.

## Sources

The nearest-neighbor threshold `γ > 1 / m` goes back to Knabe, J. Stat. Phys.
52, 627 (1988) (`Knabe1988Energy`); the same criterion is stated in
Pérez-García et al., arXiv:quant-ph/0608197, lines 1483-1489, and in
Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:2011.12127, lines 2194-2197
(paragraph "The Knabe bound").  The finite-range coefficient above is a
TNLean derivation obtained by running Knabe's window argument with a general
range; it is recorded in the note
`docs/paper-gaps/knabe_finite_range_coefficient.tex`, is not stated in any of
the cited sources, and is not attributed to any of them.

## Main results

* `LinearMap.IsSymmetricProjection.re_inner_anticommutator_le`: the pairwise
  bound `P Q + Q P ≤ P + Q` for symmetric projections.
* `ProjectionGeometry.cyclicWindowSum_sq_sum_eq`: the cyclic double-counting
  identity `∑ s A s ^ 2 = m • H + ∑ e (m - e) • Q e`.
* `ProjectionGeometry.quadraticForm_sum_projections_of_cyclic_knabe`: the
  finite-range Knabe inequality.
* `ProjectionGeometry.quadraticForm_sum_projections_of_cyclic_knabe_nearest_neighbor`:
  the nearest-neighbor specialization `R = 2`.
-/

open scoped InnerProductSpace

namespace LinearMap.IsSymmetricProjection

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Pairwise anticommutator upper bound for two symmetric projections.

For symmetric projections `P` and `Q`, the positivity of `‖(P - Q) v‖²`
(equivalently, of the operator `(P - Q) ^ 2`) expands, using idempotence of
`P` and `Q`, into the anticommutator estimate `P Q + Q P ≤ P + Q` in
quadratic-form terms:

`Re ⟪P v, Q v⟫ + Re ⟪Q v, P v⟫ ≤ Re ⟪P v, v⟫ + Re ⟪Q v, v⟫.` -/
theorem re_inner_anticommutator_le {P Q : E →ₗ[𝕜] E} (hP : P.IsSymmetricProjection)
    (hQ : Q.IsSymmetricProjection) (v : E) :
    RCLike.re ⟪P v, Q v⟫_𝕜 + RCLike.re ⟪Q v, P v⟫_𝕜 ≤
      RCLike.re ⟪P v, v⟫_𝕜 + RCLike.re ⟪Q v, v⟫_𝕜 := by
  have h0 : (0 : ℝ) ≤ RCLike.re ⟪P v - Q v, P v - Q v⟫_𝕜 :=
    inner_self_nonneg (x := P v - Q v)
  rw [inner_sub_sub_self] at h0
  simp only [map_add, map_sub] at h0
  rw [hP.re_inner_apply_apply_self, hQ.re_inner_apply_apply_self] at h0
  linarith

end LinearMap.IsSymmetricProjection

namespace ProjectionGeometry

section CyclicSums

variable {M : Type*} [AddCommMonoid M] {N : ℕ} [NeZero N]

/-- Cyclic translation invariance: summing over the cyclic group `ZMod N`
commutes with right translation of the index. -/
theorem sum_comp_addRight (F : ZMod N → M) (d : ZMod N) :
    ∑ i, F (i + d) = ∑ i, F i := by
  simpa using Equiv.sum_comp (Equiv.addRight d) F

/-- Cyclic translation invariance: summing over the cyclic group `ZMod N`
commutes with left translation of the index. -/
theorem sum_comp_addLeft (F : ZMod N → M) (d : ZMod N) :
    ∑ i, F (d + i) = ∑ i, F i := by
  simpa using Equiv.sum_comp (Equiv.addLeft d) F

/-- Weighted triangular count, upper form.  Summing the offsets `e` with
`1 ≤ e < m - q` over all `q < m` counts each `e` with `1 ≤ e < m` exactly
`m - e` times. -/
theorem sum_range_Ico_triangular (F : ℕ → M) (m : ℕ) :
    (∑ q ∈ Finset.range m, ∑ e ∈ Finset.Ico 1 (m - q), F e) =
      ∑ e ∈ Finset.Ico 1 m, (m - e) • F e := by
  classical
  have hExtend : ∀ q ∈ Finset.range m,
      (∑ e ∈ Finset.Ico 1 (m - q), F e) =
        ∑ e ∈ Finset.Ico 1 m, (if e ∈ Finset.Ico 1 (m - q) then F e else 0) := by
    intro q _
    have hfil : (Finset.Ico 1 m).filter (fun e => e ∈ Finset.Ico 1 (m - q)) =
        Finset.Ico 1 (m - q) := by
      refine Finset.ext fun x => ?_
      simp only [Finset.mem_filter, Finset.mem_Ico]
      omega
    have h1 : (∑ e ∈ Finset.Ico 1 (m - q), F e) =
        ∑ e ∈ (Finset.Ico 1 m).filter (fun e => e ∈ Finset.Ico 1 (m - q)), F e := by
      rw [hfil]
    rw [h1, Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun q hq => hExtend q hq), Finset.sum_comm]
  refine Finset.sum_congr rfl fun e he => ?_
  have hem : 1 ≤ e ∧ e < m := Finset.mem_Ico.mp he
  have hCard : ∑ q ∈ Finset.range m, (if q ∈ Finset.range (m - e) then F e else 0) =
      (m - e) • F e := by
    have hfil : (Finset.range m).filter (fun q => q ∈ Finset.range (m - e)) =
        Finset.range (m - e) := by
      refine Finset.ext fun x => ?_
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [← Finset.sum_filter (s := Finset.range m), hfil, Finset.sum_const]
    congr 1
    simp
  rw [← hCard]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hqm : q < m := Finset.mem_range.mp hq
  by_cases h1 : e ∈ Finset.Ico 1 (m - q)
  · by_cases h2 : q ∈ Finset.range (m - e)
    · simp [h1, h2]
    · exfalso
      simp only [Finset.mem_Ico, Finset.mem_range] at h1 h2
      omega
  · by_cases h2 : q ∈ Finset.range (m - e)
    · exfalso
      simp only [Finset.mem_Ico, Finset.mem_range] at h1 h2
      omega
    · simp [h1, h2]

/-- Weighted triangular count, lower form.  Summing the offsets `e` with
`1 ≤ e ≤ q` over all `q < m` counts each `e` with `1 ≤ e < m` exactly
`m - e` times. -/
theorem sum_range_Ico_triangular_lower (F : ℕ → M) (m : ℕ) :
    (∑ q ∈ Finset.range m, ∑ e ∈ Finset.Ico 1 (q + 1), F e) =
      ∑ e ∈ Finset.Ico 1 m, (m - e) • F e := by
  classical
  have hExtend : ∀ q ∈ Finset.range m,
      (∑ e ∈ Finset.Ico 1 (q + 1), F e) =
        ∑ e ∈ Finset.Ico 1 m, (if e ∈ Finset.Ico 1 (q + 1) then F e else 0) := by
    intro q hq
    have hqm : q < m := Finset.mem_range.mp hq
    have hfil : (Finset.Ico 1 m).filter (fun e => e ∈ Finset.Ico 1 (q + 1)) =
        Finset.Ico 1 (q + 1) := by
      refine Finset.ext fun x => ?_
      simp only [Finset.mem_filter, Finset.mem_Ico]
      omega
    have h1 : (∑ e ∈ Finset.Ico 1 (q + 1), F e) =
        ∑ e ∈ (Finset.Ico 1 m).filter (fun e => e ∈ Finset.Ico 1 (q + 1)), F e := by
      rw [hfil]
    rw [h1, Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun q hq => hExtend q hq), Finset.sum_comm]
  refine Finset.sum_congr rfl fun e he => ?_
  have hem : 1 ≤ e ∧ e < m := Finset.mem_Ico.mp he
  have hCard : ∑ q ∈ Finset.range m, (if q ∈ Finset.Ico e m then F e else 0) =
      (m - e) • F e := by
    have hfil : (Finset.range m).filter (fun q => q ∈ Finset.Ico e m) =
        Finset.Ico e m := by
      refine Finset.ext fun x => ?_
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [← Finset.sum_filter (s := Finset.range m), hfil, Finset.sum_const]
    congr 1
    simp
  rw [← hCard]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hqm : q < m := Finset.mem_range.mp hq
  by_cases h1 : e ∈ Finset.Ico 1 (q + 1)
  · by_cases h2 : q ∈ Finset.Ico e m
    · simp [h1, h2]
    · exfalso
      simp only [Finset.mem_Ico] at h1 h2
      omega
  · by_cases h2 : q ∈ Finset.Ico e m
    · exfalso
      simp only [Finset.mem_Ico] at h1 h2
      omega
    · simp [h1, h2]

/-- Cyclic double counting for a square window of offsets.  For any function
`T` on pairs of cyclic sites, summing `T (s + q) (s + q')` over all starting
points `s` and all pairs of offsets `q, q' < m` produces the diagonal `T i i`
with multiplicity `m`, and each ordered pair `(i, i + e)` and `(i, i - e)` with
`1 ≤ e < m` with multiplicity `m - e`. -/
theorem sum_cyclic_window_eq (T : ZMod N → ZMod N → M) (m : ℕ) :
    (∑ s : ZMod N, ∑ q ∈ Finset.range m, ∑ q' ∈ Finset.range m,
        T (s + q) (s + q')) =
      m • ∑ i : ZMod N, T i i +
        ∑ e ∈ Finset.Ico 1 m, (m - e) •
          ∑ i : ZMod N, (T i (i + e) + T i (i - e)) := by
  classical
  -- Translate the sum over starting points for each fixed pair of offsets.
  have hStep1 : ∀ q ∈ Finset.range m, ∀ q' ∈ Finset.range m,
      (∑ s : ZMod N, T (s + q) (s + q')) = ∑ i : ZMod N, T i (i + (q' - q)) := by
    intro q _ q' _
    have harg : ∀ s : ZMod N, (s + q) + (q' - q) = s + q' := by
      intro s
      abel
    calc (∑ s : ZMod N, T (s + q) (s + q'))
        = ∑ s : ZMod N, T (s + q) ((s + q) + (q' - q)) :=
          Finset.sum_congr rfl fun s _ => by rw [harg s]
      _ = ∑ i : ZMod N, T i (i + (q' - q)) :=
          sum_comp_addRight (fun u => T u (u + (q' - q))) q
  -- Flatten the sum over starting points to the inside.
  have hFlat : (∑ s : ZMod N, ∑ q ∈ Finset.range m, ∑ q' ∈ Finset.range m,
      T (s + q) (s + q')) =
      ∑ i : ZMod N, ∑ q ∈ Finset.range m, ∑ q' ∈ Finset.range m,
        T i (i + (q' - q)) := by
    conv_rhs => rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q hq => ?_
    conv_rhs => rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q' hq' => hStep1 q hq q' hq'
  -- Split each offset square into the diagonal and the two triangles.
  have hSplit : ∀ i : ZMod N,
      (∑ q ∈ Finset.range m, ∑ q' ∈ Finset.range m, T i (i + (q' - q))) =
        (∑ q ∈ Finset.range m, T i i) +
          ((∑ q ∈ Finset.range m, ∑ e ∈ Finset.Ico 1 (m - q), T i (i + e)) +
            ∑ q ∈ Finset.range m, ∑ e ∈ Finset.Ico 1 (q + 1), T i (i - e)) := by
    intro i
    have hPer : ∀ q ∈ Finset.range m,
        (∑ q' ∈ Finset.range m, T i (i + (q' - q))) =
          T i i + ((∑ e ∈ Finset.Ico 1 (m - q), T i (i + e)) +
            ∑ e ∈ Finset.Ico 1 (q + 1), T i (i - e)) := by
      intro q hq
      have hqm : q < m := Finset.mem_range.mp hq
      have hRange : Finset.range m =
          Finset.Ico 0 q ∪ insert q (Finset.Ico (q + 1) m) := by
        have h1 : Finset.range m = Finset.Ico 0 m := Finset.range_eq_Ico m
        have h2 : Finset.Ico 0 m = Finset.Ico 0 q ∪ Finset.Ico q m :=
          (Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)).symm
        have h3 : Finset.Ico q m = insert q (Finset.Ico (q + 1) m) := by
          rw [← Finset.insert_erase (Finset.mem_Ico.mpr ⟨le_refl q, by omega⟩),
            ← Nat.Ico_succ_left_eq_erase_Ico]
        rw [h1, h2, h3]
      rw [hRange, Finset.sum_union (Finset.disjoint_iff_inter_eq_empty.mpr
        (Finset.eq_empty_iff_forall_notMem.mpr fun x hx => by
          simp only [Finset.mem_inter, Finset.mem_Ico, Finset.mem_insert] at hx
          omega)), Finset.sum_insert (by
        intro hxs
        simp only [Finset.mem_Ico] at hxs
        omega)]
      -- The strict lower triangle reindexes by the positive offset difference.
      have hFirst : (∑ q' ∈ Finset.Ico 0 q, T i (i + (q' - q))) =
          ∑ e ∈ Finset.Ico 1 (q + 1), T i (i - e) := by
        refine Finset.sum_nbij' (fun q' => q - q') (fun e => q - e) ?_ ?_ ?_ ?_ ?_
        · intro q' hq'
          simp only [Finset.mem_Ico] at hq' ⊢
          omega
        · intro e he
          simp only [Finset.mem_Ico] at he ⊢
          omega
        · intro q' hq'
          simp only [Finset.mem_Ico] at hq'
          omega
        · intro e he
          simp only [Finset.mem_Ico] at he
          omega
        · intro q' hq'
          have hq'q : q' ≤ q := by
            simp only [Finset.mem_Ico] at hq'
            omega
          have hcast : ((q' : ZMod N) - q) = -((q - q' : ℕ) : ZMod N) := by
            have hsub : (((q - q' : ℕ) : ZMod N)) + (q' : ZMod N) = (q : ZMod N) := by
              rw [← Nat.cast_add, Nat.sub_add_cancel hq'q]
            linear_combination (norm := module) hsub
          change T i (i + (↑q' - ↑q)) = T i (i - ↑(q - q'))
          congr 1
          rw [hcast]
          abel
      -- The strict upper triangle reindexes by the positive offset difference.
      have hThird : (∑ q' ∈ Finset.Ico (q + 1) m, T i (i + (q' - q))) =
          ∑ e ∈ Finset.Ico 1 (m - q), T i (i + e) := by
        refine Finset.sum_nbij' (fun q' => q' - q) (fun e => q + e) ?_ ?_ ?_ ?_ ?_
        · intro q' hq'
          simp only [Finset.mem_Ico] at hq' ⊢
          omega
        · intro e he
          simp only [Finset.mem_Ico] at he ⊢
          omega
        · intro q' hq'
          simp only [Finset.mem_Ico] at hq'
          omega
        · intro e he
          simp only [Finset.mem_Ico] at he
          omega
        · intro q' hq'
          have hq'q : q < q' := by
            simp only [Finset.mem_Ico] at hq'
            omega
          change T i (i + (↑q' - ↑q)) = T i (i + ↑(q' - q))
          rw [Nat.cast_sub hq'q.le]
      rw [hFirst, hThird, sub_self, add_zero]
      ac_rfl
    rw [Finset.sum_congr rfl hPer, Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- Assemble: diagonal, then the two weighted triangles.
  rw [hFlat, Finset.sum_congr rfl fun i _ => hSplit i, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  have hDiag : (∑ i : ZMod N, ∑ q ∈ Finset.range m, T i i) = m • ∑ i : ZMod N, T i i := by
    rw [Finset.sum_comm]
    simp
  rw [hDiag]
  have hUpper : (∑ i : ZMod N, ∑ q ∈ Finset.range m, ∑ e ∈ Finset.Ico 1 (m - q),
      T i (i + e)) = ∑ e ∈ Finset.Ico 1 m, (m - e) • ∑ i : ZMod N, T i (i + e) := by
    rw [Finset.sum_congr rfl fun i _ => sum_range_Ico_triangular (fun e => T i (i + e)) m,
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun e _ => (Finset.smul_sum).symm
  have hLower : (∑ i : ZMod N, ∑ q ∈ Finset.range m, ∑ e ∈ Finset.Ico 1 (q + 1),
      T i (i - e)) = ∑ e ∈ Finset.Ico 1 m, (m - e) • ∑ i : ZMod N, T i (i - e) := by
    rw [Finset.sum_congr rfl fun i _ =>
      sum_range_Ico_triangular_lower (fun e => T i (i - e)) m, Finset.sum_comm]
    exact Finset.sum_congr rfl fun e _ => (Finset.smul_sum).symm
  have hComb : (∑ e ∈ Finset.Ico 1 m, (m - e) •
        ∑ i : ZMod N, (T i (i + e) + T i (i - e))) =
      (∑ e ∈ Finset.Ico 1 m, (m - e) • ∑ i : ZMod N, T i (i + e)) +
        (∑ e ∈ Finset.Ico 1 m, (m - e) • ∑ i : ZMod N, T i (i - e)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => by rw [Finset.sum_add_distrib, smul_add]
  rw [hUpper, hLower, ← hComb]

/-- Partition of the nonzero cyclic offsets into short offsets `1 ≤ e < m`,
the reflection `N - e` of each short offset, and middle offsets
`m ≤ k ≤ N - m`.  The partition requires `1 ≤ m ≤ N / 2`, so that the middle
interval is well placed and short offsets and their reflections are distinct. -/
theorem sum_offset_partition (F : ZMod N → M) {m : ℕ} (hm1 : 1 ≤ m) (hm : 2 * m ≤ N) :
    (∑ u ∈ (Finset.univ.erase 0 : Finset (ZMod N)), F u) =
      (∑ e ∈ Finset.Ico 1 m, (F e + F ((N - e : ℕ) : ZMod N))) +
        ∑ k ∈ Finset.Ico m (N - m + 1), F k := by
  classical
  -- Index the nonzero cyclic offsets by the integer interval `1 ≤ k < N`.
  have hBij : (∑ u ∈ Finset.univ.erase (0 : ZMod N), F u) =
      ∑ k ∈ Finset.Ico 1 N, F k := by
    refine Finset.sum_nbij' (fun u => u.val) (fun k => (k : ZMod N)) ?_ ?_ ?_ ?_ ?_
    · intro u hu
      have hu0 : u ≠ 0 := by simpa using hu
      have hlt : u.val < N := ZMod.val_lt u
      have hne : u.val ≠ 0 := fun h0 => hu0 (by
        rw [← ZMod.natCast_zmod_val u, h0]
        simp)
      simp only [Finset.mem_Ico]
      omega
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      have hkne : (k : ZMod N) ≠ 0 := by
        intro h0
        have hkmod : k % N = 0 := by
          rw [← ZMod.val_natCast N k, h0]
          simp
        rw [Nat.mod_eq_of_lt (by omega)] at hkmod
        omega
      exact Finset.mem_erase.2 ⟨hkne, Finset.mem_univ _⟩
    · intro u _
      exact ZMod.natCast_zmod_val u
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      have hkN : ((k : ZMod N)).val = k % N := ZMod.val_natCast N k
      rw [hkN, Nat.mod_eq_of_lt (by omega)]
    · intro u _
      rw [ZMod.natCast_zmod_val]
  rw [hBij]
  -- Split the interval `1 ≤ k < N` into short, middle, and long offsets.
  have hUnion : (Finset.Ico 1 m ∪ Finset.Ico m (N - m + 1)) ∪ Finset.Ico (N - m + 1) N =
      Finset.Ico 1 N := by
    have hU1 : Finset.Ico 1 m ∪ Finset.Ico m (N - m + 1) = Finset.Ico 1 (N - m + 1) :=
      Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)
    have hU2 : Finset.Ico 1 (N - m + 1) ∪ Finset.Ico (N - m + 1) N = Finset.Ico 1 N :=
      Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)
    rw [hU1, hU2]
  have hDisj1 : Disjoint (Finset.Ico 1 m) (Finset.Ico m (N - m + 1)) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    refine Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    simp only [Finset.mem_inter, Finset.mem_Ico] at hx
    omega
  have hDisj2 : Disjoint (Finset.Ico 1 m ∪ Finset.Ico m (N - m + 1))
      (Finset.Ico (N - m + 1) N) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    refine Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_Ico] at hx
    omega
  -- Reflect the long offsets `N - m + 1 ≤ k < N` back to short offsets.
  have hLong : (∑ k ∈ Finset.Ico (N - m + 1) N, F k) =
      ∑ e ∈ Finset.Ico 1 m, F ((N - e : ℕ) : ZMod N) := by
    refine Finset.sum_nbij' (fun k => N - k) (fun e => N - e) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_Ico] at hk ⊢
      omega
    · intro e he
      simp only [Finset.mem_Ico] at he ⊢
      omega
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      omega
    · intro e he
      simp only [Finset.mem_Ico] at he
      omega
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      have hkN : N - (N - k) = k := by omega
      simp only [hkN]
  rw [← hUnion, Finset.sum_union hDisj2, Finset.sum_union hDisj1, hLong,
    Finset.sum_add_distrib]
  ac_rfl

end CyclicSums



section CyclicFamily

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {N : ℕ} [NeZero N]

/-- The sum of `m` consecutive terms of a cyclic family, starting at `s`. -/
def cyclicWindowSum (h : ZMod N → E →ₗ[𝕜] E) (m : ℕ) (s : ZMod N) : E →ₗ[𝕜] E :=
  ∑ q : Fin m, h (s + (q : ℕ))

/-- The operator cross terms of a cyclic family at offset `e`. -/
def cyclicCrossTerms (h : ZMod N → E →ₗ[𝕜] E) (e : ℕ) : E →ₗ[𝕜] E :=
  ∑ i : ZMod N, (h i * h (i + e) + h i * h (i - e))

/-- Cyclic expansion of the sum of squared windows. If `H = ∑ i, h i` and
`Q e = cyclicCrossTerms h e`, then
`∑ s, (cyclicWindowSum h m s) ^ 2 = m • H + ∑ e, (m - e) • Q e`. -/
theorem cyclicWindowSum_sq_sum_eq (h : ZMod N → E →ₗ[𝕜] E)
    (hh : ∀ i, (h i).IsSymmetricProjection) (m : ℕ) :
    (∑ s : ZMod N, cyclicWindowSum h m s * cyclicWindowSum h m s) =
      m • ∑ i : ZMod N, h i +
        ∑ e ∈ Finset.Ico 1 m, (m - e) • cyclicCrossTerms h e := by
  classical
  have hWindow : ∀ s : ZMod N, cyclicWindowSum h m s =
      ∑ q ∈ Finset.range m, h (s + q) := by
    intro s
    rw [cyclicWindowSum]
    exact Fin.sum_univ_eq_sum_range (fun q : ℕ => h (s + (q : ZMod N))) m
  have hDiag : ∀ i : ZMod N, h i * h i = h i := by
    intro i
    ext v
    exact LinearMap.IsIdempotentElem.apply_apply (hh i).isIdempotentElem v
  calc
    (∑ s : ZMod N, cyclicWindowSum h m s * cyclicWindowSum h m s) =
        ∑ s : ZMod N, ∑ q ∈ Finset.range m, ∑ q' ∈ Finset.range m,
          h (s + q) * h (s + q') := by
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hWindow s, Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.mul_sum]
    _ = m • ∑ i : ZMod N, h i * h i +
        ∑ e ∈ Finset.Ico 1 m, (m - e) •
          ∑ i : ZMod N, (h i * h (i + e) + h i * h (i - e)) :=
      sum_cyclic_window_eq (fun i j => h i * h j) m
    _ = m • ∑ i : ZMod N, h i +
        ∑ e ∈ Finset.Ico 1 m, (m - e) • cyclicCrossTerms h e := by
      rw [Finset.sum_congr rfl fun i _ => hDiag i]
      rfl

/-- The ordered real cross terms of a cyclic family at offset `e`: the sum over
all sites of the two ordered quadratic forms of the pairs at cyclic offsets
`e` and `-e`. -/
def re_inner_cyclicCrossTerms (h : ZMod N → E →ₗ[𝕜] E) (e : ℕ) (v : E) : ℝ :=
  ∑ i : ZMod N, (RCLike.re ⟪h i v, h (i + e) v⟫_𝕜 + RCLike.re ⟪h i v, h (i - e) v⟫_𝕜)

/-- The cyclic double-counting identity for a family of symmetric projections:
summing the quadratic form of every window of `m` consecutive terms produces
the diagonal with multiplicity `m` and each offset pair of cross terms with
multiplicity `m - e`. -/
theorem re_inner_cyclicWindowSum_sum_eq (h : ZMod N → E →ₗ[𝕜] E)
    (hh : ∀ i, (h i).IsSymmetricProjection) (m : ℕ) (v : E) :
    (∑ s : ZMod N, RCLike.re ⟪cyclicWindowSum h m s v, cyclicWindowSum h m s v⟫_𝕜) =
      m * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 +
        ∑ e ∈ Finset.Ico 1 m, (m - e) * re_inner_cyclicCrossTerms h e v := by
  classical
  have hExpand : ∀ s : ZMod N,
      RCLike.re ⟪cyclicWindowSum h m s v, cyclicWindowSum h m s v⟫_𝕜 =
        ∑ q ∈ Finset.range m, ∑ q' ∈ Finset.range m,
          RCLike.re ⟪h (s + q) v, h (s + q') v⟫_𝕜 := by
    intro s
    rw [cyclicWindowSum, re_inner_sum_apply_apply,
      Fin.sum_univ_eq_sum_range
        (fun k : ℕ => ∑ q' : Fin m,
          RCLike.re ⟪h (s + (k : ZMod N)) v, h (s + ((q' : ℕ) : ZMod N)) v⟫_𝕜) m]
    refine Finset.sum_congr rfl fun q _ => ?_
    exact Fin.sum_univ_eq_sum_range
      (fun k' : ℕ => RCLike.re ⟪h (s + (q : ZMod N)) v, h (s + (k' : ZMod N)) v⟫_𝕜) m
  set T : ZMod N → ZMod N → ℝ := fun i j => RCLike.re ⟪h i v, h j v⟫_𝕜 with hT
  have hDiag : (∑ i : ZMod N, T i i) = RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 := by
    rw [hT]
    simp only []
    rw [re_inner_sum_apply_left h v]
    exact Finset.sum_congr rfl fun i _ => (hh i).re_inner_apply_apply_self v
  calc (∑ s : ZMod N, RCLike.re ⟪cyclicWindowSum h m s v, cyclicWindowSum h m s v⟫_𝕜)
      = ∑ s : ZMod N, ∑ q ∈ Finset.range m, ∑ q' ∈ Finset.range m,
          T (s + q) (s + q') :=
        Finset.sum_congr rfl fun s _ => hExpand s
    _ = m • ∑ i : ZMod N, T i i +
        ∑ e ∈ Finset.Ico 1 m, (m - e) • ∑ i : ZMod N, (T i (i + e) + T i (i - e)) :=
        sum_cyclic_window_eq T m
    _ = m * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 +
        ∑ e ∈ Finset.Ico 1 m, (m - e) * re_inner_cyclicCrossTerms h e v := by
        rw [hDiag, nsmul_eq_mul]
        have hsmulB : ∀ e ∈ Finset.Ico 1 m,
            ((m - e : ℕ) • (∑ i : ZMod N, (T i (i + e) + T i (i - e)))) =
              ((m : ℝ) - (e : ℝ)) * re_inner_cyclicCrossTerms h e v := by
          intro e he
          simp only [Finset.mem_Ico] at he
          rw [nsmul_eq_mul, Nat.cast_sub (by omega)]
          rfl
        refine congrArg _ ?_
        exact Finset.sum_congr rfl hsmulB

/-- Summing the quadratic forms of all windows counts every site `m` times. -/
theorem re_inner_cyclicWindowSum_sum_apply (h : ZMod N → E →ₗ[𝕜] E) (m : ℕ) (v : E) :
    (∑ s : ZMod N, RCLike.re ⟪cyclicWindowSum h m s v, v⟫_𝕜) =
      m * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 := by
  classical
  have hExpand : ∀ s : ZMod N,
      RCLike.re ⟪cyclicWindowSum h m s v, v⟫_𝕜 =
        ∑ q : Fin m, RCLike.re ⟪h (s + (q : ℕ)) v, v⟫_𝕜 := by
    intro s
    simp only [cyclicWindowSum, re_inner_sum_apply_left]
  have h1 : (∑ s : ZMod N, RCLike.re ⟪cyclicWindowSum h m s v, v⟫_𝕜) =
      ∑ s : ZMod N, ∑ q : Fin m, RCLike.re ⟪h (s + (q : ℕ)) v, v⟫_𝕜 :=
    Finset.sum_congr rfl fun s _ => hExpand s
  have hswap : (∑ s : ZMod N, ∑ q : Fin m, RCLike.re ⟪h (s + (q : ℕ)) v, v⟫_𝕜) =
      ∑ q : Fin m, ∑ s : ZMod N, RCLike.re ⟪h (s + (q : ℕ)) v, v⟫_𝕜 := Finset.sum_comm
  rw [h1, hswap]
  have hTrans : ∀ q : Fin m, (∑ s : ZMod N, RCLike.re ⟪h (s + (q : ℕ)) v, v⟫_𝕜) =
      RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 := by
    intro q
    have hTra := sum_comp_addRight (M := ℝ)
      (fun u : ZMod N => RCLike.re ⟪h u v, v⟫_𝕜) ((q : ℕ) : ZMod N)
    rw [hTra]
    exact (re_inner_sum_apply_left h v).symm
  rw [Finset.sum_congr rfl fun q _ => hTrans q]
  simp

/-- The pairwise anticommutator bound, summed over the ring: the cross terms at
any offset are bounded by twice the total quadratic form. -/
theorem re_inner_cyclicCrossTerms_le_two (h : ZMod N → E →ₗ[𝕜] E)
    (hh : ∀ i, (h i).IsSymmetricProjection) (e : ℕ) (v : E) :
    re_inner_cyclicCrossTerms h e v ≤ 2 * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 := by
  classical
  have hPair : ∀ i : ZMod N,
      RCLike.re ⟪h i v, h (i + e) v⟫_𝕜 + RCLike.re ⟪h (i + e) v, h i v⟫_𝕜 ≤
        RCLike.re ⟪h i v, v⟫_𝕜 + RCLike.re ⟪h (i + e) v, v⟫_𝕜 :=
    fun i => LinearMap.IsSymmetricProjection.re_inner_anticommutator_le (hh i)
      (hh (i + e)) v
  -- The reversed ordered pair is a translate of the pair at offset `-e`.
  have hTrans : (∑ i : ZMod N, RCLike.re ⟪h (i + e) v, h i v⟫_𝕜) =
      ∑ i : ZMod N, RCLike.re ⟪h i v, h (i - e) v⟫_𝕜 := by
    refine Fintype.sum_equiv (Equiv.addRight ((e : ZMod N))) _ _ fun i => ?_
    change RCLike.re ⟪h (i + e) v, h i v⟫_𝕜 = RCLike.re ⟪h (i + e) v, h ((i + e) - e) v⟫_𝕜
    abel_nf
  have hDiag : (∑ i : ZMod N, RCLike.re ⟪h (i + e) v, v⟫_𝕜) =
      ∑ i : ZMod N, RCLike.re ⟪h i v, v⟫_𝕜 :=
    sum_comp_addRight (fun u : ZMod N => RCLike.re ⟪h u v, v⟫_𝕜) _
  have hSplit : re_inner_cyclicCrossTerms h e v =
      (∑ i : ZMod N, (RCLike.re ⟪h i v, h (i + e) v⟫_𝕜 +
        RCLike.re ⟪h (i + e) v, h i v⟫_𝕜)) := by
    unfold re_inner_cyclicCrossTerms
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hTrans]
  calc re_inner_cyclicCrossTerms h e v
      = (∑ i : ZMod N, (RCLike.re ⟪h i v, h (i + e) v⟫_𝕜 +
        RCLike.re ⟪h (i + e) v, h i v⟫_𝕜)) := hSplit
    _ ≤ (∑ i : ZMod N, (RCLike.re ⟪h i v, v⟫_𝕜 +
        RCLike.re ⟪h (i + e) v, v⟫_𝕜)) :=
        Finset.sum_le_sum fun i _ => hPair i
    _ = (∑ i : ZMod N, RCLike.re ⟪h i v, v⟫_𝕜) +
        ∑ i : ZMod N, RCLike.re ⟪h (i + e) v, v⟫_𝕜 :=
        Finset.sum_add_distrib
    _ = 2 * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 := by
        rw [hDiag, ← Finset.sum_add_distrib, re_inner_sum_apply_left h v, two_mul,
          ← Finset.sum_add_distrib]

/-- Terms at cyclic separation at least `R` commute pointwise; commuting
symmetric projections have nonnegative ordered cross terms, so both legs of the
cross terms at an offset between `R` and `N - R` are nonnegative. -/
theorem re_inner_cyclicCrossTerms_nonneg (h : ZMod N → E →ₗ[𝕜] E)
    (hh : ∀ i, (h i).IsSymmetricProjection) {R : ℕ}
    (hcomm : ∀ d : ℕ, R ≤ d → d + R ≤ N → ∀ i : ZMod N, ∀ v : E,
      h i (h ((i + (d : ZMod N))) v) = h ((i + (d : ZMod N))) (h i v))
    {e : ℕ} (he1 : R ≤ e) (he2 : e + R ≤ N) (v : E) :
    0 ≤ re_inner_cyclicCrossTerms h e v := by
  have h1 : ∀ i : ZMod N, 0 ≤ RCLike.re ⟪h i v, h (i + e) v⟫_𝕜 :=
    fun i => LinearMap.IsSymmetricProjection.re_inner_apply_apply_nonneg_of_commute
      (hh i) (hh (i + e)) (hcomm e he1 he2 i) v
  have h2 : ∀ i : ZMod N, 0 ≤ RCLike.re ⟪h i v, h (i - e) v⟫_𝕜 := by
    intro i
    have hshift : (i - (e : ZMod N)) = (i + ((N - e : ℕ) : ZMod N)) := by
      have hzero : (((e : ZMod N)) + ((N - e : ℕ) : ZMod N)) = 0 := by
        have hsum : e + (N - e) = N := by omega
        rw [← Nat.cast_add, hsum, ZMod.natCast_self]
      have hneg : ((N - e : ℕ) : ZMod N) = -((e : ZMod N)) :=
        eq_neg_of_add_eq_zero_right hzero
      rw [sub_eq_add_neg, hneg]
    rw [hshift]
    exact LinearMap.IsSymmetricProjection.re_inner_apply_apply_nonneg_of_commute
      (hh i) (hh (i + ((N - e : ℕ) : ZMod N))) (hcomm (N - e) (by omega) (by omega) i) v
  exact Finset.sum_nonneg fun i _ => add_nonneg (h1 i) (h2 i)

/-- The diagonal-plus-cross-terms lower bound on the total square.  Expanding
`Re ⟪H v, H v⟫` over ordered pairs and grouping by cyclic offset, the offsets
between `m` and `N - m` carry nonnegative cross terms (they are at separation
at least `R`), so the total square dominates the diagonal plus the short cross
terms. -/
theorem re_inner_sum_two_ge_sum_cyclicCrossTerms (h : ZMod N → E →ₗ[𝕜] E)
    (hh : ∀ i, (h i).IsSymmetricProjection) {R m : ℕ}
    (hm1 : 1 ≤ m) (hN : 2 * m ≤ N) (hRm : R ≤ m)
    (hcomm : ∀ d : ℕ, R ≤ d → d + R ≤ N → ∀ i : ZMod N, ∀ v : E,
      h i (h ((i + (d : ZMod N))) v) = h ((i + (d : ZMod N))) (h i v))
    (v : E) :
    RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 + ∑ e ∈ Finset.Ico 1 m, re_inner_cyclicCrossTerms h e v ≤
      RCLike.re ⟪(∑ i, h i) v, (∑ i, h i) v⟫_𝕜 := by
  classical
  set T : ZMod N → ZMod N → ℝ := fun i j => RCLike.re ⟪h i v, h j v⟫_𝕜 with hT
  -- Expand over ordered pairs and translate the second site.
  have hInner : ∀ i : ZMod N, (∑ j : ZMod N, T i j) = ∑ u : ZMod N, T i (i + u) := by
    intro i
    exact (Equiv.sum_comp (Equiv.addLeft i) (T i)).symm
  -- Split off the zero offset.
  have hSplit0 : ∀ i : ZMod N, (∑ u : ZMod N, T i (i + u)) = T i i +
      ∑ u ∈ (Finset.univ.erase 0 : Finset (ZMod N)), T i (i + u) := by
    intro i
    have hEq : (∑ u : ZMod N, T i (i + u)) =
        T i (i + 0) + ∑ u ∈ (Finset.univ.erase 0 : Finset (ZMod N)), T i (i + u) := by
      have hU : (Finset.univ : Finset (ZMod N)) =
          insert (0 : ZMod N) (Finset.univ.erase (0 : ZMod N)) :=
        (Finset.insert_erase (Finset.mem_univ 0)).symm
      calc (∑ u : ZMod N, T i (i + u))
          = (∑ u ∈ insert (0 : ZMod N) (Finset.univ.erase (0 : ZMod N)), T i (i + u)) := by
            rw [← hU]
        _ = T i (i + 0) + ∑ u ∈ Finset.univ.erase (0 : ZMod N), T i (i + u) :=
            Finset.sum_insert (by simp)
    rw [hEq, add_zero]
  -- Partition the nonzero offsets.
  set F : ZMod N → ℝ := fun u => ∑ i : ZMod N, T i (i + u) with hF
  have hPart := sum_offset_partition F hm1 hN
  -- The middle offsets carry nonnegative cross terms.
  have hMidNonneg : 0 ≤ ∑ k ∈ Finset.Ico m (N - m + 1), F k := by
    refine Finset.sum_nonneg fun k hk => Finset.sum_nonneg fun i _ => ?_
    simp only [Finset.mem_Ico] at hk
    exact LinearMap.IsSymmetricProjection.re_inner_apply_apply_nonneg_of_commute
      (hh i) (hh (i + k)) (hcomm k (by omega) (by omega) i) v
  -- The reflected short offsets reproduce the second leg of the cross terms.
  have hCross : ∀ e ∈ Finset.Ico 1 m,
      F ((e : ZMod N)) + F ((N - e : ℕ) : ZMod N) =
        re_inner_cyclicCrossTerms h e v := by
    intro e he
    simp only [Finset.mem_Ico] at he
    have hshift : (∑ i : ZMod N, T i (i + ((N - e : ℕ) : ZMod N))) =
        ∑ i : ZMod N, T i (i - e) := by
      have hneg : ((N - e : ℕ) : ZMod N) = -((e : ZMod N)) := by
        have hzero : (((e : ZMod N)) + ((N - e : ℕ) : ZMod N)) = 0 := by
          have hsum : e + (N - e) = N := by omega
          rw [← Nat.cast_add, hsum, ZMod.natCast_self]
        exact eq_neg_of_add_eq_zero_right hzero
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hneg, sub_eq_add_neg]
    change (∑ i : ZMod N, T i (i + ((e : ZMod N)))) +
        (∑ i : ZMod N, T i (i + ((N - e : ℕ) : ZMod N))) = _
    rw [hshift, ← Finset.sum_add_distrib]
    rfl
  calc RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 + ∑ e ∈ Finset.Ico 1 m, re_inner_cyclicCrossTerms h e v
      = (∑ i : ZMod N, T i i) + (∑ e ∈ Finset.Ico 1 m, re_inner_cyclicCrossTerms h e v) := by
        rw [re_inner_sum_apply_left h v]
        congr 1
        exact Finset.sum_congr rfl fun i _ => ((hh i).re_inner_apply_apply_self v).symm
    _ ≤ (∑ i : ZMod N, T i i) +
        (∑ e ∈ Finset.Ico 1 m, re_inner_cyclicCrossTerms h e v +
          ∑ k ∈ Finset.Ico m (N - m + 1), F k) := by
        have hle := hMidNonneg
        linarith
    _ = RCLike.re ⟪(∑ i, h i) v, (∑ i, h i) v⟫_𝕜 := by
        have hCrossSum : (∑ e ∈ Finset.Ico 1 m, re_inner_cyclicCrossTerms h e v) =
            (∑ e ∈ Finset.Ico 1 m, (F ((e : ZMod N)) + F ((N - e : ℕ) : ZMod N))) :=
          Finset.sum_congr rfl fun e he => (hCross e he).symm
        have hswap2 : (∑ u ∈ (Finset.univ.erase 0 : Finset (ZMod N)),
            ∑ i : ZMod N, T i (i + u)) =
            (∑ i : ZMod N, ∑ u ∈ (Finset.univ.erase 0 : Finset (ZMod N)), T i (i + u)) :=
          Finset.sum_comm
        rw [re_inner_sum_apply_apply h v,
          Finset.sum_congr rfl fun i _ => hInner i,
          Finset.sum_congr rfl fun i _ => hSplit0 i, Finset.sum_add_distrib, hCrossSum,
          ← hPart, hswap2]


/-- **Finite-range cyclic Knabe inequality.**

Let `h i` be symmetric projections on a Hilbert space, indexed by the cyclic
group `ZMod N`, such that terms at cyclic separation at least `R` commute
pointwise (cyclic separation at least `R` means the offset `d` satisfies
`R ≤ d ≤ N - R`).  Let `A s = cyclicWindowSum h m s` be the sums of `m`
consecutive terms with `R ≤ m` and `2 * m ≤ N`, and suppose every window has
the quadratic-form gap `γ * Re ⟪A s v, v⟫ ≤ Re ⟪A s v, A s v⟫` uniformly.
Writing `H = ∑ i, h i`, the total term satisfies the quadratic-form gap

`δ * Re ⟪H v, v⟫ ≤ Re ⟪H v, H v⟫,  δ = (m * γ - (R - 1) ^ 2) / (m - R + 1),`

whenever the numerator is positive, `(R - 1) ^ 2 < m * γ`.  For `R = 2` this
is Knabe's nearest-neighbor coefficient `(m * γ - 1) / (m - 1)`.

The nearest-neighbor threshold `γ > 1 / m` goes back to Knabe, J. Stat. Phys.
52, 627 (1988); it is stated in this form in Pérez-García et al.,
arXiv:quant-ph/0608197, lines 1483-1489, and Cirac--Perez-Garcia--Schuch--
Verstraete, arXiv:2011.12127, lines 2194-2197.  The finite-range coefficient
is a TNLean derivation obtained by running Knabe's window argument with a
general range; see the paper-gap note
`docs/paper-gaps/knabe_finite_range_coefficient.tex`. -/
theorem quadraticForm_sum_projections_of_cyclic_knabe
    {N R m : ℕ} [NeZero N]
    (h : ZMod N → E →ₗ[𝕜] E) (hh : ∀ i, (h i).IsSymmetricProjection)
    (hN : 2 * m ≤ N) (hR : 1 ≤ R) (hmR : R ≤ m)
    (hcomm : ∀ d : ℕ, R ≤ d → d + R ≤ N → ∀ i : ZMod N, ∀ v : E,
      h i (h ((i + (d : ZMod N))) v) = h ((i + (d : ZMod N))) (h i v))
    {γ δ : ℝ} (hδ : δ = (m * γ - (R - 1) ^ 2) / (m - R + 1))
    (hnum : (R - 1) ^ 2 < m * γ)
    (hgap : ∀ s : ZMod N, ∀ v : E,
      γ * RCLike.re ⟪cyclicWindowSum h m s v, v⟫_𝕜 ≤
        RCLike.re ⟪cyclicWindowSum h m s v, cyclicWindowSum h m s v⟫_𝕜)
    (v : E) :
    δ * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 ≤
      RCLike.re ⟪(∑ i, h i) v, (∑ i, h i) v⟫_𝕜 := by
  classical
  have hm1 : 1 ≤ m := le_trans hR hmR
  -- The summed window gap.
  have hi : m * γ * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 ≤
      ∑ s : ZMod N, RCLike.re ⟪cyclicWindowSum h m s v, cyclicWindowSum h m s v⟫_𝕜 := by
    have hSumForm : (∑ s : ZMod N, RCLike.re ⟪cyclicWindowSum h m s v, v⟫_𝕜) =
        m * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 := re_inner_cyclicWindowSum_sum_apply h m v
    calc m * γ * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜
        = γ * (∑ s : ZMod N, RCLike.re ⟪cyclicWindowSum h m s v, v⟫_𝕜) := by
          rw [hSumForm]
          ring
      _ ≤ ∑ s : ZMod N, RCLike.re ⟪cyclicWindowSum h m s v, cyclicWindowSum h m s v⟫_𝕜 := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun s _ => hgap s v
  -- The cyclic expansion.
  have hii := re_inner_cyclicWindowSum_sum_eq h hh m v
  -- The pairwise bound, summed over the ring.
  have hiii : ∀ e ∈ Finset.Ico 1 m, re_inner_cyclicCrossTerms h e v ≤
      2 * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 :=
    fun e _ => re_inner_cyclicCrossTerms_le_two h hh e v
  -- Nonnegative cross terms at separated offsets.
  have hiv : ∀ e ∈ Finset.Ico R m, 0 ≤ re_inner_cyclicCrossTerms h e v := by
    intro e he
    simp only [Finset.mem_Ico] at he
    have he2 : e + R ≤ N := by omega
    exact re_inner_cyclicCrossTerms_nonneg h hh hcomm he.1 he2 v
  -- The diagonal-plus-cross lower bound on the total square.
  have hv := re_inner_sum_two_ge_sum_cyclicCrossTerms h hh hm1 hN hmR hcomm v
  -- The sum of the short-offset weights.
  have hvi : 2 * (∑ e ∈ Finset.Ico 1 R, ((R : ℝ) - 1 - e)) = ((R : ℝ) - 1) * ((R : ℝ) - 2) := by
    have hnbij : (∑ e ∈ Finset.Ico 1 R, ((R : ℝ) - 1 - e)) =
        ∑ d ∈ Finset.range (R - 1), ((d : ℕ) : ℝ) := by
      refine Finset.sum_nbij' (fun e => R - 1 - e) (fun d => R - 1 - d) ?_ ?_ ?_ ?_ ?_
      · intro e he
        simp only [Finset.mem_Ico, Finset.mem_range] at he ⊢
        omega
      · intro d hd
        simp only [Finset.mem_Ico, Finset.mem_range] at hd ⊢
        omega
      · intro e he
        simp only [Finset.mem_Ico] at he
        omega
      · intro d hd
        simp only [Finset.mem_range] at hd
        omega
      · intro e he
        have heR : e ≤ R - 1 := by
          simp only [Finset.mem_Ico] at he
          omega
        change ((R : ℝ) - 1 - e) = ((R - 1 - e : ℕ) : ℝ)
        rw [Nat.cast_sub heR, Nat.cast_sub (by omega : 1 ≤ R)]
        norm_num
    have hTwo : ∀ n : ℕ, 2 * (∑ d ∈ Finset.range n, ((d : ℕ) : ℝ)) =
        ((n : ℝ) * (((n : ℝ) - 1))) := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih =>
          rw [Finset.sum_range_succ]
          push_cast
          nlinarith
    rw [hnbij, hTwo (R - 1), Nat.cast_sub hR]
    push_cast
    ring
  -- Assemble the upper bound on the summed window squares.
  have hc : (0 : ℝ) < ((m - R + 1 : ℕ) : ℝ) := by
    have h1 : 0 < m - R + 1 := by omega
    exact_mod_cast h1
  have hSplit : (∑ e ∈ Finset.Ico 1 m, ((m : ℝ) - e) * re_inner_cyclicCrossTerms h e v) =
      (((m - R + 1 : ℕ) : ℝ) * (∑ e ∈ Finset.Ico 1 m, re_inner_cyclicCrossTerms h e v) +
        ∑ e ∈ Finset.Ico 1 m, (((R : ℝ) - 1 - e) * re_inner_cyclicCrossTerms h e v)) := by
    have hCoeff : ∀ e ∈ Finset.Ico 1 m,
        (((m : ℝ) - e) * re_inner_cyclicCrossTerms h e v) =
          (((m - R + 1 : ℕ) : ℝ) * re_inner_cyclicCrossTerms h e v +
            (((R : ℝ) - 1 - e) * re_inner_cyclicCrossTerms h e v)) := by
      intro e he
      simp only [Finset.mem_Ico] at he
      have hc2 : ((m - R + 1 : ℕ) : ℝ) = (m : ℝ) - (R : ℝ) + 1 := by
        have h1 : (m - R + 1 : ℕ) = (m - R : ℕ) + 1 := by omega
        rw [h1, Nat.cast_add, Nat.cast_sub hmR]
        push_cast
        ring
      have hEq : ((m : ℝ) - e) =
          ((m - R + 1 : ℕ) : ℝ) + (((R : ℝ) - 1) - (e : ℝ)) := by
        rw [hc2]
        ring
      rw [hEq]
      ring
    rw [Finset.sum_congr rfl hCoeff, Finset.sum_add_distrib, Finset.mul_sum]
  have hDrop : (∑ e ∈ Finset.Ico 1 m, (((R : ℝ) - 1 - e) * re_inner_cyclicCrossTerms h e v)) ≤
      ((R : ℝ) - 1) * ((R : ℝ) - 2) * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 := by
    have hUnion : Finset.Ico 1 m = Finset.Ico 1 R ∪ Finset.Ico R m :=
      (Finset.Ico_union_Ico_eq_Ico (a := 1) (b := R) (c := m) (by omega) (by omega)).symm
    have hDisj : Disjoint (Finset.Ico 1 R) (Finset.Ico R m) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      refine Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
      simp only [Finset.mem_inter, Finset.mem_Ico] at hx
      omega
    rw [hUnion, Finset.sum_union hDisj]
    have hShort : (∑ e ∈ Finset.Ico 1 R, (((R : ℝ) - 1 - e) * re_inner_cyclicCrossTerms h e v)) ≤
        ((R : ℝ) - 1) * ((R : ℝ) - 2) * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 := by
      calc (∑ e ∈ Finset.Ico 1 R, (((R : ℝ) - 1 - e) * re_inner_cyclicCrossTerms h e v))
          ≤ (∑ e ∈ Finset.Ico 1 R, (((R : ℝ) - 1 - e) *
              (2 * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜))) := by
            refine Finset.sum_le_sum fun e he => ?_
            simp only [Finset.mem_Ico] at he
            have heR : (e : ℝ) + 1 ≤ (R : ℝ) := by
              exact_mod_cast (show e + 1 ≤ R by omega)
            have hCoeffNonneg : (0 : ℝ) ≤ (R : ℝ) - 1 - e := by linarith
            exact mul_le_mul_of_nonneg_left
              (hiii e (by simp only [Finset.mem_Ico]; omega)) hCoeffNonneg
        _ = ((R : ℝ) - 1) * ((R : ℝ) - 2) * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 := by
            rw [← Finset.sum_mul]
            calc
              (∑ e ∈ Finset.Ico 1 R, (R - 1 - (e : ℝ))) *
                  (2 * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜) =
                  (2 * ∑ e ∈ Finset.Ico 1 R, (R - 1 - (e : ℝ))) *
                    RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 := by ring
              _ = _ := by rw [hvi]
    have hLong : (∑ e ∈ Finset.Ico R m, (((R : ℝ) - 1 - e) * re_inner_cyclicCrossTerms h e v)) ≤
        0 := by
      refine Finset.sum_nonpos fun e he => ?_
      have he' := Finset.mem_Ico.mp he
      have heR : (R : ℝ) ≤ (e : ℝ) := by exact_mod_cast he'.1
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hiv e he)
    linarith
  -- Combine.
  have hUpper : (∑ s : ZMod N,
      RCLike.re ⟪cyclicWindowSum h m s v, cyclicWindowSum h m s v⟫_𝕜) ≤
      (((m - R + 1 : ℕ) : ℝ) * RCLike.re ⟪(∑ i, h i) v, (∑ i, h i) v⟫_𝕜 +
        ((R : ℝ) - 1) ^ 2 * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜) := by
    have hCrossSumLe : (∑ e ∈ Finset.Ico 1 m, re_inner_cyclicCrossTerms h e v) ≤
        RCLike.re ⟪(∑ i, h i) v, (∑ i, h i) v⟫_𝕜 - RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 := by
      have h1 := hv
      linarith
    rw [hii, hSplit]
    have hMidLe : (((m - R + 1 : ℕ) : ℝ) *
        (∑ e ∈ Finset.Ico 1 m, re_inner_cyclicCrossTerms h e v)) ≤
        (((m - R + 1 : ℕ) : ℝ) *
          (RCLike.re ⟪(∑ i, h i) v, (∑ i, h i) v⟫_𝕜 -
            RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜)) :=
      mul_le_mul_of_nonneg_left hCrossSumLe (le_of_lt hc)
    have hCast : ((m - R + 1 : ℕ) : ℝ) = (m : ℝ) - (R : ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hmR]
      push_cast
      ring
    calc
      (m : ℝ) * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 +
          (((m - R + 1 : ℕ) : ℝ) *
            (∑ e ∈ Finset.Ico 1 m, re_inner_cyclicCrossTerms h e v) +
          ∑ e ∈ Finset.Ico 1 m,
            ((R : ℝ) - 1 - e) * re_inner_cyclicCrossTerms h e v)
        ≤ (m : ℝ) * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 +
            ((m - R + 1 : ℕ) : ℝ) *
              (RCLike.re ⟪(∑ i, h i) v, (∑ i, h i) v⟫_𝕜 -
                RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜) +
            ((R : ℝ) - 1) * ((R : ℝ) - 2) *
              RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 := by linarith
      _ = ((m - R + 1 : ℕ) : ℝ) *
            RCLike.re ⟪(∑ i, h i) v, (∑ i, h i) v⟫_𝕜 +
          ((R : ℝ) - 1) ^ 2 * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 := by
            rw [hCast]
            ring
  have hKey : m * γ * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 ≤
      (((m - R + 1 : ℕ) : ℝ) * RCLike.re ⟪(∑ i, h i) v, (∑ i, h i) v⟫_𝕜 +
        ((R : ℝ) - 1) ^ 2 * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜) := hi.trans hUpper
  have hCastC : ((m - R + 1 : ℕ) : ℝ) = (m : ℝ) - (R : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hmR]
    push_cast
    ring
  have hDiv : (m * γ - ((R : ℝ) - 1) ^ 2) *
      RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 / ((m : ℝ) - R + 1) ≤
      RCLike.re ⟪(∑ i, h i) v, (∑ i, h i) v⟫_𝕜 := by
    rw [← hCastC]
    refine (div_le_iff₀' hc).2 ?_
    linarith
  have _hδpos : 0 < δ := by
    rw [hδ]
    exact div_pos (sub_pos.mpr hnum) (by rw [← hCastC]; exact hc)
  rw [hδ, div_mul_eq_mul_div]
  exact hDiv

/-- **Nearest-neighbor cyclic Knabe inequality.**

For interaction range `R = 2`, the finite-range coefficient becomes
`(m * γ - 1) / (m - 1)`. Thus a window gap above `1 / m` gives a positive
periodic gap on every ring with `2 * m ≤ N`.

This is the threshold of Knabe, J. Stat. Phys. 52, 627 (1988), and the form
quoted in Pérez-García et al., arXiv:quant-ph/0608197, lines 1483-1489, and
Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:2011.12127, lines 2194-2197. -/
theorem quadraticForm_sum_projections_of_cyclic_knabe_nearest_neighbor
    {N m : ℕ} [NeZero N]
    (h : ZMod N → E →ₗ[𝕜] E) (hh : ∀ i, (h i).IsSymmetricProjection)
    (hN : 2 * m ≤ N) (hm : 2 ≤ m)
    (hcomm : ∀ d : ℕ, 2 ≤ d → d + 2 ≤ N → ∀ i : ZMod N, ∀ v : E,
      h i (h ((i + (d : ZMod N))) v) = h ((i + (d : ZMod N))) (h i v))
    {γ : ℝ} (hnum : 1 < m * γ)
    (hgap : ∀ s : ZMod N, ∀ v : E,
      γ * RCLike.re ⟪cyclicWindowSum h m s v, v⟫_𝕜 ≤
        RCLike.re ⟪cyclicWindowSum h m s v, cyclicWindowSum h m s v⟫_𝕜)
    (v : E) :
    ((m * γ - 1) / (m - 1)) * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 ≤
      RCLike.re ⟪(∑ i, h i) v, (∑ i, h i) v⟫_𝕜 := by
  apply quadraticForm_sum_projections_of_cyclic_knabe h hh hN (R := 2)
    (by norm_num) hm hcomm (γ := γ) (δ := (m * γ - 1) / (m - 1))
  · ring
  · norm_num
    exact hnum
  · exact hgap

end CyclicFamily

end ProjectionGeometry
