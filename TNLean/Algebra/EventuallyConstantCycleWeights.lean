/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Eventually constant weighted cycle sums

This file contains the finite combinatorial argument used in Beigi's
classification of one-dimensional commuting Hamiltonians.  An ordered cycle
is a finite word with its last vertex joined back to its first vertex.  Its
weight is the product of the weights of its directed edges.

If the sum of these weights is eventually constant, comparison of cycles of
two sufficiently large consecutive lengths with their repetitions at the
common length `N(N+1)` forces every cyclic edge to have weight one.  The same
comparison makes both repetition maps exhaustive.  Their common values have
periods `N` and `N+1`, hence period one, so every cycle is constant.

## References

* S. Beigi, *Classification of the phases of 1D spin chains with commuting
  Hamiltonians*, J. Phys. A 45 (2012) 025306, Section IV, equations (7)--(13).
-/

open scoped BigOperators

namespace FiniteWeightedDigraph

variable {V : Type*} [Fintype V]

/-- The successor of an index on a nonempty finite cycle.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV. -/
def next {N : ℕ} (hN : 0 < N) (i : Fin N) : Fin N :=
  ⟨(i.val + 1) % N, Nat.mod_lt _ hN⟩

/-- The product of the directed-edge weights around an ordered cycle.

Source: Beigi, J. Phys. A 45 (2012) 025306, equation (4) and Section IV. -/
def cycleWeight (w : V → V → ℕ) {N : ℕ} (hN : 0 < N)
    (x : Fin N → V) : ℕ :=
  ∏ i, w (x i) (x (next hN i))

/-- The ordered-cycle weighted sum at a positive length.

Cycles are ordered: cyclic rotations are counted separately, exactly as in
Beigi's dimension formula.

Source: Beigi, J. Phys. A 45 (2012) 025306, equation (4) and Section IV. -/
def cycleWeightSum (w : V → V → ℕ) {N : ℕ} (hN : 0 < N) : ℕ :=
  ∑ x : Fin N → V, cycleWeight w hN x

/-- The numerical cycle sum is constant at all sufficiently large positive
lengths.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV. -/
def HasEventuallyConstantCycleWeightSum (w : V → V → ℕ) : Prop :=
  ∃ c N₀ : ℕ, ∀ N : ℕ, N₀ < N → ∀ hN : 0 < N, cycleWeightSum w hN = c

omit [Fintype V] in
/-- Repeating a finite word a positive number of times is injective as a
function of the original word.

Source: Beigi, J. Phys. A 45 (2012) 025306, equations (7)--(10). -/
theorem repeat_injective {N m : ℕ} (hm : 0 < m) :
    Function.Injective (Fin.repeat m : (Fin N → V) → Fin (m * N) → V) := by
  intro x y hxy
  funext i
  have h := congrFun hxy ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_mul_of_pos_left N hm)⟩
  simpa [Fin.repeat, Fin.modNat, Nat.mod_eq_of_lt i.isLt] using h

omit [Fintype V] in
@[simp]
private theorem repeat_finProdFinEquiv {N m : ℕ} (x : Fin N → V)
    (i : Fin m) (j : Fin N) :
    Fin.repeat m x (finProdFinEquiv (i, j)) = x j := by
  simp [Fin.repeat, finProdFinEquiv, Fin.modNat, Nat.mod_eq_of_lt]

omit [Fintype V] in
@[simp]
private theorem repeat_next_finProdFinEquiv {N m : ℕ} (hN : 0 < N)
    (hm : 0 < m) (x : Fin N → V) (i : Fin m) (j : Fin N) :
    Fin.repeat m x
        (next (Nat.mul_pos hm hN) (finProdFinEquiv (i, j))) =
      x (next hN j) := by
  simp [Fin.repeat, finProdFinEquiv, Fin.modNat, next, Nat.add_mod,
    Nat.mod_eq_of_lt]

omit [Fintype V] in
/-- Repetition raises the weight of a cycle to the repetition power.

This is the product identity underlying Beigi's comparisons at lengths `N`,
`N+1`, and `N(N+1)`.

Source: Beigi, J. Phys. A 45 (2012) 025306, equations (7)--(10). -/
theorem cycleWeight_repeat (w : V → V → ℕ) {N m : ℕ}
    (hN : 0 < N) (hm : 0 < m) (x : Fin N → V) :
    cycleWeight w (Nat.mul_pos hm hN) (Fin.repeat m x) = cycleWeight w hN x ^ m := by
  unfold cycleWeight
  rw [← finProdFinEquiv.prod_comp]
  rw [Fintype.prod_prod_type]
  simp_rw [repeat_next_finProdFinEquiv hN hm x]
  simp_rw [repeat_finProdFinEquiv x]
  simp

/-- The total weight of repeated cycles is bounded by the total weight of all
cycles at the repeated length.

Source: Beigi, J. Phys. A 45 (2012) 025306, equations (7)--(10). -/
theorem sum_cycleWeight_pow_le (w : V → V → ℕ) {N m : ℕ}
    (hN : 0 < N) (hm : 0 < m) :
    (∑ x : Fin N → V, cycleWeight w hN x ^ m) ≤
      cycleWeightSum w (Nat.mul_pos hm hN) := by
  classical
  simp_rw [← cycleWeight_repeat w hN hm]
  unfold cycleWeightSum
  calc
    (∑ x : Fin N → V, cycleWeight w (Nat.mul_pos hm hN) (Fin.repeat m x)) =
        (Finset.univ.image (Fin.repeat m)).sum
          (cycleWeight w (Nat.mul_pos hm hN)) := by
      rw [Finset.sum_image]
      exact (repeat_injective (V := V) hm).injOn
    _ ≤ ∑ y : Fin (m * N) → V, cycleWeight w (Nat.mul_pos hm hN) y :=
      Finset.sum_le_sum_of_subset (Finset.image_subset_iff.mpr fun _ _ ↦ Finset.mem_univ _)

private theorem eq_zero_or_one_of_sum_pow_le {I : Type*} [Fintype I]
    (f : I → ℕ) {m : ℕ} (hm : 1 < m)
    (h : (∑ i, f i ^ m) ≤ ∑ i, f i) (i : I) :
    f i = 0 ∨ f i = 1 := by
  by_contra hi
  have hfi : 1 < f i := by omega
  have hpoint : ∀ j : I, f j ≤ f j ^ m := by
    intro j
    by_cases hj : f j = 0
    · simp [hj]
    · exact Nat.le_pow (Nat.zero_lt_of_lt hm)
  have hstrict : (∑ j, f j) < ∑ j, f j ^ m := by
    apply Finset.sum_lt_sum
    · intro j _
      exact hpoint j
    · refine ⟨i, Finset.mem_univ _, ?_⟩
      simpa only [pow_one] using Nat.pow_lt_pow_right hfi hm
  exact (Nat.not_lt_of_ge h) hstrict

/-- Every positive-weight ordered cycle has weight one when the ordered-cycle
weight sum is eventually constant.

In particular, every edge that occurs in a directed cycle has weight one.

Source: Beigi, J. Phys. A 45 (2012) 025306, equations (7)--(11). -/
theorem cycleWeight_eq_one {w : V → V → ℕ}
    (hconst : HasEventuallyConstantCycleWeightSum w) {K : ℕ}
    (hK : 0 < K) (x : Fin K → V) (hx : cycleWeight w hK x ≠ 0) :
    cycleWeight w hK x = 1 := by
  rcases hconst with ⟨c, N₀, hconst⟩
  let t := N₀ + 1
  let N := t * K
  have ht : 0 < t := by simp [t]
  have hN : 0 < N := Nat.mul_pos ht hK
  have hN₀ : N₀ < N := by
    exact (Nat.lt_succ_self N₀).trans_le (Nat.le_mul_of_pos_right t hK)
  have hm : 1 < N + 1 := by omega
  have hL : 0 < (N + 1) * N := Nat.mul_pos (Nat.succ_pos N) hN
  have hN₀L : N₀ < (N + 1) * N :=
    hN₀.trans_le (Nat.le_mul_of_pos_left N (Nat.succ_pos N))
  have hsumle :
      (∑ y : Fin N → V, cycleWeight w hN y ^ (N + 1)) ≤
        ∑ y : Fin N → V, cycleWeight w hN y := by
    calc
      (∑ y : Fin N → V, cycleWeight w hN y ^ (N + 1)) ≤
          cycleWeightSum w hL := sum_cycleWeight_pow_le w hN (Nat.succ_pos N)
      _ = c := hconst _ hN₀L hL
      _ = cycleWeightSum w hN := (hconst N hN₀ hN).symm
  have hy01 := eq_zero_or_one_of_sum_pow_le
    (fun y : Fin N → V ↦ cycleWeight w hN y) hm hsumle (Fin.repeat t x)
  have hyne : cycleWeight w hN (Fin.repeat t x) ≠ 0 := by
    rw [cycleWeight_repeat w hK ht]
    exact pow_ne_zero _ hx
  have hyone := hy01.resolve_left hyne
  rw [cycleWeight_repeat w hK ht] at hyone
  exact (Nat.pow_eq_one.mp hyone).resolve_right (Nat.ne_of_gt ht)

/-- Every edge belonging to a positive-weight directed cycle has weight one.

Source: Beigi, J. Phys. A 45 (2012) 025306, equation (11). -/
theorem cyclicEdgeWeight_eq_one {w : V → V → ℕ}
    (hconst : HasEventuallyConstantCycleWeightSum w) {N : ℕ}
    (hN : 0 < N) (x : Fin N → V) (hx : cycleWeight w hN x ≠ 0)
    (i : Fin N) :
    w (x i) (x (next hN i)) = 1 := by
  have hprod := cycleWeight_eq_one hconst hN x hx
  unfold cycleWeight at hprod
  exact (Finset.prod_eq_one_iff.mp hprod) i (Finset.mem_univ i)

/-- Positive-weight ordered cycles at a fixed positive length.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV. -/
private def PositiveCycle (w : V → V → ℕ) {N : ℕ} (hN : 0 < N) :=
  {x : Fin N → V // cycleWeight w hN x ≠ 0}

private noncomputable instance (w : V → V → ℕ) {N : ℕ} (hN : 0 < N) :
    Fintype (PositiveCycle w hN) := by
  classical
  unfold PositiveCycle
  infer_instance

private theorem positiveCycle_card_eq_cycleWeightSum {w : V → V → ℕ}
    (hconst : HasEventuallyConstantCycleWeightSum w) {N : ℕ} (hN : 0 < N) :
    Fintype.card (PositiveCycle w hN) = cycleWeightSum w hN := by
  classical
  unfold PositiveCycle
  rw [Fintype.card_subtype]
  unfold cycleWeightSum
  rw [← Finset.sum_filter_ne_zero]
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_congr rfl
  intro x hx
  exact (cycleWeight_eq_one hconst hN x (Finset.mem_filter.mp hx).2).symm

/-- Repetition sends a positive-weight ordered cycle to a positive-weight
ordered cycle.

Source: Beigi, J. Phys. A 45 (2012) 025306, equations (7)--(10). -/
private noncomputable def repeatPositiveCycle (w : V → V → ℕ) {N m : ℕ}
    (hN : 0 < N) (hm : 0 < m) :
    PositiveCycle w hN → PositiveCycle w (Nat.mul_pos hm hN) :=
  fun x ↦ ⟨Fin.repeat m x.1, by
    rw [cycleWeight_repeat w hN hm]
    exact pow_ne_zero _ x.2⟩

omit [Fintype V] in
private theorem repeatPositiveCycle_injective (w : V → V → ℕ)
    {N m : ℕ} (hN : 0 < N) (hm : 0 < m) :
    Function.Injective (repeatPositiveCycle w hN hm) := by
  intro x y hxy
  apply Subtype.ext
  exact (repeat_injective (V := V) hm) (congrArg Subtype.val hxy)

private theorem repeatPositiveCycle_surjective {w : V → V → ℕ}
    (hconst : HasEventuallyConstantCycleWeightSum w) {N m : ℕ}
    (hN : 0 < N) (hm : 0 < m)
    (hsum : cycleWeightSum w hN = cycleWeightSum w (Nat.mul_pos hm hN)) :
    Function.Surjective (repeatPositiveCycle w hN hm) := by
  apply ((Fintype.bijective_iff_injective_and_card _).mpr ⟨
    repeatPositiveCycle_injective w hN hm, ?_⟩).2
  rw [positiveCycle_card_eq_cycleWeightSum hconst hN,
    positiveCycle_card_eq_cycleWeightSum hconst (Nat.mul_pos hm hN)]
  exact hsum

omit [Fintype V] in
private theorem constant_of_repeat_succ_eq_repeat {N : ℕ} (hN : 0 < N)
    (y : Fin N → V) (e : Fin (N + 1) → V)
    (h : Fin.repeat (N + 1) y =
      Fin.repeat N e ∘ Fin.cast (Nat.mul_comm (N + 1) N)) :
    ∀ i : Fin N, y i = y ⟨0, hN⟩ := by
  cases N with
  | zero => simp at hN
  | succ n =>
      intro i
      induction i using Fin.induction with
      | zero => rfl
      | succ i ih =>
          let p₀ : Fin ((n + 1 + 1) * (n + 1)) :=
            ⟨i.val, by
              exact i.isLt.trans_le ((Nat.le_succ n).trans
                (Nat.le_mul_of_pos_left (n + 1) (by omega)))⟩
          let p₁ : Fin ((n + 1 + 1) * (n + 1)) :=
            ⟨i.val + (n + 1) + 1, by
              have hmul : 2 * (n + 1) ≤ (n + 1 + 1) * (n + 1) :=
                Nat.mul_le_mul_right (n + 1) (by omega)
              omega⟩
          have h₀ := congrFun h p₀
          have h₁ := congrFun h p₁
          have hmod₀N : i.val % (n + 1) = i.val := Nat.mod_eq_of_lt (by omega)
          have hmod₀S : i.val % (n + 1 + 1) = i.val := Nat.mod_eq_of_lt (by omega)
          have hmod₁N : (i.val + (n + 1) + 1) % (n + 1) = i.val + 1 := by
            rw [show i.val + (n + 1) + 1 = (i.val + 1) + (n + 1) by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          have hmod₁S : (i.val + (n + 1) + 1) % (n + 1 + 1) = i.val := by
            rw [show i.val + (n + 1) + 1 = i.val + (n + 1 + 1) by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          have h₀' : y i.castSucc = e i.castSucc.castSucc := by
            simp only [Fin.repeat_apply, Function.comp_apply, p₀, Fin.modNat,
              Fin.cast, hmod₀N, hmod₀S] at h₀
            convert h₀ using 1 <;> congr 1
          have h₁' : y i.succ = e i.castSucc.castSucc := by
            simp only [Fin.repeat_apply, Function.comp_apply, p₁, Fin.modNat,
              Fin.cast, hmod₁N, hmod₁S] at h₁
            convert h₁ using 1 <;> congr 1
          exact h₁'.trans (h₀'.symm.trans ih)

omit [Fintype V] in
private theorem cycleWeight_cast (w : V → V → ℕ) {N M : ℕ}
    (hNM : N = M) (hN : 0 < N) (hM : 0 < M) (x : Fin N → V) :
    cycleWeight w hM (x ∘ Fin.cast hNM.symm) = cycleWeight w hN x := by
  subst M
  rfl

/-- Every positive-weight ordered cycle is the repetition of a single loop.

Equivalently, its vertex word is constant.  The proof repeats an arbitrary
cycle to a sufficiently large length `N`, compares the exhaustive repetition
maps from lengths `N` and `N+1` into their common multiple, and uses the two
consecutive periods.

Source: Beigi, J. Phys. A 45 (2012) 025306, equations (12)--(13). -/
theorem cycle_eq_constant {w : V → V → ℕ}
    (hconst : HasEventuallyConstantCycleWeightSum w) {K : ℕ}
    (hK : 0 < K) (x : Fin K → V) (hx : cycleWeight w hK x ≠ 0) :
    ∀ i : Fin K, x i = x ⟨0, hK⟩ := by
  rcases hconst with ⟨c, N₀, hlarge⟩
  let t := N₀ + 1
  let N := t * K
  have ht : 0 < t := by simp [t]
  have hN : 0 < N := Nat.mul_pos ht hK
  have hN₀ : N₀ < N :=
    (Nat.lt_succ_self N₀).trans_le (Nat.le_mul_of_pos_right t hK)
  have hNp : 0 < N + 1 := Nat.succ_pos N
  have hN₀p : N₀ < N + 1 := hN₀.trans (Nat.lt_succ_self N)
  have hL₁ : 0 < (N + 1) * N := Nat.mul_pos hNp hN
  have hL₂ : 0 < N * (N + 1) := Nat.mul_pos hN hNp
  have hN₀L₁ : N₀ < (N + 1) * N :=
    hN₀.trans_le (Nat.le_mul_of_pos_left N hNp)
  have hN₀L₂ : N₀ < N * (N + 1) :=
    hN₀p.trans_le (Nat.le_mul_of_pos_left (N + 1) hN)
  let y : PositiveCycle w hN := repeatPositiveCycle w hK ht ⟨x, hx⟩
  let z : PositiveCycle w hL₁ := repeatPositiveCycle w hN hNp y
  let z' : PositiveCycle w hL₂ := ⟨
    z.1 ∘ Fin.cast (Nat.mul_comm N (N + 1)), by
      rw [cycleWeight_cast w (Nat.mul_comm (N + 1) N) hL₁ hL₂]
      exact z.2⟩
  have hsum₂ : cycleWeightSum w hNp = cycleWeightSum w hL₂ := by
    rw [hlarge (N + 1) hN₀p hNp, hlarge _ hN₀L₂ hL₂]
  obtain ⟨e, he⟩ := repeatPositiveCycle_surjective
    ⟨c, N₀, hlarge⟩ hNp hN hsum₂ z'
  have hrepetition : Fin.repeat (N + 1) y.1 =
      Fin.repeat N e.1 ∘ Fin.cast (Nat.mul_comm (N + 1) N) := by
    funext i
    have hei := congrFun (congrArg Subtype.val he)
      (Fin.cast (Nat.mul_comm (N + 1) N) i)
    have hcast : Fin.cast (Nat.mul_comm N (N + 1))
        (Fin.cast (Nat.mul_comm (N + 1) N) i) = i := by
      apply Fin.ext
      rfl
    simpa only [z', z, repeatPositiveCycle, Function.comp_apply, hcast] using hei.symm
  have hyconst := constant_of_repeat_succ_eq_repeat hN y.1 e.1 hrepetition
  intro i
  let j : Fin N := ⟨i.val, i.isLt.trans_le (by
    simpa [N, Nat.mul_comm] using Nat.le_mul_of_pos_right K ht)⟩
  have hj := hyconst j
  simpa [y, repeatPositiveCycle, j, Fin.repeat, Fin.modNat,
    Nat.mod_eq_of_lt i.isLt] using hj

/-- Vertices carrying a positive-weight loop.

Source: Beigi, J. Phys. A 45 (2012) 025306, equation (13). -/
def Loop (w : V → V → ℕ) := {v : V // w v v ≠ 0}

noncomputable instance (w : V → V → ℕ) : Fintype (Loop w) := by
  classical
  unfold Loop
  infer_instance

private noncomputable def positiveCycleEquivLoop {w : V → V → ℕ}
    (hconst : HasEventuallyConstantCycleWeightSum w) {N : ℕ} (hN : 0 < N) :
    PositiveCycle w hN ≃ Loop w where
  toFun x := ⟨x.1 ⟨0, hN⟩, by
    have hedge := cyclicEdgeWeight_eq_one hconst hN x.1 x.2 ⟨0, hN⟩
    rw [cycle_eq_constant hconst hN x.1 x.2 (next hN ⟨0, hN⟩)] at hedge
    omega⟩
  invFun v := ⟨fun _ ↦ v.1, by
    unfold cycleWeight
    simp only
    exact Finset.prod_ne_zero_iff.mpr fun _ _ ↦ v.2⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact (cycle_eq_constant hconst hN x.1 x.2 i).symm
  right_inv v := rfl

/-- At every positive length, the ordered-cycle weight sum is the number of
positive-weight loops.

Source: Beigi, J. Phys. A 45 (2012) 025306, equation (13). -/
theorem cycleWeightSum_eq_card_loop {w : V → V → ℕ}
    (hconst : HasEventuallyConstantCycleWeightSum w) {N : ℕ} (hN : 0 < N) :
    cycleWeightSum w hN = Fintype.card (Loop w) := by
  rw [← positiveCycle_card_eq_cycleWeightSum hconst hN]
  exact Fintype.card_congr (positiveCycleEquivLoop hconst hN)

end FiniteWeightedDigraph
