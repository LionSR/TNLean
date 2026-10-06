/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.OpenKnabePadding
import TNLean.MPS.ParentHamiltonian.Martingale.IntervalGapTransport
import TNLean.MPS.ParentHamiltonian.Martingale.QuadraticFormGap
import TNLean.MPS.ParentHamiltonian.Martingale.AbstractCriterion

/-!
# A finite-size gap criterion for open parent Hamiltonians

Zero padding embeds the local interactions of an open chain into a cyclic
family without changing the physical Hilbert space. Every nonzero finite
window is an open Hamiltonian on a shorter interval. Consequently gaps on
all open volumes between \(R\) and \(m+R-1\) imply a gap on every open volume.

The coefficient \((m\gamma-(R-1)^2)/(m-R+1)\) is the finite-range Knabe
coefficient derived in `docs/paper-gaps/knabe88_finite_range_coefficient.tex`.
-/

open scoped BigOperators ComplexOrder InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

private theorem cyclicWindowSum_zmodOpenLocalTermES_eq_interval
    {N P R m a b : ℕ} [NeZero P] (A : MPSTensor d D)
    (hR : 0 < R) (hmP : m ≤ P) (hab : a < b)
    (s : ZMod P)
    (hactive : ∀ q : Fin m, (s + (q.val : ZMod P)).val + R ≤ N ↔
      a ≤ (s + (q.val : ZMod P)).val ∧ (s + (q.val : ZMod P)).val < b)
    (hsurj : ∀ i : ℕ, a ≤ i → i < b →
      ∃ q : Fin m, (s + (q.val : ZMod P)).val = i) :
    ProjectionGeometry.cyclicWindowSum (zmodOpenLocalTermES (N := N) A R hR) m s =
      openSuffixParentHamiltonianES A R (b - a + R - 1) N (b + R - 1) := by
  classical
  let Q := Finset.univ.filter fun q : Fin m =>
    (s + (q.val : ZMod P)).val + R ≤ N
  have hstart : ∀ q ∈ Q, (s + (q.val : ZMod P)).val + R ≤ N := by
    intro q hq
    exact (Finset.mem_filter.mp hq).2
  rw [ProjectionGeometry.cyclicWindowSum, openSuffixParentHamiltonianES]
  calc
    (∑ q : Fin m, zmodOpenLocalTermES (N := N) A R hR (s + (q.val : ZMod P))) =
        ∑ q ∈ Q, zmodOpenLocalTermES (N := N) A R hR (s + (q.val : ZMod P)) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro q _ hq
      have hnot : ¬ (s + (q.val : ZMod P)).val + R ≤ N := by
        simpa [Q] using hq
      simp [zmodOpenLocalTermES, hnot]
    _ = ∑ i ∈ Finset.univ.filter (fun i : NonwrappingStart R N =>
        b + R - 1 - (b - a + R - 1) ≤ i.1.val ∧ i.1.val + R ≤ b + R - 1),
        localTermES A R i.1 := by
      apply Finset.sum_bij (fun q hq =>
        (⟨⟨(s + (q.val : ZMod P)).val, by have := hstart q hq; omega⟩,
          hstart q hq⟩ : NonwrappingStart R N))
      · intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have := (hactive q).mp (hstart q hq)
        change b + R - 1 - (b - a + R - 1) ≤ _ ∧ _ + R ≤ b + R - 1
        omega
      · intro q hq q' hq' heq
        have he : s + (q.val : ZMod P) = s + (q'.val : ZMod P) := by
          apply ZMod.val_injective
          exact congrArg (fun i : NonwrappingStart R N => i.1.val) heq
        have hc := congrArg ZMod.val (add_left_cancel he)
        simp only [ZMod.val_natCast] at hc
        rw [Nat.mod_eq_of_lt (by omega : q.val < P),
          Nat.mod_eq_of_lt (by omega : q'.val < P)] at hc
        exact Fin.ext hc
      · intro i hi
        have hi' := (Finset.mem_filter.mp hi).2
        obtain ⟨q, hq⟩ := hsurj i.1.val (by omega) (by omega)
        refine ⟨q, ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [hq]
          exact i.2
        · apply Subtype.ext
          exact Fin.ext hq
      · intro q hq
        simp [zmodOpenLocalTermES, hstart q hq]

/-- Each nonzero window of the zero-padded family is an open Hamiltonian on
an interval containing at most \(m\) interactions. -/
theorem cyclicWindowSum_zmodOpenLocalTermES_eq_zero_or_interval
    {N R m : ℕ} [NeZero (N + 2 * m)] (A : MPSTensor d D) (hR : 0 < R) (hm : 0 < m) (hRN : R ≤ N)
    (s : ZMod (N + 2 * m)) :
    ProjectionGeometry.cyclicWindowSum
        (zmodOpenLocalTermES (N := N) A R hR) m s = 0 ∨
      ∃ W n : ℕ, R ≤ W ∧ W ≤ m + R - 1 ∧ W ≤ n ∧ n ≤ N ∧
        ProjectionGeometry.cyclicWindowSum
          (zmodOpenLocalTermES (N := N) A R hR) m s =
            openSuffixParentHamiltonianES A R W N n := by
  classical
  have hs := s.val_lt
  have hqval (q : Fin m) : (q.val : ZMod (N + 2 * m)).val = q.val := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  by_cases hwrap : N + 2 * m < s.val + m
  · let b := min (s.val + m - (N + 2 * m)) (N - R + 1)
    have hb : 0 < b := by dsimp [b]; omega
    have hbN : b + R - 1 ≤ N := by dsimp [b]; omega
    have hbm : b ≤ m := by dsimp [b]; omega
    right
    refine ⟨b + R - 1, b + R - 1, by omega, by omega, le_rfl, hbN, ?_⟩
    apply cyclicWindowSum_zmodOpenLocalTermES_eq_interval A hR (by omega)
      (a := 0) (b := b) hb s
    · intro q
      by_cases hqw : s.val + q.val < N + 2 * m
      · rw [ZMod.val_add, hqval q, Nat.mod_eq_of_lt hqw]
        dsimp [b]
        omega
      · have hv := ZMod.val_add_val_of_le (a := s)
          (b := (q.val : ZMod (N + 2 * m))) (by rw [hqval q]; omega)
        rw [hqval q] at hv
        dsimp [b]
        omega
    · intro i _ hi
      have hi' : i < s.val + m - (N + 2 * m) := by dsimp [b] at hi; omega
      let q : Fin m := ⟨N + 2 * m - s.val + i, by omega⟩
      refine ⟨q, ?_⟩
      have hv := ZMod.val_add_val_of_le (a := s)
        (b := (q.val : ZMod (N + 2 * m))) (by rw [hqval q]; dsimp [q]; omega)
      rw [hqval q] at hv
      dsimp [q] at hv ⊢
      omega
  · by_cases hactive : s.val + R ≤ N
    · let b := min (s.val + m) (N - R + 1)
      have hab : s.val < b := by dsimp [b]; omega
      have hbN : b + R - 1 ≤ N := by dsimp [b]; omega
      have hbm : b - s.val ≤ m := by dsimp [b]; omega
      right
      refine ⟨b - s.val + R - 1, b + R - 1, by omega, by omega,
        by omega, hbN, ?_⟩
      apply cyclicWindowSum_zmodOpenLocalTermES_eq_interval A hR (by omega) hab s
      · intro q
        have hq := q.isLt
        rw [ZMod.val_add, hqval q, Nat.mod_eq_of_lt (by omega)]
        dsimp [b]
        omega
      · intro i hi hi'
        let q : Fin m := ⟨i - s.val, by dsimp [b] at hi'; omega⟩
        refine ⟨q, ?_⟩
        rw [ZMod.val_add, hqval q, Nat.mod_eq_of_lt (by dsimp [q]; omega)]
        dsimp [q]
        omega
    · left
      rw [ProjectionGeometry.cyclicWindowSum]
      apply Finset.sum_eq_zero
      intro q _
      have hnot : ¬ (s + (q.val : ZMod (N + 2 * m))).val + R ≤ N := by
        have hq := q.isLt
        rw [ZMod.val_add, hqval q, Nat.mod_eq_of_lt (by omega)]
        omega
      simp [zmodOpenLocalTermES, hnot]

/-- Gaps on the active open volumes supply the quadratic-form estimate for
all windows of the zero-padded family. -/
theorem cyclicWindowSum_zmodOpenLocalTermES_quadraticForm_gap
    {N R m : ℕ} [NeZero (N + 2 * m)] (A : MPSTensor d D)
    (hR : 0 < R) (hm : 0 < m) (hRN : R ≤ N) {γ : ℝ} (hγ : 0 < γ)
    (hOpenGap : ∀ W : ℕ, R ≤ W → W ≤ m + R - 1 →
      ∀ u ∈ (LinearMap.ker (openParentHamiltonianES A R W))ᗮ,
        γ * ‖u‖ ≤ ‖openParentHamiltonianES A R W u‖)
    (s : ZMod (N + 2 * m)) (v : EuclideanSpace ℂ (Cfg d N)) :
    γ * (⟪ProjectionGeometry.cyclicWindowSum
      (zmodOpenLocalTermES (N := N) A R hR) m s v, v⟫_ℂ).re ≤
      (⟪ProjectionGeometry.cyclicWindowSum
        (zmodOpenLocalTermES (N := N) A R hR) m s v,
        ProjectionGeometry.cyclicWindowSum
          (zmodOpenLocalTermES (N := N) A R hR) m s v⟫_ℂ).re := by
  rcases cyclicWindowSum_zmodOpenLocalTermES_eq_zero_or_interval A hR hm hRN s with
    hzero | ⟨W, n, hRW, hWm, hWn, hnN, hinterval⟩
  · simp [hzero]
  · rw [hinterval]
    exact (openSuffixParentHamiltonianES_isPositive A R W N n).quadraticForm_sq_ge_of_norm_gap hγ.le
      (openSuffixParentHamiltonianES_norm_gap_of_local_gap A hR hRW hWn hnN hγ
        (hOpenGap W hRW hWm)) v

/-- Gaps on finitely many open volumes imply one gap on every open-chain
length. The explicit coefficient is obtained by zero padding and applying
the finite-range cyclic Knabe inequality; see
`docs/paper-gaps/knabe88_finite_range_coefficient.tex`.

The test volume \(W\) ranges from \(R\) through \(m+R-1\), so boundary windows
are included as well as windows containing all \(m\) interactions. -/
theorem openParentHamiltonianES_gap_of_finite_open_gaps
    (A : MPSTensor d D) {R m : ℕ} (hR : 1 ≤ R) (hmR : R ≤ m)
    {γ : ℝ} (hnum : ((R : ℝ) - 1) ^ 2 < (m : ℝ) * γ)
    (hOpenGap : ∀ W : ℕ, R ≤ W → W ≤ m + R - 1 →
      ∀ u ∈ (LinearMap.ker (openParentHamiltonianES A R W))ᗮ,
        γ * ‖u‖ ≤ ‖openParentHamiltonianES A R W u‖) :
    let δ := ((m : ℝ) * γ - ((R : ℝ) - 1) ^ 2) /
      ((m : ℝ) - (R : ℝ) + 1)
    0 < δ ∧ ∀ N : ℕ, R ≤ N →
      ∀ v ∈ (LinearMap.ker (openParentHamiltonianES A R N))ᗮ,
        δ * ‖v‖ ≤ ‖openParentHamiltonianES A R N v‖ := by
  classical
  dsimp only
  have hm : 0 < m := by omega
  have hγ : 0 < γ := by
    have hsq : 0 ≤ ((R : ℝ) - 1) ^ 2 := sq_nonneg _
    have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
    nlinarith
  have hden : 0 < (m : ℝ) - (R : ℝ) + 1 := by
    exact_mod_cast (by omega : 0 < m - R + 1)
  have hδ : 0 < ((m : ℝ) * γ - ((R : ℝ) - 1) ^ 2) /
      ((m : ℝ) - (R : ℝ) + 1) := div_pos (sub_pos.mpr hnum) hden
  refine ⟨hδ, ?_⟩
  intro N hRN v hv
  let δ := ((m : ℝ) * γ - ((R : ℝ) - 1) ^ 2) /
    ((m : ℝ) - (R : ℝ) + 1)
  let _ : NeZero (N + 2 * m) := ⟨by omega⟩
  exact FrustrationFree.spectralGap_of_martingale_of_finiteDimensional hδ
    (openParentHamiltonianES_isPositive A R N) (fun x => by
      have hx := ProjectionGeometry.quadraticForm_sum_projections_of_cyclic_knabe
        (zmodOpenLocalTermES (N := N) (P := N + 2 * m) A R (by omega))
        (zmodOpenLocalTermES_isSymmetricProjection A (by omega))
        (by omega) hR hmR
        (fun e heR heP s y =>
          zmodOpenLocalTermES_commute_of_oriented_separation A (by omega) heR heP s y)
        (γ := γ) (δ := δ) rfl hnum
        (cyclicWindowSum_zmodOpenLocalTermES_quadraticForm_gap A (by omega)
          hm hRN hγ hOpenGap) x
      rwa [sum_zmodOpenLocalTermES_eq_openParentHamiltonianES A (by omega) (by omega)]
        at hx) v hv

end MPSTensor
