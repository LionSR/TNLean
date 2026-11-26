/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.OpenKnabePadding
import QICLean.Spectral.Gap.EigenvalueGap
import QICLean.ManyBody.Hamiltonian.Martingale.AbstractCriterion
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.OpenRangeComparison
import QICLean.Spectral.Gap.EuclideanFiberwiseGap
import TNLean.MPS.ParentHamiltonian.Gap.Filtration.WholeIncrementSpectatorTransport

/-!
# A finite-size gap criterion for open parent Hamiltonians

Zero padding embeds the local interactions of an open chain into a cyclic
family without changing the physical Hilbert space. Every nonzero finite
window is an open Hamiltonian on a shorter interval. Consequently gaps on
all open volumes between \(R\) and \(m+R-1\) imply a gap on every open volume.

The coefficient \((m\gamma-(R-1)^2)/(m-R+1)\) is the finite-range Knabe
coefficient derived in `docs/paper-gaps/knabe88_finite_range_coefficient.tex`.

It also contains the following results.

* `MPSTensor.hamiltonian_prefix_parentChainInteraction_gap_of_local_gap`,
  `MPSTensor.hamiltonian_restrict_parentChainInteraction_gap_of_local_gap`: gaps of interval
  Hamiltonians after adjoining free sites.
* `MPSTensor.ker_hamiltonian_restrict_parentChainInteraction_eq_of_local_kernel`,
  `MPSTensor.ker_hamiltonian_restrict_parentChainInteraction_eq_range_reassocTailBoundaryMapES`:
  terminal interval kernels and boundary spaces.
-/

section IntervalGapTransport

/-!
## Gaps of interval Hamiltonians after adjoining free sites

An interval Hamiltonian, acting on a larger chain, is an orthogonal direct
sum of copies of its finite-interval operator. Its gap, the lower bound on its
nonzero eigenvalues, is therefore preserved. The proof transports the kernel
projection and its positive comparison under the physical coordinate
isometry. This supplies the fixed-ambient interpretation of the local gaps
in Nachtergaele, arXiv:cond-mat/9410110, condition C2, lines 1045--1056.
-/

open scoped InnerProductSpace ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- Adjoining free sites to a prefix preserves its finite-interval gap: every eigenvalue of the
prefix Hamiltonian on the longer chain is `0` or at least the gap. This is the fixed-ambient
interpretation of the local gap in Nachtergaele, arXiv:cond-mat/9410110, condition C2,
lines 1045--1056. -/
theorem hamiltonian_prefix_parentChainInteraction_gap_of_local_gap
    (A : MPSTensor d D) {R n q : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (hGap : ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction A R n).hamiltonian) μ →
        μ = 0 ∨ (κ : ℂ) ≤ μ) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
      ((parentChainInteraction A R (n + q)).restrict fun i ↦ i.val + R ≤ n).hamiltonian) μ →
        μ = 0 ∨ (κ : ℂ) ≤ μ := by
  have hConj :=
    hamiltonian_prefix_parentChainInteraction_conj_rightSpectatorConfigLinearIsometryEquiv
      A (L := R) (n := n) (r := q) (p := n) le_rfl
  exact ContinuousLinearMap.forall_hasEigenvalue_of_conj_rightFiberwiseMap
    (rightSpectatorConfigLinearIsometryEquiv d n q) _
    (Matrix.toEuclideanLin (parentChainInteraction A R n).hamiltonian) hκ
    (Matrix.isPositive_toEuclideanLin_iff.mpr (posSemidef_hamiltonian_parentChainInteraction A R n))
    (by simpa only [LinearEquiv.conj_apply, LinearMap.comp_assoc,
      hamiltonian_prefix_parentChainInteraction_self_eq_hamiltonian_parentChainInteraction] using!
        hConj)
    hGap

/-- Inserting a finite terminal-interval Hamiltonian into a larger chain preserves its gap:
every eigenvalue of the interval Hamiltonian on the larger chain is `0` or at least the gap.
The physical coordinate isometry places its active sites first and the free sites second. This
is the fixed-ambient form of Nachtergaele's condition C2, arXiv:cond-mat/9410110,
lines 1045--1056. -/
theorem hamiltonian_restrict_parentChainInteraction_gap_of_local_gap
    (A : MPSTensor d D) {R W N n : ℕ} (hR : 0 < R) (hRW : R ≤ W)
    (hWn : W ≤ n) (hnN : n ≤ N) {κ : ℝ} (hκ : 0 < κ)
    (hGap : ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction A R W).hamiltonian) μ →
        μ = 0 ∨ (κ : ℂ) ≤ μ) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
      ((parentChainInteraction A R N).restrict
        fun i ↦ n - W ≤ i.val ∧ i.val + R ≤ n).hamiltonian) μ →
        μ = 0 ∨ (κ : ℂ) ≤ μ := by
  have hConj := hamiltonian_restrict_parentChainInteraction_conj_cyclicActiveBlock A hR hRW hWn hnN
  exact ContinuousLinearMap.forall_hasEigenvalue_of_conj_rightFiberwiseMap
    (cyclicActiveBlockConfigLinearIsometryEquiv d W (hWn.trans hnN) ⟨n - W, by omega⟩) _
    (Matrix.toEuclideanLin (parentChainInteraction A R W).hamiltonian) hκ
    (Matrix.isPositive_toEuclideanLin_iff.mpr (posSemidef_hamiltonian_parentChainInteraction A R W))
    (by simpa only [LinearEquiv.conj_apply, LinearMap.comp_assoc] using! hConj)
    hGap

end MPSTensor

end IntervalGapTransport

section OpenFiniteRangeKnabeGap

open scoped BigOperators ComplexOrder InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

private theorem cyclicWindowSum_hamiltonian_restrict_parentChainInteraction_eq_interval
    {N P R m a b : ℕ} [NeZero P] (A : MPSTensor d D)
    (hR : 0 < R) (hmP : m ≤ P) (hab : a < b)
    (s : ZMod P)
    (hactive : ∀ q : Fin m, (s + (q.val : ZMod P)).val + R ≤ N ↔
      a ≤ (s + (q.val : ZMod P)).val ∧ (s + (q.val : ZMod P)).val < b)
    (hsurj : ∀ i : ℕ, a ≤ i → i < b →
      ∃ q : Fin m, (s + (q.val : ZMod P)).val = i) :
    ProjectionGeometry.cyclicWindowSum (fun t : ZMod P ↦ Matrix.toEuclideanLin
        ((parentChainInteraction A R N).restrict fun i ↦ i.val = t.val).hamiltonian) m s =
      Matrix.toEuclideanLin
          ((parentChainInteraction A R N).restrict fun i ↦ b + R - 1 - (b - a + R - 1) ≤ i.val ∧
              i.val + R ≤ b + R - 1).hamiltonian := by
  rw [ProjectionGeometry.cyclicWindowSum]
  beta_reduce
  rw [← map_sum]
  refine congrArg _ ?_
  simp only [ManyBody.Interaction.hamiltonian, ManyBody.Interaction.restrict_term]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hi := i.isLt
  have hinj : ∀ q q' : Fin m,
      (s + (q.val : ZMod P)).val = (s + (q'.val : ZMod P)).val → q = q' := by
    intro q q' heq
    have hc := congrArg ZMod.val (add_left_cancel (ZMod.val_injective P heq))
    simp only [ZMod.val_natCast] at hc
    rw [Nat.mod_eq_of_lt (by omega : q.val < P),
      Nat.mod_eq_of_lt (by omega : q'.val < P)] at hc
    exact Fin.ext hc
  by_cases hQ : b + R - 1 - (b - a + R - 1) ≤ i.val ∧ i.val + R ≤ b + R - 1
  · obtain ⟨q, hq⟩ := hsurj i.val (by omega) (by omega)
    rw [ite_eq_left hQ, Finset.sum_eq_single_of_mem q (Finset.mem_univ _) fun q' _ hne ↦
      ite_eq_right fun h ↦ hne (hinj _ _ (h.symm.trans hq.symm))]
    exact ite_eq_left hq.symm
  · rw [ite_eq_right hQ]
    exact Finset.sum_eq_zero fun q _ ↦ ite_eq_right fun h ↦ hQ (by
      have := (hactive q).mp (by omega)
      omega)

/-- Each nonzero window of the zero-padded family is an open Hamiltonian on
an interval containing at most \(m\) interactions. -/
theorem cyclicWindowSum_hamiltonian_restrict_parentChainInteraction_eq_zero_or_interval
    {N R m : ℕ} [NeZero (N + 2 * m)] (A : MPSTensor d D) (hR : 0 < R) (hm : 0 < m) (hRN : R ≤ N)
    (s : ZMod (N + 2 * m)) :
    ProjectionGeometry.cyclicWindowSum (fun t : ZMod (N + 2 * m) ↦ Matrix.toEuclideanLin
        ((parentChainInteraction A R N).restrict fun i ↦ i.val = t.val).hamiltonian) m s = 0 ∨
      ∃ W n : ℕ, R ≤ W ∧ W ≤ m + R - 1 ∧ W ≤ n ∧ n ≤ N ∧
        ProjectionGeometry.cyclicWindowSum (fun t : ZMod (N + 2 * m) ↦ Matrix.toEuclideanLin
            ((parentChainInteraction A R N).restrict fun i ↦ i.val = t.val).hamiltonian) m s =
            Matrix.toEuclideanLin
                ((parentChainInteraction A R N).restrict fun i ↦ n - W ≤ i.val ∧ i.val + R ≤
                    n).hamiltonian := by
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
    apply cyclicWindowSum_hamiltonian_restrict_parentChainInteraction_eq_interval A hR (by omega)
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
      apply cyclicWindowSum_hamiltonian_restrict_parentChainInteraction_eq_interval A hR (by omega)
        hab s
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
      rw [hamiltonian_restrict_parentChainInteraction_val_eq, dite_eq_right (by omega), map_zero]

/-- Gaps above the kernel on the active open volumes supply the quadratic-form estimate for
all windows of the zero-padded family. -/
theorem cyclicWindowSum_hamiltonian_restrict_parentChainInteraction_quadraticForm_gap
    {N R m : ℕ} [NeZero (N + 2 * m)] (A : MPSTensor d D)
    (hR : 0 < R) (hm : 0 < m) (hRN : R ≤ N) {γ : ℝ} (hγ : 0 < γ)
    (hOpenGap : ∀ W : ℕ, R ≤ W → W ≤ m + R - 1 →
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentChainInteraction A R W).hamiltonian) μ →
          μ = 0 ∨ (γ : ℂ) ≤ μ)
    (s : ZMod (N + 2 * m)) (v : EuclideanSpace ℂ (Cfg d N)) :
    γ * (⟪ProjectionGeometry.cyclicWindowSum (fun t : ZMod (N + 2 * m) ↦ Matrix.toEuclideanLin
        ((parentChainInteraction A R N).restrict fun i ↦ i.val = t.val).hamiltonian) m s v,
        v⟫_ℂ).re ≤
      (⟪ProjectionGeometry.cyclicWindowSum (fun t : ZMod (N + 2 * m) ↦ Matrix.toEuclideanLin
        ((parentChainInteraction A R N).restrict fun i ↦ i.val = t.val).hamiltonian) m s v,
        ProjectionGeometry.cyclicWindowSum (fun t : ZMod (N + 2 * m) ↦ Matrix.toEuclideanLin
          ((parentChainInteraction A R N).restrict fun i ↦ i.val = t.val).hamiltonian) m s v⟫_ℂ).re
      := by
  rcases cyclicWindowSum_hamiltonian_restrict_parentChainInteraction_eq_zero_or_interval
    A hR hm hRN s with hzero | ⟨W, n, hRW, hWm, hWn, hnN, hinterval⟩
  · simp [hzero]
  · rw [hinterval]
    exact (Matrix.isPositive_toEuclideanLin_iff.mpr
      (posSemidef_hamiltonian_restrict_parentChainInteraction A R N
        _)).quadraticForm_sq_ge_of_forall_hasEigenvalue hγ.le
      (hamiltonian_restrict_parentChainInteraction_gap_of_local_gap A hR hRW hWn hnN hγ
        (hOpenGap W hRW hWm)) v

/-- Gaps above the kernel on finitely many open volumes imply one gap on every open-chain
length: every eigenvalue is `0` or at least the gap. The explicit coefficient is obtained by
zero padding and applying the finite-range cyclic Knabe inequality; see
`docs/paper-gaps/knabe88_finite_range_coefficient.tex`.

The test volume \(W\) ranges from \(R\) through \(m+R-1\), so boundary windows
are included as well as windows containing all \(m\) interactions. -/
theorem hamiltonian_parentChainInteraction_gap_of_finite_open_gaps
    (A : MPSTensor d D) {R m : ℕ} (hR : 1 ≤ R) (hmR : R ≤ m)
    {γ : ℝ} (hnum : ((R : ℝ) - 1) ^ 2 < (m : ℝ) * γ)
    (hOpenGap : ∀ W : ℕ, R ≤ W → W ≤ m + R - 1 →
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentChainInteraction A R W).hamiltonian) μ →
          μ = 0 ∨ (γ : ℂ) ≤ μ) :
    let δ : ℝ := ((m : ℝ) * γ - ((R : ℝ) - 1) ^ 2) /
      ((m : ℝ) - (R : ℝ) + 1)
    0 < δ ∧ ∀ N : ℕ, R ≤ N →
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ := by
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
  refine ⟨hδ, fun N hRN ↦ ?_⟩
  have hPSD := posSemidef_hamiltonian_parentChainInteraction A R N
  let _ : NeZero (N + 2 * m) := ⟨by omega⟩
  refine FrustrationFree.forall_hasEigenvalue_of_martingale_of_finiteDimensional hδ
    (Matrix.isPositive_toEuclideanLin_iff.mpr hPSD) fun x ↦ ?_
  have hx := ProjectionGeometry.quadraticForm_sum_projections_of_cyclic_knabe
    (fun t : ZMod (N + 2 * m) ↦ Matrix.toEuclideanLin
      ((parentChainInteraction A R N).restrict fun i ↦ i.val = t.val).hamiltonian)
    (fun t ↦ Matrix.isSymmetricProjection_toEuclideanLin_iff.mpr
      (isStarProjection_hamiltonian_restrict_parentChainInteraction_val_eq A R N t.val))
    (by omega) hR hmR
    (fun e heR heP s y ↦ by
      have h := congrArg (fun M ↦ Matrix.toEuclideanLin M y)
        (commute_hamiltonian_restrict_parentChainInteraction_of_oriented_separation
          (N := N) A (by omega) heR heP s).eq
      simpa only [Matrix.toEuclideanLin_mul, LinearMap.comp_apply] using h)
    (γ := γ) rfl hnum
    (cyclicWindowSum_hamiltonian_restrict_parentChainInteraction_quadraticForm_gap A (by omega)
      hm hRN hγ hOpenGap) x
  rwa [← map_sum, sum_hamiltonian_restrict_parentChainInteraction_val_eq A (by omega) (by omega)]
    at hx

end MPSTensor

end OpenFiniteRangeKnabeGap

section IntervalKernelTransport

/-!
## Terminal interval kernels and boundary spaces

A finite terminal interval acts independently of its free sites. Consequently,
its kernel depends only on its active finite-interval kernel. This identifies
the terminal kernel with the boundary space in the three-interval projector
estimate of Nachtergaele, arXiv:cond-mat/9410110, condition C3-prime.
-/

open scoped ComplexOrder
namespace MPSTensor
variable {d D : ℕ}
/-- Equality of the active local kernel with the MPS ground space identifies
an embedded terminal Hamiltonian with the full-window terminal ground space.
This is the interval kernel identification used in Nachtergaele,
arXiv:cond-mat/9410110, condition C3-prime, lines 1095--1107. -/
theorem ker_hamiltonian_restrict_parentChainInteraction_eq_of_local_kernel (A : MPSTensor d D)
    {R W N n : ℕ}
    (hR : 0 < R) (hRW : R ≤ W) (hWn : W ≤ n) (hnN : n ≤ N)
    (hker : LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A R W).hamiltonian) =
        groundSpaceES A W) :
    LinearMap.ker
        (Matrix.toEuclideanLin
            ((parentChainInteraction A R N).restrict fun i ↦ n - W ≤ i.val ∧ i.val + R ≤
                n).hamiltonian) =
      LinearMap.ker
          (Matrix.toEuclideanLin
              ((parentChainInteraction A W N).restrict fun i ↦ n - W ≤ i.val ∧ i.val + W ≤
                  n).hamiltonian) := by
  ext v
  let U := cyclicActiveBlockConfigLinearIsometryEquiv d W (hWn.trans hnN) ⟨n - W, by omega⟩
  have hconj (T : ℕ) (hT : 0 < T) (hTW : T ≤ W) :
      U (Matrix.toEuclideanLin
          ((parentChainInteraction A T N).restrict fun i ↦ n - W ≤ i.val ∧ i.val + T ≤
              n).hamiltonian v) =
        ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - W))
          (Matrix.toEuclideanLin (parentChainInteraction A T W).hamiltonian).toContinuousLinearMap
              (U v) := by
    simpa only [U, LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.symm_apply_apply] using
      LinearMap.congr_fun (hamiltonian_restrict_parentChainInteraction_conj_cyclicActiveBlock
        A hT hTW hWn hnN) (U v)
  rw [LinearMap.mem_ker, ← U.map_eq_zero_iff, hconj R hR hRW,
    LinearMap.mem_ker, ← U.map_eq_zero_iff, hconj W (hR.trans_le hRW) le_rfl]
  change U v ∈ LinearMap.ker
    (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - W))
      (Matrix.toEuclideanLin
          (parentChainInteraction A R W).hamiltonian).toContinuousLinearMap).toLinearMap ↔
    U v ∈ LinearMap.ker
    (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - W))
      (Matrix.toEuclideanLin
          (parentChainInteraction A W W).hamiltonian).toContinuousLinearMap).toLinearMap
  rw [ContinuousLinearMap.mem_ker_rightFiberwiseMap_iff,
    ContinuousLinearMap.mem_ker_rightFiberwiseMap_iff, LinearMap.coe_toContinuousLinearMap,
    hker, hamiltonian_parentChainInteraction_self, toEuclideanLin_toMatrix'_parentInteraction]
  simp only [LinearMap.coe_toContinuousLinearMap,
    Submodule.ker_starProjection, Submodule.orthogonal_orthogonal]
/-- The kernel of a terminal interval Hamiltonian is the reassociated tail
boundary space whenever its active finite-interval kernel is the MPS ground
space. Source: Nachtergaele, arXiv:cond-mat/9410110, condition C3-prime,
lines 1095--1107. -/
theorem ker_hamiltonian_restrict_parentChainInteraction_eq_range_reassocTailBoundaryMapES
    (A : MPSTensor d D) {R K L Q : ℕ}
    (hR : 0 < R) (hRW : R ≤ L + Q)
    (hker : LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A R (L + Q)).hamiltonian) =
      groundSpaceES A (L + Q)) :
    LinearMap.ker
        (Matrix.toEuclideanLin
            ((parentChainInteraction A R (K + L + Q)).restrict fun i ↦ K + L + Q - (L + Q) ≤ i.val ∧
                i.val + R ≤ K + L + Q).hamiltonian) =
                    (reassocTailBoundaryMapES A K L Q).range := by
  simpa only [ker_hamiltonian_restrict_parentChainInteraction_eq_of_local_kernel
    A hR hRW (by omega : L + Q ≤ K + L + Q) le_rfl hker] using
    (range_reassocTailBoundaryMapES_eq_ker_hamiltonian_restrict_parentChainInteraction
      A (hR.trans_le hRW)).symm
end MPSTensor

end IntervalKernelTransport
