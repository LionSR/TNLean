/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyCommutator
import TNLean.Lattice.LowEnergyBasisIteration

/-!
# The sum of the low-energy commutators over all terms

Hastings, *Solving gapped Hamiltonians locally*, arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 1689–1694, sums the bound
`o(i) ≤ ‖[P M_i P, P M_j P]‖ / δλ_j` over all `i`: by eq. `blecm` the commutator decays
exponentially in `d(i, j)`, so `∑_i o(i) ≤ O(J² / (c₁ l ΔE δλ_j))` independently of the system
size (eq. `oibu`).

The compression `P M_i P` of a filtered term equals that of `h_i` for every `q ≥ 0`
(`groundCompression_gaussianFilteredTerm`), so the graph form of eq. `blecm` may be applied to
each pair with its own time window. When `X_i` is disjoint from the sites within distance `l` of
`X_j`, the choice `T = l / (4v)` and `q = T ΔE`, with `v = 2 v_R |b₀| e^{2R} + 1`, makes every
term decay as `e^{-γ l}` with `γ = min (1/4) (ΔE / (8v))`. In terms of the anchors `a_i ∈ X_i`
the separation is at least `d(a_j, a_i) - 2R - 1`. Grouping the terms by their anchor, the
norm budget `b₀` of each site and the polynomial growth of the graph spheres bound the sum over
`i` by a constant that does not depend on the number of sites or terms.

## Main results

* `add_one_pow_mul_exp_neg_le`, `sum_add_one_pow_mul_exp_neg_le`,
  `sum_exp_neg_edist_le`: shell sums at any rate `γ > 0`.
* `norm_groundCompression_commutator_le_exp`: eq. `blecm` with an exponential rate in the
  separation `l`.
* `norm_groundCompression_commutator_le_exp_edist`: the same in the distance of the anchors.
* `sum_norm_groundCompression_commutator_le`: the sum over all terms.
* `sum_norm_offDiagonalPartFamily_le_oibu`: eq. `oibu`, the sum of the off-diagonal parts in an
  eigenbasis of `P M_j P`.
-/

open GaussianFilter Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator InnerProductSpace Nat Topology

namespace TNLean.Lattice

section ShellSums

/-- **A power against an exponential at rate `γ`.** For `γ > 0` and `x ≥ 0`,
`(x + 1)^k e^{-γ x} ≤ k! (2/γ)^k e^{γ/2} e^{-(γ/2) x}`. -/
theorem add_one_pow_mul_exp_neg_le {γ : ℝ} (hγ : 0 < γ) (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (x + 1) ^ k * Real.exp (-(γ * x)) ≤
      k ! * (2 / γ) ^ k * Real.exp (γ / 2) * Real.exp (-(γ / 2 * x)) := by
  have hfac : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  have h := Real.pow_div_factorial_le_exp (x := γ * (x + 1) / 2) (by positivity) k
  rw [div_le_iff₀ hfac] at h
  have hpow : (x + 1) ^ k = (2 / γ) ^ k * (γ * (x + 1) / 2) ^ k := by
    rw [← mul_pow]
    congr 1
    field_simp
  calc (x + 1) ^ k * Real.exp (-(γ * x))
      = (2 / γ) ^ k * (γ * (x + 1) / 2) ^ k * Real.exp (-(γ * x)) := by rw [hpow]
    _ ≤ (2 / γ) ^ k * (Real.exp (γ * (x + 1) / 2) * k !) * Real.exp (-(γ * x)) := by
        gcongr
    _ = k ! * (2 / γ) ^ k * Real.exp (γ / 2) * Real.exp (-(γ / 2 * x)) := by
        rw [show γ * (x + 1) / 2 = γ / 2 + γ / 2 * x by ring, Real.exp_add]
        have : Real.exp (γ / 2 * x) * Real.exp (-(γ * x)) = Real.exp (-(γ / 2 * x)) := by
          rw [← Real.exp_add]; ring_nf
        calc (2 / γ) ^ k * (Real.exp (γ / 2) * Real.exp (γ / 2 * x) * k !) *
              Real.exp (-(γ * x))
            = k ! * (2 / γ) ^ k * Real.exp (γ / 2) *
                (Real.exp (γ / 2 * x) * Real.exp (-(γ * x))) := by ring
          _ = _ := by rw [this]

/-- The constant `S_{γ,k} = k! (2/γ)^k e^{γ/2} / (1 - e^{-γ/2})` bounding
`∑_{d ≥ 0} (d + 1)^k e^{-γ d}`. -/
noncomputable def shellSumConst (γ : ℝ) (k : ℕ) : ℝ :=
  k ! * (2 / γ) ^ k * Real.exp (γ / 2) / (1 - Real.exp (-(γ / 2)))

theorem shellSumConst_nonneg {γ : ℝ} (hγ : 0 < γ) (k : ℕ) : 0 ≤ shellSumConst γ k := by
  have h1 : Real.exp (-(γ / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  unfold shellSumConst
  have : 0 < 1 - Real.exp (-(γ / 2)) := by linarith
  positivity

/-- **Shell sum at rate `γ`.** For every finite set `T` of natural numbers,
`∑_{d ∈ T} (d + 1)^k e^{-γ d} ≤ S_{γ,k}`. -/
theorem sum_add_one_pow_mul_exp_neg_le {γ : ℝ} (hγ : 0 < γ) (k : ℕ) (T : Finset ℕ) :
    ∑ d ∈ T, ((d : ℝ) + 1) ^ k * Real.exp (-(γ * d)) ≤ shellSumConst γ k := by
  set r := Real.exp (-(γ / 2)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  set M : ℝ := k ! * (2 / γ) ^ k * Real.exp (γ / 2) with hM
  have hM0 : 0 ≤ M := by positivity
  have hterm (d : ℕ) : ((d : ℝ) + 1) ^ k * Real.exp (-(γ * d)) ≤ M * r ^ d := by
    have hrd : r ^ d = Real.exp (-(γ / 2 * d)) := by
      rw [hr, ← Real.exp_nat_mul]; ring_nf
    rw [hrd]
    exact add_one_pow_mul_exp_neg_le hγ k (Nat.cast_nonneg d)
  obtain ⟨m, hm⟩ : ∃ m, T ⊆ Finset.range m :=
    ⟨T.sup id + 1, fun d hd => Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Finset.le_sup (f := id) hd))⟩
  calc _ ≤ ∑ d ∈ T, M * r ^ d := Finset.sum_le_sum fun d _ => hterm d
    _ ≤ ∑ d ∈ Finset.range m, M * r ^ d :=
      Finset.sum_le_sum_of_subset_of_nonneg hm fun d _ _ => by positivity
    _ = M * ∑ d ∈ Finset.range m, r ^ d := (Finset.mul_sum _ _ _).symm
    _ ≤ M * (1 / (1 - r)) := by
        gcongr
        have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := m) hr0 hr1
        rw [pow_zero] at h
        rw [Finset.range_eq_Ico]
        exact h
    _ = shellSumConst γ k := by rw [shellSumConst, hM, hr]; ring

/-- **Exponential decay summed over the sites.** If the sphere of radius `d` about `x` has at
most `K_g (d + 1)^k` sites, then `∑_y e^{-γ d(x, y)}` over the sites at finite distance is at
most `K_g S_{γ,k}`. -/
theorem sum_exp_neg_edist_le {ι : Type*} [Fintype ι] (G : SimpleGraph ι) (x : ι) (Kg : ℝ)
    (kg : ℕ) (hGrowth : ∀ d : ℕ,
      ((Finset.univ.filter fun y => G.edist x y = d).card : ℝ) ≤ Kg * ((d : ℝ) + 1) ^ kg)
    {γ : ℝ} (hγ : 0 < γ) :
    ∑ y ∈ Finset.univ.filter (fun y => G.edist x y ≠ ⊤),
      Real.exp (-(γ * ((G.edist x y).toNat : ℝ))) ≤ Kg * shellSumConst γ kg := by
  classical
  have hKg : 0 ≤ Kg := by
    have := hGrowth 0
    simp only [CharP.cast_eq_zero, zero_add, one_pow, mul_one] at this
    exact (Nat.cast_nonneg _).trans this
  set S := Finset.univ.filter fun y => G.edist x y ≠ ⊤
  set D : ι → ℕ := fun y => (G.edist x y).toNat
  have hfib : ∀ d ∈ S.image D, ((S.filter fun y => D y = d).card : ℝ) ≤
      Kg * ((d : ℝ) + 1) ^ kg := by
    intro d _
    refine le_trans ?_ (hGrowth d)
    exact_mod_cast Finset.card_le_card fun y hy => by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [← hy.2]
      exact (ENat.natCast_toNat hy.1).symm
  calc ∑ y ∈ S, Real.exp (-(γ * (D y : ℝ)))
      = ∑ d ∈ S.image D, ∑ y ∈ S.filter (fun y => D y = d), Real.exp (-(γ * (D y : ℝ))) :=
        (Finset.sum_fiberwise_of_maps_to (fun y hy => Finset.mem_image_of_mem D hy) _).symm
    _ = ∑ d ∈ S.image D, ((S.filter fun y => D y = d).card : ℝ) * Real.exp (-(γ * d)) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_congr rfl fun y hy => by rw [(Finset.mem_filter.mp hy).2],
          Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ d ∈ S.image D, Kg * ((d : ℝ) + 1) ^ kg * Real.exp (-(γ * d)) :=
        Finset.sum_le_sum fun d hd =>
          mul_le_mul_of_nonneg_right (hfib d hd) (Real.exp_pos _).le
    _ = Kg * ∑ d ∈ S.image D, ((d : ℝ) + 1) ^ kg * Real.exp (-(γ * d)) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun d _ => by ring
    _ ≤ Kg * shellSumConst γ kg :=
        mul_le_mul_of_nonneg_left (sum_add_one_pow_mul_exp_neg_le hγ kg _) hKg

end ShellSums

section Compression

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The compression of an operator to the ground space has norm at most that of the operator. -/
theorem norm_groundCompression_le (H : Matrix n n ℂ) (E₀ : ℝ) (W : Matrix n n ℂ) :
    ‖groundCompression H E₀ W‖ ≤ ‖W‖ := by
  set P := (groundEigenspace H E₀).starProjection
  have hP : ‖P‖ ≤ 1 := (groundEigenspace H E₀).starProjection_norm_le
  calc ‖groundCompression H E₀ W‖ ≤ ‖P‖ * ‖toEuclideanCLM (n := n) (𝕜 := ℂ) W‖ * ‖P‖ := by
        unfold groundCompression
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
          (norm_nonneg _))
    _ ≤ 1 * ‖W‖ * 1 := by
        rw [l2_opNorm_toEuclideanCLM]
        gcongr
    _ = ‖W‖ := by ring

/-- The commutator of two compressions has norm at most `2 ‖W‖ ‖B‖`. -/
theorem norm_groundCompression_commutator_le_two_mul (H : Matrix n n ℂ) (E₀ : ℝ)
    (W B : Matrix n n ℂ) :
    ‖groundCompression H E₀ W * groundCompression H E₀ B -
        groundCompression H E₀ B * groundCompression H E₀ W‖ ≤ 2 * ‖W‖ * ‖B‖ := by
  have hW := norm_groundCompression_le H E₀ W
  have hB := norm_groundCompression_le H E₀ B
  calc _ ≤ ‖groundCompression H E₀ W * groundCompression H E₀ B‖ +
        ‖groundCompression H E₀ B * groundCompression H E₀ W‖ := norm_sub_le _ _
    _ ≤ ‖W‖ * ‖B‖ + ‖B‖ * ‖W‖ := by
        gcongr
        · exact (norm_mul_le _ _).trans (mul_le_mul hW hB (norm_nonneg _) (norm_nonneg _))
        · exact (norm_mul_le _ _).trans (mul_le_mul hB hW (norm_nonneg _) (norm_nonneg _))
    _ = 2 * ‖W‖ * ‖B‖ := by ring

/-- The compression of a Hermitian matrix to the ground space is self-adjoint. -/
theorem isSelfAdjoint_groundCompression (H : Matrix n n ℂ) (E₀ : ℝ) {W : Matrix n n ℂ}
    (hW : W.IsHermitian) : IsSelfAdjoint (groundCompression H E₀ W) := by
  have hT : IsSelfAdjoint (toEuclideanCLM (n := n) (𝕜 := ℂ) W) :=
    (hW.isSelfAdjoint).map toEuclideanCLM
  unfold groundCompression
  exact hT.conjugate_self (isSelfAdjoint_starProjection _)

end Compression

section Graph

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
  (G : SimpleGraph ι) (X : κ → Finset ι) (a : κ → ι) (ha : ∀ k, a k ∈ X k)
  (h : κ → Matrix (ι → Fin d) (ι → Fin d) ℂ) (hHerm : ∀ k, (h k).IsHermitian)
  (hSupport : ∀ k, h k ∈ supportedOperators d (X k : Set ι))
  (R : ℕ) (hDiam : ∀ k, ∀ x ∈ X k, ∀ z ∈ X k, G.edist x z ≤ R)
  (vR : ℕ) (hCard : ∀ k, (X k).card ≤ vR)
  (b₀ : ℝ) (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ X j), ‖h j‖ ≤ b₀)

/-- The Lieb–Robinson velocity `v = 2 v_R |b₀| e^{2R} + 1` of the terms. -/
noncomputable def lrVelocity (R vR : ℕ) (b₀ : ℝ) : ℝ :=
  2 * vR * |b₀| * Real.exp (2 * R) + 1

theorem one_le_lrVelocity (R vR : ℕ) (b₀ : ℝ) : 1 ≤ lrVelocity R vR b₀ := by
  unfold lrVelocity
  have : 0 ≤ 2 * (vR : ℝ) * |b₀| * Real.exp (2 * R) := by positivity
  linarith

/-- The decay rate `γ = min (1/4) (ΔE / (8 v))` of the low-energy commutators. -/
noncomputable def commutatorRate (R vR : ℕ) (b₀ ΔE : ℝ) : ℝ :=
  min (1 / 4) (ΔE / (8 * lrVelocity R vR b₀))

theorem commutatorRate_pos {ΔE : ℝ} (hΔE : 0 < ΔE) (R vR : ℕ) (b₀ : ℝ) :
    0 < commutatorRate R vR b₀ ΔE := by
  have := one_le_lrVelocity R vR b₀
  exact lt_min (by norm_num) (by positivity)

/-- The constant `2 (2 + 4 |b₀| e^{2R}) v_R² K_g C_k + 6` of the pairwise bound, with
`C_k = 2^k k! e^{1/2} / (1 - e^{-1/2})` the shell constant of the Lieb–Robinson estimate. -/
noncomputable def commutatorConst (R vR : ℕ) (b₀ Kg : ℝ) (kg : ℕ) : ℝ :=
  2 * (2 + 4 * |b₀| * Real.exp (2 * R)) * (vR : ℝ) ^ 2 * Kg *
    (2 ^ kg * kg ! * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))) + 6

theorem six_le_commutatorConst (R vR : ℕ) (b₀ : ℝ) {Kg : ℝ} (hKg : 0 ≤ Kg) (kg : ℕ) :
    6 ≤ commutatorConst R vR b₀ Kg kg := by
  have h1 : Real.exp (-(1 / 2 : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have h2 : 0 < 1 - Real.exp (-(1 / 2 : ℝ)) := by linarith
  unfold commutatorConst
  have : 0 ≤ 2 * (2 + 4 * |b₀| * Real.exp (2 * R)) * (vR : ℝ) ^ 2 * Kg *
      (2 ^ kg * kg ! * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))) := by positivity
  linarith

omit [Fintype κ] in
include ha hDiam in
/-- If the anchors of two terms are at graph distance more than `2R + l`, then the second term
is disjoint from the sites within distance `l` of the first. -/
theorem disjoint_biUnion_graphBall_of_lt_edist (i j : κ) (l : ℕ)
    (hlt : ((2 * R + l : ℕ) : ℕ∞) < G.edist (a j) (a i)) :
    Disjoint (((X j).biUnion fun x => graphBall G x l : Finset ι) : Set ι) (X i) := by
  rw [Set.disjoint_left]
  intro y hy hyi
  simp only [Finset.coe_biUnion, Finset.mem_coe, Set.mem_iUnion, exists_prop] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  have hxy' := mem_graphBall.mp hxy
  have h1 := hDiam j (a j) (ha j) x hx
  have h2 := hDiam i y (Finset.mem_coe.mp hyi) (a i) (ha i)
  have htri : G.edist (a j) (a i) ≤ G.edist (a j) x + G.edist x y + G.edist y (a i) :=
    calc G.edist (a j) (a i) ≤ G.edist (a j) y + G.edist y (a i) := SimpleGraph.edist_triangle
      _ ≤ G.edist (a j) x + G.edist x y + G.edist y (a i) := by
          gcongr
          exact SimpleGraph.edist_triangle
  have : G.edist (a j) (a i) ≤ ((2 * R + l : ℕ) : ℕ∞) := by
    refine htri.trans ?_
    calc G.edist (a j) x + G.edist x y + G.edist y (a i) ≤ (R : ℕ∞) + l + R := by
          gcongr
      _ = ((2 * R + l : ℕ) : ℕ∞) := by push_cast; ring
  exact absurd hlt (not_lt.mpr this)

include ha hHerm hSupport hDiam hCard hBudget

/-- **Eq. `blecm` with an exponential rate.** Let every eigenvalue of `H = ∑ₖ hₖ` equal `E₀` or
be at least `E₀ + ΔE`, and let `X_i` be disjoint from the sites within graph distance `l` of
`X_j`. Then `‖[P h_j P, P h_i P]‖ ≤ C ‖h_j‖ ‖h_i‖ e^{-γ l}`, with `C = commutatorConst` and
`γ = commutatorRate`. The time window `T = l / (4v)` and `q = T ΔE` of the Gaussian filter are
chosen for the pair, which is allowed because the compression of a filtered term does not depend
on `q`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `blecm` (lines 1562–1601). -/
theorem norm_groundCompression_commutator_le_exp [NeZero d] (Kg : ℝ) (kg : ℕ)
    (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {ΔE : ℝ} (hΔE : 0 < ΔE) (hH : (∑ k, h k).IsHermitian) {E₀ : ℝ}
    (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + ΔE ≤ hH.eigenvalues k) (i j : κ) (l : ℕ)
    (hY : Disjoint (((X j).biUnion fun x => graphBall G x l : Finset ι) : Set ι) (X i)) :
    ‖groundCompression (∑ k, h k) E₀ (h j) * groundCompression (∑ k, h k) E₀ (h i) -
        groundCompression (∑ k, h k) E₀ (h i) * groundCompression (∑ k, h k) E₀ (h j)‖ ≤
      commutatorConst R vR b₀ Kg kg * ‖h j‖ * ‖h i‖ *
        Real.exp (-(commutatorRate R vR b₀ ΔE * l)) := by
  have hKg : 0 ≤ Kg := by
    have := hGrowth (a i) 0
    simp only [CharP.cast_eq_zero, zero_add, one_pow, mul_one] at this
    exact (Nat.cast_nonneg _).trans this
  set v := lrVelocity R vR b₀ with hv
  have hv1 : 1 ≤ v := one_le_lrVelocity R vR b₀
  set γ := commutatorRate R vR b₀ ΔE with hγ
  set T : ℝ := l / (4 * v) with hT
  have hT0 : 0 ≤ T := by positivity
  set q : ℝ := T * ΔE with hq
  have hq0 : 0 ≤ q := by positivity
  have hb := norm_groundCompression_commutator_le_graphNeighborhood G X a ha h hHerm hSupport R
    hDiam vR hCard b₀ hBudget Kg kg hGrowth hq0 hΔE hH hgap (X j) (hSupport j) l (X i : Set ι)
    hY (hSupport i) hT0
  set A : ℝ := 2 + 4 * |b₀| * Real.exp (2 * R)
  set Ck : ℝ := 2 ^ kg * kg ! * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))
  have hA : 0 ≤ A := by positivity
  have hCk : 0 ≤ Ck := by
    have h1 : Real.exp (-(1 / 2 : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    have : 0 < 1 - Real.exp (-(1 / 2 : ℝ)) := by linarith
    positivity
  have hW := norm_nonneg (h j)
  have hB := norm_nonneg (h i)
  have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  -- The three exponentials.
  have e1 : Real.exp ((2 * vR * |b₀| * Real.exp (2 * R) + 1) * T - l / 2) ≤
      Real.exp (-(γ * l)) := by
    apply Real.exp_le_exp.mpr
    have hvT : (2 * vR * |b₀| * Real.exp (2 * R) + 1) * T = l / 4 := by
      rw [hT, show (2 * (vR : ℝ) * |b₀| * Real.exp (2 * R) + 1) = v from rfl]
      field_simp
    have hγ4 : γ ≤ 1 / 4 := min_le_left _ _
    rw [hvT]
    nlinarith
  have hqT : (T * ΔE) ^ 2 / (2 * q) = q / 2 := by
    rw [hq]
    rcases eq_or_ne (T * ΔE) 0 with h0 | h0
    · rw [h0]; simp
    · field_simp
  have e2 : Real.exp (-(T * ΔE) ^ 2 / (2 * q)) ≤ Real.exp (-(γ * l)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, hqT]
    have hq8 : q / 2 = ΔE / (8 * v) * l := by
      rw [hq, hT]; field_simp; ring
    have hγ8 : γ ≤ ΔE / (8 * v) := min_le_right _ _
    rw [hq8]
    nlinarith
  have e3 : Real.exp (-q / 2) ≤ Real.exp (-(γ * l)) := by
    apply Real.exp_le_exp.mpr
    have hq8 : q / 2 = ΔE / (8 * v) * l := by
      rw [hq, hT]; field_simp; ring
    have hγ8 : γ ≤ ΔE / (8 * v) := min_le_right _ _
    rw [neg_div, hq8]
    nlinarith
  have hS : ((X j).card : ℝ) ^ 2 ≤ (vR : ℝ) ^ 2 := by
    have : ((X j).card : ℝ) ≤ vR := by exact_mod_cast hCard j
    gcongr
  set E := Real.exp (-(γ * l))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  refine hb.trans ?_
  calc 2 * ‖h i‖ * (A * ((X j).card : ℝ) ^ 2 * ‖h j‖ * Kg * Ck *
          Real.exp ((2 * vR * |b₀| * Real.exp (2 * R) + 1) * T - l / 2) +
        2 * ‖h j‖ * Real.exp (-(T * ΔE) ^ 2 / (2 * q))) +
        2 * ‖h j‖ * ‖h i‖ * Real.exp (-q / 2)
      ≤ 2 * ‖h i‖ * (A * (vR : ℝ) ^ 2 * ‖h j‖ * Kg * Ck * E + 2 * ‖h j‖ * E) +
        2 * ‖h j‖ * ‖h i‖ * E := by
        gcongr
    _ = commutatorConst R vR b₀ Kg kg * ‖h j‖ * ‖h i‖ * E := by
        unfold commutatorConst
        ring

/-- **Eq. `blecm` in the distance of the anchors.** If the anchors `a_j`, `a_i` are at finite
graph distance `D`, then `‖[P h_j P, P h_i P]‖ ≤ C e^{γ(2R+1)} ‖h_j‖ ‖h_i‖ e^{-γ D}`; at
infinite distance the commutator vanishes. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
eq. `blecm` (lines 1562–1601). -/
theorem norm_groundCompression_commutator_le_exp_edist [NeZero d] (Kg : ℝ) (kg : ℕ)
    (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {ΔE : ℝ} (hΔE : 0 < ΔE) (hH : (∑ k, h k).IsHermitian) {E₀ : ℝ}
    (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + ΔE ≤ hH.eigenvalues k) (i j : κ) :
    ‖groundCompression (∑ k, h k) E₀ (h j) * groundCompression (∑ k, h k) E₀ (h i) -
        groundCompression (∑ k, h k) E₀ (h i) * groundCompression (∑ k, h k) E₀ (h j)‖ ≤
      commutatorConst R vR b₀ Kg kg * Real.exp (commutatorRate R vR b₀ ΔE * (2 * R + 1)) *
        ‖h j‖ * ‖h i‖ *
        (if G.edist (a j) (a i) = ⊤ then 0 else
          Real.exp (-(commutatorRate R vR b₀ ΔE * ((G.edist (a j) (a i)).toNat : ℝ)))) := by
  have hKg : 0 ≤ Kg := by
    have := hGrowth (a i) 0
    simp only [CharP.cast_eq_zero, zero_add, one_pow, mul_one] at this
    exact (Nat.cast_nonneg _).trans this
  set γ := commutatorRate R vR b₀ ΔE
  have hγ : 0 < γ := commutatorRate_pos hΔE R vR b₀
  set C := commutatorConst R vR b₀ Kg kg
  have hC6 : 6 ≤ C := six_le_commutatorConst R vR b₀ hKg kg
  set N := ‖groundCompression (∑ k, h k) E₀ (h j) * groundCompression (∑ k, h k) E₀ (h i) -
    groundCompression (∑ k, h k) E₀ (h i) * groundCompression (∑ k, h k) E₀ (h j)‖
  have hpair (l : ℕ) (hlt : ((2 * R + l : ℕ) : ℕ∞) < G.edist (a j) (a i)) :
      N ≤ C * ‖h j‖ * ‖h i‖ * Real.exp (-(γ * l)) :=
    norm_groundCompression_commutator_le_exp G X a ha h hHerm hSupport R hDiam vR hCard b₀
      hBudget Kg kg hGrowth hΔE hH hgap i j l
      (disjoint_biUnion_graphBall_of_lt_edist G X a ha R hDiam i j l hlt)
  have hW := norm_nonneg (h j)
  have hB := norm_nonneg (h i)
  split_ifs with htop
  · -- At infinite distance the bound holds for every `l`, so the commutator vanishes.
    rw [mul_zero]
    have hlim : Filter.Tendsto (fun l : ℕ => C * ‖h j‖ * ‖h i‖ * Real.exp (-(γ * l)))
        Filter.atTop (𝓝 0) := by
      have h1 : Filter.Tendsto (fun l : ℕ => γ * (l : ℝ)) Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop hγ tendsto_natCast_atTop_atTop
      have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul (C * ‖h j‖ * ‖h i‖)
      simpa [Function.comp_def] using h2
    exact ge_of_tendsto' hlim fun l => hpair l (by rw [htop]; exact ENat.natCast_lt_top _)
  · set D := (G.edist (a j) (a i)).toNat
    have hD : G.edist (a j) (a i) = (D : ℕ∞) := (ENat.natCast_toNat htop).symm
    by_cases hfar : 2 * R + 1 < D
    · -- Far apart: the separation `l = D - 2R - 1` gives the decay.
      have hl := hpair (D - (2 * R + 1)) (by rw [hD]; exact_mod_cast (by omega))
      refine hl.trans (le_of_eq ?_)
      have hcast : ((D - (2 * R + 1) : ℕ) : ℝ) = (D : ℝ) - (2 * R + 1) := by
        rw [Nat.cast_sub hfar.le]; push_cast; ring
      rw [hcast, show -(γ * ((D : ℝ) - (2 * R + 1))) = γ * (2 * R + 1) + -(γ * D) by ring,
        Real.exp_add]
      ring
    · -- Near: the trivial bound `2 ‖h_j‖ ‖h_i‖`.
      push Not at hfar
      have hexp : 1 ≤ Real.exp (γ * (2 * R + 1)) * Real.exp (-(γ * D)) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp
        have : (D : ℝ) ≤ 2 * R + 1 := by exact_mod_cast hfar
        nlinarith
      calc N ≤ 2 * ‖h j‖ * ‖h i‖ := norm_groundCompression_commutator_le_two_mul _ _ _ _
        _ ≤ C * ‖h j‖ * ‖h i‖ * 1 := by
            rw [mul_one]
            have : 0 ≤ ‖h j‖ * ‖h i‖ := mul_nonneg hW hB
            nlinarith
        _ ≤ C * ‖h j‖ * ‖h i‖ * (Real.exp (γ * (2 * R + 1)) * Real.exp (-(γ * D))) := by
            gcongr
        _ = _ := by ring

/-- **The sum of the low-energy commutators over all terms.** Let every eigenvalue of
`H = ∑ₖ hₖ` equal `E₀` or be at least `E₀ + ΔE`, and let the spheres of the graph grow at most
polynomially, `|{y : d(x, y) = r}| ≤ K_g (r + 1)^k`. Then for every term `j`,
`∑_i ‖[P h_j P, P h_i P]‖ ≤ C e^{γ(2R+1)} |b₀| K_g S_{γ,k} ‖h_j‖`, a bound independent of the
number of sites and of terms. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1689–1694: summing the decay of eq. `blecm` over all `i`. -/
theorem sum_norm_groundCompression_commutator_le [NeZero d] (Kg : ℝ) (kg : ℕ)
    (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {ΔE : ℝ} (hΔE : 0 < ΔE) (hH : (∑ k, h k).IsHermitian) {E₀ : ℝ}
    (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + ΔE ≤ hH.eigenvalues k) (j : κ) :
    ∑ i, ‖groundCompression (∑ k, h k) E₀ (h j) * groundCompression (∑ k, h k) E₀ (h i) -
        groundCompression (∑ k, h k) E₀ (h i) * groundCompression (∑ k, h k) E₀ (h j)‖ ≤
      commutatorConst R vR b₀ Kg kg * Real.exp (commutatorRate R vR b₀ ΔE * (2 * R + 1)) *
        ‖h j‖ * (|b₀| * (Kg * shellSumConst (commutatorRate R vR b₀ ΔE) kg)) := by
  classical
  set γ := commutatorRate R vR b₀ ΔE
  have hγ : 0 < γ := commutatorRate_pos hΔE R vR b₀
  have hKg : 0 ≤ Kg := by
    have := hGrowth (a j) 0
    simp only [CharP.cast_eq_zero, zero_add, one_pow, mul_one] at this
    exact (Nat.cast_nonneg _).trans this
  set C := commutatorConst R vR b₀ Kg kg * Real.exp (γ * (2 * R + 1)) * ‖h j‖
  have hC : 0 ≤ C := by
    have := six_le_commutatorConst R vR b₀ hKg kg
    have : 0 ≤ commutatorConst R vR b₀ Kg kg := by linarith
    positivity
  set w : ι → ℝ := fun x => if G.edist (a j) x = ⊤ then 0 else
    Real.exp (-(γ * ((G.edist (a j) x).toNat : ℝ)))
  have hw0 (x : ι) : 0 ≤ w x := by
    simp only [w]; split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
  -- Each term is at most `C ‖h_i‖ w(a_i)`.
  have hterm (i : κ) :
      ‖groundCompression (∑ k, h k) E₀ (h j) * groundCompression (∑ k, h k) E₀ (h i) -
        groundCompression (∑ k, h k) E₀ (h i) * groundCompression (∑ k, h k) E₀ (h j)‖ ≤
        C * (‖h i‖ * w (a i)) := by
    refine (norm_groundCompression_commutator_le_exp_edist G X a ha h hHerm hSupport R hDiam vR
      hCard b₀ hBudget Kg kg hGrowth hΔE hH hgap i j).trans (le_of_eq ?_)
    simp only [C, w]
    ring
  -- Group the terms by their anchor and use the norm budget of each site.
  have hgroup : ∑ i, ‖h i‖ * w (a i) ≤ ∑ x, |b₀| * w x := by
    calc ∑ i, ‖h i‖ * w (a i)
        = ∑ x, ∑ i ∈ Finset.univ.filter (fun i => a i = x), ‖h i‖ * w (a i) :=
          (Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_univ (a i)) _).symm
      _ = ∑ x, (∑ i ∈ Finset.univ.filter (fun i => a i = x), ‖h i‖) * w x := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]
      _ ≤ ∑ x, |b₀| * w x := by
          refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right ?_ (hw0 x)
          refine le_trans ?_ ((hBudget x).trans (le_abs_self b₀))
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (fun i hi => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
              rw [← hi]; exact ha i)
            fun i _ _ => norm_nonneg _
  have hsites : ∑ x, w x ≤ Kg * shellSumConst γ kg := by
    have hsplit : ∑ x, w x = ∑ x ∈ Finset.univ.filter (fun x => G.edist (a j) x ≠ ⊤),
        Real.exp (-(γ * ((G.edist (a j) x).toNat : ℝ))) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [w]
      split_ifs <;> simp_all
    rw [hsplit]
    exact sum_exp_neg_edist_le G (a j) Kg kg (hGrowth (a j)) hγ
  calc _ ≤ ∑ i, C * (‖h i‖ * w (a i)) := Finset.sum_le_sum fun i _ => hterm i
    _ = C * ∑ i, ‖h i‖ * w (a i) := (Finset.mul_sum _ _ _).symm
    _ ≤ C * ∑ x, |b₀| * w x := mul_le_mul_of_nonneg_left hgroup hC
    _ = C * (|b₀| * ∑ x, w x) := by rw [← Finset.mul_sum]
    _ ≤ C * (|b₀| * (Kg * shellSumConst γ kg)) := by
        gcongr
    _ = _ := by simp only [C]

/-- **Eq. `oibu`.** In an orthonormal eigenbasis `v` of the compression `P M_j P` of the filtered
term `M_j`, with eigenvalues pairwise at least `δ > 0` apart, the off-diagonal parts of the
compressions `P M_i P` of all filtered terms satisfy
`∑_i o(i) ≤ (n - 1) C e^{γ(2R+1)} |b₀| K_g S_{γ,k} ‖h_j‖ / δ`, independently of the number of
sites and terms. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `oibu`
(lines 1689–1694). -/
theorem sum_norm_offDiagonalPartFamily_le_oibu [NeZero d] (Kg : ℝ) (kg : ℕ)
    (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {q ΔE : ℝ} (hq : 0 ≤ q) (hΔE : 0 < ΔE) (hH : (∑ k, h k).IsHermitian) {E₀ : ℝ}
    (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + ΔE ≤ hH.eigenvalues k) (j : κ) {m : ℕ}
    [NeZero m] {v : Fin m → EuclideanSpace ℂ (ι → Fin d)} (hv : Orthonormal ℂ v)
    {r : Fin m → ℝ}
    (hAv : ∀ c, groundCompression (∑ k, h k) E₀ (gaussianFilteredTerm q ΔE (∑ k, h k) (h j))
      (v c) = (r c : ℂ) • v c) {δ : ℝ} (hδ : 0 < δ) (hgap' : ∀ c c', c ≠ c' → δ ≤ |r c - r c'|) :
    ∑ i, ‖offDiagonalPartFamily v
        (groundCompression (∑ k, h k) E₀ (gaussianFilteredTerm q ΔE (∑ k, h k) (h i)))‖ ≤
      (m - 1 : ℕ) * (commutatorConst R vR b₀ Kg kg *
        Real.exp (commutatorRate R vR b₀ ΔE * (2 * R + 1)) * ‖h j‖ *
          (|b₀| * (Kg * shellSumConst (commutatorRate R vR b₀ ΔE) kg)) / δ) := by
  simp only [groundCompression_gaussianFilteredTerm hq hH] at hAv ⊢
  refine (sum_norm_offDiagonalPartFamily_le Finset.univ
    (isSelfAdjoint_groundCompression _ E₀ (hHerm j)) _ hv hAv hδ hgap').trans ?_
  gcongr
  exact sum_norm_groundCompression_commutator_le G X a ha h hHerm hSupport R hDiam vR hCard b₀
    hBudget Kg kg hGrowth hΔE hH hgap j

/-- A compression to the ground space maps every vector into the ground space, so in an
orthonormal basis `v` of the ground space it is determined by its matrix elements. -/
theorem groundCompression_apply_eq_sum {E₀ : ℝ} {m : ℕ} {v : Fin m → EuclideanSpace ℂ (ι → Fin d)}
    (hspan : ∀ u ∈ groundEigenspace (∑ k, h k) E₀, u = ∑ c, ⟪v c, u⟫_ℂ • v c)
    (W : Matrix (ι → Fin d) (ι → Fin d) ℂ) (x : EuclideanSpace ℂ (ι → Fin d)) :
    groundCompression (∑ k, h k) E₀ W x =
      ∑ c, ⟪v c, groundCompression (∑ k, h k) E₀ W x⟫_ℂ • v c :=
  hspan _ ((groundEigenspace (∑ k, h k) E₀).starProjection_apply_mem _)

/-- **Eq. `oibu` for a degenerate ground space.** Let `v : Fin m → E` be an orthonormal basis of
the ground space, and record the source's iteration by labels `r ℓ` and the terms `j ℓ` whose
compressions `A ℓ = P h_{j ℓ} P` act diagonally on the classes of level `ℓ`, every pair of basis
vectors being separated below level `L` and every `j ℓ` being one of `j 0, …, j (L - 1)`. If all
terms have norm at most `J`, then the off-diagonal parts of the compressions of all filtered terms
satisfy `∑_i o(i) ≤ (m - 1) β_{L-1} ∑_{ℓ < L} C' ‖h_{j ℓ}‖`, where `β_{L-1} = levelBoundB` with
`K = 2 J²` and `K_B = 1`, and `C'` is the constant of `sum_norm_groundCompression_commutator_le`.
The bound does not depend on the number of sites or terms. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, eq. `oibu` (lines 1689–1694) and the iteration of lines 1695–1708. -/
theorem sum_norm_offDiagonalPartFamily_le_oibu_levels [NeZero d] (Kg : ℝ) (kg : ℕ)
    (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {q ΔE : ℝ} (hq : 0 ≤ q) (hΔE : 0 < ΔE) (hH : (∑ k, h k).IsHermitian) {E₀ : ℝ}
    (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + ΔE ≤ hH.eigenvalues k) {J : ℝ}
    (hJ : ∀ k, ‖h k‖ ≤ J) {m : ℕ} [NeZero m] {v : Fin m → EuclideanSpace ℂ (ι → Fin d)}
    (hv : Orthonormal ℂ v)
    (hspan : ∀ u ∈ groundEigenspace (∑ k, h k) E₀, u = ∑ c, ⟪v c, u⟫_ℂ • v c)
    {L : ℕ} (j : ℕ → κ) (hj : ∀ ℓ, ∃ ℓ' < L, j ℓ' = j ℓ) (r : ℕ → Fin m → ℝ)
    (hdiag : ∀ ℓ a, ∀ c ∈ labelClass r ℓ a, ∀ e ∈ labelClass r ℓ a,
      ⟪v c, groundCompression (∑ k, h k) E₀ (h (j ℓ)) (v e)⟫_ℂ =
        if c = e then (r ℓ c : ℂ) else 0)
    (hsep : ∀ a b, a ≠ b → ∃ ℓ < L, r ℓ a ≠ r ℓ b) :
    ∑ i, ‖offDiagonalPartFamily v
        (groundCompression (∑ k, h k) E₀ (gaussianFilteredTerm q ΔE (∑ k, h k) (h i)))‖ ≤
      (m - 1 : ℕ) * levelBoundB m r (2 * J ^ 2) 1 (L - 1) *
        ∑ ℓ ∈ Finset.range L, commutatorConst R vR b₀ Kg kg *
          Real.exp (commutatorRate R vR b₀ ΔE * (2 * R + 1)) * ‖h (j ℓ)‖ *
            (|b₀| * (Kg * shellSumConst (commutatorRate R vR b₀ ΔE) kg)) := by
  simp only [groundCompression_gaussianFilteredTerm hq hH]
  set A : ℕ → _ := fun ℓ => groundCompression (∑ k, h k) E₀ (h (j ℓ))
  set B : κ → _ := fun i => groundCompression (∑ k, h k) E₀ (h i)
  set KB : κ → ℝ := fun i => ∑ ℓ ∈ Finset.range L, ‖A ℓ * B i - B i * A ℓ‖
  have hKA : ∀ ℓ ℓ', ‖A ℓ * A ℓ' - A ℓ' * A ℓ‖ ≤ 2 * J ^ 2 := fun ℓ ℓ' => by
    refine (norm_groundCompression_commutator_le_two_mul _ E₀ _ _).trans ?_
    have h1 := hJ (j ℓ)
    have h2 := hJ (j ℓ')
    nlinarith [norm_nonneg (h (j ℓ)), norm_nonneg (h (j ℓ'))]
  have hKBB : ∀ i ℓ, ‖A ℓ * B i - B i * A ℓ‖ ≤ KB i := fun i ℓ => by
    obtain ⟨ℓ', hℓ', hjj⟩ := hj ℓ
    have hA : A ℓ = A ℓ' := by simp only [A, hjj]
    rw [hA]
    exact Finset.single_le_sum (f := fun ℓ => ‖A ℓ * B i - B i * A ℓ‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr hℓ')
  have h := sum_norm_offDiagonalPartFamily_le_levelBoundB A r hv
    (fun ℓ b => groundCompression_apply_eq_sum h hspan _ _) hdiag (by positivity) hKA
    Finset.univ B (fun i b => groundCompression_apply_eq_sum h hspan _ _) KB
    (fun i => Finset.sum_nonneg fun _ _ => norm_nonneg _) hKBB hsep
  refine h.trans ?_
  gcongr
  · exact mul_nonneg (Nat.cast_nonneg _)
      (levelBoundB_nonneg r (by positivity) zero_le_one _)
  · simp only [KB]
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun ℓ _ => sum_norm_groundCompression_commutator_le G X a ha h
      hHerm hSupport R hDiam vR hCard b₀ hBudget Kg kg hGrowth hΔE hH hgap (j ℓ)

end Graph

end TNLean.Lattice
