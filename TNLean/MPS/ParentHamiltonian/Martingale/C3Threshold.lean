/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.FNWContraction
import TNLean.MPS.ParentHamiltonian.Martingale.OpenChain
import TNLean.Wielandt.Primitivity.StronglyIrreducibleToFullRank

/-!
# The open-chain C3 threshold

This file chooses an overlap length, measured in sites of the input tensor, at which the
spectator-uniform geometric projector-defect estimate satisfies Nachtergaele's condition
C3. If the input tensor is already a blocked representative, one such site is one
blocked-chain filtration step.

## Main results

* `MPSTensor.IsPrimitiveMPS.exists_uniform_wholeIncrement_defect_le_seven_sixteenths`
  chooses one original-site scale uniformly for every prefix length.
* `MPSTensor.IsPrimitiveMPS.exists_threeBlock_wholeIncrement_defect_le_seven_sixteenths`
  specializes the uniform estimate to three equal original-site blocks.
* `MPSTensor.IsPrimitiveMPS.exists_openChain_groundProjection_defect_lt_c3_threshold`
  chooses a block-injective overlap length and one uniform C3 defect coefficient.
* `MPSTensor.IsPrimitiveMPS.exists_re_inner_openChain_anticommutator_ge_c3_threshold`
  gives the corresponding open-chain excitation-projection anticommutator estimate.

## References

* B. Nachtergaele, arXiv:cond-mat/9410110, eqs. (2.4)--(2.5), Theorem 3,
  and Section 6.
-/

open Filter
open scoped ComplexOrder InnerProductSpace Topology

namespace MPSTensor

variable {d D : ℕ}

private theorem groundSpaceESHasOrthogonalProjection
    (A : MPSTensor d D) (N : ℕ) : (groundSpaceES A N).HasOrthogonalProjection := by
  let : CompleteSpace (groundSpaceES A N) := FiniteDimensional.complete ℂ _
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

attribute [local instance] groundSpaceESHasOrthogonalProjection

private theorem tendsto_sqrt_succ_mul_pow_of_lt_one {r : ℝ}
    (hr : 0 ≤ r) (hr_lt_one : r < 1) :
    Tendsto (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) * r ^ n) atTop (𝓝 0) := by
  apply squeeze_zero
  · intro n
    positivity
  · intro n
    have hsqrt : Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      rw [Real.sqrt_le_self_iff]
      exact Or.inr (by norm_num [Nat.cast_add])
    exact mul_le_mul_of_nonneg_right hsqrt (pow_nonneg hr n)
  · simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, zero_add] using
      (tendsto_self_mul_const_pow_of_lt_one hr hr_lt_one).add
        (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr_lt_one)

private theorem tendsto_geometric_c3_coefficient_mul_sqrt
    {C c r : ℝ} (hr : 0 ≤ r) (hr_lt_one : r < 1) :
    Tendsto
      (fun n : ℕ =>
        (1 - c * r ^ n)⁻¹ * (C * r ^ n) * Real.sqrt ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
  have hr_pow : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr hr_lt_one
  have hden : Tendsto (fun n : ℕ => 1 - c * r ^ n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hr_pow)
  have hinv : Tendsto (fun n : ℕ => (1 - c * r ^ n)⁻¹) atTop (𝓝 1) := by
    simpa using hden.inv₀ one_ne_zero
  have hdecay := tendsto_sqrt_succ_mul_pow_of_lt_one hr hr_lt_one
  have hscaled : Tendsto
      (fun n : ℕ => C * (Real.sqrt ((n + 1 : ℕ) : ℝ) * r ^ n))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hdecay
  simpa only [mul_assoc, mul_left_comm, mul_comm, one_mul, zero_mul, mul_zero] using
    hinv.mul hscaled

private theorem tendsto_geometric_coefficient
    {C c r : ℝ} (hr : 0 ≤ r) (hr_lt_one : r < 1) :
    Tendsto (fun n : ℕ => (1 - c * r ^ n)⁻¹ * (C * r ^ n))
      atTop (𝓝 0) := by
  have hr_pow : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr hr_lt_one
  have hden : Tendsto (fun n : ℕ => 1 - c * r ^ n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hr_pow)
  have hinv : Tendsto (fun n : ℕ => (1 - c * r ^ n)⁻¹) atTop (𝓝 1) := by
    simpa using hden.inv₀ one_ne_zero
  have hscaled : Tendsto (fun n : ℕ => C * r ^ n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hr_pow
  simpa using hinv.mul hscaled

/-- There is a positive block-injective length \(p\), measured in sites of the
input tensor, such that the whole-increment projector defect with overlap and
suffix lengths \(L=Q=p\) is at most \(7/16\) for every prefix length \(K\). -/
theorem IsPrimitiveMPS.exists_uniform_wholeIncrement_defect_le_seven_sixteenths
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) :
    ∃ p : ℕ,
      0 < p ∧ Kraus.IsNBlkInjective A p ∧
        ∀ K : ℕ,
          ‖(reassocTailBoundaryMapES A K p p).range.starProjection ∘L
                (leftBoundaryMapES A (K + p) p).range.starProjection -
              (groundSpaceES A (K + p + p)).starProjection‖ ≤ 7 / 16 := by
  obtain ⟨C, c, r, hC, hc, hr, hr_lt_one, hDefect⟩ :=
    hP.wholeIncrement_groundProjection_defect_le_geometric hρ
  obtain ⟨L, hLpos, hLinj⟩ := isNormal_of_isPrimitiveMPS_with_posDef hP hρ
  have hr_pow : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr_lt_one
  have hsmall_lim : Tendsto (fun n : ℕ => c * r ^ n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hr_pow
  have hcoefficient_lim :=
    tendsto_geometric_coefficient (C := C) (c := c) hr.le hr_lt_one
  have hsmall : ∀ᶠ n : ℕ in atTop, c * r ^ n < 1 :=
    (tendsto_order.1 hsmall_lim).2 1 zero_lt_one
  have hcoefficient : ∀ᶠ n : ℕ in atTop,
      (1 - c * r ^ n)⁻¹ * (C * r ^ n) < 7 / 16 :=
    (tendsto_order.1 hcoefficient_lim).2 (7 / 16) (by norm_num)
  have hlarge : ∀ᶠ n : ℕ in atTop, max 1 L ≤ n := eventually_ge_atTop _
  obtain ⟨p, hp_large, hp_small, hp_coefficient⟩ :=
    (hlarge.and (hsmall.and hcoefficient)).exists
  have hp : 0 < p := lt_of_lt_of_le (by omega) hp_large
  have hLle : L ≤ p := le_trans (le_max_right 1 L) hp_large
  have hInj : Kraus.IsNBlkInjective A p := isNBlkInjective_of_le hLpos hLinj hLle
  refine ⟨p, hp, hInj, fun K ↦ ?_⟩
  exact (hDefect K p p (by omega) hp_small).trans hp_coefficient.le

/-- At the length \(p\) chosen uniformly above, taking the prefix length
\(K=p\) gives three consecutive blocks of \(p\) original sites and projector
defect at most \(7/16\). -/
theorem IsPrimitiveMPS.exists_threeBlock_wholeIncrement_defect_le_seven_sixteenths
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) :
    ∃ p : ℕ,
      0 < p ∧ Kraus.IsNBlkInjective A p ∧
        ‖(reassocTailBoundaryMapES A p p p).range.starProjection ∘L
              (leftBoundaryMapES A (p + p) p).range.starProjection -
            (groundSpaceES A (p + p + p)).starProjection‖ ≤ 7 / 16 := by
  obtain ⟨p, hp, hInj, hDefect⟩ :=
    hP.exists_uniform_wholeIncrement_defect_le_seven_sixteenths hρ
  exact ⟨p, hp, hInj, hDefect p⟩

/-- A primitive MPS with faithful fixed point has a block-injective overlap length
at which the uniform open-chain ground-projector defect satisfies Nachtergaele's
condition C3, arXiv:cond-mat/9410110, eq. (2.4).

The coefficient is the geometric-over-denominator bound reconstructed in
`openChain_groundProjection_defect_le_geometric`. It is sufficient for C3; this
statement does not assert the optimized numerator quoted in Nachtergaele, Section 6. -/
theorem IsPrimitiveMPS.exists_openChain_groundProjection_defect_lt_c3_threshold
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) :
    ∃ l : ℕ, ∃ ε : ℝ,
      1 < l ∧ Kraus.IsNBlkInjective A l ∧ 0 ≤ ε ∧
      ε < 1 / Real.sqrt ((l + 1 : ℕ) : ℝ) ∧
      ∀ K : ℕ,
        ‖openChainTailGroundProjectionES A K (l + 1) ∘L
              openChainLeftGroundProjectionES A (K + l) -
            (groundSpaceES A (K + l + 1)).starProjection‖ ≤ ε := by
  obtain ⟨C, c, r, hC, hc, hr, hr_lt_one, hDefect⟩ :=
    hP.openChain_groundProjection_defect_le_geometric hρ
  obtain ⟨L, hLpos, hLinj⟩ := isNormal_of_isPrimitiveMPS_with_posDef hP hρ
  have hr_pow : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr_lt_one
  have hsmall_lim : Tendsto (fun n : ℕ => c * r ^ n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hr_pow
  have hcoefficient_lim :=
    tendsto_geometric_c3_coefficient_mul_sqrt (C := C) (c := c) hr.le hr_lt_one
  have hsmall : ∀ᶠ n : ℕ in atTop, c * r ^ n < 1 :=
    (tendsto_order.1 hsmall_lim).2 1 zero_lt_one
  have hcoefficient : ∀ᶠ n : ℕ in atTop,
      (1 - c * r ^ n)⁻¹ * (C * r ^ n) *
          Real.sqrt ((n + 1 : ℕ) : ℝ) < 1 :=
    (tendsto_order.1 hcoefficient_lim).2 1 zero_lt_one
  have hlarge : ∀ᶠ n : ℕ in atTop, max 2 L ≤ n := eventually_ge_atTop _
  obtain ⟨l, hl_large, hl_small, hl_coefficient⟩ :=
    (hlarge.and (hsmall.and hcoefficient)).exists
  let ε := (1 - c * r ^ l)⁻¹ * (C * r ^ l)
  have hl : 1 < l := lt_of_lt_of_le (by omega) hl_large
  have hLle : L ≤ l := le_trans (le_max_right 2 L) hl_large
  have hInj : Kraus.IsNBlkInjective A l := isNBlkInjective_of_le hLpos hLinj hLle
  have hden : 0 < 1 - c * r ^ l := sub_pos.mpr hl_small
  have hε : 0 ≤ ε := by
    dsimp only [ε]
    positivity
  have hsqrt : 0 < Real.sqrt ((l + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hε_lt : ε < 1 / Real.sqrt ((l + 1 : ℕ) : ℝ) := by
    rw [lt_div_iff₀ hsqrt]
    simpa only [ε, one_mul] using hl_coefficient
  refine ⟨l, ε, hl, hInj, hε, hε_lt, ?_⟩
  intro K
  exact hDefect K l (by omega) hl_small

/-- The C3 threshold yields the uniform open-chain anticommutator estimate for
the complementary excitation projections. Nachtergaele's identity following condition
C3 identifies the projector defect, arXiv:cond-mat/9410110, eq. (2.4); the
anticommutator estimate is the two-projection consequence proved in this development. -/
theorem IsPrimitiveMPS.exists_re_inner_openChain_anticommutator_ge_c3_threshold
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) :
    ∃ l : ℕ, ∃ ε : ℝ,
      1 < l ∧ 0 ≤ ε ∧ ε < 1 / Real.sqrt ((l + 1 : ℕ) : ℝ) ∧
      ∀ (K : ℕ) (v : EuclideanSpace ℂ (Cfg d (K + l + 1))),
        -ε *
            (RCLike.re
                (⟪(openChainTailGroundSpaceES A K (l + 1))ᗮ.starProjection v, v⟫_ℂ) +
              RCLike.re
                (⟪(openChainLeftGroundSpaceES A (K + l))ᗮ.starProjection v, v⟫_ℂ)) ≤
          RCLike.re
              (⟪(openChainTailGroundSpaceES A K (l + 1))ᗮ.starProjection v,
                (openChainLeftGroundSpaceES A (K + l))ᗮ.starProjection v⟫_ℂ) +
            RCLike.re
              (⟪(openChainLeftGroundSpaceES A (K + l))ᗮ.starProjection v,
                (openChainTailGroundSpaceES A K (l + 1))ᗮ.starProjection v⟫_ℂ) := by
  obtain ⟨l, ε, hl, hInj, hε, hε_lt, hDefect⟩ :=
    hP.exists_openChain_groundProjection_defect_lt_c3_threshold hρ
  refine ⟨l, ε, hl, hε, hε_lt, ?_⟩
  intro K v
  exact re_inner_openChain_anticommutator_ge_neg_of_groundProjection_defect
    hInj hl.le (hDefect K) v

end MPSTensor
