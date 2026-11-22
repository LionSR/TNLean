/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.SparseGroupedOpenGap
import QICLean.ManyBody.Hamiltonian.Martingale.TwoGroundProjectionGap
import TNLean.MPS.ParentHamiltonian.Martingale.IntervalKernelTransport
import TNLean.MPS.ParentHamiltonian.BlockDiagonalNormalization
import TNLean.MPS.ParentHamiltonian.Martingale.PrimitiveBlockGap

/-!
# Prescribed gaps for long canonical open-chain interactions

The grouped martingale coefficient tends to one as its projector error tends
to zero. For a chain of length \(N=pM+q\), the sparse grouped prefix
interaction and one terminal range-\(2p\) projection form a subfamily of
the full interaction. Their ground spaces overlap in \(2p-q\geq p\)
sites. The sharp two-ground-projection comparison therefore retains a gap
tending to one without a divisibility condition on \(N\).

This is a quantitative consequence of Nachtergaele,
arXiv:cond-mat/9410110, Theorem 2.1(ii), lines 1131--1136, and Section 6,
Lemma `commutation` (ii), lines 2443--2464. The interaction range increases
with the prescribed lower bound. No improvement at a fixed range is asserted.
-/

open Filter
open scoped BigOperators Topology ComplexOrder InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

/-- A sparse grouped prefix and one terminal interaction retain the grouped
coefficient up to the three-interval projector error. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorem 2.1(ii) and Section 6, Lemma `commutation` (ii). -/
theorem hamiltonian_parentChainInteraction_gap_of_sparse_grouped_and_terminal
    (A : MPSTensor d D) {p M q : ℕ} (hp : 0 < p) (hM : 2 ≤ M)
    (hq : 0 < q) (hqp : q < p)
    (hKernel : ∀ N, 2 * p ≤ N →
      LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A (2 * p) N).hamiltonian) =
          groundSpaceES A N)
    {ε : ℝ} (hε : 0 ≤ ε) (hεlt : ε < 1 / Real.sqrt 2)
    (hDefect : ∀ L, p ≤ L → ∀ K Q, 0 < Q →
      ‖(groundSpaceES A (K + L + Q)).starProjection -
        (leftBoundaryMapES A (K + L) Q).range.starProjection.comp
          (reassocTailBoundaryMapES A K L Q).range.starProjection‖ ≤ ε) :
    ∀ z : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction A (2 * p) (p * M + q)).hamiltonian) z →
        z = 0 ∨ (((1 - ε * Real.sqrt 2) ^ 2 * (1 - ε) : ℝ) : ℂ) ≤ z := by
  refine (ManyBody.forall_hasEigenvalue_iff_norm
    (posSemidef_hamiltonian_parentChainInteraction A (2 * p) (p * M + q))).mpr ?_
  let N := p * M + q
  let κ := (1 - ε * Real.sqrt 2) ^ 2
  let U := LinearMap.ker
      (Matrix.toEuclideanLin
          ((parentChainInteraction A (2 * p) N).restrict fun i ↦ i.val + 2 * p ≤ p * M).hamiltonian)
  let V := LinearMap.ker
      (Matrix.toEuclideanLin
          ((parentChainInteraction A (2 * p) N).restrict fun i ↦ N - 2 * p ≤ i.val ∧ i.val + 2 * p ≤
              N).hamiltonian)
  let T := Matrix.toEuclideanLin
      ((parentChainInteraction A (2 * p) N).restrict fun i ↦ N - 2 * p ≤ i.val ∧ i.val + 2 * p ≤
          N).hamiltonian
  have hMN : p * M ≤ N := by dsimp [N]; omega
  have hRN : 2 * p ≤ N := by nlinarith
  have hsqrt : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hεs : ε * Real.sqrt 2 < 1 := (lt_div_iff₀ (by positivity)).mp hεlt
  have hκ : 0 ≤ κ := sq_nonneg _
  have hκone : κ ≤ 1 := by dsimp [κ]; nlinarith [mul_nonneg hε (le_trans zero_le_one hsqrt)]
  have hc : ε < 1 := by nlinarith [mul_le_mul_of_nonneg_left hsqrt hε]
  have hSparse := sparseGrouped_projection_bound_of_grouped_c3
    A hp hMN hε hεlt
    (grouped_martingaleDifference_norm_le_of_projector_defect_of_le A hp hMN
      hKernel hε (fun K => hDefect p le_rfl K p hp))
  have hTV : T = Vᗮ.starProjection.toLinearMap :=
    toEuclideanLin_hamiltonian_restrict_parentChainInteraction_eq_starProjection A hRN le_rfl
  have hTbound : (κ : ℂ) • T ≤ T := by
    simpa only [one_smul] using smul_le_smul_of_nonneg_right
      (show (κ : ℂ) ≤ 1 by exact_mod_cast hκone)
      (LinearMap.nonneg_iff_isPositive.mpr (Matrix.isPositive_toEuclideanLin_iff.mpr
        (posSemidef_hamiltonian_restrict_parentChainInteraction A _ _ _)))
  apply FrustrationFree.norm_gap_of_two_ground_projection_bounds
    (Matrix.toEuclideanLin (parentChainInteraction A (2 * p) N).hamiltonian) U V hκ hc
  · intro v hv
    rw [← hamiltonian_prefix_parentChainInteraction_self_eq_hamiltonian_parentChainInteraction]
      at hv
    exact ker_hamiltonian_prefix_parentChainInteraction_antitone A (2 * p) N hMN hv
  · intro v hv
    rw [← hamiltonian_prefix_parentChainInteraction_self_eq_hamiltonian_parentChainInteraction]
      at hv
    have hNpos : 0 < N := by omega
    have h := ker_hamiltonian_prefix_parentChainInteraction_le_ker_restrict
      A (L := 2 * p) (l := 2 * p - 1) (N := N) (m := N) (n := N - 1) (by omega) hv
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ 2 * p), Nat.sub_add_cancel hNpos] using h
  · calc
      (κ : ℂ) • (Uᗮ.starProjection.toLinearMap + Vᗮ.starProjection.toLinearMap) =
          (κ : ℂ) • Uᗮ.starProjection.toLinearMap + (κ : ℂ) • T := by rw [hTV, smul_add]
      _ ≤ Matrix.toEuclideanLin ((parentChainInteraction A (2 * p) N).restrict
            fun i ↦ p ∣ i.val ∧ i.val + 2 * p ≤ p * M).hamiltonian + T :=
        add_le_add hSparse hTbound
      _ ≤ Matrix.toEuclideanLin (parentChainInteraction A (2 * p) N).hamiltonian :=
        (map_add Matrix.toEuclideanLin _ _).symm.trans_le
          (Matrix.toEuclideanLin_le_toEuclideanLin_iff.mpr (sparseGrouped_add_terminal_le A p M hq))
  · let L := 2 * p - q
    let K := p * M - L
    have hLp : p ≤ L := by dsimp [L]; omega
    have hpM : 2 * p ≤ p * M := by nlinarith
    have hKL : K + L = p * M := by
      exact Nat.sub_add_cancel ((Nat.sub_le (2 * p) q).trans hpM)
    have hLq : L + q = 2 * p := by dsimp [L]; omega
    have hN : N = K + L + q := by dsimp [N]; omega
    have hSuffix : LinearMap.ker
        (Matrix.toEuclideanLin
            ((parentChainInteraction A (2 * p) (K + L + q)).restrict fun i ↦ K + L + q - 2 * p ≤
                i.val ∧ i.val + 2 * p ≤ K + L + q).hamiltonian) =
                    (reassocTailBoundaryMapES A K L q).range := by
      simpa only [hLq] using
          ker_hamiltonian_restrict_parentChainInteraction_eq_range_reassocTailBoundaryMapES
        A (R := 2 * p) (K := K) (L := L) (Q := q) (by omega) (by omega)
        (hKernel (L + q) (by omega))
    change ‖(LinearMap.ker
        (Matrix.toEuclideanLin (parentChainInteraction A (2 * p) N).hamiltonian)).starProjection -
      (LinearMap.ker
          (Matrix.toEuclideanLin
              ((parentChainInteraction A (2 * p) N).restrict fun i ↦ i.val + 2 * p ≤ p *
                  M).hamiltonian)).starProjection.comp
        (LinearMap.ker
            (Matrix.toEuclideanLin
                ((parentChainInteraction A (2 * p) N).restrict fun i ↦ N - 2 * p ≤ i.val ∧ i.val +
                    2 * p ≤ N).hamiltonian)).starProjection‖ ≤ ε
    rw [hN, ← hKL]
    rw [hKernel _ (by omega),
      ker_hamiltonian_prefix_parentChainInteraction_eq_range_leftBoundaryMapES A
        (hKernel _ (by simpa only [hKL] using hpM)), hSuffix]
    exact hDefect L hLp K q hq


/-- For inequivalent primitive blocks, the canonical open-chain gap tends to
one at sufficiently large even interaction ranges, uniformly over every
chain length at least the interaction range. This follows from Nachtergaele,
arXiv:cond-mat/9410110, Theorem 2.1(ii) and Section 6, Lemma `commutation` (ii),
using a sparse grouped interaction and one terminal projection. -/
theorem eventually_toTensorFromBlocks_hamiltonian_parentChainInteraction_gap_ge_one_sub
    {r : ℕ} {dim : Fin r → ℕ} [NeZero d] [∀ j, NeZero (dim j)]
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    {η : ℝ} (hη : 0 < η) (hηone : η < 1) :
    ∀ᶠ p : ℕ in atTop, ∀ N : ℕ, 2 * p ≤ N →
      ∀ z : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
        (parentChainInteraction (toTensorFromBlocks (d := d) (μ := μ) A) (2 * p) N).hamiltonian)
          z → z = 0 ∨ ((1 - η : ℝ) : ℂ) ≤ z := by
  let B := toTensorFromBlocks (d := d) (μ := μ) A
  let ε := η / (4 * Real.sqrt 2)
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtone : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hε : 0 < ε := div_pos hη (mul_pos (by norm_num) hsqrt)
  have hεsqrt : ε * Real.sqrt 2 = η / 4 := by
    dsimp only [ε]
    field_simp
  have hεlt : ε < 1 / Real.sqrt 2 := by
    apply (lt_div_iff₀ hsqrt).2
    rw [hεsqrt]
    linarith
  have hcoef : 1 - η / 2 ≤ (1 - ε * Real.sqrt 2) ^ 2 := by
    rw [hεsqrt]
    nlinarith [sq_nonneg η]
  have hcoefsharp : 1 - η ≤ (1 - ε * Real.sqrt 2) ^ 2 * (1 - ε) := by
    have hεsmall : ε ≤ η / 4 := by
      nlinarith [mul_le_mul_of_nonneg_left hsqrtone hε.le]
    have hκone : (1 - ε * Real.sqrt 2) ^ 2 ≤ 1 := by
      rw [hεsqrt]
      nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hκone) hε.le]
  obtain ⟨L₀, _, hKernel⟩ :=
    exists_ker_hamiltonian_parentChainInteraction_toTensorFromBlocks_eq_groundSpaceES
      μ A hμ ρ hP hρ hDistinct
  obtain ⟨L₁, hDefect⟩ := Filter.eventually_atTop.1
    (eventually_toTensorFromBlocks_projector_defect_le μ A hμ ρ hP hρ hDistinct hε)
  filter_upwards [eventually_ge_atTop (max L₀ (max L₁ 1))] with p hp
  have hp0 : 0 < p := by omega
  have hK : ∀ n, 2 * p ≤ n →
      LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction B (2 * p) n).hamiltonian) =
          groundSpaceES B n :=
    fun n hn => hKernel (2 * p) n (by omega) hn
  have hD : ∀ L, p ≤ L → ∀ K Q, 0 < Q →
      ‖(groundSpaceES B (K + L + Q)).starProjection -
        (leftBoundaryMapES B (K + L) Q).range.starProjection.comp
          (reassocTailBoundaryMapES B K L Q).range.starProjection‖ ≤ ε :=
    fun L hL => hDefect L (by omega)
  intro N hN
  have hM : 2 ≤ N / p := (Nat.le_div_iff_mul_le hp0).2 (by simpa [mul_comm] using hN)
  have hq : N % p < p := Nat.mod_lt N hp0
  let F (n : ℕ) : Prop := ∀ z : ℂ, Module.End.HasEigenvalue
    (Matrix.toEuclideanLin (parentChainInteraction B (2 * p) n).hamiltonian) z →
      z = 0 ∨ ((1 - η : ℝ) : ℂ) ≤ z
  change F N
  suffices hAll : F (p * (N / p) + N % p) by
    simpa only [Nat.div_add_mod] using hAll
  change ∀ z : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
    (parentChainInteraction B (2 * p) (p * (N / p) + N % p)).hamiltonian) z →
      z = 0 ∨ ((1 - η : ℝ) : ℂ) ≤ z
  by_cases hqzero : N % p = 0
  · rw [hqzero, Nat.add_zero]
    exact ManyBody.forall_hasEigenvalue_mono (by linarith)
      (hamiltonian_parentChainInteraction_gap_of_grouped_c3 B (M := N / p) hp0 hε.le hεlt
        (grouped_martingaleDifference_norm_le_of_projector_defect B hp0 hK hε.le
          (fun K => hD p le_rfl K p hp0)))
  · exact ManyBody.forall_hasEigenvalue_mono hcoefsharp
      (hamiltonian_parentChainInteraction_gap_of_sparse_grouped_and_terminal B hp0 hM
        (Nat.pos_of_ne_zero hqzero) hq hK hε.le hεlt hD)

/-- The same near-one bound holds for inequivalent normal blocks without a
normalization hypothesis. Independent primitive normalization preserves every
local ground space, and therefore every canonical open-chain interaction.
Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b) and Section 6. -/
theorem eventually_toTensorFromBlocks_hamiltonian_parentChainInteraction_gap_ge_one_sub_of_isNormal
    {r : ℕ} {dim : Fin r → ℕ} [NeZero d] [∀ j, NeZero (dim j)]
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) (hNormal : ∀ j, Kraus.IsNormal (A j))
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    {η : ℝ} (hη : 0 < η) (hηone : η < 1) :
    ∀ᶠ p : ℕ in atTop, ∀ N : ℕ, 2 * p ≤ N →
      ∀ z : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
        (parentChainInteraction (toTensorFromBlocks (d := d) (μ := μ) A) (2 * p) N).hamiltonian)
          z → z = 0 ∨ ((1 - η : ℝ) : ℂ) ≤ z := by
  obtain ⟨B, ρ, hP, hρ, hGS, hDistinctB⟩ :=
    exists_hasComplementaryFixedPointGap_family_of_isNormal A hNormal hDistinct
  filter_upwards [eventually_toTensorFromBlocks_hamiltonian_parentChainInteraction_gap_ge_one_sub
    μ B hμ ρ hP hρ hDistinctB hη hηone] with p hp
  intro N hN
  rw [parentChainInteraction_eq_of_groundSpace_eq
    (groundSpace_toTensorFromBlocks_eq_of_block_groundSpace_eq μ μ A B hμ hμ
      (fun j => hGS j (2 * p))) N]
  exact hp N hN

end MPSTensor
