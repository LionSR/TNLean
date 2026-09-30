/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockDiagonalNormalization
import TNLean.MPS.ParentHamiltonian.Martingale.PrimitiveBlockGap

/-!
# Prescribed gaps for sufficiently long parent interactions

For every \(0<\eta<1\), a primitive tensor has canonical parent gap at
least \(1-\eta\) at every sufficiently large interaction range and every
sufficiently long periodic chain. The same conclusion holds for inequivalent
primitive block sums at sufficiently large even ranges. The local
interactions are orthogonal projectors with coefficient one. Primitive
normalization extends both conclusions to normal tensors without changing
the Hamiltonians.

These are quantitative consequences of Nachtergaele's projector decay and
martingale bounds, arXiv:cond-mat/9410110, Theorem 2.1 and Section 6, together
with the finite-range comparison in
`docs/paper-gaps/knabe88_finite_range_coefficient.tex`. The interaction range
increases with the requested lower bound; no improvement at a fixed shorter
range is asserted.
-/

open Filter
open scoped Topology ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- An open-chain gap \(1-\eta/2\) on a sufficiently long comparison window
implies the periodic gap \(1-\eta\). The explicit window condition is
\(2(R-1)^2\le m\eta\), where \(m\) counts local interactions. -/
theorem parentHamiltonianES_gap_ge_one_sub_of_open_gap
    (A : MPSTensor d D) {R m : ℕ} (hR : 1 ≤ R) (hmR : R ≤ m)
    {η : ℝ} (hη : 0 < η) (hηone : η < 1)
    (hmη : 2 * ((R : ℝ) - 1) ^ 2 ≤ (m : ℝ) * η)
    (hOpen : ∀ u ∈
      (LinearMap.ker (openParentHamiltonianES A R (m + R - 1)))ᗮ,
      (1 - η / 2) * ‖u‖ ≤ ‖openParentHamiltonianES A R (m + R - 1) u‖)
    (N : ℕ) (hN : 2 * m ≤ N) :
    ∀ v ∈ (LinearMap.ker (parentHamiltonianES A R N))ᗮ,
      (1 - η) * ‖v‖ ≤ ‖parentHamiltonianES A R N v‖ := by
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hmR' : (R : ℝ) ≤ m := by exact_mod_cast hmR
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one (hR'.trans hmR')
  have hden : 0 < (m : ℝ) - R + 1 := by linarith
  have hnum : ((R : ℝ) - 1) ^ 2 < (m : ℝ) * (1 - η / 2) := by
    nlinarith [mul_pos hmpos (sub_pos.mpr hηone)]
  have hcoef : 1 - η ≤
      ((m : ℝ) * (1 - η / 2) - ((R : ℝ) - 1) ^ 2) /
        ((m : ℝ) - R + 1) := by
    apply (le_div_iff₀ hden).2
    nlinarith [mul_nonneg (sub_pos.mpr hηone).le (sub_nonneg.mpr hR')]
  obtain ⟨_, hGap⟩ := parentHamiltonianES_gap_of_openParentHamiltonianES_gap
    A hR hmR hnum hOpen
  intro v hv
  exact (mul_le_mul_of_nonneg_right hcoef (norm_nonneg v)).trans (hGap N hN v hv)

/-- Every sufficiently long canonical interaction of a primitive tensor has
periodic gap at least \(1-\eta\). A comparison window containing \(m\)
interactions suffices when \(l+1\le m\) and \(2l^2\le m\eta\); the
periodic chain then needs at least \(2m\) sites. -/
theorem IsPrimitiveMPS.eventually_parentHamiltonianES_gap_ge_one_sub
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) {η : ℝ}
    (hη : 0 < η) (hηone : η < 1) :
    ∀ᶠ l : ℕ in atTop, ∀ m : ℕ, l + 1 ≤ m →
      2 * (l : ℝ) ^ 2 ≤ (m : ℝ) * η →
      ∀ N : ℕ, 2 * m ≤ N →
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES A (l + 1) N))ᗮ,
        (1 - η) * ‖v‖ ≤ ‖parentHamiltonianES A (l + 1) N v‖ := by
  filter_upwards [hP.eventually_openChain_groundProjection_defect_mul_sqrt_lt hρ
    (div_pos hη (by norm_num : (0 : ℝ) < 4))] with l hl
  obtain ⟨hl, hInj, ε, hε, hsmall, hDefect⟩ := hl
  have hsqrt : 0 < Real.sqrt ((l + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hεlt : ε < 1 / Real.sqrt ((l + 1 : ℕ) : ℝ) := by
    apply (lt_div_iff₀ hsqrt).2
    linarith
  have hcoef : 1 - η / 2 ≤ (1 - ε * Real.sqrt ((l + 1 : ℕ) : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (ε * Real.sqrt ((l + 1 : ℕ) : ℝ))]
  have hC3 : ∀ (K : ℕ) (hK : 0 < K),
      ‖openChainTailGroundProjectionES A K (l + 1) ∘L
        openChainMartingaleDifferenceES A K l hInj hl.le hK‖ ≤ ε := by
    intro K hK
    rw [openChainTailGroundProjection_comp_martingaleDifference hInj hl.le hK]
    exact hDefect K
  intro m hm hmη N hN
  apply parentHamiltonianES_gap_ge_one_sub_of_open_gap A (by omega) hm hη hηone
    (by simpa using hmη) ?_ N hN
  intro u hu
  have hOpen := openParentHamiltonianES_norm_gap_of_fixedAmbient_c3
    A hl.le hInj (by omega : l + 1 ≤ m + (l + 1) - 1) hε hεlt
    (fun n hn ↦ fixedAmbient_martingaleDifference_norm_le_of_openChain hl hInj hε hC3
      _ n (Finset.mem_range.mp hn))
  rw [ker_openParentHamiltonianES_eq_groundSpaceES_of_isNBlkInjective
    hInj hl.le (by omega)] at hu
  exact (mul_le_mul_of_nonneg_right hcoef (norm_nonneg u)).trans (hOpen u hu)

/-- For a weighted sum of inequivalent primitive blocks, every sufficiently
large even interaction range has periodic gap at least \(1-\eta\) at all
sufficiently large chain lengths. The block weights are nonzero; the local
interactions remain orthogonal projectors with coefficient one. -/
theorem eventually_toTensorFromBlocks_parentHamiltonianES_gap_ge_one_sub
    {r : ℕ} {dim : Fin r → ℕ} [NeZero d] [∀ j, NeZero (dim j)]
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    {η : ℝ} (hη : 0 < η) (hηone : η < 1) :
    ∀ᶠ p : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES
        (toTensorFromBlocks (d := d) (μ := μ) A) (2 * p) N))ᗮ,
        (1 - η) * ‖v‖ ≤ ‖parentHamiltonianES
          (toTensorFromBlocks (d := d) (μ := μ) A) (2 * p) N v‖ := by
  let B := toTensorFromBlocks (d := d) (μ := μ) A
  let ε := η / (4 * Real.sqrt 2)
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
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
  obtain ⟨L₀, hL₀, hKernel⟩ :=
    exists_ker_openParentHamiltonianES_toTensorFromBlocks_eq_groundSpaceES_of_isPrimitiveMPS
      μ A hμ ρ hP hρ hDistinct
  filter_upwards [eventually_ge_atTop (max L₀ 1),
    eventually_toTensorFromBlocks_projector_defect_le μ A hμ ρ hP hρ hDistinct hε]
    with p hp hDefect
  have hp0 : 0 < p := by omega
  have hOpen (M : ℕ) (hM : 2 ≤ M) : ∀ u ∈
      (LinearMap.ker (openParentHamiltonianES B (2 * p) (p * M)))ᗮ,
      (1 - η / 2) * ‖u‖ ≤ ‖openParentHamiltonianES B (2 * p) (p * M) u‖ := by
    intro u hu
    have hGap := openParentHamiltonianES_norm_gap_of_grouped_c3 B hp0 hM hε.le hεlt
      (grouped_martingaleDifference_norm_le_of_projector_defect B hp0 hM
        (fun n hn ↦ hKernel (2 * p) n (by omega) hn) hε.le
        (fun K ↦ hDefect K p hp0))
    exact (mul_le_mul_of_nonneg_right hcoef (norm_nonneg u)).trans (hGap u hu)
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * (((2 * p : ℕ) : ℝ) - 1) ^ 2 / η)
  let M := n + 4 * p + 2
  have hMp : M ≤ p * M := Nat.le_mul_of_pos_left M hp0
  let m := p * M - 2 * p + 1
  have hm : 2 * p ≤ m ∧ n ≤ m ∧ m + 2 * p - 1 = p * M := by
    dsimp only [m, M] at *
    omega
  have hmη : 2 * (((2 * p : ℕ) : ℝ) - 1) ^ 2 ≤ (m : ℝ) * η :=
    ((div_lt_iff₀ hη).mp hn).le.trans
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hm.2.1) hη.le)
  have hPeriodic := parentHamiltonianES_gap_ge_one_sub_of_open_gap B (by omega) hm.1
    hη hηone hmη (hm.2.2.symm ▸ hOpen M (by dsimp [M]; omega))
  exact (eventually_ge_atTop (2 * m)).mono hPeriodic

/-- The prescribed-gap conclusion for an arbitrary normal tensor, with no
normalization hypothesis. Primitive normalization preserves each parent
Hamiltonian exactly, so the same interaction and chain-length bounds apply. -/
theorem eventually_parentHamiltonianES_gap_ge_one_sub_of_isNormal
    [NeZero D] {A : MPSTensor d D} (hA : Kraus.IsNormal A)
    {η : ℝ} (hη : 0 < η) (hηone : η < 1) :
    ∀ᶠ l : ℕ in atTop, ∀ m : ℕ, l + 1 ≤ m →
      2 * (l : ℝ) ^ 2 ≤ (m : ℝ) * η →
      ∀ N : ℕ, 2 * m ≤ N →
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES A (l + 1) N))ᗮ,
        (1 - η) * ‖v‖ ≤ ‖parentHamiltonianES A (l + 1) N v‖ := by
  obtain ⟨B, _, ρ, _, _, _, hP, hρ, hGS, _, _⟩ :=
    exists_isPrimitiveMPS_gauge_of_isNormal hA
  filter_upwards [hP.eventually_parentHamiltonianES_gap_ge_one_sub hρ hη hηone] with l hl
  intro m hm hmη N hN v hv
  rw [parentHamiltonianES_eq_of_groundSpace_eq (hGS (l + 1)) N] at hv ⊢
  exact hl m hm hmη N hN v hv

/-- Independent normalization also preserves the prescribed gap of a weighted
sum of inequivalent normal blocks at sufficiently large even ranges. -/
theorem eventually_toTensorFromBlocks_parentHamiltonianES_gap_ge_one_sub_of_isNormal
    {r : ℕ} {dim : Fin r → ℕ} [NeZero d] [∀ j, NeZero (dim j)]
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) (hNormal : ∀ j, Kraus.IsNormal (A j))
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    {η : ℝ} (hη : 0 < η) (hηone : η < 1) :
    ∀ᶠ p : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES
        (toTensorFromBlocks (d := d) (μ := μ) A) (2 * p) N))ᗮ,
        (1 - η) * ‖v‖ ≤ ‖parentHamiltonianES
          (toTensorFromBlocks (d := d) (μ := μ) A) (2 * p) N v‖ := by
  obtain ⟨B, ρ, hP, hρ, hDistinctB, hEq⟩ :=
    exists_isPrimitiveMPS_family_parentHamiltonianES_eq_of_isNormal
      μ A hμ hNormal hDistinct
  simpa only [hEq] using
    eventually_toTensorFromBlocks_parentHamiltonianES_gap_ge_one_sub
      μ B hμ ρ hP hρ hDistinctB hη hηone

end MPSTensor
