/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockDiagonalNormalization

/-!
# Primitive normalization at a prescribed injectivity length

Normalizing each block preserves injectivity at every specified word length.
Thus the common length in condition C1, and consequently the interaction bound
in PGVWC07, Theorem 12, need not be increased during normalization.
-/

open scoped ComplexOrder

namespace MPSTensor

/-- Primitive normalization preserves a prescribed common injectivity length,
pairwise inequivalence, and every periodic parent Hamiltonian of the block sum.
This retains the C1 length used in PGVWC07, arXiv:quant-ph/0608197,
Theorem 12, lines 1424--1458. -/
theorem exists_isPrimitiveMPS_family_parentHamiltonianES_eq_of_common_isNBlkInjective
    {d r L₀ : ℕ} {dim : Fin r → ℕ} [∀ j, NeZero (dim j)]
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) (hL₀ : 0 < L₀)
    (hBlk : ∀ j, Kraus.IsNBlkInjective (A j) L₀)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i)) :
    ∃ (B : (j : Fin r) → MPSTensor d (dim j))
      (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ),
      (∀ j, IsPrimitiveMPS (B j) (ρ j)) ∧ (∀ j, (ρ j).PosDef) ∧
      (∀ j, Kraus.IsNBlkInjective (B j) L₀) ∧
      (∀ i j, i ≠ j → ∀ h : dim j = dim i,
        ¬ GaugePhaseEquiv (h ▸ B j) (B i)) ∧
      (∀ L N, parentHamiltonianES (toTensorFromBlocks (d := d) (μ := μ) A) L N =
        parentHamiltonianES (toTensorFromBlocks (d := d) (μ := μ) B) L N) := by
  classical
  choose B ζ ρ hζ hGauge _hmpv hP hρ hGS _hPI _hCGS using
    fun j ↦ exists_isPrimitiveMPS_gauge_of_isNormal ⟨L₀, hL₀, hBlk j⟩
  refine ⟨B, ρ, hP, hρ, fun j ↦ ?_, ?_, ?_⟩
  · exact isNBlkInjective_of_gaugeEquiv
      ((isNBlkInjective_smul_iff (hζ j) (A j) L₀).2 (hBlk j)) (hGauge j)
  · intro i j hij h hGP
    exact hDistinct i j hij h (by
      simpa only [eqRec_eq_cast] using
        gaugePhaseEquiv_of_smul_smul_cast h (hζ j) (hζ i)
          (gaugePhaseEquiv_of_gaugeEquiv_left_right_cast h (hGauge j)
            (by simpa only [eqRec_eq_cast] using hGP) (hGauge i)))
  · intro L N
    exact parentHamiltonianES_toTensorFromBlocks_eq_of_block_groundSpace_eq
      μ μ A B hμ hμ (fun j ↦ hGS j L) N

end MPSTensor
