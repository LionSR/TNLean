/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.PowerSumCoefficients
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.BlockSumGroundSpace
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.PrimitiveGaugeExistence

/-!
# Primitive representatives of inequivalent normal blocks

Each normal block can be independently rescaled and gauged into trace-preserving
primitive form with a positive definite invariant matrix. The local ground
spaces are unchanged, and inequivalence under conjugation and a nonzero scalar
is preserved. Thus this normalization can be applied to a block sum without
changing its parent interaction.

The normalization is the one used by Nachtergaele, arXiv:cond-mat/9410110,
equations (3.1)--(3.2b), lines 1394--1435, and by Pérez-García, Verstraete,
Wolf, and Cirac, arXiv:quant-ph/0608197, Theorem 4, proof lines 765--770.

## Parent Hamiltonians under independent block normalization

Replacing every normal block by a normalized primitive representative leaves
the local ground spaces of a weighted direct sum unchanged. Consequently,
the periodic parent Hamiltonians themselves are equal at every range and
volume. This is the normalization used before the block-injective gap
argument in Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b),
and Section 6.

## Primitive normalization at a prescribed injectivity length

Normalizing each block preserves injectivity at every specified word length.
Thus the common length in condition C1, and consequently the interaction bound
in PGVWC07, Theorem 12, need not be increased during normalization.
-/

section

open scoped ComplexOrder

namespace MPSTensor

variable {ι : Type*} {d : ℕ} {D : ι → ℕ} [∀ i, NeZero (D i)]

/-- A family of pairwise inequivalent normal tensors admits normalized primitive
representatives with the same local ground spaces and the same inequivalence.
Here equivalence allows both a virtual gauge and any nonzero complex scalar.
The normalization is that of Nachtergaele, arXiv:cond-mat/9410110,
equations (3.1)--(3.2b), lines 1394--1435. -/
theorem exists_hasComplementaryFixedPointGap_family_of_isNormal
    (A : ∀ i, MPSTensor d (D i)) (hNormal : ∀ i, Kraus.IsNormal (A i))
    (hDistinct : ∀ i j, i ≠ j → ∀ h : D j = D i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i)) :
    ∃ (B : ∀ i, MPSTensor d (D i))
      (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ),
      (∀ i, Kraus.HasComplementaryFixedPointGap (B i) (ρ i)) ∧ (∀ i, (ρ i).PosDef) ∧
      (∀ i L, groundSpace (A i) L = groundSpace (B i) L) ∧
      (∀ i j, i ≠ j → ∀ h : D j = D i, ¬ GaugePhaseEquiv (h ▸ B j) (B i)) := by
  classical
  choose B ζ ρ hζ hGauge _hmpv hP hρ hGS _hPI _hCGS using
    fun i ↦ exists_hasComplementaryFixedPointGap_gauge_of_isNormal (hNormal i)
  refine ⟨B, ρ, hP, hρ, hGS, fun i j hij h hGP ↦ ?_⟩
  exact hDistinct i j hij h (by
    simpa only [eqRec_eq_cast] using
      gaugePhaseEquiv_of_smul_smul_cast h (hζ j) (hζ i)
        (gaugePhaseEquiv_of_gaugeEquiv_left_right_cast h (hGauge j)
          (by simpa only [eqRec_eq_cast] using hGP) (hGauge i)))

end MPSTensor

end

section

open scoped ComplexOrder

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- Equal block ground spaces give equal assembled ground spaces, independently
of the nonzero block coefficients. This follows from the local direct-sum
identity in PGVWC07, Theorem 12, proof lines 1430--1434. -/
theorem groundSpace_toTensorFromBlocks_eq_of_block_groundSpace_eq
    (μ ν : Fin r → ℂ) (A B : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) (hν : ∀ j, ν j ≠ 0) {L : ℕ}
    (hGS : ∀ j, groundSpace (A j) L = groundSpace (B j) L) :
    groundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L =
      groundSpace (toTensorFromBlocks (d := d) (μ := ν) B) L := by
  simp only [groundSpace_toTensorFromBlocks_eq_iSup μ A hμ,
    groundSpace_toTensorFromBlocks_eq_iSup ν B hν, hGS]

/-- Independent replacements preserving the block ground spaces preserve the
periodic parent Hamiltonian. The parent interaction is the orthogonal
projection onto the complement of the local ground space, as in
Nachtergaele, arXiv:cond-mat/9410110, equation (3.12). -/
theorem hamiltonian_parentRingInteraction_toTensorFromBlocks_eq_of_block_groundSpace_eq
    (μ ν : Fin r → ℂ) (A B : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) (hν : ∀ j, ν j ≠ 0) {L : ℕ}
    (hGS : ∀ j, groundSpace (A j) L = groundSpace (B j) L) (N : ℕ) [NeZero N] :
    (parentRingInteraction (toTensorFromBlocks (d := d) (μ := μ) A) L N).hamiltonian =
      (parentRingInteraction (toTensorFromBlocks (d := d) (μ := ν) B) L N).hamiltonian :=
  hamiltonian_parentRingInteraction_eq_of_groundSpace_eq
    (groundSpace_toTensorFromBlocks_eq_of_block_groundSpace_eq μ ν A B hμ hν hGS) N

/-- Normalizing inequivalent normal blocks preserves the entire family of
periodic parent Hamiltonians of their weighted direct sum. This is the
normalization in Nachtergaele, arXiv:cond-mat/9410110,
equations (3.1)--(3.2b), before the gap argument of Section 6. -/
theorem exists_hasComplementaryFixedPointGap_family_hamiltonian_eq_of_isNormal
    [∀ j, NeZero (dim j)]
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) (hNormal : ∀ j, Kraus.IsNormal (A j))
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i)) :
    ∃ (B : (j : Fin r) → MPSTensor d (dim j))
      (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ),
      (∀ j, Kraus.HasComplementaryFixedPointGap (B j) (ρ j)) ∧ (∀ j, (ρ j).PosDef) ∧
      (∀ i j, i ≠ j → ∀ h : dim j = dim i,
        ¬ GaugePhaseEquiv (h ▸ B j) (B i)) ∧
      (∀ (L N : ℕ) [NeZero N],
        (parentRingInteraction (toTensorFromBlocks (d := d) (μ := μ) A) L N).hamiltonian =
          (parentRingInteraction (toTensorFromBlocks (d := d) (μ := μ) B) L N).hamiltonian) := by
  exact (exists_hasComplementaryFixedPointGap_family_of_isNormal A hNormal hDistinct).elim
    fun B ⟨ρ, hP, hρ, hGS, hDistinctB⟩ ↦
      ⟨B, ρ, hP, hρ, hDistinctB, fun L N _ ↦
        hamiltonian_parentRingInteraction_toTensorFromBlocks_eq_of_block_groundSpace_eq
          μ μ A B hμ hμ (fun j ↦ hGS j L) N⟩

end MPSTensor

end

section

open scoped ComplexOrder

namespace MPSTensor

/-- Primitive normalization preserves a prescribed common injectivity length,
pairwise inequivalence, and every periodic parent Hamiltonian of the block sum.
This retains the C1 length used in PGVWC07, arXiv:quant-ph/0608197,
Theorem 12, lines 1424--1458. -/
theorem exists_hasComplementaryFixedPointGap_family_hamiltonian_eq_of_common_isNBlkInjective
    {d r L₀ : ℕ} {dim : Fin r → ℕ} [∀ j, NeZero (dim j)]
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) (hL₀ : 0 < L₀)
    (hBlk : ∀ j, Kraus.IsNBlkInjective (A j) L₀)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i)) :
    ∃ (B : (j : Fin r) → MPSTensor d (dim j))
      (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ),
      (∀ j, Kraus.HasComplementaryFixedPointGap (B j) (ρ j)) ∧ (∀ j, (ρ j).PosDef) ∧
      (∀ j, Kraus.IsNBlkInjective (B j) L₀) ∧
      (∀ i j, i ≠ j → ∀ h : dim j = dim i,
        ¬ GaugePhaseEquiv (h ▸ B j) (B i)) ∧
      (∀ (L N : ℕ) [NeZero N],
        (parentRingInteraction (toTensorFromBlocks (d := d) (μ := μ) A) L N).hamiltonian =
          (parentRingInteraction (toTensorFromBlocks (d := d) (μ := μ) B) L N).hamiltonian) := by
  classical
  choose B ζ ρ hζ hGauge _hmpv hP hρ hGS _hPI _hCGS using
    fun j ↦ exists_hasComplementaryFixedPointGap_gauge_of_isNormal ⟨L₀, hL₀, hBlk j⟩
  refine ⟨B, ρ, hP, hρ, fun j ↦ ?_, ?_, ?_⟩
  · exact isNBlkInjective_of_gaugeEquiv
      ((isNBlkInjective_smul_iff (hζ j) (A j) L₀).2 (hBlk j)) (hGauge j)
  · intro i j hij h hGP
    exact hDistinct i j hij h (by
      simpa only [eqRec_eq_cast] using
        gaugePhaseEquiv_of_smul_smul_cast h (hζ j) (hζ i)
          (gaugePhaseEquiv_of_gaugeEquiv_left_right_cast h (hGauge j)
            (by simpa only [eqRec_eq_cast] using hGP) (hGauge i)))
  · intro L N _
    exact hamiltonian_parentRingInteraction_toTensorFromBlocks_eq_of_block_groundSpace_eq
      μ μ A B hμ hμ (fun j ↦ hGS j L) N

end MPSTensor

end
