/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.PowerSumCoefficients

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
-/

open scoped ComplexOrder

namespace MPSTensor

variable {ι : Type*} {d : ℕ} {D : ι → ℕ} [∀ i, NeZero (D i)]

/-- A family of pairwise inequivalent normal tensors admits normalized primitive
representatives with the same local ground spaces and the same inequivalence.
Here equivalence allows both a virtual gauge and any nonzero complex scalar.
The normalization is that of Nachtergaele, arXiv:cond-mat/9410110,
equations (3.1)--(3.2b), lines 1394--1435. -/
theorem exists_isPrimitiveMPS_family_of_isNormal
    (A : ∀ i, MPSTensor d (D i)) (hNormal : ∀ i, Kraus.IsNormal (A i))
    (hDistinct : ∀ i j, i ≠ j → ∀ h : D j = D i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i)) :
    ∃ (B : ∀ i, MPSTensor d (D i))
      (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ),
      (∀ i, IsPrimitiveMPS (B i) (ρ i)) ∧ (∀ i, (ρ i).PosDef) ∧
      (∀ i L, groundSpace (A i) L = groundSpace (B i) L) ∧
      (∀ i j, i ≠ j → ∀ h : D j = D i, ¬ GaugePhaseEquiv (h ▸ B j) (B i)) := by
  classical
  choose B ζ ρ hζ hGauge _hmpv hP hρ hGS _hPI _hCGS using
    fun i ↦ exists_isPrimitiveMPS_gauge_of_isNormal (hNormal i)
  refine ⟨B, ρ, hP, hρ, hGS, fun i j hij h hGP ↦ ?_⟩
  exact hDistinct i j hij h (by
    simpa only [eqRec_eq_cast] using
      gaugePhaseEquiv_of_smul_smul_cast h (hζ j) (hζ i)
        (gaugePhaseEquiv_of_gaugeEquiv_left_right_cast h (hGauge j)
          (by simpa only [eqRec_eq_cast] using hGP) (hGauge i)))

end MPSTensor
