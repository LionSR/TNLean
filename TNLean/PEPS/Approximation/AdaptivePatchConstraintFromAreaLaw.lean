/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.NestedPatchApproximation
import TNLean.PEPS.Approximation.NestedCylinderSquarePatch
import TNLean.PEPS.Approximation.SquarePatchIntegerCoordinates
import TNLean.PEPS.Approximation.BoundedRadiusSquarePatch
import TNLean.PEPS.Approximation.SquarePatchRelabel

/-!
# Adaptive square patches from the square entropy area law

The square entropy area law gives an approximation by nested regional cylinders
whose total inside dimension is polynomially bounded in the side length. The
constants are chosen before the Hamiltonian, ground vector, center, and radius.
Bounded radii admit an exact patch with at most `q ^ 81` terms.

The theorem takes the square entropy area law as the hypothesis `harea`. That
law is proved as `TNLean.PEPS.AreaLaw.squareEntropyAreaLaw`, and the
unconditional Proposition 4.1 is `adaptivePatchConstraint` in
`TNLean.PEPS.Approximation.PolynomialPEPSTheorem`.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, Proposition 4.1, `03-patches.tex`, lines 26–54 and 534–603, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open scoped BigOperators
namespace TNLean.PEPS.Approximation
open EncodedFrame

/-- Conditional assembly of the adaptive patch constraint from the square
entropy area law. The construction uses the same cylinder sum in the source
statement, including when a sample is empty.

Source: polynomial-PEPS manuscript, Proposition 4.1, `03-patches.tex`,
lines 26–54 and 534–603, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The area-law premise is discharged
in `adaptivePatchConstraint`. -/
theorem SquareEntropyAreaLaw.adaptivePatchConstraint
    (harea : SquareEntropyAreaLaw) : AdaptivePatchConstraint := by
  classical
  intro q hq J Δ hJ hΔ B₀ p hB₀ hp
  obtain ⟨R₀, hR₀, hcyl⟩ := harea.exists_uniform_nestedPatch_cylinders hq hJ hΔ hB₀ hp
  refine ⟨max ((q : ℝ) ^ 81) (1 + B₀ / 2), R₀ + 1,
    lt_of_lt_of_le (by positivity) (le_max_right _ _), by positivity, ?_⟩
  intro L hL h E₀ Ω hgs z u hu huL
  suffices hpatch : HasAdaptivePatch
      (fun x : Lattice.Site (AreaLaw.rectangularDomain L L) ↦
        ((x.1.1 : ℝ), (x.1.2 : ℝ))) (squareAreaLawState Ω)
      (max ((q : ℝ) ^ 81) (1 + B₀ / 2)) (R₀ + 1) p L (z - (1, 1)) u by
    have ht := (hpatch.relabel (AreaLaw.rectangleSiteEquiv L L).symm).translate (1, 1)
    have hΩ : (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.arrowCongr (AreaLaw.rectangleSiteEquiv L L).symm (Equiv.refl (Fin q))))
        (squareAreaLawState Ω) = Ω := by
      ext σ
      simp [squareAreaLawState, AreaLaw.rectangleConfigurationEquiv,
        LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft',
        Equiv.arrowCongr, Function.comp_def]
    simpa only [Equiv.symm_symm, integerCoordinates_add_one_eq_latticePos,
      sub_add_cancel, hΩ] using ht
  let : LinearOrder (Lattice.Site (AreaLaw.rectangularDomain L L)) :=
    (Fintype.equivFin (Lattice.Site (AreaLaw.rectangularDomain L L))).linearOrder
  by_cases hu4 : 4 ≤ u
  · let P (regions : Fin (AreaLaw.Geometry.nestedPatchCount u) →
        Finset (Lattice.Site (AreaLaw.rectangularDomain L L))) : Prop :=
      ∃ (S : (j : Fin (AreaLaw.Geometry.nestedPatchCount u)) →
          Submodule ℂ ((regions j → Fin q) → ℂ))
        (v : EuclideanSpace ℂ
          ((w : (Finset.univ : Finset (Lattice.Site (AreaLaw.rectangularDomain L L)))) → Fin q)),
        (∀ j, (Module.finrank ℂ (S j) : ℝ) ≤ (L : ℝ) ^ R₀) ∧
        v.ofLp ∈ (⨆ j, dependentRegionCylinder (Out := fun _ ↦ Fin q) (regions j) (S j)) ∧
        ‖dependentGlobalConfigIsometry.symm (squareAreaLawState Ω) - v‖ ≤ (L : ℝ) ^ (-p)
    have hc : P (fun j ↦ squareSample
        (fun x : Lattice.Site (AreaLaw.rectangularDomain L L) ↦
          ((x.1.1 : ℝ), (x.1.2 : ℝ))) (z - (1, 1))
        (AreaLaw.Geometry.nestedPatchRadius u j.val)) := by
      rw [show (fun j : Fin (AreaLaw.Geometry.nestedPatchCount u) ↦ squareSample
          (fun x : Lattice.Site (AreaLaw.rectangularDomain L L) ↦
            ((x.1.1 : ℝ), (x.1.2 : ℝ))) (z - (1, 1))
          (AreaLaw.Geometry.nestedPatchRadius u j.val)) =
          (fun j ↦ AreaLaw.Geometry.nestedPatch (AreaLaw.rectangularDomain L L)
            (z - (1, 1)) u j.val) from
        funext (fun _ ↦ squareSample_integerCoordinates _ _ _)]
      exact hcyl L hL h E₀ Ω hgs (z - (1, 1)) u hu4 huL
    obtain ⟨S, v, hdim, hv, herr⟩ := hc
    obtain ⟨Q, _, hz, hs, _, hd, he⟩ :=
      exists_squarePatch_of_mem_iSup_dependentRegionCylinder
        (fun x : Lattice.Site (AreaLaw.rectangularDomain L L) ↦
          ((x.1.1 : ℝ), (x.1.2 : ℝ))) (z - (1, 1)) hu
        (fun j : Fin (AreaLaw.Geometry.nestedPatchCount u) ↦
          AreaLaw.Geometry.nestedPatchRadius u j.val)
        (fun i j hij ↦ add_le_add_right
          (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hij) (by norm_num : (0 : ℝ) ≤ 2)) u)
        (fun j ↦ AreaLaw.Geometry.le_nestedPatchRadius u j.val)
        (fun j ↦ AreaLaw.Geometry.nestedPatchRadius_le_two_mul hu.le j.isLt)
        S (dependentGlobalConfigIsometry.symm (squareAreaLawState Ω)) v hv
    refine ⟨Q, hz, hs, ?_, by simpa only [LinearIsometryEquiv.apply_symm_apply] using he.trans herr⟩
    have htotal : ((∑ j, Q.dim j : ℕ) : ℝ) ≤
        (AreaLaw.Geometry.nestedPatchCount u : ℝ) * (L : ℝ) ^ R₀ := by
      calc
        _ ≤ ∑ j, (Module.finrank ℂ (S j) : ℝ) := by exact_mod_cast hd
        _ ≤ ∑ _j : Fin (AreaLaw.Geometry.nestedPatchCount u), (L : ℝ) ^ R₀ :=
          Finset.sum_le_sum (fun j _ ↦ hdim j)
        _ = _ := by simp
    have hf : (⌊u / 2⌋₊ : ℝ) ≤ u / 2 :=
      Nat.floor_le (R := ℝ) (a := u / 2) (div_nonneg hu.le zero_le_two)
    have hm : (AreaLaw.Geometry.nestedPatchCount u : ℝ) ≤ B₀ / 2 * Real.log L + 1 := by
      simp only [AreaLaw.Geometry.nestedPatchCount, Nat.cast_add, Nat.cast_one]
      linarith only [hf, huL]
    exact htotal.trans
      ((mul_rpow_le_succ_rpow_of_le_log hB₀.le (by exact_mod_cast hL) hm).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _)
          (Real.rpow_nonneg (Nat.cast_nonneg L) _)))
  · obtain ⟨Q, hz, hs, hd, he⟩ :=
      exists_squarePatch_integerCoordinates_of_radius_le_four
        (AreaLaw.rectangularDomain L L) (by omega : 1 ≤ q) (z - (1, 1)) hu
        (lt_of_not_ge hu4).le (dependentGlobalConfigIsometry.symm (squareAreaLawState Ω))
    refine ⟨Q, hz, hs, ?_, ?_⟩
    · exact (show ((∑ j, Q.dim j : ℕ) : ℝ) ≤ (q : ℝ) ^ 81 by exact_mod_cast hd).trans
        ((le_max_left _ _).trans (le_mul_of_one_le_right (by positivity)
          (Real.one_le_rpow (by exact_mod_cast (show 1 ≤ L by omega)) (by positivity))))
    · simpa only [LinearIsometryEquiv.apply_symm_apply] using
        he.le.trans (Real.rpow_nonneg (Nat.cast_nonneg L) (-p))

end TNLean.PEPS.Approximation
