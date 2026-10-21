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
open TNLean.Lattice
namespace TNLean.PEPS.Approximation
open EncodedFrame

/-- The prefactor `C = max (q ^ 81) (1 + B₀ / 2)` of the adaptive patch
constraint. The first entry covers radii below four, the second the
logarithmic number of nested cylinders.

Source: polynomial-PEPS manuscript, Proposition 4.1, `03-patches.tex`,
lines 53–55 and 595–601. -/
noncomputable def adaptivePatchPrefactor (q : ℕ) (B₀ : ℝ) : ℝ :=
  max ((q : ℝ) ^ 81) (1 + B₀ / 2)

/-- The exponent `c = R₀ + 1` of the adaptive patch constraint, for a square
area law at the constant `C_A`, where `R₀` is the radius exponent
`nestedPatchRadiusExponent q J Δ B₀ p C_A`. The added one absorbs the
logarithmic number of nested cylinders.

Source: polynomial-PEPS manuscript, Proposition 4.1, `03-patches.tex`,
lines 540–547 and 595–601. -/
noncomputable def adaptivePatchExponent (q : ℕ) (J Δ B₀ p C_A : ℝ) : ℝ :=
  nestedPatchRadiusExponent q J Δ B₀ p C_A + 1

/-- The prefactor of the adaptive patch constraint is positive for `B₀ ≥ 0`
(`03-patches.tex`, lines 595–601). -/
theorem adaptivePatchPrefactor_pos (q : ℕ) {B₀ : ℝ} (hB₀ : 0 ≤ B₀) :
    0 < adaptivePatchPrefactor q B₀ :=
  lt_of_lt_of_le (by positivity) (le_max_right _ _)

/-- The exponent of the adaptive patch constraint is positive
(`03-patches.tex`, lines 540–547 and 595–601). -/
theorem adaptivePatchExponent_pos {q : ℕ} {J Δ B₀ p : ℝ} (C_A : ℝ)
    (hq : 0 < q) (hJ : 0 < J) (hΔ : 0 < Δ) (hB₀ : 0 ≤ B₀) (hp : 0 ≤ p) :
    0 < adaptivePatchExponent q J Δ B₀ p C_A :=
  add_pos (nestedPatchRadiusExponent_pos C_A hq hJ hΔ hB₀ hp) one_pos

/-- Nested cylinder approximations on a family of closed squares supply adaptive square patches
with at most `C L ^ (R₀ + 1)` cylinder terms, where `C = adaptivePatchPrefactor q B₀`.

For every scale `u` the family has `m u` squares with nondecreasing radii between `u` and `2 u`,
and `m u ≤ B₀ / 2 · log L + 1` at the admissible scales. At every center and every scale
`4 ≤ u ≤ B₀ log L` the hypothesis supplies cylinders with inside dimensions at most `L ^ R₀` and
error at most `L ^ (-p)`. Radii below four use the exact patch with at most `q ^ 81` terms. This
is the common step of the nearest-neighbour and range-`R` patch constructions.

Source: polynomial-PEPS manuscript, Proposition 4.1, `03-patches.tex`, lines 26–54 and
534–603, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem adaptivePatchSupply_of_closedSquare_cylinders
    {q : ℕ} (hq : 1 ≤ q) {B₀ p R₀ : ℝ} (hB₀ : 0 < B₀) (hR₀ : 0 ≤ R₀)
    {L : ℕ} (hL : 2 ≤ L) (Ω : StateSpace L q)
    (m : ℝ → ℕ) (r : (u : ℝ) → Fin (m u) → ℝ)
    (hr : ∀ u, Monotone (r u)) (hle : ∀ u j, u ≤ r u j)
    (hle₂ : ∀ u, 0 ≤ u → ∀ j, r u j ≤ 2 * u)
    (hm : ∀ u, 0 ≤ u → u ≤ B₀ * Real.log L → (m u : ℝ) ≤ B₀ / 2 * Real.log L + 1)
    (hcyl : ∀ (z : ℝ × ℝ) (u : ℝ), 4 ≤ u → u ≤ B₀ * Real.log L →
      letI : LinearOrder (Lattice.Site (AreaLaw.rectangularDomain L L)) :=
        (Fintype.equivFin (Lattice.Site (AreaLaw.rectangularDomain L L))).linearOrder
      ∃ (S : (j : Fin (m u)) → Submodule ℂ
          ((AreaLaw.Geometry.closedSquareSample (AreaLaw.rectangularDomain L L) z (r u j) →
            Fin q) → ℂ))
        (v : EuclideanSpace ℂ
          ((w : (Finset.univ : Finset (Lattice.Site (AreaLaw.rectangularDomain L L)))) →
            Fin q)),
        (∀ j, (Module.finrank ℂ (S j) : ℝ) ≤ (L : ℝ) ^ R₀) ∧
        v.ofLp ∈ (⨆ j, dependentRegionCylinder (Out := fun _ ↦ Fin q)
          (AreaLaw.Geometry.closedSquareSample (AreaLaw.rectangularDomain L L) z (r u j))
          (S j)) ∧
        ‖dependentGlobalConfigIsometry.symm (squareAreaLawState Ω) - v‖ ≤ (L : ℝ) ^ (-p)) :
    AdaptivePatchSupply (latticePos L) Ω B₀ (adaptivePatchPrefactor q B₀) (R₀ + 1) p L := by
  classical
  intro z u hu huL
  suffices hpatch : HasAdaptivePatch
      (fun x : Lattice.Site (AreaLaw.rectangularDomain L L) ↦
        ((x.1.1 : ℝ), (x.1.2 : ℝ))) (squareAreaLawState Ω)
      (adaptivePatchPrefactor q B₀) (R₀ + 1) p L (z - (1, 1)) u by
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
  · let P (regions : Fin (m u) →
        Finset (Lattice.Site (AreaLaw.rectangularDomain L L))) : Prop :=
      ∃ (S : (j : Fin (m u)) → Submodule ℂ ((regions j → Fin q) → ℂ))
        (v : EuclideanSpace ℂ
          ((w : (Finset.univ : Finset (Lattice.Site (AreaLaw.rectangularDomain L L)))) → Fin q)),
        (∀ j, (Module.finrank ℂ (S j) : ℝ) ≤ (L : ℝ) ^ R₀) ∧
        v.ofLp ∈ (⨆ j, dependentRegionCylinder (Out := fun _ ↦ Fin q) (regions j) (S j)) ∧
        ‖dependentGlobalConfigIsometry.symm (squareAreaLawState Ω) - v‖ ≤ (L : ℝ) ^ (-p)
    have hc : P (fun j ↦ squareSample
        (fun x : Lattice.Site (AreaLaw.rectangularDomain L L) ↦
          ((x.1.1 : ℝ), (x.1.2 : ℝ))) (z - (1, 1)) (r u j)) := by
      rw [show (fun j : Fin (m u) ↦ squareSample
          (fun x : Lattice.Site (AreaLaw.rectangularDomain L L) ↦
            ((x.1.1 : ℝ), (x.1.2 : ℝ))) (z - (1, 1)) (r u j)) =
          (fun j ↦ AreaLaw.Geometry.closedSquareSample (AreaLaw.rectangularDomain L L)
            (z - (1, 1)) (r u j)) from
        funext (fun _ ↦ squareSample_integerCoordinates _ _ _)]
      exact hcyl (z - (1, 1)) u hu4 huL
    obtain ⟨S, v, hdim, hv, herr⟩ := hc
    obtain ⟨Q, _, hz, hs, _, hd, he⟩ :=
      exists_squarePatch_of_mem_iSup_dependentRegionCylinder
        (fun x : Lattice.Site (AreaLaw.rectangularDomain L L) ↦
          ((x.1.1 : ℝ), (x.1.2 : ℝ))) (z - (1, 1)) hu (r u)
        (fun i j hij ↦ hr u hij) (hle u) (hle₂ u hu.le)
        S (dependentGlobalConfigIsometry.symm (squareAreaLawState Ω)) v hv
    refine ⟨Q, hz, hs, ?_, by simpa only [LinearIsometryEquiv.apply_symm_apply] using he.trans herr⟩
    have htotal : ((∑ j, Q.dim j : ℕ) : ℝ) ≤ (m u : ℝ) * (L : ℝ) ^ R₀ := by
      calc
        _ ≤ ∑ j, (Module.finrank ℂ (S j) : ℝ) := by exact_mod_cast hd
        _ ≤ ∑ _j : Fin (m u), (L : ℝ) ^ R₀ := Finset.sum_le_sum (fun j _ ↦ hdim j)
        _ = _ := by simp
    exact htotal.trans
      ((mul_rpow_le_succ_rpow_of_le_log hB₀.le (by exact_mod_cast hL) (hm u hu.le huL)).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _)
          (Real.rpow_nonneg (Nat.cast_nonneg L) _)))
  · obtain ⟨Q, hz, hs, hd, he⟩ :=
      exists_squarePatch_integerCoordinates_of_radius_le_four
        (AreaLaw.rectangularDomain L L) hq (z - (1, 1)) hu
        (lt_of_not_ge hu4).le (dependentGlobalConfigIsometry.symm (squareAreaLawState Ω))
    refine ⟨Q, hz, hs, ?_, ?_⟩
    · exact (show ((∑ j, Q.dim j : ℕ) : ℝ) ≤ (q : ℝ) ^ 81 by exact_mod_cast hd).trans
        ((le_max_left _ _).trans (le_mul_of_one_le_right (adaptivePatchPrefactor_pos q hB₀.le).le
          (Real.one_le_rpow (by exact_mod_cast (show 1 ≤ L by omega)) (by linarith))))
    · simpa only [LinearIsometryEquiv.apply_symm_apply] using
        he.le.trans (Real.rpow_nonneg (Nat.cast_nonneg L) (-p))

/-- A square entropy area law at the constant `C_A` supplies adaptive square
patches with at most `C L ^ c` cylinder terms, where
`C = adaptivePatchPrefactor q B₀` and `c = adaptivePatchExponent q J Δ B₀ p C_A`.
The construction uses the same cylinder sum as the source statement, including
when a sample is empty.

Source: polynomial-PEPS manuscript, Proposition 4.1, `03-patches.tex`,
lines 26–54 and 534–603, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem SquareEntropyAreaLawAt.adaptivePatchSupply
    {q : ℕ} {J Δ C_A : ℝ} (hA : SquareEntropyAreaLawAt q (IsSquareGroundState q J Δ) C_A)
    (hq : 2 ≤ q) (hJ : 0 < J) (hΔ : 0 < Δ) {B₀ p : ℝ} (hB₀ : 0 < B₀) (hp : 0 < p) :
    ∀ L : ℕ, 2 ≤ L → ∀ Ω : StateSpace L q, IsSquareGroundState q J Δ L Ω →
        AdaptivePatchSupply (latticePos L) Ω B₀ (adaptivePatchPrefactor q B₀)
          (adaptivePatchExponent q J Δ B₀ p C_A) p L := by
  intro L hL Ω ⟨h, E₀, hgs⟩
  refine adaptivePatchSupply_of_closedSquare_cylinders (by omega) hB₀
    (nestedPatchRadiusExponent_pos C_A (by omega) hJ hΔ hB₀.le hp.le).le hL Ω
    AreaLaw.Geometry.nestedPatchCount (fun u j ↦ AreaLaw.Geometry.nestedPatchRadius u j.val)
    (fun u i j hij ↦ add_le_add_right
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hij) (by norm_num : (0 : ℝ) ≤ 2)) u)
    (fun u j ↦ AreaLaw.Geometry.le_nestedPatchRadius u j.val)
    (fun u hu j ↦ AreaLaw.Geometry.nestedPatchRadius_le_two_mul hu j.isLt)
    (fun u hu huL ↦ ?_)
    (fun z u hu4 huL ↦ hA.uniform_nestedPatch_cylinders hq hJ hΔ hB₀ hp L hL h E₀ Ω hgs z u
      hu4 huL)
  have hf : (⌊u / 2⌋₊ : ℝ) ≤ u / 2 :=
    Nat.floor_le (R := ℝ) (a := u / 2) (div_nonneg hu zero_le_two)
  simp only [AreaLaw.Geometry.nestedPatchCount, Nat.cast_add, Nat.cast_one]
  linarith only [hf, huL]

/-- Conditional assembly of the adaptive patch constraint from the square
entropy area law. The constants are `adaptivePatchPrefactor q B₀` and
`adaptivePatchExponent q J Δ B₀ p C_A` at an area-law constant `C_A`, as in
`SquareEntropyAreaLawAt.adaptivePatchSupply`.

Source: polynomial-PEPS manuscript, Proposition 4.1, `03-patches.tex`,
lines 26–54 and 534–603, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The area-law premise is discharged
in `adaptivePatchConstraint`. -/
theorem SquareEntropyAreaLaw.adaptivePatchConstraint
    (harea : SquareEntropyAreaLaw) : AdaptivePatchConstraint := by
  intro q hq J Δ hJ hΔ B₀ p hB₀ hp
  obtain ⟨C_A, hA⟩ := harea.exists_squareEntropyAreaLawAt hq hJ hΔ
  exact ⟨adaptivePatchPrefactor q B₀, adaptivePatchExponent q J Δ B₀ p C_A,
    adaptivePatchPrefactor_pos q hB₀.le,
    adaptivePatchExponent_pos C_A (by omega) hJ hΔ hB₀.le hp.le,
    hA.adaptivePatchSupply hq hJ hΔ hB₀ hp⟩

end TNLean.PEPS.Approximation
