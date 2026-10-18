/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BoundaryTheoremFromTwoFamilies
import TNLean.PEPS.AreaLaw.Geometry.TwoFamilyAssembly
import TNLean.PEPS.AreaLaw.RectangularSpecialization
import TNLean.PEPS.AreaLaw.VertexBoundaryCorollaries

/-!
# The two-dimensional area law

Theorem 1.1 of the area-law manuscript: for every finite induced domain of the
square lattice, every admissible local Hamiltonian with a gapped ground state
and every cut, the regional entropy is at most a constant times the number of
cut edges, with the constant chosen before the domain, Hamiltonian, state and
cut. Corollary 1.2 restates the bound for the vertex boundaries and for
rectangles.

## Main results

* `uniformAreaLawConstant`, `exists_regionalEntropy_le_uniformAreaLawConstant`: the
  constant produced by the proof of Theorem 1.1 from the named constants of
  Propositions 9.6, 10.2 and 11.2, and the bound with this constant.
* `uniformAreaLaw`: Theorem 1.1.
* `uniformAreaLaw_vertex_boundary_bounds`, `rectangularEntropyAreaLaw`:
  Corollary 1.2.
* `squareEntropyAreaLaw`: the square-grid specialization used by the
  polynomial-PEPS manuscript as Proposition 2.1.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Theorem 1.1 (`00-introduction.tex`, lines 39–53) and
  Corollary 1.2 (lines 69–86), with the proof in `10-geometry.tex`,
  lines 803–857. Source revision:
  `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

The explicit constant is recorded in `docs/notes/arealaw2d_explicit_constant.tex`
(Section `sec:top`).

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix SpectralFilter
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw

/-- The constant of Theorem 1.1 produced by its proof from the named constants of
Propositions 9.6, 10.2 and 11.2, at the template constants `D₀ = 2R + 11` and `C_tpl = 24`:
* `C₁ = sublinearCollarConstant q J Δ Cbox` and
  `N₁ = sublinearCollarThreshold q R J Δ Cbox Ctr ct Cent eent Cen een` (Proposition 9.6),
  for a safe-box constant `Cbox` at clearance `2R + 11` and the truncation and transport
  constants `Ctr, ct, Cent, eent, Cen, een` of the scanner;
* `C₂ = amplificationConstant q R J Δ C₀ Cloc cloc 100` and
  `N₂ = max (amplificationThreshold q R J Δ C₀ Cloc cloc 100) N₃` with `C₀ = max C₁ 1` and
  `N₃ = Exponents.collarRadiusThreshold C₂ 1` (Proposition 10.2), for the filter-locality
  constants `Cloc, cloc` of the positive constraints;
* `C₃ = twoFamilyDecompositionConstant (2R + 11) 24 n_* c₁` at the lower scale
  `n_* = uniformAreaLawScale N₁ N₂ C₂` (Proposition 11.2), for the birth-separation
  constant `c₁ = Geometry.birthTemplateSeparationConstant = 1/112`;
and the constant is `uniformAreaLawConstantOf q C₂ C₃ = c_D log q + c_M c_D / 2` with
`c_D = max C₃ 0` and `c_M = max C₂ 0`. The source asserts only that a constant exists.
Source: proof of Theorem 1.1, `10-geometry.tex`, lines 803–857; the constant is tabulated
in `docs/notes/arealaw2d_explicit_constant.tex`, Section `sec:top`. -/
noncomputable def uniformAreaLawConstant (q R : ℕ)
    (J Δ Cbox Ctr ct Cent eent Cen een Cloc cloc : ℝ) : ℝ :=
  let C₀ := max (sublinearCollarConstant q J Δ Cbox) 1
  let C₂ := amplificationConstant q R J Δ C₀ Cloc cloc 100
  let N₂ := max (amplificationThreshold q R J Δ C₀ Cloc cloc 100)
    (Exponents.collarRadiusThreshold C₂ 1)
  let nstar := uniformAreaLawScale (sublinearCollarThreshold q R J Δ Cbox Ctr ct Cent eent Cen een)
    N₂ C₂
  uniformAreaLawConstantOf q C₂ (twoFamilyDecompositionConstant (2 * (R : ℝ) + 11) 24 nstar
    Geometry.birthTemplateSeparationConstant)

/-- **The area law with the constant of its proof, from the named constants of the three
propositions.** Let `Cbox ≥ 0` bound the safe-box entropy at clearance `2R + 11` by
`Cbox r^(1 + ε_box)`, and let `Cloc ≥ 0`, `cloc > 0` be filter-locality constants of the
positive constraints in the form of `amplificationBound_of_locality`. Then there are
truncation and transport constants `Ctr, ct, Cent, eent, Cen, een` of the scanner such that
every cut of every finite induced domain, for every gapped ground state, has regional entropy
at most `uniformAreaLawConstant q R J Δ Cbox Ctr ct Cent eent Cen een Cloc cloc` times the
number of cut edges, where the birth-separation constant is `c₁ = 1/112`. The truncation and
transport constants remain existential because the sublinear collar bound
`sublinearCollarBound_real_of_boxEntropy` supplies them so.

This is an auxiliary result: Theorem 1.1 of the source (`00-introduction.tex`, lines 39–53)
asserts only that a constant exists, and `uniformAreaLaw` is that statement. Source: proof
of Theorem 1.1, `10-geometry.tex`, lines 803–857; the constant is tabulated in
`docs/notes/arealaw2d_explicit_constant.tex`, Section `sec:top`. -/
theorem exists_regionalEntropy_le_uniformAreaLawConstant
    (q R : ℕ) (hq : 1 ≤ q) {J Δ Cbox Cloc cloc : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hCbox : 0 ≤ Cbox)
    (hbox : ∀ r : ℕ, 1 ≤ r → boxEntropy q R J Δ (2 * R + 11) r ≤
      Cbox * (r : ℝ) ^ (1 + (Exponents.boxError : ℝ)))
    (hCloc : 0 ≤ Cloc) (hcloc : 0 < cloc)
    (htail : ∀ {n : Type} [Fintype n] [DecidableEq n]
      {H : Matrix n n ℂ} {Ω : EuclideanSpace ℂ n} {h : Matrix n n ℂ},
      H.IsHermitian → ‖Ω‖ = 1 → h.IsHermitian → ‖h‖ ≤ J →
      ∀ (L : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ), (∀ X, ‖L X‖ ≤ ‖X‖) → L 1 = 1 →
      (∀ X, X.IsHermitian → (L X).IsHermitian) →
      L (CFC.abs (L (centeredFilter Exponents.amplificationPower (Δ / 2) H Ω h))) =
        CFC.abs (L (centeredFilter Exponents.amplificationPower (Δ / 2) H Ω h)) →
      ∀ {l : ℝ}, 0 ≤ l →
      (∀ t : ℝ, ‖Matrix.hermitianUnitaryPath H t * h * Matrix.hermitianUnitaryPath H (-t) -
          L (Matrix.hermitianUnitaryPath H t * h * Matrix.hermitianUnitaryPath H (-t))‖ ≤
        ‖h‖ * min 2 (localizationPrefactor R 2 2 * Real.exp (localizationVelocity R
          (1 + 2 * R * (R + 1)) (((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ) * J) * |t| -
            1 / 2 * l))) →
      ‖positiveConstraint (positiveNormalization Exponents.amplificationPower (Δ / 2) J)
          (centeredFilter Exponents.amplificationPower (Δ / 2) H Ω h) -
          L (positiveConstraint (positiveNormalization Exponents.amplificationPower (Δ / 2) J)
            (centeredFilter Exponents.amplificationPower (Δ / 2) H Ω h))‖ ≤
        Cloc * Real.exp (-(cloc * l ^ kernelExponent Exponents.amplificationPower))) :
    ∃ Ctr ct Cent eent Cen een : ℝ, 0 < Ctr ∧ 0 < ct ∧
      0 ≤ uniformAreaLawConstant q R J Δ Cbox Ctr ct Cent eent Cen een Cloc cloc ∧
      ∀ Λ : Finset (ℤ × ℤ), ∀ H : LocalHamiltonian Λ q R J, ∀ E₀ : ℝ, ∀ Ω : StateSpace Λ q,
        IsGappedGroundState Λ q H.operator E₀ Ω Δ → ∀ A : Finset (Site Λ),
          regionalEntropy Λ q Ω A ≤
            uniformAreaLawConstant q R J Δ Cbox Ctr ct Cent eent Cen een Cloc cloc *
              (edgeBoundary Λ A).card := by
  obtain ⟨Ctr, ct, Cent, eent, Cen, een, hCtr, hct, hcol⟩ :=
    sublinearCollarBound_real_of_boxEntropy (D₀ := 2 * (R : ℝ) + 11) (Ctpl := 24) q R hq hJ
      hΔ (by linarith) le_rfl hCbox hbox
  have hamp := amplificationBound_of_locality (q := q) (R := R) (J := J)
    (C₀ := max (sublinearCollarConstant q J Δ Cbox) 1) hΔ (lt_max_of_lt_right one_pos) hCloc
    hcloc htail 100
  exact ⟨Ctr, ct, Cent, eent, Cen, een, hCtr, hct, uniformAreaLawConstantOf_nonneg hq _ _,
    regionalEntropy_le_of_collar_amplification_twoFamilies_constants hq hΔ hcol hamp
      (isTwoFamilyDecompositionConstant_twoFamilyDecompositionConstant _ _ _
        Geometry.isBirthSeparationConstant_birthTemplateSeparationConstant)⟩

/-- Theorem 1.1 of the area-law manuscript, `00-introduction.tex`, lines 39–53:
the uniform boundary law for gapped ground states on finite induced domains of
the square lattice. The constant is `uniformAreaLawConstant` at a safe-box constant and
filter-locality constants whose existence is proved
(`exists_regionalEntropy_le_uniformAreaLawConstant`). -/
theorem uniformAreaLaw : UniformAreaLaw := by
  intro q hq R J Δ hJ hΔ
  obtain ⟨Cbox, hCbox, hbox⟩ := Scan.exists_boxEntropy_le_boxError q R hq hJ.le hΔ
  obtain ⟨Cloc, cloc, hCloc, hcloc, htail⟩ := exists_norm_positiveConstraint_sub_map_le
    (by norm_num [Exponents.amplificationPower] : 1 ≤ Exponents.amplificationPower) hΔ hJ.le
    (localizationPrefactor_nonneg R 2 2) (localizationVelocity_pos R (1 + 2 * R * (R + 1))
      (((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ) * J)) one_half_pos
  obtain ⟨_, _, _, _, _, _, _, _, hC, hbound⟩ :=
    exists_regionalEntropy_le_uniformAreaLawConstant q R hq hJ.le hΔ hCbox.le
      (hbox _ (by omega)) hCloc hcloc htail
  exact ⟨_, hC, hbound⟩

/-- Corollary 1.2 of the area-law manuscript, `00-introduction.tex`, lines
69–86: the uniform bound in terms of the inner and the endpoint vertex
boundaries. -/
theorem uniformAreaLaw_vertex_boundary_bounds :
    ∀ q : ℕ, 1 ≤ q → ∀ R : ℕ, ∀ J Δ : ℝ, 0 < J → 0 < Δ →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ Λ : Finset (ℤ × ℤ), ∀ H : LocalHamiltonian Λ q R J,
          ∀ E₀ : ℝ, ∀ Ω : StateSpace Λ q,
            IsGappedGroundState Λ q H.operator E₀ Ω Δ →
              ∀ A : Finset (Site Λ),
                regionalEntropy Λ q Ω A ≤ 4 * C * (innerBoundary Λ A).card ∧
                regionalEntropy Λ q Ω A ≤ 2 * C * (endpointBoundary Λ A).card :=
  uniformAreaLaw.vertex_boundary_bounds

/-- Corollary 1.2 of the area-law manuscript for rectangles,
`00-introduction.tex`, lines 69–86. -/
theorem rectangularEntropyAreaLaw : RectangularEntropyAreaLaw :=
  uniformAreaLaw.rectangularEntropyAreaLaw

/-- The square-grid entropy area law, Proposition 2.1 of the polynomial-PEPS
manuscript, `01-preliminaries.tex`, lines 39–58. -/
theorem squareEntropyAreaLaw : Approximation.SquareEntropyAreaLaw :=
  rectangularEntropyAreaLaw.squareEntropyAreaLaw

end TNLean.PEPS.AreaLaw
