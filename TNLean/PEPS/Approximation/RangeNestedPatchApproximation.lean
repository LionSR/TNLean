/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AdaptivePatchConstraintFromAreaLaw
import TNLean.PEPS.Approximation.RangeNestedPatchMarginalCloseness
import TNLean.PEPS.Approximation.RangeSquareGroundState

/-!
# Adaptive square patches at interaction range `R`

For the range-`R` family `IsRangeSquareGroundState q R J Δ` obeying the square entropy area law
at a constant `C_A`, the range-`R` nested squares give nested regional cylinders with inside
dimensions at most `L ^ R₀`, and adaptive square patches with at most `C L ^ (R₀ + 1)` cylinder
terms. Here `C = adaptivePatchPrefactor q B₀` is the nearest-neighbour prefactor and
`R₀ = rangeNestedPatchRadiusExponent q R J Δ B₀ p C_A` uses the range-`R` filter exponent.

The statements are instances of the closed-square cores
`SquareEntropyAreaLawAt.closedSquareSample_entropy_le`,
`exists_closedSquare_cylinders_of_marginal_closeness` and
`adaptivePatchSupply_of_closedSquare_cylinders`, which also give the nearest-neighbour
statements.

**Extension beyond the source:** the source proves Proposition 4.1 for on-site and
nearest-neighbour interactions; the range-`R` statements are not in the source.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
Proposition 4.1, `03-patches.tex`, lines 26–54 and 335–603, read with interactions of range `R`
as in *A two-dimensional area law from a global spectral gap*, `eq:hamiltonian`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscripts; no upstream Lean text is reused.
-/

open scoped BigOperators
open TNLean.Lattice

namespace TNLean.PEPS.Approximation
open EncodedFrame

/-- The radius exponent `R₀` of the range-`R` nested cylinders, for a square area law at the
constant `C_A`: the explicit radius exponent at `C_0 = 16 C_S + log 8` with
`C_S = max 1 (16 C_A)` and at the range-`R` filter exponent `rangePatchFilterExponent q R J Δ`.

Extension of polynomial-PEPS `eq:patch-explicit-radius`, `03-patches.tex`, lines 540–547, to
interactions of range `R`. -/
noncomputable def rangeNestedPatchRadiusExponent (q R : ℕ) (J Δ B₀ p C_A : ℝ) : ℝ :=
  regularizedPatchRadiusExponent (16 * max 1 (16 * C_A) + Real.log 8) B₀ p
    (rangePatchFilterExponent q R J Δ)

/-- The range-`R` radius exponent is positive. -/
theorem rangeNestedPatchRadiusExponent_pos {q R : ℕ} {J Δ B₀ p : ℝ} (C_A : ℝ)
    (hq : 0 < q) (hR : 1 ≤ R) (hJ : 0 < J) (hΔ : 0 < Δ) (hB₀ : 0 ≤ B₀) (hp : 0 ≤ p) :
    0 < rangeNestedPatchRadiusExponent q R J Δ B₀ p C_A := by
  have hκ := rangePatchFilterExponent_pos hq hR hJ hΔ
  have hC : 0 ≤ 16 * max 1 (16 * C_A) + Real.log 8 :=
    add_nonneg (by positivity) (Real.log_nonneg (by norm_num))
  unfold rangeNestedPatchRadiusExponent regularizedPatchRadiusExponent
  positivity

/-- The exponent `c = R₀ + 1` of the range-`R` adaptive patches. -/
noncomputable def rangeAdaptivePatchExponent (q R : ℕ) (J Δ B₀ p C_A : ℝ) : ℝ :=
  rangeNestedPatchRadiusExponent q R J Δ B₀ p C_A + 1

/-- The range-`R` adaptive patch exponent is positive. -/
theorem rangeAdaptivePatchExponent_pos {q R : ℕ} {J Δ B₀ p : ℝ} (C_A : ℝ)
    (hq : 0 < q) (hR : 1 ≤ R) (hJ : 0 < J) (hΔ : 0 < Δ) (hB₀ : 0 ≤ B₀) (hp : 0 ≤ p) :
    0 < rangeAdaptivePatchExponent q R J Δ B₀ p C_A :=
  add_pos (rangeNestedPatchRadiusExponent_pos C_A hq hR hJ hΔ hB₀ hp) one_pos

/-- The original-state entropy of every range-`R` nested square is at most `C_S (1 + u)` with
`C_S = max 1 (16 C_A)`, for every state of a family `G` obeying the square entropy area law at
`C_A`.

Extension of polynomial-PEPS `03-patches.tex`, lines 362–368, to the range-`R` squares. -/
theorem SquareEntropyAreaLawAt.rangeNestedPatch_entropy_le
    {q : ℕ} {G : ∀ L : ℕ, StateSpace L q → Prop} {C_A : ℝ}
    (hA : SquareEntropyAreaLawAt q G C_A) (R : ℕ) :
    ∀ (L : ℕ) (Ω : StateSpace L q), G L Ω →
      ∀ (z : ℝ × ℝ) (u : ℝ), 0 ≤ u →
        ∀ j : Fin (AreaLaw.Geometry.rangeNestedPatchCount R u),
          Entropy.regionEntropy
            (AreaLaw.Geometry.rangeNestedPatch (AreaLaw.rectangularDomain L L) z R u j.val)
            (squareAreaLawState Ω) ≤ max 1 (16 * C_A) * (1 + u) := fun L Ω hΩ z u hu j ↦
  hA.closedSquareSample_entropy_le L Ω hΩ z u _
    (hu.trans (AreaLaw.Geometry.le_rangeNestedPatchRadius R u j.val))
    (AreaLaw.Geometry.rangeNestedPatchRadius_le_two_mul hu j.isLt)

open Classical in
/-- A square entropy area law at the constant `C_A` for the range-`R` family gives a sum of
range-`R` nested regional cylinders with inside dimensions at most `L ^ R₀`, where
`R₀ = rangeNestedPatchRadiusExponent q R J Δ B₀ p C_A`, and error at most `L ^ (-p)`. The
exponent depends only on `q`, `R`, `J`, `Δ`, `B₀`, `p` and `C_A`.

Extension of polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 484–563, to
interactions of range `R`. -/
theorem SquareEntropyAreaLawAt.uniform_rangeNestedPatch_cylinders
    {q R : ℕ} {J Δ C_A : ℝ}
    (hA : SquareEntropyAreaLawAt q (IsRangeSquareGroundState q R J Δ) C_A)
    (hq : 0 < q) (hR : 1 ≤ R) (hJ : 0 < J) (hΔ : 0 < Δ) {B₀ p : ℝ} (hB₀ : 0 < B₀)
    (hp : 0 < p) :
    ∀ (L : ℕ), 2 ≤ L → ∀ Ω : StateSpace L q, IsRangeSquareGroundState q R J Δ L Ω →
      ∀ (center : ℝ × ℝ) (u : ℝ), 0 ≤ u → u ≤ B₀ * Real.log L →
        let Λ := AreaLaw.rectangularDomain L L
        letI : LinearOrder (Lattice.Site Λ) :=
          (Fintype.equivFin (Lattice.Site Λ)).linearOrder
        let m := AreaLaw.Geometry.rangeNestedPatchCount R u
        let regions : Fin m → Finset (Lattice.Site Λ) :=
          fun j ↦ AreaLaw.Geometry.rangeNestedPatch Λ center R u j.val
        let U := dependentGlobalConfigIsometry
          (V := Lattice.Site Λ) (Out := fun _ ↦ Fin q)
        let Ωᵤ := U.symm (squareAreaLawState Ω)
        ∃ (S : (j : Fin m) → Submodule ℂ ((regions j → Fin q) → ℂ))
          (v : EuclideanSpace ℂ
            ((w : (Finset.univ : Finset (Lattice.Site Λ))) → Fin q)),
          (∀ j, (Module.finrank ℂ (S j) : ℝ) ≤
            (L : ℝ) ^ rangeNestedPatchRadiusExponent q R J Δ B₀ p C_A) ∧
          (v : (((w : (Finset.univ : Finset (Lattice.Site Λ))) → Fin q) → ℂ)) ∈
            (⨆ j, dependentRegionCylinder
              (Out := fun _ : Lattice.Site Λ ↦ Fin q) (regions j) (S j)) ∧
          ‖Ωᵤ - v‖ ≤ (L : ℝ) ^ (-p) := by
  intro L hL Ω hΩ center u hu huL
  obtain ⟨H, E₀, hgs⟩ := hΩ
  have hκ := rangePatchFilterExponent_pos hq hR hJ hΔ
  exact exists_closedSquare_cylinders_of_marginal_closeness hL hB₀ hp hκ
    (lt_of_lt_of_le zero_lt_one (le_max_left 1 (16 * C_A))) (squareAreaLawState Ω) hgs.1
    center hu huL (AreaLaw.Geometry.rangeNestedPatchCount_pos R u)
    (fun j ↦ AreaLaw.Geometry.rangeNestedPatchRadius R u j.val)
    (fun _ _ hij ↦ AreaLaw.Geometry.rangeNestedPatchRadius_mono R u hij)
    (fun j ↦ hA.rangeNestedPatch_entropy_le R L Ω ⟨H, E₀, hgs⟩ center u hu j)
    (fun b hb ↦ rangeNestedPatch_minimizer_marginal_closeness q R hR hJ.le hΔ hκ
      (rangePatchFilterExponent_le_half q R J Δ)
      (mul_sq_le_div_1024_of_le_rangePatchFilterExponent hJ.le hΔ.le hκ.le le_rfl)
      _ H E₀ _ hgs center u b hu hb)

/-- A square entropy area law at the constant `C_A` for the range-`R` family supplies adaptive
square patches with at most `C L ^ c` cylinder terms, where `C = adaptivePatchPrefactor q B₀`
and `c = rangeAdaptivePatchExponent q R J Δ B₀ p C_A`.

Extension of polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 26–54 and 534–603, to
interactions of range `R`. -/
theorem SquareEntropyAreaLawAt.rangeAdaptivePatchSupply
    {q R : ℕ} {J Δ C_A : ℝ}
    (hA : SquareEntropyAreaLawAt q (IsRangeSquareGroundState q R J Δ) C_A)
    (hq : 0 < q) (hR : 1 ≤ R) (hJ : 0 < J) (hΔ : 0 < Δ) {B₀ p : ℝ} (hB₀ : 0 < B₀)
    (hp : 0 < p) :
    ∀ L : ℕ, 2 ≤ L → ∀ Ω : StateSpace L q, IsRangeSquareGroundState q R J Δ L Ω →
        AdaptivePatchSupply (latticePos L) Ω B₀ (adaptivePatchPrefactor q B₀)
          (rangeAdaptivePatchExponent q R J Δ B₀ p C_A) p L := by
  intro L hL Ω hΩ
  refine adaptivePatchSupply_of_closedSquare_cylinders hq hB₀
    (rangeNestedPatchRadiusExponent_pos C_A hq hR hJ hΔ hB₀.le hp.le).le hL Ω
    (AreaLaw.Geometry.rangeNestedPatchCount R)
    (fun u j ↦ AreaLaw.Geometry.rangeNestedPatchRadius R u j.val)
    (fun u _ _ hij ↦ AreaLaw.Geometry.rangeNestedPatchRadius_mono R u hij)
    (fun u j ↦ AreaLaw.Geometry.le_rangeNestedPatchRadius R u j.val)
    (fun u hu j ↦ AreaLaw.Geometry.rangeNestedPatchRadius_le_two_mul hu j.isLt)
    (fun u hu huL ↦ ?_)
    (fun z u hu4 huL ↦ hA.uniform_rangeNestedPatch_cylinders hq hR hJ hΔ hB₀ hp L hL Ω hΩ z u
      (by linarith) huL)
  have hs : (2 : ℝ) ≤ AreaLaw.Geometry.rangePatchSpacing R := by
    exact_mod_cast AreaLaw.Geometry.two_le_rangePatchSpacing hR
  have hf : (⌊u / AreaLaw.Geometry.rangePatchSpacing R⌋₊ : ℝ) ≤
      u / AreaLaw.Geometry.rangePatchSpacing R :=
    Nat.floor_le (div_nonneg hu (by linarith))
  have hdiv : u / AreaLaw.Geometry.rangePatchSpacing R ≤ u / 2 :=
    div_le_div_of_nonneg_left hu (by norm_num) hs
  simp only [AreaLaw.Geometry.rangeNestedPatchCount, Nat.cast_add, Nat.cast_one]
  linarith only [hf, hdiv, huL]

end TNLean.PEPS.Approximation
