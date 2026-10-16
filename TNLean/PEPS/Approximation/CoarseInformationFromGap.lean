/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.CoarseInformation
import TNLean.PEPS.AreaLaw.PhysicalCollarInformation

/-!
# Coarse mutual information from the global spectral gap

The physical sublinear collar bound discharges the remaining premise in Proposition 3.1
of the polynomial-PEPS manuscript. The constants precede the scale, finite domain,
Hamiltonian, ground vector and regions. The first physical region may be any subset of
the sampled rectangle union; empty samples and arbitrary choices of rectangle sides are
included. No collar or area-law estimate is assumed.

Source: polynomial-PEPS manuscript, Proposition 3.1 (`prop:coarse`),
`02-information.tex`, lines 91–145, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.Approximation

open AreaLaw

/-- Coarse mutual information on any finite induced domain, from the original
Hamiltonian and its full-system gap. The constants are uniform in the finite
physical data, scale and rectangle union.
Source: polynomial-PEPS manuscript, Proposition 3.1 (`prop:coarse`),
`02-information.tex`, lines 91–145. This version also allows arbitrary finite
induced domains and interaction range. -/
theorem coarse_mutualInformation_le {q R : ℕ} (hq : 1 ≤ q) {J Δ : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) (N₀ : ℕ) (A₀ : ℝ) :
    ∃ β : ℝ, β < 1 ∧ ∃ C u₀ : ℝ, ∀ u : ℝ, u₀ ≤ u →
      ∀ (Λ : Finset (ℤ × ℤ)) (h : AreaLaw.LocalHamiltonian Λ q R J) (E₀ : ℝ)
        (Ω : AreaLaw.StateSpace Λ q),
        AreaLaw.IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        ∀ T : Finset (ℤ × ℤ), IsBoxUnion N₀ T →
          (∀ x ∈ T, ∀ y ∈ T, (Scan.ambientSupDistance x y : ℝ) ≤ A₀ * u) →
          ∀ X ⊆ Finset.univ.filter (fun x : Site Λ ↦ x.val ∈ T),
          ∀ E : Finset (Site Λ),
            (∀ t ∈ T, ∀ y ∈ E, u ^ β < (Scan.ambientSupDistance t y.val : ℝ)) →
            FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω X E ≤ C := by
  have hcol : SublinearCollarBound q R J Δ (2 * (R : ℝ) + 11) 24 :=
    sublinearCollarBound_real q R hq hJ hΔ (by linarith) (by norm_num)
  exact coarse_mutualInformation_le_of_sublinearCollarBound hΔ hcol N₀ A₀

/-- Proposition 3.1 on the original square grid, with no assumed collar bound.
The constants precede the scale, Hamiltonian, ground vector, translated
rectangle union and both physical regions. The local dimension may be one
and the interaction bound may be zero.
Source: polynomial-PEPS manuscript, Proposition 3.1 (`prop:coarse`),
`02-information.tex`, lines 91–145. -/
theorem coarse_mutualInformation_le_square {q : ℕ} (hq : 1 ≤ q)
    {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (N₀ : ℕ) (A₀ : ℝ) :
    ∃ β : ℝ, β < 1 ∧ ∃ C u₀ : ℝ, ∀ u : ℝ, u₀ ≤ u →
      ∀ (L : ℕ) (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
        h.IsGappedGroundState E₀ Ω Δ → ∀ c : ℤ × ℤ, ∀ T : Finset (ℤ × ℤ), IsBoxUnion N₀ T →
          (∀ x ∈ T, ∀ y ∈ T, (Scan.ambientSupDistance x y : ℝ) ≤ A₀ * u) →
          ∀ X ⊆ Finset.univ.filter (fun v : Vertex L ↦ rectangleEmbedding v + c ∈ T),
          ∀ E : Finset (Vertex L),
            (∀ t ∈ T, ∀ v ∈ E,
              u ^ β < (Scan.ambientSupDistance t (rectangleEmbedding v + c) : ℝ)) →
            FiniteProduct.mutualInformation (fun _ : Vertex L ↦ Fin q) Ω X E ≤ C := by
  have hcol : SublinearCollarBound q 1 J Δ 13 24 :=
    sublinearCollarBound_real q 1 hq hJ hΔ (by norm_num) (by norm_num)
  exact coarse_mutualInformation_le_square_of_sublinearCollarBound hJ hΔ hcol N₀ A₀

/-- Coarse information after an arbitrary common real translation of the
ambient lattice and physical coordinates. All constants are chosen before
that translation. Rectangle samples are indexed on the untranslated lattice;
the rectangles themselves may have arbitrary real endpoints.
Source: polynomial-PEPS manuscript, Proposition 3.1 (`prop:coarse`),
`02-information.tex`, lines 91–108, including its common-translation clause. -/
theorem coarse_mutualInformation_le_translated_square {q : ℕ} (hq : 1 ≤ q)
    {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) (N₀ : ℕ) (A₀ : ℝ) :
    ∃ β : ℝ, β < 1 ∧ ∃ C u₀ : ℝ, ∀ u : ℝ, u₀ ≤ u →
      ∀ (L : ℕ) (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
        h.IsGappedGroundState E₀ Ω Δ → ∀ d : ℝ × ℝ,
          ∀ T : Finset (ℤ × ℤ), IsBoxUnion N₀ T →
          (∀ x ∈ T, ∀ y ∈ T,
            dist (Geometry.integerPoint x + d) (Geometry.integerPoint y + d) ≤ A₀ * u) →
          ∀ X ⊆ Finset.univ.filter (fun v : Vertex L ↦ rectangleEmbedding v ∈ T),
          ∀ E : Finset (Vertex L),
            (∀ t ∈ T, ∀ v ∈ E, u ^ β <
              dist (Geometry.integerPoint t + d)
                (Geometry.integerPoint (rectangleEmbedding v) + d)) →
            FiniteProduct.mutualInformation (fun _ : Vertex L ↦ Fin q) Ω X E ≤ C := by
  obtain ⟨β, hβ, C, u₀, hmain⟩ := coarse_mutualInformation_le_square hq hJ hΔ N₀ A₀
  refine ⟨β, hβ, C, u₀, fun u hu L h E₀ Ω hΩ d T hT hdiam X hX E hE ↦ ?_⟩
  have hdist (x y : ℤ × ℤ) :
      dist (Geometry.integerPoint x + d) (Geometry.integerPoint y + d) =
        (Scan.ambientSupDistance x y : ℝ) := by
    simp only [dist_add_right, Scan.ambientSupDistance, Geometry.integerPoint,
      Prod.dist_eq, Real.dist_eq, Int.cast_max, Int.cast_abs, Int.cast_sub]
  exact hmain u hu L h E₀ Ω hΩ 0 T hT
    (fun x hx y hy ↦ by simpa only [hdist] using hdiam x hx y hy)
    X (by simpa only [add_zero] using hX) E
    (fun t ht v hv ↦ by simpa only [hdist, add_zero] using hE t ht v hv)

end TNLean.PEPS.Approximation
