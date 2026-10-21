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

At every interaction range `R`, the collar constant and threshold at the transport constants of
the companion library are closed-form functions of `q, R, J, Δ` (`collarConstantClosed`,
`collarThresholdClosed`), and so are the constant and the scale threshold of Proposition 3.1
(`coarseInformationConstantClosed`, `coarseInformationThresholdClosed`). The polynomial-PEPS
manuscript treats only nearest-neighbour interactions, so the statements at range `R` are
auxiliary results.

Source: polynomial-PEPS manuscript, Proposition 3.1 (`prop:coarse`),
`02-information.tex`, lines 91–145, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open TNLean.Lattice

namespace TNLean.PEPS.Approximation

open AreaLaw

/-! ### The collar constants at range `R` -/

/-- The safe-box constant of area-law Proposition 9.5 at interaction range `R`, at the transport
constants of the companion library: `Scan.physicalBoxConstantExplicit q R J Δ` at threshold
`1/8`, entropy constant `200000` with exponent `2`, and energy constant
`3 (18 π² + 6144 e^{π² + 1})` with exponent `4`. Source: area-law Proposition 9.5,
`08-scanner.tex`, lines 681–805, with Proposition 7.4, `06-transport.tex`, lines 377–434. -/
noncomputable def collarBoxConstantClosed (q R : ℕ) (J Δ : ℝ) : ℝ :=
  AreaLaw.Scan.physicalBoxConstantExplicit q R J Δ TensorPower.ReplicaTransport.transportThreshold
    TensorPower.ReplicaTransport.transportEntropyConst
    TensorPower.ReplicaTransport.transportEntropyExponent
    TensorPower.ReplicaTransport.transportEnergyConst
    TensorPower.ReplicaTransport.transportEnergyExponent

/-- The constant of the sublinear collar bound at range `R`, at the transport constants of the
companion library: `sublinearCollarConstant q J Δ (collarBoxConstantClosed q R J Δ)`. Source:
area-law Proposition 9.6, `08-scanner.tex`, lines 808–827 and 942–943. -/
noncomputable def collarConstantClosed (q R : ℕ) (J Δ : ℝ) : ℝ :=
  AreaLaw.sublinearCollarConstant q J Δ (collarBoxConstantClosed q R J Δ)

/-- The threshold of the sublinear collar bound at range `R`, at the transport constants of the
companion library, with the truncation constant `latticeTruncationRadiusConstant R J Δ 10`.
Source: area-law Proposition 9.6, `08-scanner.tex`, lines 808–827 and 942–943. -/
noncomputable def collarThresholdClosed (q R : ℕ) (J Δ : ℝ) : ℕ :=
  AreaLaw.sublinearCollarThreshold q R J Δ (collarBoxConstantClosed q R J Δ)
    (AreaLaw.latticeTruncationRadiusConstant R J Δ 10)
    TensorPower.ReplicaTransport.transportThreshold
    TensorPower.ReplicaTransport.transportEntropyConst
    TensorPower.ReplicaTransport.transportEntropyExponent
    TensorPower.ReplicaTransport.transportEnergyConst
    TensorPower.ReplicaTransport.transportEnergyExponent

/-- **Proposition 9.6 at range `R`, at closed-form constants.** For `q ≥ 1`, `J ≥ 0`,
`Δ > 0` and every clearance `D₀ > 2R + 10`, the sublinear collar bound at range `R`, clearance
`D₀` and template constant `24` holds with the constant `collarConstantClosed q R J Δ` and the
threshold `collarThresholdClosed q R J Δ`; neither depends on `D₀`. Source: area-law
Propositions 9.5 and 9.6, `08-scanner.tex`, lines 681–827 and 942–943, with Proposition 7.4,
`06-transport.tex`, lines 377–434. -/
theorem sublinearCollarBoundAt_closed {q R : ℕ} (hq : 1 ≤ q) {J Δ D₀ : ℝ} (hJ : 0 ≤ J)
    (hΔ : 0 < Δ) (hD₀ : 2 * (R : ℝ) + 10 < D₀) :
    AreaLaw.SublinearCollarBoundAt q R J Δ D₀ 24 (collarConstantClosed q R J Δ)
      (collarThresholdClosed q R J Δ) :=
  AreaLaw.sublinearCollarBound_real_explicit (D₀ := D₀) (Ctpl := 24) q R hq hJ hΔ hD₀
    (by norm_num) _ _ _ _ _ TensorPower.ReplicaTransport.transportThreshold_pos
    AreaLaw.Scan.CollarScan.finiteFamilyTransportBound_explicit

/-- The constant of Proposition 3.1 at range `R` at closed-form constants: the amplification
constant of Proposition 10.2 at the collar constant `collarConstantClosed q R J Δ`, made
nonnegative. Source: polynomial-PEPS Proposition 3.1, `02-information.tex`, lines 91–145, with
area-law Proposition 10.2, `09-amplification.tex`, lines 261–296. -/
noncomputable def coarseInformationConstantClosed (q R : ℕ) (J Δ : ℝ) : ℝ :=
  max (collarAmplificationConstant q R J Δ (collarConstantClosed q R J Δ)) 0

/-- The scale threshold of Proposition 3.1 at range `R` at closed-form constants:
`coarseInformationThreshold` at the template constant `24`, the collar threshold
`collarThresholdClosed q R J Δ`, and the amplification constant and threshold at the collar
constant `collarConstantClosed q R J Δ`. Source: polynomial-PEPS Proposition 3.1,
`02-information.tex`, lines 91–145. -/
noncomputable def coarseInformationThresholdClosed (q R : ℕ) (J Δ : ℝ) (N₀ : ℕ) (A₀ : ℝ) :
    ℝ :=
  coarseInformationThreshold 24 N₀ A₀ (collarThresholdClosed q R J Δ)
    (collarAmplificationConstant q R J Δ (collarConstantClosed q R J Δ))
    (collarAmplificationThreshold q R J Δ (collarConstantClosed q R J Δ))

/-- **Proposition 3.1 at range `R`, at closed-form constants.** For `q ≥ 1`, `J ≥ 0` and
`Δ > 0`, the coarse mutual-information bound holds with the exponent `Exponents.beta < 1`, the
constant `coarseInformationConstantClosed q R J Δ` and the scale threshold
`coarseInformationThresholdClosed q R J Δ N₀ A₀`, on every finite induced domain and for every
Hamiltonian of range `R` and bound `J`. Source: polynomial-PEPS Proposition 3.1
(`prop:coarse`), `02-information.tex`, lines 91–145; this version also allows arbitrary finite
induced domains and interaction range. -/
theorem coarse_mutualInformation_le_closed {q R : ℕ} (hq : 1 ≤ q) {J Δ : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) (N₀ : ℕ) (A₀ : ℝ) :
    ∀ u : ℝ, coarseInformationThresholdClosed q R J Δ N₀ A₀ ≤ u →
      ∀ (Λ : Finset (ℤ × ℤ)) (h : Lattice.LocalHamiltonian Λ q R J) (E₀ : ℝ)
        (Ω : Lattice.StateSpace Λ q),
        Lattice.IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        ∀ T : Finset (ℤ × ℤ), IsBoxUnion N₀ T →
          (∀ x ∈ T, ∀ y ∈ T, (Scan.ambientSupDistance x y : ℝ) ≤ A₀ * u) →
          ∀ X ⊆ Finset.univ.filter (fun x : Site Λ ↦ x.val ∈ T),
          ∀ E : Finset (Site Λ),
            (∀ t ∈ T, ∀ y ∈ E,
              u ^ (Exponents.beta : ℝ) < (Scan.ambientSupDistance t y.val : ℝ)) →
            FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω X E ≤
              coarseInformationConstantClosed q R J Δ := by
  have hcol := sublinearCollarBoundAt_closed (R := R) (D₀ := 2 * (R : ℝ) + 11) hq hJ hΔ
    (by linarith)
  exact coarse_mutualInformation_le_of_sublinearCollarBoundAt hcol
    (amplificationBoundAt_collarAmplification hΔ _) N₀ A₀

/-- Coarse mutual information on any finite induced domain, from the original
Hamiltonian and its full-system gap. The constants are uniform in the finite
physical data, scale and rectangle union.
Source: polynomial-PEPS manuscript, Proposition 3.1 (`prop:coarse`),
`02-information.tex`, lines 91–145. This version also allows arbitrary finite
induced domains and interaction range. -/
theorem coarse_mutualInformation_le {q R : ℕ} (hq : 1 ≤ q) {J Δ : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) (N₀ : ℕ) (A₀ : ℝ) :
    ∃ β : ℝ, β < 1 ∧ ∃ C u₀ : ℝ, ∀ u : ℝ, u₀ ≤ u →
      ∀ (Λ : Finset (ℤ × ℤ)) (h : Lattice.LocalHamiltonian Λ q R J) (E₀ : ℝ)
        (Ω : Lattice.StateSpace Λ q),
        Lattice.IsGappedGroundState Λ q h.operator E₀ Ω Δ →
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
  exact coarse_mutualInformation_le_square_of_sublinearCollarBound hΔ hcol N₀ A₀

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
