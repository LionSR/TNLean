/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.FiniteDomain
import TNLean.PEPS.NormalBlocking
import TNLean.Lattice.StateSpace
import QICLean.ManyBody.Sites.PlacedConfiguration
import QICLean.ManyBody.Sites.ProductVector
import QICLean.Entropy.RegionUnion
import QICLean.ManyBody.Sites.Lattice.Rectangle
import QICLean.ManyBody.Hamiltonian.Models
import QICLean.ManyBody.Hamiltonian.HermitianPart
import QICLean.ManyBody.Hamiltonian.GroundSpace
import QICLean.Algebra.L2OpNormReindex
import Mathlib.Analysis.Complex.Basic

/-!
# Rectangular interactions as range-one interactions on the integer rectangle

A rectangle has arbitrary natural width and height, including zero. The input is a
`ManyBody.RectangleInteraction`: one matrix per native site and undirected nearest-neighbor
edge, supported on that site or on the two endpoints. The source's bound `‖h_i‖ ≤ J` and
its Hermiticity of the total sum are hypotheses of the statements that use them. Taking
Hermitian parts (`ManyBody.Interaction.hermitianPart`) preserves the bound and, for a
Hermitian total, the total; placing these terms at distinct singleton and pair supports
(`ManyBody.RectangleInteraction.toPlaneInteraction`) gives an actual finite-domain
Hamiltonian. The configuration isometry preserves the unit vector and gap.

The configurations of the native rectangle are carried to those of its integer domain by
precomposition with the inverse site identification, `rectangleConfigurationEquiv`, which is
the configuration bijection `ManyBody.siteConfigurationEquiv` of the site identification
(`siteConfigurationEquiv_rectangleSiteEquiv`).

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Corollary 1.2 (`cor:rectangles`), and *Polynomial PEPS approximation of gapped
square-grid ground states*, `eq:model` and `eq:global-gap`, September 24, 2026.
Immutable source revision: `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscripts; no upstream Lean proof text is reused.
-/

open ManyBody (SquareLatticeVertex rectangularDomain rectangleSiteEquiv)

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section

open TNLean.Lattice

open ManyBody (AdmissibleSupport)

namespace TNLean.PEPS.AreaLaw

/-- Configuration coordinates on an arbitrary native rectangle.
Source: area-law Corollary 1.2, the site tensor factors. -/
abbrev RectangleConfiguration (width height q : ℕ) :=
  SquareLatticeVertex width height → Fin q

/-- The physical Hilbert space of the native rectangle.
Source: area-law Corollary 1.2. -/
abbrev RectangleStateSpace (width height q : ℕ) :=
  EuclideanSpace ℂ (RectangleConfiguration width height q)

/-- Configuration coordinates transported from the native rectangle to its
integer domain. Source: area-law Corollary 1.2 and polynomial-PEPS Section 1. -/
noncomputable def rectangleConfigurationEquiv (width height q : ℕ) :
    (SquareLatticeVertex width height → Fin q) ≃
      Configuration (rectangularDomain width height) q :=
  Equiv.arrowCongr (rectangleSiteEquiv width height) (Equiv.refl (Fin q))

/-- The configuration transport of the rectangle is the configuration bijection of the site
identification. Source: area-law Corollary 1.2. -/
theorem siteConfigurationEquiv_rectangleSiteEquiv (width height q : ℕ) :
    ManyBody.siteConfigurationEquiv (X := fun _ : SquareLatticeVertex width height ↦ Fin q)
        (X' := fun _ : ↥(rectangularDomain width height) ↦ Fin q)
        (rectangleSiteEquiv width height) (fun _ ↦ Equiv.refl (Fin q)) =
      rectangleConfigurationEquiv width height q := by
  ext σ v
  obtain ⟨u, rfl⟩ := (rectangleSiteEquiv width height).surjective v
  simp only [ManyBody.siteConfigurationEquiv, rectangleConfigurationEquiv,
    Equiv.piCongr_apply_apply, Equiv.arrowCongr_apply, Function.comp_apply, Equiv.refl_apply]
  rw [Equiv.symm_apply_apply]

/-- The original vector in the actual integer-domain coordinates.
Source: area-law Corollary 1.2, finite tensor factors. -/
def rectangleAreaLawState {width height q : ℕ} (Ω : RectangleStateSpace width height q) :
    StateSpace (rectangularDomain width height) q :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (rectangleConfigurationEquiv width height q) Ω

/-- The physical coordinate identification preserves the norm.
Source: area-law Corollary 1.2. -/
theorem norm_rectangleAreaLawState {width height q : ℕ} (Ω : RectangleStateSpace width height q) :
    ‖rectangleAreaLawState Ω‖ = ‖Ω‖ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (rectangleConfigurationEquiv width height q)).norm_map Ω

end TNLean.PEPS.AreaLaw

namespace ManyBody.RectangleInteraction

open TNLean.PEPS.AreaLaw

variable {width height q : ℕ} {J : ℝ}

/-- The terms on the integer rectangle of the Hermitian parts are Hermitian: they are
transported Hermitian parts or zero. Source: area-law Corollary 1.2 and polynomial-PEPS
`eq:model`. -/
theorem isHermitian_toPlaneInteraction_hermitianPart_term
    (Φ : RectangleInteraction width height q)
    (X : AdmissibleSupport (rectangularDomain width height) 1) :
    ((toPlaneInteraction Φ.hermitianPart).term X).IsHermitian := by
  refine Interaction.isHermitian_extend_term (fun i ↦ ?_) X
  exact Interaction.isHermitian_relabel_term _ _ _ _ (Φ.isHermitian_hermitianPart_term i)

/-- The terms on the integer rectangle of the Hermitian parts keep the bound `J`, for every
real `J`: each unused admissible support is nonempty, so one of its sites supplies the
nonnegative bound needed for its zero term. Source: area-law Corollary 1.2 and
polynomial-PEPS `eq:model`. -/
theorem norm_toPlaneInteraction_hermitianPart_term_le (Φ : RectangleInteraction width height q)
    (hΦ : ∀ i, ‖Φ.term i‖ ≤ J) (X : AdmissibleSupport (rectangularDomain width height) 1) :
    ‖(toPlaneInteraction Φ.hermitianPart).term X‖ ≤ J := by
  obtain ⟨v, _⟩ := X.property.1
  refine Interaction.norm_extend_term_le
    ((norm_nonneg _).trans (hΦ (.inl ((rectangleSiteEquiv width height).symm v)))) (fun i ↦ ?_) X
  rw [Interaction.norm_relabel_term]
  exact (Φ.norm_hermitianPart_term_le i).trans (hΦ i)

/-- For a Hermitian total, the Hermitian parts on the integer rectangle have exactly the
transported original sum. Source: area-law Corollary 1.2 and polynomial-PEPS `eq:model`. -/
theorem hamiltonian_toPlaneInteraction_hermitianPart (Φ : RectangleInteraction width height q)
    (hH : Φ.hamiltonian.IsHermitian) :
    (toPlaneInteraction Φ.hermitianPart).hamiltonian =
      Matrix.reindex (rectangleConfigurationEquiv width height q)
        (rectangleConfigurationEquiv width height q) Φ.hamiltonian := by
  rw [hamiltonian_toPlaneInteraction, Φ.hamiltonian_hermitianPart hH,
    siteConfigurationEquiv_rectangleSiteEquiv]

/-- The original unit ground vector and full-system gap are preserved by the Hermitian parts
on the integer rectangle. Source: area-law Corollary 1.2 and polynomial-PEPS
`eq:global-gap`. -/
theorem isGapped_toPlaneInteraction_hermitianPart (Φ : RectangleInteraction width height q)
    (hH : Φ.hamiltonian.IsHermitian)
    {E₀ Δ : ℝ} {Ω : RectangleStateSpace width height q} (hΩ : ‖Ω‖ = 1)
    (hgap : IsGapped Φ.hamiltonian E₀ Δ)
    (hspan : groundSpace Φ.hamiltonian E₀ = Submodule.span ℂ {Ω}) :
    ‖rectangleAreaLawState Ω‖ = 1 ∧
      IsGapped (toPlaneInteraction Φ.hermitianPart).hamiltonian E₀ Δ ∧
      groundSpace (toPlaneInteraction Φ.hermitianPart).hamiltonian E₀ =
        Submodule.span ℂ {rectangleAreaLawState Ω} := by
  rw [Φ.hamiltonian_toPlaneInteraction_hermitianPart hH]
  exact ⟨(norm_rectangleAreaLawState Ω).trans hΩ, (ManyBody.isGapped_reindex_iff _).mpr hgap,
    ManyBody.groundSpace_reindex_eq_span _ hspan⟩

end ManyBody.RectangleInteraction
