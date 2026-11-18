/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RectangularDomain
import TNLean.Lattice.LocalHamiltonian
import TNLean.Circuit.SiteEmbedding
import TNLean.Circuit.SupportedMatrixElements
import QICLean.Entropy.RegionUnion
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
Hermitian parts preserves the bound and, for a Hermitian total, the total; placing these
terms at distinct singleton and pair supports gives an actual finite-domain Hamiltonian. The
configuration isometry preserves the unit vector and gap.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Corollary 1.2 (`cor:rectangles`), and *Polynomial PEPS approximation of gapped
square-grid ground states*, `eq:model` and `eq:global-gap`, September 24, 2026.
Immutable source revision: `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscripts; no upstream Lean proof text is reused.
-/

open ManyBody (Edge SquareLatticeVertex squareLatticeGraph SquareLatticeSiteOrEdge
  squareLatticeSiteOrEdgeSupport)

open Matrix ComplexStarModule
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section

open TNLean.Lattice

open ManyBody (AdmissibleSupport isAdmissibleSupport_singleton)

namespace TNLean.PEPS.AreaLaw

/-- Configuration coordinates on an arbitrary native rectangle.
Source: area-law Corollary 1.2, the site tensor factors. -/
abbrev RectangleConfiguration (width height q : ℕ) :=
  SquareLatticeVertex width height → Fin q

/-- The physical Hilbert space of the native rectangle.
Source: area-law Corollary 1.2. -/
abbrev RectangleStateSpace (width height q : ℕ) :=
  EuclideanSpace ℂ (RectangleConfiguration width height q)

/-- Each original site or undirected edge determines its actual admissible
range-one support in the integer rectangle. Source: area-law Corollary 1.2
and polynomial-PEPS `eq:model`. -/
def rectangleAreaLawSupport (width height : ℕ) (i : SquareLatticeSiteOrEdge width height) :
    AdmissibleSupport (rectangularDomain width height) 1 := by
  classical
  refine ⟨(squareLatticeSiteOrEdgeSupport i).image (rectangleSiteEquiv width height), ?_⟩
  cases i with
  | inl v =>
    simpa only [squareLatticeSiteOrEdgeSupport, Finset.image_singleton] using
      isAdmissibleSupport_singleton (rectangularDomain width height) 1
        (rectangleSiteEquiv width height v)
  | inr e =>
    simpa only [squareLatticeSiteOrEdgeSupport, Finset.image_insert, Finset.image_singleton] using
      isAdmissibleSupport_rectangle_pair_of_adj
        e.property.2

/-- Distinct original interactions have distinct designated supports.
Source: polynomial-PEPS `eq:model`, one term per site and nearest-neighbor edge. -/
theorem rectangleAreaLawSupport_injective (width height : ℕ) :
    Function.Injective (rectangleAreaLawSupport width height) := by
  intro i j hij
  apply squareLatticeSiteOrEdgeSupport_injective width height
  exact Finset.image_injective (rectangleSiteEquiv width height).injective
    (congrArg Subtype.val hij)

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

/-- Embedding an operator along the rectangle site identification is the same as
reindexing its configuration coordinates. Source: area-law Corollary 1.2. -/
theorem embedOp_rectangular_eq_reindex {width height q : ℕ}
    (A : Matrix (RectangleConfiguration width height q) (RectangleConfiguration width height q) ℂ) :
    QuantumCircuit.embedOp (rectangleSiteEquiv width height) A =
      Matrix.reindex (rectangleConfigurationEquiv width height q)
        (rectangleConfigurationEquiv width height q) A := by
  ext x y
  rw [QuantumCircuit.embedOp_apply, ite_eq_left]
  · rfl
  · intro v hv
    exact False.elim (hv ((rectangleSiteEquiv width height).symm v)
      ((rectangleSiteEquiv width height).apply_symm_apply v))

end TNLean.PEPS.AreaLaw

namespace ManyBody.RectangleInteraction

open TNLean.PEPS.AreaLaw

variable {width height q : ℕ} {J : ℝ}

/-- The rectangular interaction, with Hermitian parts at its actual range-one supports and
zero at unused supports. The bound `J` is unchanged, for every real `J`: each unused
admissible support is nonempty, so one of its sites supplies the nonnegative bound needed
for its zero term. Source: area-law Corollary 1.2 and polynomial-PEPS `eq:model`. -/
def toAreaLawHamiltonian (Φ : RectangleInteraction width height q)
    (hΦ : ∀ i, ‖Φ.term i‖ ≤ J) :
    TNLean.Lattice.LocalHamiltonian (rectangularDomain width height) q 1 J := by
  classical
  let e := rectangleConfigurationEquiv width height q
  let T := fun i : SquareLatticeSiteOrEdge width height =>
    Matrix.reindex e e (Φ.hermitianPart.term i)
  refine { term := Function.extend (rectangleAreaLawSupport width height) T 0
           supported := ?_, hermitian := ?_, norm_le := ?_ }
  · intro X
    by_cases hx : ∃ i, rectangleAreaLawSupport width height i = X
    · obtain ⟨i, rfl⟩ := hx
      rw [(rectangleAreaLawSupport_injective width height).extend_apply]
      have hs := QuantumCircuit.embedOp_mem_supportedOperators_image
        (rectangleSiteEquiv width height).injective
        (Φ.hermitianPart.mem i)
      rw [embedOp_rectangular_eq_reindex] at hs
      simpa only [T, e, rectangleAreaLawSupport, Finset.coe_image] using hs
    · rw [Function.extend_apply' _ _ _ hx]
      change _ ∈ ManyBody.supportedOperators _ _
      exact zero_mem _
  · intro X
    by_cases hx : ∃ i, rectangleAreaLawSupport width height i = X
    · obtain ⟨i, rfl⟩ := hx
      rw [(rectangleAreaLawSupport_injective width height).extend_apply]
      exact (Φ.isHermitian_hermitianPart_term i).submatrix e.symm
    · rw [Function.extend_apply' _ _ _ hx]
      exact Matrix.isHermitian_zero
  · intro X
    by_cases hx : ∃ i, rectangleAreaLawSupport width height i = X
    · obtain ⟨i, rfl⟩ := hx
      rw [(rectangleAreaLawSupport_injective width height).extend_apply]
      exact (Matrix.l2_opNorm_reindex_equiv e (Φ.hermitianPart.term i)).le.trans
        ((Φ.norm_hermitianPart_term_le i).trans (hΦ i))
    · rw [Function.extend_apply' _ _ _ hx]
      obtain ⟨v, _⟩ := X.property.1
      simpa only [Pi.zero_apply, norm_zero] using
        (norm_nonneg _).trans (hΦ (.inl ((rectangleSiteEquiv width height).symm v)))

/-- For a Hermitian total, the interaction conversion has exactly the transported original
sum. Source: area-law Corollary 1.2 and polynomial-PEPS `eq:model`. -/
theorem toAreaLawHamiltonian_operator (Φ : RectangleInteraction width height q)
    (hΦ : ∀ i, ‖Φ.term i‖ ≤ J) (hH : Φ.hamiltonian.IsHermitian) :
    (Φ.toAreaLawHamiltonian hΦ).operator =
      Matrix.reindex (rectangleConfigurationEquiv width height q)
        (rectangleConfigurationEquiv width height q) Φ.hamiltonian := by
  classical
  let e := rectangleConfigurationEquiv width height q
  let T := fun i : SquareLatticeSiteOrEdge width height =>
    Matrix.reindex e e (Φ.hermitianPart.term i)
  let f := Function.extend (rectangleAreaLawSupport width height) T 0
  have hsum : (∑ i : SquareLatticeSiteOrEdge width height, T i) =
      ∑ X : ManyBody.AdmissibleSupport (rectangularDomain width height) 1, f X := by
    apply Finset.sum_of_injOn (rectangleAreaLawSupport width height)
      (rectangleAreaLawSupport_injective width height).injOn (fun _ _ => Finset.mem_univ _)
    · intro X _ hX
      exact Function.extend_apply' _ _ _ (by simpa using hX)
    · intro i _
      exact ((rectangleAreaLawSupport_injective width height).extend_apply T 0 i).symm
  change (∑ X, f X) = _
  rw [← hsum]
  change (∑ i : SquareLatticeSiteOrEdge width height,
    (Matrix.reindexAlgEquiv ℂ ℂ e) (Φ.hermitianPart.term i)) = _
  rw [← map_sum (Matrix.reindexAlgEquiv ℂ ℂ e)]
  change (Matrix.reindexAlgEquiv ℂ ℂ e) Φ.hermitianPart.hamiltonian = _
  rw [Φ.hamiltonian_hermitianPart hH]
  rfl

/-- The original unit ground vector and full-system gap are preserved by the actual
conversion. Source: area-law Corollary 1.2 and polynomial-PEPS `eq:global-gap`. -/
theorem isGapped_toAreaLawHamiltonian (Φ : RectangleInteraction width height q)
    (hΦ : ∀ i, ‖Φ.term i‖ ≤ J) (hH : Φ.hamiltonian.IsHermitian)
    {E₀ Δ : ℝ} {Ω : RectangleStateSpace width height q} (hΩ : ‖Ω‖ = 1)
    (hgap : IsGapped Φ.hamiltonian E₀ Δ)
    (hspan : groundSpace Φ.hamiltonian E₀ = Submodule.span ℂ {Ω}) :
    ‖rectangleAreaLawState Ω‖ = 1 ∧ IsGapped (Φ.toAreaLawHamiltonian hΦ).operator E₀ Δ ∧
      groundSpace (Φ.toAreaLawHamiltonian hΦ).operator E₀ =
        Submodule.span ℂ {rectangleAreaLawState Ω} := by
  rw [Φ.toAreaLawHamiltonian_operator hΦ hH]
  exact ⟨(norm_rectangleAreaLawState Ω).trans hΩ, (ManyBody.isGapped_reindex_iff _).mpr hgap,
    ManyBody.groundSpace_reindex_eq_span _ hspan⟩

/-- Coordinate transport of the projector gap inequality, valid for every real `Δ`.
Source: polynomial-PEPS `eq:global-gap`. No uniqueness is assumed. -/
theorem projectorGap_toAreaLawHamiltonian (Φ : RectangleInteraction width height q)
    (hΦ : ∀ i, ‖Φ.term i‖ ≤ J) (hH : Φ.hamiltonian.IsHermitian)
    {E₀ Δ : ℝ} {Ω : RectangleStateSpace width height q} (hΩ : ‖Ω‖ = 1)
    (hgap : (Φ.hamiltonian - (E₀ : ℂ) • 1 - (Δ : ℂ) •
      (1 - Matrix.vecMulVec (fun x ↦ Ω x) (star (fun x ↦ Ω x)))).PosSemidef)
    (hmem : Ω ∈ groundSpace Φ.hamiltonian E₀) :
    ‖rectangleAreaLawState Ω‖ = 1 ∧ ((Φ.toAreaLawHamiltonian hΦ).operator - (E₀ : ℂ) • 1 - (Δ : ℂ) •
      (1 - Matrix.vecMulVec (fun x ↦ rectangleAreaLawState Ω x)
        (star (fun x ↦ rectangleAreaLawState Ω x)))).PosSemidef ∧
      rectangleAreaLawState Ω ∈ groundSpace (Φ.toAreaLawHamiltonian hΦ).operator E₀ := by
  classical
  let e := rectangleConfigurationEquiv width height q
  rw [Φ.toAreaLawHamiltonian_operator hΦ hH]
  refine ⟨(norm_rectangleAreaLawState Ω).trans hΩ, ?_, ?_⟩
  · have hg := hgap.submatrix e.symm
    convert hg using 1
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      e.symm.injective.eq_iff]
    rfl
  · apply (ManyBody.mem_groundSpace_reindex_iff e).mpr
    simpa only [rectangleAreaLawState, e, LinearIsometryEquiv.symm_apply_apply] using hmem

end ManyBody.RectangleInteraction
