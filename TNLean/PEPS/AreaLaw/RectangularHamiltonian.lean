/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RectangularDomain
import TNLean.PEPS.AreaLaw.LocalHamiltonian
import QICLean.Algebra.HermitianPartSum
import QICLean.Algebra.L2OpNormReindex
import Mathlib.Analysis.Complex.Basic

/-!
# Native rectangular Hamiltonians and range-one interactions

A rectangle has arbitrary natural width and height, including zero. The input
is one matrix per native site and undirected nearest-neighbor edge, with the
source support and Euclidean operator-norm bounds. Only their total sum must
be Hermitian. Taking Hermitian parts preserves the bound and total; placing
these terms at distinct singleton and pair supports gives an actual finite-domain
Hamiltonian. The configuration isometry preserves the unit vector and gap.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Corollary 1.2 (`cor:rectangles`), and *Polynomial PEPS approximation of gapped
square-grid ground states*, `eq:model` and `eq:global-gap`, September 24, 2026.
Immutable source revision: `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscripts; no upstream Lean proof text is reused.
-/

open Matrix ComplexStarModule
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace TNLean.PEPS.AreaLaw

/-- Configuration coordinates on an arbitrary native rectangle.
Source: area-law Corollary 1.2, the site tensor factors. -/
abbrev RectangleConfiguration (width height q : ℕ) :=
  SquareLatticeVertex width height → Fin q

/-- The physical Hilbert space of the native rectangle.
Source: area-law Corollary 1.2. -/
abbrev RectangleStateSpace (width height q : ℕ) :=
  EuclideanSpace ℂ (RectangleConfiguration width height q)

/-- Bounded native site and edge interactions, with Hermiticity only for their
sum. No positivity of the side lengths or lower bound on `q` is built in.
Source: area-law Corollary 1.2 and polynomial-PEPS `eq:model`. -/
structure RectangularHamiltonian (width height q : ℕ) (J : ℝ) where
  /-- One matrix for each site, as in `eq:model`. -/
  siteTerm : SquareLatticeVertex width height →
    Matrix (RectangleConfiguration width height q) (RectangleConfiguration width height q) ℂ
  /-- One matrix for each undirected nearest-neighbor edge, as in `eq:model`. -/
  edgeTerm : Edge (squareLatticeGraph width height) →
    Matrix (RectangleConfiguration width height q) (RectangleConfiguration width height q) ℂ
  /-- The site support condition in `eq:model`. -/
  site_supported : ∀ v, siteTerm v ∈ QuantumCircuit.supportedOperators q {v}
  /-- The edge support condition in `eq:model`. -/
  edge_supported : ∀ e, edgeTerm e ∈
    QuantumCircuit.supportedOperators q {e.1.1, e.1.2}
  /-- The site-term Euclidean operator-norm bound in `eq:model`. -/
  site_norm_le : ∀ v, ‖siteTerm v‖ ≤ J
  /-- The edge-term Euclidean operator-norm bound in `eq:model`. -/
  edge_norm_le : ∀ e, ‖edgeTerm e‖ ≤ J
  /-- Only total Hermiticity is required by `eq:model`. -/
  hermitian : ((∑ v, siteTerm v) + ∑ e, edgeTerm e).IsHermitian

/-- The original sum, before taking Hermitian parts. Source: `eq:model`. -/
def RectangularHamiltonian.operator {width height q : ℕ} {J : ℝ}
    (h : RectangularHamiltonian width height q J) :
    Matrix (RectangleConfiguration width height q) (RectangleConfiguration width height q) ℂ :=
  (∑ v, h.siteTerm v) + ∑ e, h.edgeTerm e

/-- The unit eigenvector and full-system projector gap in native coordinates.
Source: area-law Theorem 1.1 and polynomial-PEPS `eq:global-gap`. -/
def RectangularHamiltonian.IsGappedGroundState {width height q : ℕ} {J : ℝ}
    (h : RectangularHamiltonian width height q J) (E₀ : ℝ)
    (Ω : RectangleStateSpace width height q) (Δ : ℝ) : Prop :=
  Matrix.IsGappedGroundState h.operator E₀ Ω Δ

/-- Exactly one label per site or undirected edge. Source: `eq:model`. -/
abbrev RectangleInteraction (width height : ℕ) :=
  SquareLatticeVertex width height ⊕ Edge (squareLatticeGraph width height)

/-- The actual designated support of the native interaction. Source: `eq:model`. -/
def rectangleInteractionSupport {width height : ℕ} :
    RectangleInteraction width height → Finset (SquareLatticeVertex width height)
  | .inl v => {v}
  | .inr e => {e.val.1, e.val.2}

private def rectangleInteractionTerm {width height q : ℕ} {J : ℝ}
    (h : RectangularHamiltonian width height q J) : RectangleInteraction width height →
      Matrix (RectangleConfiguration width height q) (RectangleConfiguration width height q) ℂ
  | .inl v => h.siteTerm v
  | .inr e => h.edgeTerm e

/-- The Hermitian part of each original interaction. Source:
`00-introduction.tex`, lines 39–44; `03-patches.tex`, lines 214–333. -/
def RectangularHamiltonian.hermitianTerm {width height q : ℕ} {J : ℝ}
    (h : RectangularHamiltonian width height q J) (i : RectangleInteraction width height) :
    Matrix (RectangleConfiguration width height q) (RectangleConfiguration width height q) ℂ :=
  ℜ (rectangleInteractionTerm h i)

/-- The Hermitian part of an original interaction remains in its designated
circuit supported-operator algebra, since that algebra is closed under
adjoints and real linear combinations. Source: `00-introduction.tex`, `eq:model`. -/
theorem RectangularHamiltonian.hermitianTerm_mem_supportedOperators {width height q : ℕ} {J : ℝ}
    (h : RectangularHamiltonian width height q J) (i : RectangleInteraction width height) :
    h.hermitianTerm i ∈ QuantumCircuit.supportedOperators q
      (rectangleInteractionSupport i : Set (SquareLatticeVertex width height)) := by
  have hs : rectangleInteractionTerm h i ∈
      QuantumCircuit.supportedOperators q
        (rectangleInteractionSupport i : Set (SquareLatticeVertex width height)) := by
    cases i with
    | inl v =>
      simpa only [rectangleInteractionTerm, rectangleInteractionSupport, Finset.coe_singleton]
        using h.site_supported v
    | inr e =>
      simpa only [rectangleInteractionTerm, rectangleInteractionSupport, Finset.coe_insert,
        Finset.coe_singleton]
        using h.edge_supported e
  exact coe_realPart_mem_of_star_mem
    (S := (QuantumCircuit.supportedOperators q
      (rectangleInteractionSupport i : Set (SquareLatticeVertex width height))).restrictScalars ℝ)
    hs (QuantumCircuit.star_mem_supportedOperators hs)

/-- Every replaced interaction is Hermitian. Source:
`00-introduction.tex`, `eq:model`. -/
theorem RectangularHamiltonian.hermitianTerm_isHermitian {width height q : ℕ} {J : ℝ}
    (h : RectangularHamiltonian width height q J) (i : RectangleInteraction width height) :
    (h.hermitianTerm i).IsHermitian :=
  (ℜ (rectangleInteractionTerm h i)).property.isHermitian

/-- The original norm bound holds without any factor loss. Source:
`00-introduction.tex`, `eq:model`. -/
theorem RectangularHamiltonian.hermitianTerm_norm_le {width height q : ℕ} {J : ℝ}
    (h : RectangularHamiltonian width height q J) (i : RectangleInteraction width height) :
    ‖h.hermitianTerm i‖ ≤ J := by
  apply (realPart.norm_le (rectangleInteractionTerm h i)).trans
  cases i with
  | inl v => exact h.site_norm_le v
  | inr e => exact h.edge_norm_le e

/-- Hermitian replacement recovers exactly the original Hamiltonian.
Only total Hermiticity is used. Source: `00-introduction.tex`, `eq:model`. -/
theorem RectangularHamiltonian.sum_hermitianTerm {width height q : ℕ} {J : ℝ}
    (h : RectangularHamiltonian width height q J) :
    (∑ i : RectangleInteraction width height, h.hermitianTerm i) = h.operator := by
  have hsum : (∑ i : RectangleInteraction width height, rectangleInteractionTerm h i) =
      h.operator := by
    rw [Fintype.sum_sum_type]
    change (∑ v, h.siteTerm v) + (∑ e, h.edgeTerm e) = _
    rfl
  have hh : IsSelfAdjoint
      (∑ i : RectangleInteraction width height, rectangleInteractionTerm h i) := by
    rw [hsum]
    exact h.hermitian.isSelfAdjoint
  exact (sum_coe_realPart_of_isSelfAdjoint Finset.univ (rectangleInteractionTerm h) hh).trans hsum

private theorem rectangleInteractionSupport_injective (width height : ℕ) :
    Function.Injective (rectangleInteractionSupport (width := width) (height := height)) := by
  intro i j hij
  unfold rectangleInteractionSupport at hij
  cases i with
  | inl v =>
    cases j with
    | inl w =>
      exact congrArg Sum.inl (Finset.singleton_inj.mp hij)
    | inr e =>
      dsimp only at hij
      have h₁ : e.val.1 = v := by
        have := hij.symm ▸ (Finset.mem_insert_self e.val.1 {e.val.2})
        simpa only [rectangleInteractionSupport, Finset.mem_singleton] using this
      have h₂ : e.val.2 = v := by
        have := hij.symm ▸ (Finset.mem_insert_of_mem (Finset.mem_singleton_self e.val.2))
        simpa only [rectangleInteractionSupport, Finset.mem_singleton] using this
      exact False.elim ((squareLatticeGraph width height).ne_of_adj e.property.2 (h₁.trans h₂.symm))
  | inr e =>
    cases j with
    | inl v =>
      dsimp only at hij
      have h₁ : e.val.1 = v := by
        have := hij ▸ (Finset.mem_insert_self e.val.1 {e.val.2})
        simpa only [rectangleInteractionSupport, Finset.mem_singleton] using this
      have h₂ : e.val.2 = v := by
        have := hij ▸ (Finset.mem_insert_of_mem (Finset.mem_singleton_self e.val.2))
        simpa only [rectangleInteractionSupport, Finset.mem_singleton] using this
      exact False.elim ((squareLatticeGraph width height).ne_of_adj e.property.2 (h₁.trans h₂.symm))
    | inr f =>
      dsimp only at hij
      have h₁ : e.val.1 = f.val.1 ∨ e.val.1 = f.val.2 := by
        have := hij ▸ (Finset.mem_insert_self e.val.1 {e.val.2})
        simpa only [rectangleInteractionSupport, Finset.mem_insert, Finset.mem_singleton] using this
      have h₂ : e.val.2 = f.val.1 ∨ e.val.2 = f.val.2 := by
        have := hij ▸ (Finset.mem_insert_of_mem (Finset.mem_singleton_self e.val.2))
        simpa only [rectangleInteractionSupport, Finset.mem_insert, Finset.mem_singleton] using this
      rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
      · exact False.elim
          ((squareLatticeGraph width height).ne_of_adj e.property.2 (h₁.trans h₂.symm))
      · exact congrArg Sum.inr (Subtype.ext (Prod.ext h₁ h₂))
      · exact congrArg Sum.inr ((Edge.ofAdj_eq_of_endpoints e.property.2 e
          (Or.inl ⟨rfl, rfl⟩)).symm.trans
            (Edge.ofAdj_eq_of_endpoints e.property.2 f (Or.inr ⟨h₁, h₂⟩)))
      · exact False.elim
          ((squareLatticeGraph width height).ne_of_adj e.property.2 (h₁.trans h₂.symm))

/-- Each original site or undirected edge determines its actual admissible
range-one support in the integer rectangle. Source: area-law Corollary 1.2
and polynomial-PEPS `eq:model`. -/
def rectangleAreaLawSupport (width height : ℕ) (i : RectangleInteraction width height) :
    AdmissibleSupport (rectangularDomain width height) 1 := by
  classical
  refine ⟨(rectangleInteractionSupport i).image (rectangleSiteEquiv width height), ?_⟩
  cases i with
  | inl v =>
    simpa only [rectangleInteractionSupport, Finset.image_singleton] using
      isAdmissibleSupport_singleton (rectangularDomain width height) 1
        (rectangleSiteEquiv width height v)
  | inr e =>
    simpa only [rectangleInteractionSupport, Finset.image_insert, Finset.image_singleton] using
      isAdmissibleSupport_rectangle_pair_of_adj
        e.property.2

/-- Distinct original interactions have distinct designated supports.
Source: polynomial-PEPS `eq:model`, one term per site and nearest-neighbor edge. -/
theorem rectangleAreaLawSupport_injective (width height : ℕ) :
    Function.Injective (rectangleAreaLawSupport width height) := by
  intro i j hij
  apply rectangleInteractionSupport_injective width height
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

/-- The original rectangular Hamiltonian, with Hermitian parts at its actual
range-one supports and zero at unused supports. The interaction bound is
unchanged. Source: area-law Corollary 1.2 and polynomial-PEPS `eq:model`. -/
def RectangularHamiltonian.toAreaLawHamiltonian {width height q : ℕ} {J : ℝ}
    (h : RectangularHamiltonian width height q J) (hJ : 0 ≤ J) :
    LocalHamiltonian (rectangularDomain width height) q 1 J := by
  classical
  let e := rectangleConfigurationEquiv width height q
  let T := fun i : RectangleInteraction width height => Matrix.reindex e e (h.hermitianTerm i)
  refine { term := Function.extend (rectangleAreaLawSupport width height) T 0
           supported := ?_, hermitian := ?_, norm_le := ?_ }
  · intro X
    by_cases hx : ∃ i, rectangleAreaLawSupport width height i = X
    · obtain ⟨i, rfl⟩ := hx
      rw [(rectangleAreaLawSupport_injective width height).extend_apply]
      have hs := QuantumCircuit.embedOp_mem_supportedOperators_image
        (rectangleSiteEquiv width height).injective (h.hermitianTerm_mem_supportedOperators i)
      rw [embedOp_rectangular_eq_reindex] at hs
      simpa only [T, e, rectangleAreaLawSupport, Finset.coe_image] using hs
    · rw [Function.extend_apply' _ _ _ hx]
      exact Submodule.zero_mem _
  · intro X
    by_cases hx : ∃ i, rectangleAreaLawSupport width height i = X
    · obtain ⟨i, rfl⟩ := hx
      rw [(rectangleAreaLawSupport_injective width height).extend_apply]
      exact (h.hermitianTerm_isHermitian i).submatrix e.symm
    · rw [Function.extend_apply' _ _ _ hx]
      exact Matrix.isHermitian_zero
  · intro X
    by_cases hx : ∃ i, rectangleAreaLawSupport width height i = X
    · obtain ⟨i, rfl⟩ := hx
      rw [(rectangleAreaLawSupport_injective width height).extend_apply]
      exact (Matrix.l2_opNorm_reindex_equiv e (h.hermitianTerm i)).le.trans
        (h.hermitianTerm_norm_le i)
    · rw [Function.extend_apply' _ _ _ hx]
      simpa only [Pi.zero_apply, norm_zero] using hJ

/-- The interaction conversion has exactly the transported original sum.
Source: area-law Corollary 1.2 and polynomial-PEPS `eq:model`. -/
theorem RectangularHamiltonian.toAreaLawHamiltonian_operator {width height q : ℕ} {J : ℝ}
    (h : RectangularHamiltonian width height q J) (hJ : 0 ≤ J) :
    (h.toAreaLawHamiltonian hJ).operator =
      Matrix.reindex (rectangleConfigurationEquiv width height q)
        (rectangleConfigurationEquiv width height q) h.operator := by
  classical
  let e := rectangleConfigurationEquiv width height q
  let T := fun i : RectangleInteraction width height => Matrix.reindex e e (h.hermitianTerm i)
  let f := Function.extend (rectangleAreaLawSupport width height) T 0
  have hsum : (∑ i : RectangleInteraction width height, T i) =
      ∑ X : AdmissibleSupport (rectangularDomain width height) 1, f X := by
    apply Finset.sum_of_injOn (rectangleAreaLawSupport width height)
      (rectangleAreaLawSupport_injective width height).injOn (fun _ _ => Finset.mem_univ _)
    · intro X _ hX
      exact Function.extend_apply' _ _ _ (by simpa using hX)
    · intro i _
      exact ((rectangleAreaLawSupport_injective width height).extend_apply T 0 i).symm
  change (∑ X, f X) = _
  rw [← hsum]
  change (∑ i : RectangleInteraction width height,
    (Matrix.reindexAlgEquiv ℂ ℂ e) (h.hermitianTerm i)) = _
  rw [← map_sum (Matrix.reindexAlgEquiv ℂ ℂ e), h.sum_hermitianTerm]
  rfl

/-- The original unit ground vector and full-system gap are preserved by
the actual conversion. Source: area-law Corollary 1.2 and polynomial-PEPS
`eq:global-gap`. -/
theorem RectangularHamiltonian.isGappedGroundState_toAreaLawHamiltonian
    {width height q : ℕ} {J : ℝ} (h : RectangularHamiltonian width height q J) (hJ : 0 ≤ J)
    {E₀ Δ : ℝ} {Ω : RectangleStateSpace width height q} (hΩ : h.IsGappedGroundState E₀ Ω Δ) :
    IsGappedGroundState (rectangularDomain width height) q
      (h.toAreaLawHamiltonian hJ).operator E₀ (rectangleAreaLawState Ω) Δ := by
  classical
  let e := rectangleConfigurationEquiv width height q
  let E := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  refine ⟨(norm_rectangleAreaLawState Ω).trans hΩ.1, ?_, ?_⟩
  · rw [h.toAreaLawHamiltonian_operator hJ]
    have heq : Matrix.toEuclideanLin (Matrix.reindex e e h.operator) (E Ω) =
        E (Matrix.toEuclideanLin h.operator Ω) := by
      ext x
      change (h.operator.submatrix e.symm e.symm *ᵥ (Ω.ofLp ∘ e.symm)) x =
        (h.operator *ᵥ Ω.ofLp) (e.symm x)
      rw [Matrix.submatrix_mulVec_equiv]
      simp only [Function.comp_def, Equiv.symm_symm, Equiv.symm_apply_apply]
    change Matrix.toEuclideanLin (Matrix.reindex e e h.operator) (E Ω) = _
    rw [heq, show Matrix.toEuclideanLin h.operator Ω = (E₀ : ℂ) • Ω from hΩ.2.1,
      map_smul]
    rfl
  · rw [h.toAreaLawHamiltonian_operator hJ]
    have hg := hΩ.2.2.submatrix e.symm
    have hdef : (h.operator - (E₀ : ℂ) • 1 -
        (Δ : ℂ) • (1 - vecMulVec (fun x ↦ Ω x) (star (fun x ↦ Ω x)))).submatrix
        e.symm e.symm = Matrix.reindex e e h.operator - (E₀ : ℂ) • 1 -
          (Δ : ℂ) • (1 - vecMulVec (fun x ↦ rectangleAreaLawState Ω x)
            (star (fun x ↦ rectangleAreaLawState Ω x))) := by
      ext i j
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply,
        Matrix.smul_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.star_apply,
        e.symm.injective.eq_iff]
      rfl
    exact hdef ▸ hg

end TNLean.PEPS.AreaLaw
