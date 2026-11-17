/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SquareHamiltonianHermitianTerms
import TNLean.PEPS.AreaLaw.RectangularDomain
import TNLean.Lattice.LocalHamiltonian
import QICLean.Algebra.L2OpNormReindex
import QICLean.ManyBody.Hamiltonian.GroundSpace

/-!
# The original square Hamiltonian on its integer lattice domain

The native sites and forward edges give distinct admissible supports of
range one in the integer rectangle. Place the Hermitian part of each
original interaction at its corresponding support, and put zero at every
other admissible support. The resulting interaction family has the same
bound, and its total is exactly the original Hamiltonian in the canonical
configuration coordinates. The unit ground vector and full-system gap are
transported by the same isometry.

## References

OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
September 24, 2026, `00-introduction.tex`, `eq:model`, `eq:global-gap`, and
`03-patches.tex`, lines 335–413; *A two-dimensional area law from a global
spectral gap*, Theorem 1.1 and Corollary 1.2. Source revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open ManyBody (SquareLatticeSiteOrEdge squareLatticeSiteOrEdgeSupport)

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section

open TNLean.Lattice

open ManyBody (IsGapped groundSpace)

namespace TNLean.PEPS.Approximation

/-- Each original site or forward edge determines its actual admissible
range-one support in the integer rectangle. Source: area-law Corollary 1.2
and polynomial-PEPS `eq:model`. -/
def squareAreaLawSupport (L : ℕ) (i : SquareLatticeSiteOrEdge L L) :
    ManyBody.AdmissibleSupport (AreaLaw.rectangularDomain L L) 1 := by
  classical
  refine ⟨(squareLatticeSiteOrEdgeSupport i).image (AreaLaw.rectangleSiteEquiv L L), ?_⟩
  cases i with
  | inl v =>
    simpa only [squareLatticeSiteOrEdgeSupport, Finset.image_singleton] using
      ManyBody.isAdmissibleSupport_singleton (AreaLaw.rectangularDomain L L) 1
        (AreaLaw.rectangleSiteEquiv L L v)
  | inr e =>
    simpa only [squareLatticeSiteOrEdgeSupport, Finset.image_insert, Finset.image_singleton] using
      AreaLaw.isAdmissibleSupport_rectangle_pair_of_adj
        e.property.2

/-- Distinct original interactions have distinct designated supports.
Source: polynomial-PEPS `eq:model`, one term per site and nearest-neighbor edge. -/
theorem squareAreaLawSupport_injective (L : ℕ) :
    Function.Injective (squareAreaLawSupport L) := by
  intro i j hij
  apply AreaLaw.squareLatticeSiteOrEdgeSupport_injective L L
  exact Finset.image_injective (AreaLaw.rectangleSiteEquiv L L).injective
    (congrArg Subtype.val hij)

/-- The original vector in the actual integer-domain coordinates.
Source: area-law Corollary 1.2, finite tensor factors. -/
def squareAreaLawState {L q : ℕ} (Ω : StateSpace L q) :
    Lattice.StateSpace (AreaLaw.rectangularDomain L L) q :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (AreaLaw.rectangleConfigurationEquiv L L q) Ω

/-- The physical coordinate identification preserves the norm.
Source: area-law Corollary 1.2. -/
theorem norm_squareAreaLawState {L q : ℕ} (Ω : StateSpace L q) :
    ‖squareAreaLawState Ω‖ = ‖Ω‖ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (AreaLaw.rectangleConfigurationEquiv L L q)).norm_map Ω

/-- Embedding an operator along the rectangle site identification is the same as
reindexing its configuration coordinates. Source: area-law Corollary 1.2. -/
theorem embedOp_rectangle_eq_reindex {L q : ℕ}
    (A : Matrix (Configuration L q) (Configuration L q) ℂ) :
    QuantumCircuit.embedOp (AreaLaw.rectangleSiteEquiv L L) A =
      Matrix.reindex (AreaLaw.rectangleConfigurationEquiv L L q)
        (AreaLaw.rectangleConfigurationEquiv L L q) A := by
  ext x y
  rw [QuantumCircuit.embedOp_apply, ite_eq_left]
  · rfl
  · intro v hv
    exact False.elim (hv ((AreaLaw.rectangleSiteEquiv L L).symm v)
      ((AreaLaw.rectangleSiteEquiv L L).apply_symm_apply v))

/-- The original square Hamiltonian, with Hermitian parts at its actual
range-one supports and zero at unused supports. The interaction bound is
unchanged, for every real interaction bound. Each unused admissible support is
nonempty, so one of its sites supplies the nonnegative bound needed for its zero
term. Source: area-law Corollary 1.2 and polynomial-PEPS `eq:model`. -/
def SquareHamiltonian.toAreaLawHamiltonian {L q : ℕ} {J : ℝ}
    (h : SquareHamiltonian L q J) :
    Lattice.LocalHamiltonian (AreaLaw.rectangularDomain L L) q 1 J := by
  classical
  let e := AreaLaw.rectangleConfigurationEquiv L L q
  let T := fun i : SquareLatticeSiteOrEdge L L => Matrix.reindex e e (h.hermitianTerm i)
  refine { term := Function.extend (squareAreaLawSupport L) T 0
           supported := ?_, hermitian := ?_, norm_le := ?_ }
  · intro X
    by_cases hx : ∃ i, squareAreaLawSupport L i = X
    · obtain ⟨i, rfl⟩ := hx
      rw [(squareAreaLawSupport_injective L).extend_apply]
      have hs := QuantumCircuit.embedOp_mem_supportedOperators_image
        (AreaLaw.rectangleSiteEquiv L L).injective (h.hermitianTerm_mem_supportedOperators i)
      rw [embedOp_rectangle_eq_reindex] at hs
      simpa only [T, e, squareAreaLawSupport, Finset.coe_image] using hs
    · rw [Function.extend_apply' _ _ _ hx]
      change _ ∈ ManyBody.supportedOperators _ _
      exact zero_mem _
  · intro X
    by_cases hx : ∃ i, squareAreaLawSupport L i = X
    · obtain ⟨i, rfl⟩ := hx
      rw [(squareAreaLawSupport_injective L).extend_apply]
      exact (h.hermitianTerm_isHermitian i).submatrix e.symm
    · rw [Function.extend_apply' _ _ _ hx]
      exact Matrix.isHermitian_zero
  · intro X
    by_cases hx : ∃ i, squareAreaLawSupport L i = X
    · obtain ⟨i, rfl⟩ := hx
      rw [(squareAreaLawSupport_injective L).extend_apply]
      exact (Matrix.l2_opNorm_reindex_equiv e (h.hermitianTerm i)).le.trans
        (h.hermitianTerm_norm_le i)
    · rw [Function.extend_apply' _ _ _ hx]
      obtain ⟨v, _⟩ := X.property.1
      simpa only [Pi.zero_apply, norm_zero] using
        (norm_nonneg _).trans
          (h.site_norm_le ((AreaLaw.rectangleSiteEquiv L L).symm v))

/-- The interaction conversion has exactly the transported original sum.
Source: area-law Corollary 1.2 and polynomial-PEPS `eq:model`. -/
theorem SquareHamiltonian.toAreaLawHamiltonian_operator {L q : ℕ} {J : ℝ}
    (h : SquareHamiltonian L q J) :
    h.toAreaLawHamiltonian.operator =
      Matrix.reindex (AreaLaw.rectangleConfigurationEquiv L L q)
        (AreaLaw.rectangleConfigurationEquiv L L q) h.operator := by
  classical
  let e := AreaLaw.rectangleConfigurationEquiv L L q
  let T := fun i : SquareLatticeSiteOrEdge L L => Matrix.reindex e e (h.hermitianTerm i)
  let f := Function.extend (squareAreaLawSupport L) T 0
  have hsum : (∑ i : SquareLatticeSiteOrEdge L L, T i) =
      ∑ X : ManyBody.AdmissibleSupport (AreaLaw.rectangularDomain L L) 1, f X := by
    apply Finset.sum_of_injOn (squareAreaLawSupport L)
      (squareAreaLawSupport_injective L).injOn (fun _ _ => Finset.mem_univ _)
    · intro X _ hX
      exact Function.extend_apply' _ _ _ (by simpa using hX)
    · intro i _
      exact ((squareAreaLawSupport_injective L).extend_apply T 0 i).symm
  change (∑ X, f X) = _
  rw [← hsum]
  change (∑ i : SquareLatticeSiteOrEdge L L,
    (Matrix.reindexAlgEquiv ℂ ℂ e) (h.hermitianTerm i)) = _
  rw [← map_sum (Matrix.reindexAlgEquiv ℂ ℂ e), h.sum_hermitianTerm]
  rfl

/-- The original unit ground vector and full-system gap are preserved by
the actual conversion. Source: area-law Corollary 1.2 and polynomial-PEPS
`eq:global-gap`. -/
theorem SquareHamiltonian.isGapped_toAreaLawHamiltonian
    {L q : ℕ} {J : ℝ} (h : SquareHamiltonian L q J)
    {E₀ Δ : ℝ} {Ω : StateSpace L q} (hΩ : ‖Ω‖ = 1)
    (hgap : IsGapped h.operator E₀ Δ) (hspan : groundSpace h.operator E₀ = Submodule.span ℂ {Ω}) :
    ‖squareAreaLawState Ω‖ = 1 ∧ IsGapped h.toAreaLawHamiltonian.operator E₀ Δ ∧
      groundSpace h.toAreaLawHamiltonian.operator E₀ =
        Submodule.span ℂ {squareAreaLawState Ω} := by
  rw [h.toAreaLawHamiltonian_operator]
  exact ⟨(norm_squareAreaLawState Ω).trans hΩ, (ManyBody.isGapped_reindex_iff _).mpr hgap,
    ManyBody.groundSpace_reindex_eq_span _ hspan⟩

end TNLean.PEPS.Approximation
