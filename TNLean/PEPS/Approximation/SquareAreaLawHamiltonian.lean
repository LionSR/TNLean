/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SquareHamiltonianHermitianTerms
import TNLean.PEPS.AreaLaw.RectangularDomain
import TNLean.PEPS.AreaLaw.LocalHamiltonian
import QICLean.Algebra.L2OpNormReindex

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

open Classical Matrix ComplexStarModule
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace TNLean.PEPS.Approximation

private theorem forwardAdjacent_ne {L : ℕ} {v w : Vertex L}
    (h : ForwardAdjacent v w) : v ≠ w := by
  intro heq
  subst w
  rcases h with h | h <;> omega

private theorem forwardAdjacent_not_reverse {L : ℕ} {v w : Vertex L}
    (h : ForwardAdjacent v w) : ¬ ForwardAdjacent w v := by
  intro h'
  rcases h with h | h <;> rcases h' with h' | h'
  · omega
  · have := congrArg Fin.val h'.1
    omega
  · have := congrArg Fin.val h.1
    omega
  · omega

private theorem squareInteractionSupport_injective (L : ℕ) :
    Function.Injective (squareInteractionSupport (L := L)) := by
  intro i j hij
  unfold squareInteractionSupport at hij
  cases i with
  | inl v =>
    cases j with
    | inl w =>
      exact congrArg Sum.inl (Finset.singleton_inj.mp hij)
    | inr e =>
      dsimp only at hij
      have h₁ : e.val.1 = v := by
        have := hij.symm ▸ (Finset.mem_insert_self e.val.1 {e.val.2})
        simpa only [squareInteractionSupport, Finset.mem_singleton] using this
      have h₂ : e.val.2 = v := by
        have := hij.symm ▸ (Finset.mem_insert_of_mem (Finset.mem_singleton_self e.val.2))
        simpa only [squareInteractionSupport, Finset.mem_singleton] using this
      exact False.elim (forwardAdjacent_ne e.property (h₁.trans h₂.symm))
  | inr e =>
    cases j with
    | inl v =>
      dsimp only at hij
      have h₁ : e.val.1 = v := by
        have := hij ▸ (Finset.mem_insert_self e.val.1 {e.val.2})
        simpa only [squareInteractionSupport, Finset.mem_singleton] using this
      have h₂ : e.val.2 = v := by
        have := hij ▸ (Finset.mem_insert_of_mem (Finset.mem_singleton_self e.val.2))
        simpa only [squareInteractionSupport, Finset.mem_singleton] using this
      exact False.elim (forwardAdjacent_ne e.property (h₁.trans h₂.symm))
    | inr f =>
      dsimp only at hij
      have h₁ : e.val.1 = f.val.1 ∨ e.val.1 = f.val.2 := by
        have := hij ▸ (Finset.mem_insert_self e.val.1 {e.val.2})
        simpa only [squareInteractionSupport, Finset.mem_insert, Finset.mem_singleton] using this
      have h₂ : e.val.2 = f.val.1 ∨ e.val.2 = f.val.2 := by
        have := hij ▸ (Finset.mem_insert_of_mem (Finset.mem_singleton_self e.val.2))
        simpa only [squareInteractionSupport, Finset.mem_insert, Finset.mem_singleton] using this
      rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
      · exact False.elim (forwardAdjacent_ne e.property (h₁.trans h₂.symm))
      · exact congrArg Sum.inr (Subtype.ext (Prod.ext h₁ h₂))
      · exact False.elim (forwardAdjacent_not_reverse f.property (by
          simpa only [h₁, h₂] using e.property))
      · exact False.elim (forwardAdjacent_ne e.property (h₁.trans h₂.symm))

/-- Each original site or forward edge determines its actual admissible
range-one support in the integer rectangle. Source: area-law Corollary 1.2
and polynomial-PEPS `eq:model`. -/
def squareAreaLawSupport (L : ℕ) (i : SquareInteraction L) :
    AreaLaw.AdmissibleSupport (AreaLaw.rectangularDomain L L) 1 := by
  classical
  refine ⟨(squareInteractionSupport i).image (AreaLaw.rectangleSiteEquiv L L), ?_⟩
  cases i with
  | inl v =>
    simpa only [squareInteractionSupport, Finset.image_singleton] using
      AreaLaw.isAdmissibleSupport_singleton (AreaLaw.rectangularDomain L L) 1
        (AreaLaw.rectangleSiteEquiv L L v)
  | inr e =>
    simpa only [squareInteractionSupport, Finset.image_insert, Finset.image_singleton,
      forwardSquareEdgeEquiv_val] using
      AreaLaw.isAdmissibleSupport_rectangle_pair_of_adj
        (forwardSquareEdgeEquiv L e).property.2

/-- Distinct original interactions have distinct designated supports.
Source: polynomial-PEPS `eq:model`, one term per site and nearest-neighbor edge. -/
theorem squareAreaLawSupport_injective (L : ℕ) :
    Function.Injective (squareAreaLawSupport L) := by
  intro i j hij
  apply squareInteractionSupport_injective L
  exact Finset.image_injective (AreaLaw.rectangleSiteEquiv L L).injective
    (congrArg Subtype.val hij)

/-- The original vector in the actual integer-domain coordinates.
Source: area-law Corollary 1.2, finite tensor factors. -/
def squareAreaLawState {L q : ℕ} (Ω : StateSpace L q) :
    AreaLaw.StateSpace (AreaLaw.rectangularDomain L L) q :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (AreaLaw.rectangleConfigurationEquiv L L q) Ω

/-- The physical coordinate identification preserves the norm.
Source: area-law Corollary 1.2. -/
theorem norm_squareAreaLawState {L q : ℕ} (Ω : StateSpace L q) :
    ‖squareAreaLawState Ω‖ = ‖Ω‖ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (AreaLaw.rectangleConfigurationEquiv L L q)).norm_map Ω

private theorem embedOp_rectangle_eq_reindex {L q : ℕ}
    (A : Matrix (Configuration L q) (Configuration L q) ℂ) :
    QuantumCircuit.embedOp (AreaLaw.rectangleSiteEquiv L L) A =
      Matrix.reindex (AreaLaw.rectangleConfigurationEquiv L L q)
        (AreaLaw.rectangleConfigurationEquiv L L q) A := by
  ext x y
  rw [QuantumCircuit.embedOp_apply, if_pos]
  · rfl
  · intro v hv
    exact False.elim (hv ((AreaLaw.rectangleSiteEquiv L L).symm v)
      ((AreaLaw.rectangleSiteEquiv L L).apply_symm_apply v))

/-- The Hermitian part of an original interaction remains in its designated
circuit supported-operator algebra. Source: polynomial-PEPS `eq:model`.
This is the support form used by the partially swapped interaction construction. -/
theorem SquareHamiltonian.hermitianTerm_mem_supportedOperators {L q : ℕ} {J : ℝ}
    (h : SquareHamiltonian L q J) (i : SquareInteraction L) :
    h.hermitianTerm i ∈ QuantumCircuit.supportedOperators q
      (squareInteractionSupport i : Set (Vertex L)) := by
  cases i with
  | inl v =>
    simpa only [squareInteractionSupport, Finset.coe_singleton] using!
      coe_realPart_mem_of_star_mem
        (S := (QuantumCircuit.supportedOperators q ({v} : Set (Vertex L))).restrictScalars ℝ)
        (h.site_supported v) (QuantumCircuit.star_mem_supportedOperators (h.site_supported v))
  | inr e =>
    simpa only [squareInteractionSupport, Finset.coe_insert, Finset.coe_singleton] using!
      coe_realPart_mem_of_star_mem
        (S := (QuantumCircuit.supportedOperators q
          ({e.val.1, e.val.2} : Set (Vertex L))).restrictScalars ℝ)
        (h.edge_supported (forwardSquareEdgeEquiv L e))
        (QuantumCircuit.star_mem_supportedOperators (h.edge_supported (forwardSquareEdgeEquiv L e)))

/-- The original square Hamiltonian, with Hermitian parts at its actual
range-one supports and zero at unused supports. The interaction bound is
unchanged. Source: area-law Corollary 1.2 and polynomial-PEPS `eq:model`. -/
def SquareHamiltonian.toAreaLawHamiltonian {L q : ℕ} {J : ℝ}
    (h : SquareHamiltonian L q J) (hJ : 0 ≤ J) :
    AreaLaw.LocalHamiltonian (AreaLaw.rectangularDomain L L) q 1 J := by
  classical
  let e := AreaLaw.rectangleConfigurationEquiv L L q
  let T := fun i : SquareInteraction L => Matrix.reindex e e (h.hermitianTerm i)
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
      exact Submodule.zero_mem _
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
      simpa only [Pi.zero_apply, norm_zero] using hJ

/-- The interaction conversion has exactly the transported original sum.
Source: area-law Corollary 1.2 and polynomial-PEPS `eq:model`. -/
theorem SquareHamiltonian.toAreaLawHamiltonian_operator {L q : ℕ} {J : ℝ}
    (h : SquareHamiltonian L q J) (hJ : 0 ≤ J) :
    (h.toAreaLawHamiltonian hJ).operator =
      Matrix.reindex (AreaLaw.rectangleConfigurationEquiv L L q)
        (AreaLaw.rectangleConfigurationEquiv L L q) h.operator := by
  classical
  let e := AreaLaw.rectangleConfigurationEquiv L L q
  let T := fun i : SquareInteraction L => Matrix.reindex e e (h.hermitianTerm i)
  let f := Function.extend (squareAreaLawSupport L) T 0
  have hsum : (∑ i : SquareInteraction L, T i) =
      ∑ X : AreaLaw.AdmissibleSupport (AreaLaw.rectangularDomain L L) 1, f X := by
    apply Finset.sum_of_injOn (squareAreaLawSupport L)
      (squareAreaLawSupport_injective L).injOn (fun _ _ => Finset.mem_univ _)
    · intro X _ hX
      exact Function.extend_apply' _ _ _ (by simpa using hX)
    · intro i _
      exact ((squareAreaLawSupport_injective L).extend_apply T 0 i).symm
  change (∑ X, f X) = _
  rw [← hsum]
  change (∑ i : SquareInteraction L,
    (Matrix.reindexAlgEquiv ℂ ℂ e) (h.hermitianTerm i)) = _
  rw [← map_sum (Matrix.reindexAlgEquiv ℂ ℂ e), h.sum_hermitianTerm]
  rfl

/-- The original unit ground vector and full-system gap are preserved by
the actual conversion. Source: area-law Corollary 1.2 and polynomial-PEPS
`eq:global-gap`. -/
theorem SquareHamiltonian.isGappedGroundState_toAreaLawHamiltonian
    {L q : ℕ} {J : ℝ} (h : SquareHamiltonian L q J) (hJ : 0 ≤ J)
    {E₀ Δ : ℝ} {Ω : StateSpace L q} (hΩ : h.IsGappedGroundState E₀ Ω Δ) :
    AreaLaw.IsGappedGroundState (AreaLaw.rectangularDomain L L) q
      (h.toAreaLawHamiltonian hJ).operator E₀ (squareAreaLawState Ω) Δ := by
  classical
  let e := AreaLaw.rectangleConfigurationEquiv L L q
  let E := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  refine ⟨(norm_squareAreaLawState Ω).trans hΩ.1, ?_, ?_⟩
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
          (Δ : ℂ) • (1 - vecMulVec (fun x ↦ squareAreaLawState Ω x)
            (star (fun x ↦ squareAreaLawState Ω x))) := by
      ext i j
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply,
        Matrix.smul_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.star_apply,
        e.symm.injective.eq_iff]
      rfl
    done

end TNLean.PEPS.Approximation
