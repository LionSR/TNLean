/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.QuantumDoubleLatticeGauge
import TNLean.Algebra.FinitePermutationAverage
import QICLean.Algebra.MatrixAux

/-!
# All placed terms of the periodic blocked quantum-double Hamiltonian

SCP10, arXiv:1001.3807v3, Section 7.2, source lines 2918–2923:
local product-one, hole product-one, and coherent bond averaging terms act
on the full periodic physical space. Their complementary projectors are
orthogonal and commute pairwise on the entire ambient space. The bond
average has the necessary factor `|G|⁻¹`, as in the approved local model.
No commutator or kernel equality is assumed as a hypothesis.

**Scope restriction (native simple torus):** Both periods are at least three.
See `docs/paper-gaps/rmp_peps_examples_small_torus.tex`.

**Local fix (normalization):** The missing one-bond factor in the printed
source is supplied; see `docs/paper-gaps/scp10_quantum_double_local_hamiltonian.tex`.
-/

open scoped BigOperators Matrix ComplexOrder

noncomputable section
namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "E" => Edge (torusGraph width height)
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
local notation "C" => QuantumDoubleKLatticeConfig width height G

/-- Local and plaquette product-one conditions, indexed separately even
when their lower-left corners agree. -/
def QuantumDoubleKLatticeFlatAt (j : X ⊕ X) (x : C) : Prop :=
  match j with
  | .inl v => quantumDoubleKHolonomy (x v) = 1
  | .inr v => quantumDoubleKLatticePlaquetteHolonomy x v = 1

instance (j : X ⊕ X) (x : C) : Decidable (QuantumDoubleKLatticeFlatAt j x) := by
  unfold QuantumDoubleKLatticeFlatAt
  split <;> infer_instance

/-- The actual full-space diagonal placement of either product-one projector. -/
def quantumDoubleKLatticeFlatProjector (j : X ⊕ X) : Matrix C C ℂ :=
  Matrix.diagonal fun x => if QuantumDoubleKLatticeFlatAt j x then 1 else 0

/-- Actual full-lattice coherent bond matrices, with the forward ket convention. -/
def quantumDoubleKLatticeBondMatrix (e : E) (u : G) : Matrix C C ℂ :=
  Matrix.permMatrixHom (quantumDoubleKLatticeBondPermutation e u)

/-- The source's bond term uses this normalized average over the single
shared virtual bond color, with all other lattice spins as spectators. -/
def quantumDoubleKLatticeBondAverage (e : E) : Matrix C C ℂ :=
  (Fintype.card G : ℂ)⁻¹ • ∑ u : G, quantumDoubleKLatticeBondMatrix e u

/-- The three explicitly placed types of source constraints. -/
def quantumDoubleKLatticeProjector (j : (X ⊕ X) ⊕ E) : Matrix C C ℂ :=
  match j with
  | .inl k => quantumDoubleKLatticeFlatProjector k
  | .inr e => quantumDoubleKLatticeBondAverage e

/-- The complementary local, hole, or bond Hamiltonian term. -/
def quantumDoubleKLatticeTerm (j : (X ⊕ X) ⊕ E) : Matrix C C ℂ :=
  1 - quantumDoubleKLatticeProjector j

/-- The full periodic Hamiltonian, summing all three types of terms. -/
def quantumDoubleKLatticeHamiltonian : Matrix C C ℂ :=
  ∑ j : (X ⊕ X) ⊕ E, quantumDoubleKLatticeTerm j

omit [Fact (2 < width)] [Fact (2 < height)] in
/-- Every placed product-one projector is orthogonal on the full spin space. -/
theorem quantumDoubleKLatticeFlatProjector_isStarProjection (j : X ⊕ X) :
    IsStarProjection (quantumDoubleKLatticeFlatProjector (G := G) j) := by
  apply (isStarProjection_iff').mpr
  constructor
  · rw [quantumDoubleKLatticeFlatProjector, Matrix.diagonal_mul_diagonal]
    congr 1
    funext x
    split_ifs <;> simp
  · change (quantumDoubleKLatticeFlatProjector (G := G) j)ᴴ = _
    ext x y
    simp only [quantumDoubleKLatticeFlatProjector, Matrix.conjTranspose_apply,
      Matrix.diagonal_apply]
    split_ifs <;> simp_all

/-- Every single-bond average is a normalized orthogonal projector. -/
theorem quantumDoubleKLatticeBondAverage_isStarProjection (e : E) :
    IsStarProjection (quantumDoubleKLatticeBondAverage (G := G) e) := by
  exact TNLean.Algebra.isStarProjection_inv_card_smul_sum_permMatrixHom
    (quantumDoubleKLatticeBondPermutation (G := G) e)

/-- All three kinds of placed projectors are orthogonal. -/
theorem quantumDoubleKLatticeProjector_isStarProjection (j : (X ⊕ X) ⊕ E) :
    IsStarProjection (quantumDoubleKLatticeProjector (G := G) j) := by
  cases j with
  | inl k => exact quantumDoubleKLatticeFlatProjector_isStarProjection k
  | inr e => exact quantumDoubleKLatticeBondAverage_isStarProjection e

/-- All actual physical Hamiltonian terms are orthogonal projectors. -/
theorem quantumDoubleKLatticeTerm_isStarProjection (j : (X ⊕ X) ⊕ E) :
    IsStarProjection (quantumDoubleKLatticeTerm (G := G) j) :=
  (quantumDoubleKLatticeProjector_isStarProjection j).one_sub

omit [Fintype G] [DecidableEq G] in
/-- The placed local and hole conditions are invariant under any collection
of coherent bond actions. -/
theorem quantumDoubleKLatticeFlatAt_gauge_iff (j : X ⊕ X) (u : E → G) (x : C) :
    QuantumDoubleKLatticeFlatAt j (quantumDoubleKLatticeGauge u x) ↔
      QuantumDoubleKLatticeFlatAt j x := by
  cases j with
  | inl v => exact quantumDoubleKHolonomy_latticeGauge_eq_one_iff u x v
  | inr v => exact quantumDoubleKLatticePlaquetteHolonomy_gauge_eq_one_iff u x v

/-- Product-one constraints commute with every full-lattice color change,
including incident bonds and seam-crossing placements. -/
theorem quantumDoubleKLatticeFlatProjector_commute_gauge (j : X ⊕ X) (u : E → G) :
    Commute (quantumDoubleKLatticeFlatProjector (G := G) j)
      (Matrix.permMatrixHom (R := ℂ) (quantumDoubleKLatticeGaugePermutation u)) := by
  change Commute _ ((quantumDoubleKLatticeGaugePermutation u)⁻¹.permMatrix ℂ)
  apply Matrix.commute_permMatrix_of_entry_invariant
  intro x y
  simp only [quantumDoubleKLatticeFlatProjector, Matrix.diagonal_apply,
    (quantumDoubleKLatticeGaugePermutation u)⁻¹.injective.eq_iff]
  change (if x = y then
    (if QuantumDoubleKLatticeFlatAt j (quantumDoubleKLatticeGauge u⁻¹ x)
      then (1 : ℂ) else 0) else 0) = _
  simp only [quantumDoubleKLatticeFlatAt_gauge_iff]

/-- Every local or hole projector commutes with every normalized bond average. -/
theorem quantumDoubleKLatticeFlatProjector_commute_bondAverage (j : X ⊕ X) (e : E) :
    Commute (quantumDoubleKLatticeFlatProjector (G := G) j)
      (quantumDoubleKLatticeBondAverage e) := by
  apply Commute.smul_right
  apply Commute.sum_right
  intro u _
  exact quantumDoubleKLatticeFlatProjector_commute_gauge j (Pi.mulSingle e u)

/-- All bond averages commute. On distinct bonds this follows from the
actual commuting color actions, rather than from any flatness assumption. -/
theorem quantumDoubleKLatticeBondAverage_commute (e f : E) :
    Commute (quantumDoubleKLatticeBondAverage (G := G) e)
      (quantumDoubleKLatticeBondAverage f) := by
  by_cases hef : e = f
  · subst f
    exact Commute.refl _
  · apply Commute.smul_left
    apply Commute.smul_right
    apply Commute.sum_left
    intro u _
    apply Commute.sum_right
    intro w _
    exact (quantumDoubleKLatticeBondPermutation_commute hef u w).map
      (Matrix.permMatrixHom (R := ℂ))

omit [Fact (2 < width)] [Fact (2 < height)] in
/-- The two diagonal families commute at arbitrary, possibly overlapping sites. -/
theorem quantumDoubleKLatticeFlatProjector_commute (j k : X ⊕ X) :
    Commute (quantumDoubleKLatticeFlatProjector (G := G) j)
      (quantumDoubleKLatticeFlatProjector k) := by
  change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  simp only [Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  exact mul_comm _ _

/-- Pairwise commutation of all placed source projectors on the full periodic space. -/
theorem quantumDoubleKLatticeProjector_commute (j k : (X ⊕ X) ⊕ E) :
    Commute (quantumDoubleKLatticeProjector (G := G) j) (quantumDoubleKLatticeProjector k) := by
  cases j with
  | inl i =>
    cases k with
    | inl l => exact quantumDoubleKLatticeFlatProjector_commute i l
    | inr e => exact quantumDoubleKLatticeFlatProjector_commute_bondAverage i e
  | inr e =>
    cases k with
    | inl i => exact (quantumDoubleKLatticeFlatProjector_commute_bondAverage i e).symm
    | inr f => exact quantumDoubleKLatticeBondAverage_commute e f

/-- All three types of actual Hamiltonian terms commute pairwise. -/
theorem quantumDoubleKLatticeTerm_commute (j k : (X ⊕ X) ⊕ E) :
    Commute (quantumDoubleKLatticeTerm (G := G) j) (quantumDoubleKLatticeTerm k) :=
  (Commute.one_left _).sub_left
    ((Commute.one_right _).sub_right (quantumDoubleKLatticeProjector_commute j k))

/-- Each term is positive, derived from its orthogonal-projector identities. -/
theorem quantumDoubleKLatticeTerm_posSemidef (j : (X ⊕ X) ⊕ E) :
    (quantumDoubleKLatticeTerm (G := G) j).PosSemidef := by
  have hp := quantumDoubleKLatticeTerm_isStarProjection (G := G) j
  have h := Matrix.posSemidef_conjTranspose_mul_self (quantumDoubleKLatticeTerm (G := G) j)
  rwa [← Matrix.star_eq_conjTranspose, hp.isSelfAdjoint.star_eq,
    hp.isIdempotentElem.eq] at h

/-- The full Hamiltonian is positive semidefinite. -/
theorem quantumDoubleKLatticeHamiltonian_posSemidef :
    (quantumDoubleKLatticeHamiltonian (width := width) (height := height) (G := G)).PosSemidef :=
  Matrix.posSemidef_sum Finset.univ fun j _ => quantumDoubleKLatticeTerm_posSemidef j

/-- Positivity identifies the total periodic kernel with the actual common
kernel, without assuming commutation or restricting the physical alphabet. -/
theorem quantumDoubleKLatticeHamiltonian_mulVec_eq_zero_iff (ψ : C → ℂ) :
    quantumDoubleKLatticeHamiltonian *ᵥ ψ = 0 ↔
      ∀ j, quantumDoubleKLatticeTerm j *ᵥ ψ = 0 := by
  constructor
  · intro h j
    exact Matrix.PosSemidef.mulVec_eq_zero_of_sum_mulVec_eq_zero
      quantumDoubleKLatticeTerm_posSemidef h j
  · intro h
    rw [quantumDoubleKLatticeHamiltonian, Matrix.sum_mulVec]
    simp only [h, Finset.sum_const_zero]

end TNLean.PEPS
