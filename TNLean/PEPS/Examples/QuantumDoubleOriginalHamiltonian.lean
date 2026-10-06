/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.QuantumDoubleOriginalGeometry
import TNLean.PEPS.Examples.QuantumDoubleLatticeBlocking

/-!
# The literal original-spin quantum-double Hamiltonian

SCP10, arXiv:1001.3807v3, Section 7.2, lines 2858–2923. Original A
penalties are ordered product-one constraints. Original B penalties are
the complements of the normalized four-spin L/R averages, with identities
on all spectator spins. The definitions precede, and do not use, the physical
transport comparison. Their coefficients are then proved equal to the K terms.

**Local fix (normalization):** the printed B sum needs the factor |G|⁻¹.
See `docs/paper-gaps/scp10_quantum_double_local_hamiltonian.tex`.
**Scope restriction (native even torus):** fine periods are 2w,2h with w,h≥3.
See `docs/paper-gaps/rmp_peps_examples_small_torus.tex`.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
local notation "V" => TorusVertex width height
local notation "F" => TorusVertex (width * 2) (height * 2)
local notation "E" => Edge (torusGraph width height)
local notation "C" => (F → G)
local notation "block" => quantumDoublePhysicalBlockingEquiv
  (G := G) (width := width) (height := height)

/-- The source's literal original four-spin A penalty, with the arrow-ordered
product and a Kronecker identity on all spectator spins. -/
def quantumDoubleOriginalATerm (j : V ⊕ V) : Matrix C C ℂ :=
  1 - Matrix.diagonal (fun σ => if quantumDoubleOriginalAHolonomy j σ = 1 then 1 else 0)

/-- The forward ket matrix of the independently specified original B action. -/
def quantumDoubleOriginalBMatrix (e : E) (u : G) : Matrix C C ℂ :=
  Matrix.permMatrixHom (quantumDoubleOriginalBPermutation e u)

/-- The printed coherent four-spin sum with its necessary |G|⁻¹ normalization. -/
def quantumDoubleOriginalBAverage (e : E) : Matrix C C ℂ :=
  (Fintype.card G : ℂ)⁻¹ • ∑ u : G, quantumDoubleOriginalBMatrix e u

/-- The literal original four-spin B penalty, including all spectator identities. -/
def quantumDoubleOriginalBTerm (e : E) : Matrix C C ℂ :=
  1 - quantumDoubleOriginalBAverage e

/-- One penalty for every A or B face of the fine periodic lattice. -/
def quantumDoubleOriginalTerm (j : (V ⊕ V) ⊕ E) : Matrix C C ℂ :=
  match j with
  | .inl k => quantumDoubleOriginalATerm k
  | .inr e => quantumDoubleOriginalBTerm e

/-- The actual original-spin Hamiltonian, counting every fine face once. -/
def quantumDoubleOriginalHamiltonian : Matrix C C ℂ := ∑ j, quantumDoubleOriginalTerm j

/-- The B matrix is the source's forward ket coefficient, not its transpose. -/
theorem quantumDoubleOriginalBMatrix_apply (e : E) (u : G) (x y : C) :
    quantumDoubleOriginalBMatrix e u x y =
      if x = quantumDoubleOriginalBAction e u y then 1 else 0 := by
  simp only [quantumDoubleOriginalBMatrix, Matrix.permMatrixHom_apply,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_some_iff]
  have he : (quantumDoubleOriginalBPermutation e u)⁻¹ x = y ↔
      x = quantumDoubleOriginalBAction e u y :=
    (quantumDoubleOriginalBPermutation e u).symm_apply_eq
  simp only [he]

omit [Fact (2 < width)] [Fact (2 < height)] in
/-- The A penalty kills exactly the vectors supported on the ordered product-one
configurations, as in SCP10, Section 7.2, lines 2863–2868. -/
theorem quantumDoubleOriginalATerm_mulVec_eq_zero_iff (j : V ⊕ V) (ψ : C → ℂ) :
    quantumDoubleOriginalATerm j *ᵥ ψ = 0 ↔
      ∀ σ, quantumDoubleOriginalAHolonomy j σ ≠ 1 → ψ σ = 0 := by
  simp only [quantumDoubleOriginalATerm, Matrix.sub_mulVec, Matrix.one_mulVec,
    sub_eq_zero, funext_iff, Matrix.mulVec_diagonal]
  constructor
  · intro h σ hσ
    simpa [hσ] using h σ
  · intro h σ
    by_cases hσ : quantumDoubleOriginalAHolonomy j σ = 1
    · simp [hσ]
    · simp [hσ, h σ hσ]

/-- The original B kernel is precisely invariance under all of its four-spin
L/R actions; the normalized average does not select a single group element. -/
theorem quantumDoubleOriginalBTerm_mulVec_eq_zero_iff (e : E) (ψ : C → ℂ) :
    quantumDoubleOriginalBTerm e *ᵥ ψ = 0 ↔
      ∀ u σ, ψ (quantumDoubleOriginalBAction e u σ) = ψ σ := by
  rw [quantumDoubleOriginalBTerm, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero, eq_comm]
  exact TNLean.Algebra.inv_card_smul_sum_permMatrixHom_mulVec_eq_self_iff
    (quantumDoubleOriginalBPermutation e) ψ

omit [Fact (2 < width)] [Fact (2 < height)] [Group G] in
/-- Entrywise formula for the already derived physical regrouping. -/
theorem quantumDoubleUnblockOperator_apply
    (H : Matrix (QuantumDoubleKLatticeConfig width height G)
      (QuantumDoubleKLatticeConfig width height G) ℂ) (x y : C) :
    quantumDoubleUnblockOperator H x y = H (block x) (block y) := by
  simp [quantumDoubleUnblockOperator, quantumDoublePhysicalBlockingMatrix,
    Matrix.mul_apply, Matrix.conjTranspose_apply, endpointEmbeddingMatrix]

/-- Literal original A coefficients equal the actual K local/hole flatness
coefficients on the entire spin space, including nonflat configurations. -/
theorem quantumDoubleOriginalATerm_eq_unblocked (j : V ⊕ V) :
    quantumDoubleOriginalATerm (G := G) j = quantumDoubleKLatticeUnblockedTerm (.inl j) := by
  ext x y
  rw [quantumDoubleKLatticeUnblockedTerm, quantumDoubleUnblockOperator_apply]
  simp only [quantumDoubleOriginalATerm, quantumDoubleKLatticeTerm,
    quantumDoubleKLatticeProjector, quantumDoubleKLatticeFlatProjector,
    Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply, (block).injective.eq_iff,
    quantumDoubleOriginalAHolonomy_block]
  cases j <;> rfl

/-- Equality of the original L/R coefficient and the physical pullback of a
single coherent K bond action, before taking the group average. -/
theorem quantumDoubleOriginalBMatrix_eq_unblocked (e : E) (u : G) :
    quantumDoubleOriginalBMatrix e u =
      quantumDoubleUnblockOperator (quantumDoubleKLatticeBondMatrix e u) := by
  ext x y
  rw [quantumDoubleUnblockOperator_apply]
  simp only [quantumDoubleOriginalBMatrix, quantumDoubleKLatticeBondMatrix,
    Matrix.permMatrixHom_apply, ← map_inv]
  have h := quantumDoubleOriginalBAction_block e u⁻¹ x
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_some_iff, ← h, (block).injective.eq_iff]
  rfl

/-- The independently defined normalized original B average equals the
transported K average coefficientwise, with exactly the same scalar. -/
theorem quantumDoubleOriginalBAverage_eq_unblocked (e : E) :
    quantumDoubleOriginalBAverage (G := G) e =
      quantumDoubleUnblockOperator (quantumDoubleKLatticeBondAverage e) := by
  ext x y
  simp only [quantumDoubleOriginalBAverage, quantumDoubleOriginalBMatrix_eq_unblocked,
    quantumDoubleUnblockOperator_apply, quantumDoubleKLatticeBondAverage,
    Matrix.smul_apply, Matrix.sum_apply]

/-- The literal original B penalty equals the complementary K bond average. -/
theorem quantumDoubleOriginalBTerm_eq_unblocked (e : E) :
    quantumDoubleOriginalBTerm (G := G) e = quantumDoubleKLatticeUnblockedTerm (.inr e) := by
  ext x y
  simp only [quantumDoubleOriginalBTerm, quantumDoubleOriginalBAverage_eq_unblocked,
    quantumDoubleUnblockOperator_apply, quantumDoubleKLatticeUnblockedTerm,
    quantumDoubleKLatticeTerm, quantumDoubleKLatticeProjector, Matrix.sub_apply,
    Matrix.one_apply, (block).injective.eq_iff]

/-- Coefficient equality of every independently defined original physical
term with its K counterpart, for arbitrary finite groups. -/
theorem quantumDoubleOriginalTerm_eq_unblocked (j : (V ⊕ V) ⊕ E) :
    quantumDoubleOriginalTerm (G := G) j = quantumDoubleKLatticeUnblockedTerm j := by
  cases j with
  | inl k => exact quantumDoubleOriginalATerm_eq_unblocked k
  | inr e => exact quantumDoubleOriginalBTerm_eq_unblocked e

/-- The whole original Hamiltonian equals the derived physical pullback,
as a consequence of the separate coefficient comparisons. -/
theorem quantumDoubleOriginalHamiltonian_eq_unblocked :
    quantumDoubleOriginalHamiltonian (width := width) (height := height) =
      quantumDoubleKLatticeUnblockedHamiltonian (G := G) := by
  rw [quantumDoubleOriginalHamiltonian, quantumDoubleKLatticeUnblockedHamiltonian_eq_sum]
  exact Finset.sum_congr rfl fun j _ => quantumDoubleOriginalTerm_eq_unblocked j

/-- Every literal A or B term is an orthogonal projector on the full physical space. -/
theorem quantumDoubleOriginalTerm_isStarProjection (j : (V ⊕ V) ⊕ E) :
    IsStarProjection (quantumDoubleOriginalTerm (G := G) j) := by
  rw [quantumDoubleOriginalTerm_eq_unblocked]
  exact quantumDoubleKLatticeUnblockedTerm_isStarProjection j

/-- All actual original-lattice quantum-double terms commute, even on overlapping faces. -/
theorem quantumDoubleOriginalTerm_commute (j k : (V ⊕ V) ⊕ E) :
    Commute (quantumDoubleOriginalTerm (G := G) j) (quantumDoubleOriginalTerm k) := by
  simp only [quantumDoubleOriginalTerm_eq_unblocked]
  exact quantumDoubleKLatticeUnblockedTerm_commute j k

/-- Every original physical penalty is positive semidefinite. -/
theorem quantumDoubleOriginalTerm_posSemidef (j : (V ⊕ V) ⊕ E) :
    (quantumDoubleOriginalTerm (G := G) j).PosSemidef := by
  rw [quantumDoubleOriginalTerm_eq_unblocked, quantumDoubleKLatticeUnblockedTerm,
    quantumDoubleUnblockOperator]
  exact (quantumDoubleKLatticeTerm_posSemidef j).conjTranspose_mul_mul_same _

/-- The actual quantum-double Hamiltonian is positive, so its nonzero zero-energy
vectors are ground states. -/
theorem quantumDoubleOriginalHamiltonian_posSemidef :
    (quantumDoubleOriginalHamiltonian (width := width) (height := height) (G := G)).PosSemidef :=
  Matrix.posSemidef_sum Finset.univ fun j _ => quantumDoubleOriginalTerm_posSemidef j

/-- The kernel of the literal quantum-double Hamiltonian is precisely the common
zero-energy space of all its A and B projectors. -/
theorem quantumDoubleOriginalHamiltonian_mulVec_eq_zero_iff (ψ : C → ℂ) :
    quantumDoubleOriginalHamiltonian *ᵥ ψ = 0 ↔ ∀ j, quantumDoubleOriginalTerm j *ᵥ ψ = 0 := by
  simp only [quantumDoubleOriginalHamiltonian_eq_unblocked, quantumDoubleOriginalTerm_eq_unblocked,
    quantumDoubleKLatticeUnblockedHamiltonian, quantumDoubleKLatticeUnblockedTerm,
    quantumDoubleUnblockOperator_mulVec_eq_zero_iff]
  exact quantumDoubleKLatticeHamiltonian_mulVec_eq_zero_iff _

/-- All topological sectors are retained: physical blocking identifies the
entire original quantum-double kernel with the actual commuting K closure span. -/
theorem quantumDoubleOriginalHamiltonian_mulVec_eq_zero_iff_closureSpan (ψ : C → ℂ) :
    quantumDoubleOriginalHamiltonian *ᵥ ψ = 0 ↔
      quantumDoublePhysicalBlockingMatrix *ᵥ ψ ∈
        quantumDoubleKCommutingClosureSpan (width := width) (height := height) := by
  rw [quantumDoubleOriginalHamiltonian_eq_unblocked]
  exact quantumDoubleKLatticeUnblockedHamiltonian_mulVec_eq_zero_iff ψ

/-- Every original A/B term annihilates the literal source elementary T
contraction. This state is defined by its original physical-site network. -/
theorem quantumDoubleOriginalTerm_checkerboard (j : (V ⊕ V) ⊕ E) :
    quantumDoubleOriginalTerm (G := G) j *ᵥ
      (fun σ => torusBondNetwork (quantumDoublePeriodicElementarySite σ) 1 1) = 0 := by
  rw [quantumDoubleOriginalTerm_eq_unblocked]
  exact quantumDoubleKLatticeUnblockedTerm_checkerboard j

/-- The source elementary PEPS has zero energy for the literal quantum-double Hamiltonian. -/
theorem quantumDoubleOriginalHamiltonian_checkerboard :
    quantumDoubleOriginalHamiltonian (width := width) (height := height) (G := G) *ᵥ
      (fun σ => torusBondNetwork (quantumDoublePeriodicElementarySite σ) 1 1) = 0 := by
  rw [quantumDoubleOriginalHamiltonian_eq_unblocked]
  exact quantumDoubleKLatticeUnblockedHamiltonian_checkerboard

end TNLean.PEPS
