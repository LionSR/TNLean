/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.ToricCodePlaquetteGeometry
import TNLean.PEPS.Examples.QuantumDoubleLatticeBlocking

/-!
# The original physical toric-code Hamiltonian

The A and B terms are defined independently as (I−Z⊗Z⊗Z⊗Z)/2 and
(I−X⊗X⊗X⊗X)/2 on the four original qubits of each checkerboard face,
with identities on every other qubit. A coefficient comparison identifies
these operators with the Z₂ specialization of the actual K Hamiltonian
transported through the proved physical regrouping. Thus the full-space
commutation, orthogonal projection, and common-kernel statements refer
to the literal original-lattice Pauli operators.

Source: SCP10, arXiv:1001.3807v3, Section 7.1, lines 2636–2685.
**Local fix (sign and normalization):** the coherent sum in the printed
B equation is I+X⊗4, and the ground projector is I−h_B, not (I−h_B)/2.
See `docs/paper-gaps/scp10_toric_code_projector_normalization.tex`.
The finite native torus comparison uses coarse periods at least three.

**Scope restriction (native even torus):** the full comparison uses fine
periods 2w,2h with w,h≥3. Small periodic lattices are not classified here.
See `docs/paper-gaps/scp10_toric_code_projector_normalization.tex`.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "V" => TorusVertex width height
local notation "F" => TorusVertex (width * 2) (height * 2)
local notation "E" => Edge (torusGraph width height)
local notation "C" => (F → ToricCodeGroup)
local notation "block" => quantumDoublePhysicalBlockingEquiv
  (G := ToricCodeGroup) (width := width) (height := height)

/-- SCP10 equation `eq:ex:A-stabilizer`: four physical Z factors at an A face. -/
def toricCodeATerm (j : V ⊕ V) : Matrix C C ℂ :=
  (1 / 2 : ℂ) • (1 - toricCodePlacedZ (toricCodeARegion j))

/-- SCP10 equation `eq:ex:B-stabilizer`: four physical X factors at a B face. -/
def toricCodeBTerm (e : E) : Matrix C C ℂ :=
  (1 / 2 : ℂ) • (1 - toricCodePlacedX (toricCodeBRegion e))

omit [Fact (2 < width)] [Fact (2 < height)] in
/-- An A penalty has exactly the even-parity physical support stated in
SCP10, Section 7.1, lines 2643–2645. -/
theorem toricCodeATerm_mulVec_eq_zero_iff (j : V ⊕ V) (ψ : C → ℂ) :
    toricCodeATerm j *ᵥ ψ = 0 ↔
      ∀ σ, (∏ p ∈ toricCodeARegion j, σ p) ≠ 1 → ψ σ = 0 := by
  have hhalf : (1 / 2 : ℂ) ≠ 0 := by norm_num
  simp only [toricCodeATerm, Matrix.smul_mulVec, smul_eq_zero, hhalf, false_or,
    Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  constructor
  · intro h σ hσ
    have he := congrFun h σ
    rw [toricCodePlacedZ_mulVec, toricCodePauliSign_eq_ite, ite_eq_right hσ] at he
    linear_combination (1 / 2 : ℂ) * he
  · intro h
    funext σ
    rw [toricCodePlacedZ_mulVec, toricCodePauliSign_eq_ite]
    split_ifs with hσ
    · simp
    · rw [h σ hσ]
      simp

/-- A B penalty kills exactly the physical vectors invariant under flipping
all four adjacent spins, as stated in SCP10, Section 7.1, lines 2655–2658. -/
theorem toricCodeBTerm_mulVec_eq_zero_iff (e : E) (ψ : C → ℂ) :
    toricCodeBTerm e *ᵥ ψ = 0 ↔
      ∀ σ, ψ (toricCodeFlipSites (toricCodeBRegion e) σ) = ψ σ := by
  have hhalf : (1 / 2 : ℂ) ≠ 0 := by norm_num
  simp only [toricCodeBTerm, Matrix.smul_mulVec, smul_eq_zero, hhalf, false_or,
    Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero, toricCodePlacedX_mulVec]
  rw [eq_comm, funext_iff]
  rfl

/-- All original physical Pauli terms, retaining the A/B face distinction. -/
def toricCodePauliTerm (j : (V ⊕ V) ⊕ E) : Matrix C C ℂ :=
  match j with
  | .inl k => toricCodeATerm k
  | .inr e => toricCodeBTerm e

/-- The actual original-lattice Hamiltonian H_A+H_B, with one term per face. -/
def toricCodePauliHamiltonian : Matrix C C ℂ := ∑ j, toricCodePauliTerm j

omit [Fact (2 < width)] [Fact (2 < height)] in
private theorem unblockOperator_apply
    (H : Matrix (QuantumDoubleKLatticeConfig width height ToricCodeGroup)
      (QuantumDoubleKLatticeConfig width height ToricCodeGroup) ℂ) (x y : C) :
    quantumDoubleUnblockOperator H x y = H (block x) (block y) := by
  simp [quantumDoubleUnblockOperator, quantumDoublePhysicalBlockingMatrix,
    Matrix.mul_apply, Matrix.conjTranspose_apply, endpointEmbeddingMatrix]

/-- The diagonal four-Z term equals the corresponding explicit K flatness
term after physical regrouping, on every input and output coefficient. -/
theorem toricCodeATerm_eq_unblocked (j : V ⊕ V) :
    toricCodeATerm j =
      quantumDoubleKLatticeUnblockedTerm (G := ToricCodeGroup) (.inl j) := by
  ext x y
  rw [quantumDoubleKLatticeUnblockedTerm, unblockOperator_apply]
  simp only [toricCodeATerm, toricCodePlacedZ_eq_diagonal,
    quantumDoubleKLatticeTerm, quantumDoubleKLatticeProjector,
    quantumDoubleKLatticeFlatProjector, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.one_apply, Matrix.diagonal_apply, (block).injective.eq_iff, smul_eq_mul]
  by_cases hxy : x = y
  · subst y
    simp only [ite_true, toricCodePauliSign_eq_ite, toricCodeARegion_product]
    cases j <;> simp only [QuantumDoubleKLatticeFlatAt] <;> split_ifs <;> norm_num
  · simp [hxy]

private theorem bondAverage_binary (e : E) :
    quantumDoubleKLatticeBondAverage (G := ToricCodeGroup) e =
      (1 / 2 : ℂ) • (1 + quantumDoubleKLatticeBondMatrix e toricCodeBitOne) := by
  have hsum : (∑ g : ToricCodeGroup, quantumDoubleKLatticeBondMatrix e g) =
      quantumDoubleKLatticeBondMatrix e 1 +
        quantumDoubleKLatticeBondMatrix e toricCodeBitOne := Fin.sum_univ_two _
  rw [quantumDoubleKLatticeBondAverage, hsum]
  simp [quantumDoubleKLatticeBondMatrix, ToricCodeGroup]

/-- The full four-X coefficient is the actual single-bond permutation
coefficient, including its spectators and the periodic boundary. -/
theorem toricCodePlacedX_BRegion_eq_unblocked (e : E) :
    toricCodePlacedX (toricCodeBRegion e) =
      quantumDoubleUnblockOperator
        (quantumDoubleKLatticeBondMatrix e toricCodeBitOne) := by
  ext x y
  rw [toricCodePlacedX_eq_permMatrix, unblockOperator_apply]
  simp only [quantumDoubleKLatticeBondMatrix, Matrix.permMatrixHom_apply,
    ← map_inv, toricCodeGroup_inv]
  have h := toricCodeBRegion_flip_block e x
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_some_iff, ← h, (block).injective.eq_iff]

/-- The literal original B term is the normalized complementary binary bond
average after regrouping. The printed unnormalized coherent sum is not h_B. -/
theorem toricCodeBTerm_eq_unblocked (e : E) :
    toricCodeBTerm e = quantumDoubleKLatticeUnblockedTerm (G := ToricCodeGroup) (.inr e) := by
  ext x y
  rw [quantumDoubleKLatticeUnblockedTerm, unblockOperator_apply]
  simp only [toricCodeBTerm, toricCodePlacedX_BRegion_eq_unblocked,
    unblockOperator_apply, quantumDoubleKLatticeTerm, quantumDoubleKLatticeProjector,
    bondAverage_binary, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.one_apply, (block).injective.eq_iff, smul_eq_mul]
  ring

/-- Coefficient equality of every independently defined original-lattice
Pauli term with its physically regrouped K counterpart. -/
theorem toricCodePauliTerm_eq_unblocked (j : (V ⊕ V) ⊕ E) :
    toricCodePauliTerm j = quantumDoubleKLatticeUnblockedTerm (G := ToricCodeGroup) j := by
  cases j with
  | inl k => exact toricCodeATerm_eq_unblocked k
  | inr e => exact toricCodeBTerm_eq_unblocked e

/-- The whole original Hamiltonian equals the derived physical pullback,
as a consequence of the separate coefficient comparisons. -/
theorem toricCodePauliHamiltonian_eq_unblocked :
    toricCodePauliHamiltonian (width := width) (height := height) =
      quantumDoubleKLatticeUnblockedHamiltonian (G := ToricCodeGroup) := by
  rw [toricCodePauliHamiltonian, quantumDoubleKLatticeUnblockedHamiltonian_eq_sum]
  exact Finset.sum_congr rfl fun j _ => toricCodePauliTerm_eq_unblocked j

/-- Every literal A or B term is an orthogonal projector on the full physical space. -/
theorem toricCodePauliTerm_isStarProjection (j : (V ⊕ V) ⊕ E) :
    IsStarProjection (toricCodePauliTerm j) := by
  rw [toricCodePauliTerm_eq_unblocked]
  exact quantumDoubleKLatticeUnblockedTerm_isStarProjection j

/-- All actual original-lattice Pauli terms commute, even on overlapping faces. -/
theorem toricCodePauliTerm_commute (j k : (V ⊕ V) ⊕ E) :
    Commute (toricCodePauliTerm j) (toricCodePauliTerm k) := by
  simp only [toricCodePauliTerm_eq_unblocked]
  exact quantumDoubleKLatticeUnblockedTerm_commute j k

/-- Every original physical penalty is positive semidefinite. -/
theorem toricCodePauliTerm_posSemidef (j : (V ⊕ V) ⊕ E) :
    (toricCodePauliTerm j).PosSemidef := by
  rw [toricCodePauliTerm_eq_unblocked, quantumDoubleKLatticeUnblockedTerm,
    quantumDoubleUnblockOperator]
  exact (quantumDoubleKLatticeTerm_posSemidef j).conjTranspose_mul_mul_same _

/-- The actual Pauli Hamiltonian is positive, so its nonzero zero-energy
vectors are ground states. -/
theorem toricCodePauliHamiltonian_posSemidef :
    (toricCodePauliHamiltonian (width := width) (height := height)).PosSemidef :=
  Matrix.posSemidef_sum Finset.univ fun j _ => toricCodePauliTerm_posSemidef j

/-- The kernel of the literal Pauli Hamiltonian is precisely the common
zero-energy space of all its A and B projectors. -/
theorem toricCodePauliHamiltonian_mulVec_eq_zero_iff (ψ : C → ℂ) :
    toricCodePauliHamiltonian *ᵥ ψ = 0 ↔ ∀ j, toricCodePauliTerm j *ᵥ ψ = 0 := by
  simp only [toricCodePauliHamiltonian_eq_unblocked, toricCodePauliTerm_eq_unblocked,
    quantumDoubleKLatticeUnblockedHamiltonian, quantumDoubleKLatticeUnblockedTerm,
    quantumDoubleUnblockOperator_mulVec_eq_zero_iff]
  exact quantumDoubleKLatticeHamiltonian_mulVec_eq_zero_iff _

/-- All topological sectors are retained: physical blocking identifies the
entire original Pauli kernel with the actual commuting K closure span. -/
theorem toricCodePauliHamiltonian_mulVec_eq_zero_iff_closureSpan (ψ : C → ℂ) :
    toricCodePauliHamiltonian *ᵥ ψ = 0 ↔
      quantumDoublePhysicalBlockingMatrix *ᵥ ψ ∈
        quantumDoubleKCommutingClosureSpan (width := width) (height := height) := by
  rw [toricCodePauliHamiltonian_eq_unblocked]
  exact quantumDoubleKLatticeUnblockedHamiltonian_mulVec_eq_zero_iff ψ

/-- Every original A/B term annihilates the literal source elementary T
contraction. This state is defined by its original physical-site network. -/
theorem toricCodePauliTerm_checkerboard (j : (V ⊕ V) ⊕ E) :
    toricCodePauliTerm j *ᵥ
      (fun σ => torusBondNetwork (quantumDoublePeriodicElementarySite σ) 1 1) = 0 := by
  rw [toricCodePauliTerm_eq_unblocked]
  exact quantumDoubleKLatticeUnblockedTerm_checkerboard j

/-- The source elementary PEPS has zero energy for the literal Pauli Hamiltonian. -/
theorem toricCodePauliHamiltonian_checkerboard :
    toricCodePauliHamiltonian (width := width) (height := height) *ᵥ
      (fun σ => torusBondNetwork (quantumDoublePeriodicElementarySite σ) 1 1) = 0 := by
  rw [toricCodePauliHamiltonian_eq_unblocked]
  exact quantumDoubleKLatticeUnblockedHamiltonian_checkerboard

end TNLean.PEPS
