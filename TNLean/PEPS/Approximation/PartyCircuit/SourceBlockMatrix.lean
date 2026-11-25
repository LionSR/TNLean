/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyCircuit.PreparedMatrixNorm

/-!
# Joint contraction of free source inputs

The columns associated with all source assignments form one matrix of the
remaining allowed word. Its operator norm is at most one, independently of the
number and dimensions of the sources. This bound applies to arbitrary
superpositions of source and physical inputs.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 383–468, in particular the free-input contractions
used to separate the corrected source coefficients.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator
open Matrix ManyBody

namespace QuantumCircuit.Party.Word

open SourceInventory

variable {P : Type} [Fintype P] [DecidableEq P] (R : SourceInventory P)
  (B : SlotBases R.length) (X : P → Type) [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
  {Y : P → Type} [∀ p, Fintype (Y p)]

omit [Fintype P] [DecidableEq P] [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
  [∀ p, Fintype (Y p)] in
/-- The slot vector of basis vectors is a basis vector. -/
private theorem slotVector_single (a : ∀ i, B.left i × B.right i) :
    slotVector R B (fun i ↦ EuclideanSpace.vecKron
      (EuclideanSpace.single (a i).1 (1 : ℂ)) (EuclideanSpace.single (a i).2 1)) =
      EuclideanSpace.single a 1 := by
  ext f
  rw [slotVector_apply, PiLp.single_apply]
  split_ifs with h
  · subst h
    simp [EuclideanSpace.vecKron]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    by_cases h₁ : (f i).1 = (a i).1
    · have h₂ : (f i).2 ≠ (a i).2 := fun h₂ ↦ hi (Prod.ext h₁ h₂)
      simp [EuclideanSpace.vecKron, h₂]
    · simp [EuclideanSpace.vecKron, h₁]

/-- The matrix of the remaining word with every source coordinate and every
physical input coordinate free. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 383–427. -/
def freeSourceMatrix (v : Word (slotSystem R B X) Y) :
    Matrix (Config Y) ((∀ i, B.left i × B.right i) × Config X) ℂ :=
  v.op.submatrix id (slotColumnEquiv R B X).symm

omit [∀ p, Fintype (Y p)] in
/-- A block of the full matrix is the actual branch prepared with the corresponding
endpoint basis vectors. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 409–427. -/
theorem freeSourceMatrix_apply (v : Word (slotSystem R B X) Y)
    (a : ∀ i, B.left i × B.right i) (j : Config X) (k : Config Y) :
    v.freeSourceMatrix R B X k (a, j) =
      v.preparedMatrix R B (fun i ↦ EuclideanSpace.vecKron
        (EuclideanSpace.single (a i).1 1) (EuclideanSpace.single (a i).2 1)) X k j := by
  rw [preparedMatrix, op_prepareSlots, slotVector_single, mul_apply,
    ← (slotColumnEquiv R B X).symm.sum_comp, Fintype.sum_prod_type]
  simp only [prepMatrix_apply, Equiv.apply_symm_apply, PiLp.single_apply, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_eq_single a (fun b _ hb ↦ by simp [hb]) (by simp),
    Finset.sum_eq_single j (fun b _ hb ↦ by simp [hb]) (by simp)]
  simp [freeSourceMatrix]

/-- The complete matrix is a contraction on arbitrary joint source/input vectors.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–427. -/
theorem norm_freeSourceMatrix_le_one (v : Word (slotSystem R B X) Y) (hv : v.IsAllowed) :
    ‖v.freeSourceMatrix R B X‖ ≤ 1 :=
  (l2_opNorm_submatrix_le_of_injective _ Function.injective_id
    (slotColumnEquiv R B X).symm.injective).trans (PartyCircuit.norm_op_le_one _ hv)

section BraKet

variable (R' : SourceInventory P) (B' : SlotBases R'.length) (X' : P → Type)
  [∀ p, Fintype (X' p)] [∀ p, DecidableEq (X' p)]

/-- The overlap of the complete bra and ket operators has exactly the overlaps
of the prepared coefficient operators as its blocks. The bra source assignment
is the row index. Their source and physical input systems may differ.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–468. -/
theorem freeSourceMatrix_conjTranspose_mul_apply (v : Word (slotSystem R B X) Y)
    (v' : Word (slotSystem R' B' X') Y)
    (a : ∀ i, B.left i × B.right i) (b : ∀ i, B'.left i × B'.right i) (i : Config X)
    (j : Config X') :
    ((v'.freeSourceMatrix R' B' X')ᴴ * v.freeSourceMatrix R B X) (b, j) (a, i) =
      ((v'.preparedMatrix R' B' (fun e ↦ EuclideanSpace.vecKron
          (EuclideanSpace.single (b e).1 1) (EuclideanSpace.single (b e).2 1)) X')ᴴ *
        v.preparedMatrix R B (fun e ↦ EuclideanSpace.vecKron
          (EuclideanSpace.single (a e).1 1) (EuclideanSpace.single (a e).2 1)) X) j i := by
  simp only [mul_apply, conjTranspose_apply, freeSourceMatrix_apply]

/-- The actual bra-adjoint–ket product is a rectangular contraction, with no
factor depending on the number of source coordinates. Source: polynomial-PEPS
Theorem 5.2, `04-compression.tex`, lines 409–427. -/
theorem norm_freeSourceMatrix_conjTranspose_mul_le_one (v : Word (slotSystem R B X) Y)
    (v' : Word (slotSystem R' B' X') Y) (hv : v.IsAllowed) (hv' : v'.IsAllowed) :
    ‖(v'.freeSourceMatrix R' B' X')ᴴ * v.freeSourceMatrix R B X‖ ≤ 1 := by
  classical
  refine l2_opNorm_mul_le_one _ _ ?_ (norm_freeSourceMatrix_le_one R B X v hv)
  rw [l2_opNorm_conjTranspose]
  exact norm_freeSourceMatrix_le_one R' B' X' v' hv'

/-- A rectangular input coefficient pairs with the opposite-index block of the
actual bra-adjoint–ket operator after the common output is traced out.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–468. -/
theorem trace_preparedMatrix_mul_conjTranspose_eq (v : Word (slotSystem R B X) Y)
    (v' : Word (slotSystem R' B' X') Y) (ρ : Matrix (Config X) (Config X') ℂ)
    (a : ∀ i, B.left i × B.right i) (b : ∀ i, B'.left i × B'.right i) :
    trace
      (v.preparedMatrix R B (fun e ↦ EuclideanSpace.vecKron
          (EuclideanSpace.single (a e).1 1) (EuclideanSpace.single (a e).2 1)) X * ρ *
        (v'.preparedMatrix R' B' (fun e ↦ EuclideanSpace.vecKron
          (EuclideanSpace.single (b e).1 1) (EuclideanSpace.single (b e).2 1)) X')ᴴ) =
      ∑ i, ∑ j, ρ i j *
        ((v'.freeSourceMatrix R' B' X')ᴴ * v.freeSourceMatrix R B X) (b, j) (a, i) := by
  rw [trace_mul_cycle, trace_mul_comm]
  simp only [freeSourceMatrix_conjTranspose_mul_apply]
  rfl

end BraKet

/-- Tracing an actual density coefficient pairs the input matrix with the
corresponding block of the complete bra-adjoint–ket contraction. The input
matrix need not be Hermitian or positive. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 409–468. -/
theorem trace_preparedDensityCoefficient_eq_freeSourceMatrix (v v' : Word (slotSystem R B X) Y)
    (ρ : Matrix (Config X) (Config X) ℂ) (a b : ∀ i, B.left i × B.right i) :
    trace (v.preparedDensityCoefficient R B X (fun _ a ↦ EuclideanSpace.single a 1)
        (fun _ a ↦ EuclideanSpace.single a 1) (fun _ a ↦ EuclideanSpace.single a 1)
        (fun _ a ↦ EuclideanSpace.single a 1) v' ρ a b) =
      ∑ i, ∑ j, ρ i j *
        ((v'.freeSourceMatrix R B X)ᴴ * v.freeSourceMatrix R B X) (b, j) (a, i) :=
  trace_preparedMatrix_mul_conjTranspose_eq R B X R B X v v' ρ a b

end QuantumCircuit.Party.Word
