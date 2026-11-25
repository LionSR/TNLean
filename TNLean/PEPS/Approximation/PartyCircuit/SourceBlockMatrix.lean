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
superpositions of source and physical inputs. The input and output memories carry arbitrary
coordinates `E` and `F`, matrices whose columns are the coordinate vectors (for instance the
vectors of orthonormal bases), and the bound holds when they have norm at most one. Other
coordinates of the source slots are obtained by composing the word with the local maps of the
slots (`Word.sourceFrameMatrix`).

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 383–468, in particular the free-input contractions
used to separate the corrected source coefficients.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

noncomputable section

open scoped ComplexConjugate Matrix Kronecker Matrix.Norms.L2Operator
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

omit [∀ p, Fintype (Y p)] in
/-- The column of the matrix of the word at a source assignment and an input configuration is
the column of the branch prepared with the corresponding endpoint basis vectors. -/
private theorem op_submatrix_slotColumnEquiv_apply (v : Word (slotSystem R B X) Y)
    (a : ∀ i, B.left i × B.right i) (j : Config X) (k : Config Y) :
    v.op.submatrix id (slotColumnEquiv R B X).symm k (a, j) =
      v.preparedMatrix R B (fun i ↦ EuclideanSpace.vecKron
        (EuclideanSpace.single (a i).1 1) (EuclideanSpace.single (a i).2 1)) X k j := by
  rw [preparedMatrix, op_prepareSlots, slotVector_single, mul_apply,
    ← (slotColumnEquiv R B X).symm.sum_comp, Fintype.sum_prod_type]
  simp only [prepMatrix_apply, Equiv.apply_symm_apply, PiLp.single_apply, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_eq_single a (fun b _ hb ↦ by simp [hb]) (by simp),
    Finset.sum_eq_single j (fun b _ hb ↦ by simp [hb]) (by simp)]
  simp

/-- The matrix of the remaining word with every source coordinate and every physical input
coordinate free, in input coordinates `E` and output coordinates `F`: the columns of `E` and
`F` are the coordinate vectors, for instance the vectors of orthonormal bases. Source:
polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–427. -/
def freeSourceMatrix {m n : Type} (E : Matrix (Config X) n ℂ) (F : Matrix (Config Y) m ℂ)
    (v : Word (slotSystem R B X) Y) : Matrix m ((∀ i, B.left i × B.right i) × n) ℂ :=
  Fᴴ * v.op.submatrix id (slotColumnEquiv R B X).symm *
    ((1 : Matrix (∀ i, B.left i × B.right i) (∀ i, B.left i × B.right i) ℂ) ⊗ₖ E)

/-- A block of the full matrix is the actual branch prepared with the corresponding
endpoint basis vectors, in the same input and output coordinates. Source: polynomial-PEPS
Theorem 5.2, `04-compression.tex`, lines 409–427. -/
theorem freeSourceMatrix_apply {m n : Type} (E : Matrix (Config X) n ℂ)
    (F : Matrix (Config Y) m ℂ) (v : Word (slotSystem R B X) Y)
    (a : ∀ i, B.left i × B.right i) (j : n) (k : m) :
    v.freeSourceMatrix R B X E F k (a, j) =
      (Fᴴ * v.preparedMatrix R B (fun i ↦ EuclideanSpace.vecKron
        (EuclideanSpace.single (a i).1 1) (EuclideanSpace.single (a i).2 1)) X * E) k j := by
  simp only [freeSourceMatrix, mul_apply (M := Fᴴ * _), Fintype.sum_prod_type,
    kroneckerMap_apply, one_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_eq_single a (fun b _ hb ↦ by simp [hb]) (by simp)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [mul_apply, op_submatrix_slotColumnEquiv_apply, ↓reduceIte]

/-- The complete matrix is a contraction on arbitrary joint source/input vectors, in input
and output coordinates of norm at most one, for instance orthonormal bases.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–427. -/
theorem norm_freeSourceMatrix_le_one {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (E : Matrix (Config X) n ℂ) (F : Matrix (Config Y) m ℂ)
    (v : Word (slotSystem R B X) Y) (hv : v.IsAllowed) (hE : ‖E‖ ≤ 1) (hF : ‖F‖ ≤ 1) :
    ‖v.freeSourceMatrix R B X E F‖ ≤ 1 := by
  classical
  refine l2_opNorm_mul_le_one _ _ (l2_opNorm_mul_le_one _ _ ?_ ?_)
    ((l2_opNorm_one_kronecker_le E).trans hE)
  · rwa [l2_opNorm_conjTranspose]
  · exact (l2_opNorm_submatrix_le_of_injective _ Function.injective_id
      (slotColumnEquiv R B X).symm.injective).trans (PartyCircuit.norm_op_le_one _ hv)

section BraKet

variable (R' : SourceInventory P) (B' : SlotBases R'.length) (X' : P → Type)
  [∀ p, Fintype (X' p)] [∀ p, DecidableEq (X' p)]

/-- The overlap of the complete bra and ket operators has exactly the overlaps
of the prepared coefficient operators as its blocks. The bra source assignment
is the row index. Their source and physical input systems, and their input coordinates, may
differ; the output coordinates are shared.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–468. -/
theorem freeSourceMatrix_conjTranspose_mul_apply {m n n' : Type} [Fintype m]
    (E : Matrix (Config X) n ℂ) (E' : Matrix (Config X') n' ℂ) (F : Matrix (Config Y) m ℂ)
    (v : Word (slotSystem R B X) Y) (v' : Word (slotSystem R' B' X') Y)
    (a : ∀ i, B.left i × B.right i) (b : ∀ i, B'.left i × B'.right i) (i : n) (j : n') :
    ((v'.freeSourceMatrix R' B' X' E' F)ᴴ * v.freeSourceMatrix R B X E F) (b, j) (a, i) =
      ((Fᴴ * v'.preparedMatrix R' B' (fun e ↦ EuclideanSpace.vecKron
          (EuclideanSpace.single (b e).1 1) (EuclideanSpace.single (b e).2 1)) X' * E')ᴴ *
        (Fᴴ * v.preparedMatrix R B (fun e ↦ EuclideanSpace.vecKron
          (EuclideanSpace.single (a e).1 1) (EuclideanSpace.single (a e).2 1)) X * E)) j i := by
  simp only [mul_apply, conjTranspose_apply, freeSourceMatrix_apply]

/-- The actual bra-adjoint–ket product is a rectangular contraction, with no
factor depending on the number of source coordinates, in input and output coordinates of norm
at most one. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–427. -/
theorem norm_freeSourceMatrix_conjTranspose_mul_le_one {m n n' : Type} [Fintype m]
    [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (E : Matrix (Config X) n ℂ) (E' : Matrix (Config X') n' ℂ) (F : Matrix (Config Y) m ℂ)
    (v : Word (slotSystem R B X) Y) (v' : Word (slotSystem R' B' X') Y) (hv : v.IsAllowed)
    (hv' : v'.IsAllowed) (hE : ‖E‖ ≤ 1) (hE' : ‖E'‖ ≤ 1) (hF : ‖F‖ ≤ 1) :
    ‖(v'.freeSourceMatrix R' B' X' E' F)ᴴ * v.freeSourceMatrix R B X E F‖ ≤ 1 := by
  refine l2_opNorm_mul_le_one _ _ ?_ (norm_freeSourceMatrix_le_one R B X E F v hv hE hF)
  rw [l2_opNorm_conjTranspose]
  exact norm_freeSourceMatrix_le_one R' B' X' E' F v' hv' hE' hF

/-- A rectangular input coefficient pairs with the opposite-index block of the
actual bra-adjoint–ket operator after the common output is traced out; the prepared matrices
are taken in the input coordinates `E`, `E'` and the output coordinates `F`.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–468. -/
theorem trace_preparedMatrix_mul_conjTranspose_eq {m n n' : Type} [Fintype m] [Fintype n]
    [Fintype n'] (E : Matrix (Config X) n ℂ) (E' : Matrix (Config X') n' ℂ)
    (F : Matrix (Config Y) m ℂ) (v : Word (slotSystem R B X) Y)
    (v' : Word (slotSystem R' B' X') Y) (ρ : Matrix n n' ℂ)
    (a : ∀ i, B.left i × B.right i) (b : ∀ i, B'.left i × B'.right i) :
    trace
      (Fᴴ * v.preparedMatrix R B (fun e ↦ EuclideanSpace.vecKron
          (EuclideanSpace.single (a e).1 1) (EuclideanSpace.single (a e).2 1)) X * E * ρ *
        (Fᴴ * v'.preparedMatrix R' B' (fun e ↦ EuclideanSpace.vecKron
          (EuclideanSpace.single (b e).1 1) (EuclideanSpace.single (b e).2 1)) X' * E')ᴴ) =
      ∑ i, ∑ j, ρ i j *
        ((v'.freeSourceMatrix R' B' X' E' F)ᴴ * v.freeSourceMatrix R B X E F) (b, j) (a, i) := by
  rw [trace_mul_cycle, trace_mul_comm]
  simp only [freeSourceMatrix_conjTranspose_mul_apply]
  rfl

end BraKet

/-- Tracing an actual density coefficient pairs the input matrix with the
corresponding block of the complete bra-adjoint–ket contraction. In input coordinates `E` and
output coordinates `F`, the density coefficient of the input matrix `ρ` is
`Fᴴ * C(E * ρ * Eᴴ) * F`. The input matrix need not be Hermitian or positive. Source:
polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–468. -/
theorem trace_preparedDensityCoefficient_eq_freeSourceMatrix {m n : Type} [Fintype m]
    [Fintype n] (E : Matrix (Config X) n ℂ) (F : Matrix (Config Y) m ℂ)
    (v v' : Word (slotSystem R B X) Y) (ρ : Matrix n n ℂ) (a b : ∀ i, B.left i × B.right i) :
    trace (Fᴴ * v.preparedDensityCoefficient R B X (fun _ a ↦ EuclideanSpace.single a 1)
        (fun _ a ↦ EuclideanSpace.single a 1) (fun _ a ↦ EuclideanSpace.single a 1)
        (fun _ a ↦ EuclideanSpace.single a 1) v' (E * ρ * Eᴴ) a b * F) =
      ∑ i, ∑ j, ρ i j *
        ((v'.freeSourceMatrix R B X E F)ᴴ * v.freeSourceMatrix R B X E F) (b, j) (a, i) := by
  rw [← trace_preparedMatrix_mul_conjTranspose_eq R B X R B X E E F v v' ρ a b]
  simp only [preparedDensityCoefficient, conjTranspose_mul, conjTranspose_conjTranspose,
    Matrix.mul_assoc]

end QuantumCircuit.Party.Word
