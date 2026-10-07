import TNLean.PEPS.Approximation.PreparedMatrixNorm
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-! Density checks with a nonreal bra phase, proper source subspaces, and no source slots. -/

noncomputable section
open scoped TensorProduct ComplexConjugate Matrix
namespace TNLean.PEPS.PairEffect.DensityRegression

abbrev InputIndex := Fin 2 × Unit
abbrev OutputIndex := Fin 3 × (Fin 3 × InputIndex)

abbrev inputLayout : Layout Bool := [⟨false, euc (Fin 2)⟩]
abbrev inputBasis : OrthonormalBasis InputIndex ℂ (Mem inputLayout) :=
  (EuclideanSpace.basisFun (Fin 2) ℂ).tensorProduct (OrthonormalBasis.singleton Unit ℂ)

abbrev reference : SourceInventory Bool := [PairSource.unit false true (by decide)]
abbrev halfspaces : Fin reference.length → HSpace := fun _ ↦ euc (Fin 3)
abbrev sourceLayout : Layout Bool := SourceInventory.slotLayout reference halfspaces halfspaces

abbrev outputBasis : OrthonormalBasis OutputIndex ℂ (Mem (sourceLayout ++ inputLayout)) :=
  (EuclideanSpace.basisFun (Fin 3) ℂ).tensorProduct
    ((EuclideanSpace.basisFun (Fin 3) ℂ).tensorProduct inputBasis)

abbrev sourceWord : Word (sourceLayout ++ inputLayout) (sourceLayout ++ inputLayout) := .id _

abbrev basisVector (i : Fin 3) : euc (Fin 3) := EuclideanSpace.single i 1

abbrev ketFamily (_ : Fin reference.length) (_ : Unit) : euc (Fin 3) := basisVector 0
abbrev braFamily (_ : Fin reference.length) (a : Bool) : euc (Fin 3) :=
  basisVector (if a then 1 else 0)

abbrev ketCoefficient (_ : Fin reference.length) (_ : Unit × Unit) : ℂ := 1
abbrev braCoefficient (_ : Fin reference.length) (a : Bool × Unit) : ℂ :=
  if a.1 then 0 else Complex.I

abbrev inputMatrix : Matrix InputIndex InputIndex ℂ := Matrix.single (0, ()) (1, ()) 1

/-- This input has a nonzero upper off-diagonal entry and zero transposed entry. -/
theorem inputMatrix_not_isHermitian : ¬ inputMatrix.IsHermitian := by
  intro h
  have hentry := congrArg (fun M : Matrix InputIndex InputIndex ℂ ↦ M (0, ()) (1, ())) h
  norm_num [inputMatrix, Matrix.conjTranspose_apply, Matrix.single] at hentry

private theorem sum_one_slot {I T E : Type} [Unique I] [DecidableEq I] [Fintype I]
    [Fintype T] [AddCommMonoid E] (f : (I → T) → E) : ∑ a, f a = ∑ t, f (fun _ ↦ t) := by
  apply Fintype.sum_equiv (Equiv.funUnique I T)
  intro a
  congr 1
  funext i
  exact congrArg a (Subsingleton.elim i default)

/-- A bra coefficient I appears as -I, with unequal proper endpoint families. -/
theorem proper_families_bra_phase (ρ : Matrix InputIndex InputIndex ℂ) :
    sourceWord.preparedMatrix reference halfspaces halfspaces
        (fun _ ↦ basisVector 0 ⊗ₜ[ℂ] basisVector 0) inputLayout inputBasis outputBasis * ρ *
      (sourceWord.preparedMatrix reference halfspaces halfspaces
        (fun _ ↦ Complex.I • (basisVector 0 ⊗ₜ[ℂ] basisVector 0))
        inputLayout inputBasis outputBasis)ᴴ =
      (-Complex.I) •
        (sourceWord.preparedMatrix reference halfspaces halfspaces
          (fun _ ↦ basisVector 0 ⊗ₜ[ℂ] basisVector 0) inputLayout inputBasis outputBasis * ρ *
          (sourceWord.preparedMatrix reference halfspaces halfspaces
            (fun _ ↦ basisVector 0 ⊗ₜ[ℂ] basisVector 0)
            inputLayout inputBasis outputBasis)ᴴ) := by
  let : Unique (Fin reference.length) := inferInstanceAs (Unique (Fin 1))
  let : DecidableEq (Fin reference.length) := instDecidableEqFin _
  have h := sourceWord.preparedMatrix_density_sum_smul reference halfspaces halfspaces
    ketFamily ketFamily braFamily ketFamily ketCoefficient braCoefficient
    inputLayout sourceWord inputBasis outputBasis ρ
  simp [Fintype.sum_prod_type, ketCoefficient, braCoefficient,
    ketFamily, braFamily, Word.preparedDensityCoefficient] at h
  refine h.trans ((sum_one_slot (I := Fin reference.length) (T := Bool × Unit) _).trans ?_)
  simp [Fintype.sum_prod_type]

/-- Both endpoint families lie in the proper coordinate hyperplane with coordinate 2 zero. -/
theorem endpoint_families_in_proper_hyperplane :
    (∀ a : Unit, ketFamily 0 a (2 : Fin 3) = 0) ∧
      (∀ a : Bool, braFamily 0 a (2 : Fin 3) = 0) ∧ basisVector 2 (2 : Fin 3) = 1 := by
  constructor
  · intro a
    simp [ketFamily, basisVector]
  constructor
  · intro a
    cases a <;> simp [braFamily, basisVector]
  · simp [basisVector]

abbrev noHalfspaces : Fin ([] : SourceInventory Bool).length → HSpace := Fin.elim0
abbrev noVectors : ∀ i, noHalfspaces i ⊗[ℂ] noHalfspaces i := fun i ↦ Fin.elim0 i
abbrev noBases (_ : Bool) (i : Fin ([] : SourceInventory Bool).length) :
    OrthonormalBasis Empty ℂ (noHalfspaces i) := Fin.elim0 i
abbrev gateCoefficient (a : Bool) : ℂ := if a then Complex.I else 1

private theorem empty_preparedMatrix (η : ∀ i, noHalfspaces i ⊗[ℂ] noHalfspaces i) :
    (Word.id inputLayout).preparedMatrix [] noHalfspaces noHalfspaces η
      inputLayout inputBasis inputBasis = (1 : Matrix InputIndex InputIndex ℂ) := by
  classical
  ext i j
  change inputBasis.repr (inputBasis j) i = _
  simp [Matrix.one_apply]

theorem zero_slots_weighted_gate (ρ : Matrix InputIndex InputIndex ℂ) :
    (∑ a : Bool, gateCoefficient a •
      (Word.id inputLayout).preparedMatrix [] noHalfspaces noHalfspaces noVectors
        inputLayout inputBasis inputBasis) * ρ *
      (∑ a : Bool, gateCoefficient a •
        (Word.id inputLayout).preparedMatrix [] noHalfspaces noHalfspaces noVectors
          inputLayout inputBasis inputBasis)ᴴ = (2 : ℂ) • ρ := by
  have h := Word.preparedMatrix_gate_density_eq_sum_basis [] noHalfspaces noHalfspaces
    noBases noBases gateCoefficient (fun _ ↦ noVectors) inputLayout
    (fun _ ↦ Word.id inputLayout) inputBasis inputBasis ρ
  apply h.trans
  simp only [Fintype.univ_bool, gateCoefficient, ite_mul, one_mul, List.length_nil,
    Finset.univ_unique, Finset.univ_eq_empty, Finset.prod_empty,
    Word.preparedDensityCoefficient, one_smul, Finset.sum_singleton, ite_smul,
    Finset.sum_ite_irrel, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
    Finset.sum_insert, ↓reduceIte, Complex.conj_I, mul_neg, Complex.I_mul_I,
    neg_neg, Bool.false_eq_true, map_one, mul_one, neg_smul, add_add_neg_add_cancel]
  rw [empty_preparedMatrix]
  simp [two_smul]

end TNLean.PEPS.PairEffect.DensityRegression
