import TNLean.PEPS.Approximation.SourceBlockMatrix

/-!
# Free-source block regressions

The first example fixes a rectangular input with a nonreal coefficient, retaining
independent ket and bra endpoint indices. The second checks that an empty list of
sources leaves exactly the physical identity matrix.
-/

noncomputable section
open scoped TensorProduct Matrix ComplexConjugate

namespace TNLean.PEPS.PairEffect.SourceBlockRegression

/-- An imaginary rectangular matrix unit pairs with the bra-row, ket-column block
without conjugating the input coefficient. -/
theorem rectangular_imaginary_input {P m : Type} [Fintype m]
    (R R' : SourceInventory P) (U V : Fin R.length → HSpace)
    (U' V' : Fin R'.length → HSpace)
    {A B : Fin R.length → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    {A' B' : Fin R'.length → Type} [∀ i, Fintype (A' i)] [∀ i, Fintype (B' i)]
    (bU : ∀ i, OrthonormalBasis (A i) ℂ (U i))
    (bV : ∀ i, OrthonormalBasis (B i) ℂ (V i))
    (bU' : ∀ i, OrthonormalBasis (A' i) ℂ (U' i))
    (bV' : ∀ i, OrthonormalBasis (B' i) ℂ (V' i))
    (ℓ ℓb ℓ' : Layout P)
    (v : Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ')
    (v' : Word (SourceInventory.slotLayout R' U' V' ++ ℓb) ℓ')
    (bIn : OrthonormalBasis (Fin 2) ℂ (Mem ℓ))
    (bBra : OrthonormalBasis (Fin 3) ℂ (Mem ℓb))
    (bOut : OrthonormalBasis m ℂ (Mem ℓ'))
    (a : ∀ i, A i × B i) (b : ∀ i, A' i × B' i) :
    Matrix.trace
      (v.preparedMatrix R U V (fun e ↦ bU e (a e).1 ⊗ₜ bV e (a e).2) ℓ bIn bOut *
        Matrix.single (0 : Fin 2) (2 : Fin 3) Complex.I *
        (v'.preparedMatrix R' U' V' (fun e ↦ bU' e (b e).1 ⊗ₜ bV' e (b e).2)
          ℓb bBra bOut)ᴴ) =
      Complex.I *
        ((v'.freeSourceMatrix R' U' V' bU' bV' ℓb bBra bOut)ᴴ *
          v.freeSourceMatrix R U V bU bV ℓ bIn bOut) (b, 2) (a, 0) := by
  classical
  rw [Word.trace_preparedMatrix_mul_conjTranspose_eq]
  simp [Matrix.single_apply]

abbrev inputLayout : Layout Bool := [⟨false, HSpace.of (EuclideanSpace ℂ (Fin 2))⟩]
abbrev inputBasis : OrthonormalBasis (Fin 2 × Unit) ℂ (Mem inputLayout) :=
  (EuclideanSpace.basisFun (Fin 2) ℂ).tensorProduct (OrthonormalBasis.singleton Unit ℂ)
abbrev noHalfspaces : Fin ([] : SourceInventory Bool).length → HSpace := Fin.elim0
abbrev noBases (i : Fin ([] : SourceInventory Bool).length) :
    OrthonormalBasis Empty ℂ (noHalfspaces i) := Fin.elim0 i

/-- The sole empty source assignment contributes no extra coordinate or scalar. -/
theorem empty_sources_identity
    (a : ∀ _i : Fin ([] : SourceInventory Bool).length, Empty × Empty)
    (j k : Fin 2 × Unit) :
    (Word.id inputLayout).freeSourceMatrix [] noHalfspaces noHalfspaces
      noBases noBases inputLayout inputBasis inputBasis k (a, j) =
        if k = j then 1 else 0 := by
  classical
  have h := Word.freeSourceMatrix_apply [] noHalfspaces noHalfspaces noBases noBases
    inputLayout (Word.id inputLayout) inputBasis inputBasis a j k
  apply h.trans
  change inputBasis.repr (inputBasis j) k = _
  simp

end TNLean.PEPS.PairEffect.SourceBlockRegression
