import TNLean.MPS.Chain.OneSidedInverse

/-!
# Physical realization map for virtual insertions

For an injective MPS tensor `A : Fin d → M_D(ℂ)`, a virtual insertion `X` on a bond
can be re-expressed as a physical operation on the local physical index.
This file defines the corresponding realization maps using the decomposition map
constructed in `OneSidedInverse`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- The physical realization of a right virtual insertion.
For injective `A`, `physRealize A hA X` is the `d × d` matrix of coefficients
that rewrites each `A i * X` in the spanning family `{A j}`. -/
noncomputable def physRealize (A : MPSTensor d D) (hA : IsInjective A)
    (X : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => decompositionMap (A := A) hA (A i * X) j

/-- Defining property of `physRealize`: each right-inserted matrix decomposes
in the span of `{A j}` with coefficients read from `physRealize`. -/
theorem physRealize_spec (A : MPSTensor d D) (hA : IsInjective A)
    (X : Matrix (Fin D) (Fin D) ℂ) (i : Fin d) :
    A i * X = ∑ j, (physRealize A hA X) i j • A j := by
  simpa [physRealize] using
    (decompositionMap_sum (A := A) hA (A i * X)).symm

/-- Left-bond analogue of `physRealize`:
`physRealizeRight A hA X` records coefficients that rewrite each `X * A i`. -/
noncomputable def physRealizeRight (A : MPSTensor d D) (hA : IsInjective A)
    (X : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => decompositionMap (A := A) hA (X * A i) j

/-- Defining property for the left-bond realization map. -/
theorem physRealizeRight_spec (A : MPSTensor d D) (hA : IsInjective A)
    (X : Matrix (Fin D) (Fin D) ℂ) (i : Fin d) :
    X * A i = ∑ j, (physRealizeRight A hA X) i j • A j := by
  simpa [physRealizeRight] using
    (decompositionMap_sum (A := A) hA (X * A i)).symm

/-- Three-site coefficient with a virtual insertion `X` between the first and
second local tensors. -/
def virtualInsertCoeff (A₁ A₂ A₃ : MPSTensor d D)
    (σ : Fin 3 → Fin d) (X : Matrix (Fin D) (Fin D) ℂ) : ℂ :=
  Matrix.trace (A₁ (σ 0) * X * A₂ (σ 1) * A₃ (σ 2))

@[simp] lemma virtualInsertCoeff_eq (A₁ A₂ A₃ : MPSTensor d D)
    (σ : Fin 3 → Fin d) (X : Matrix (Fin D) (Fin D) ℂ) :
    virtualInsertCoeff A₁ A₂ A₃ σ X =
      Matrix.trace (A₁ (σ 0) * X * A₂ (σ 1) * A₃ (σ 2)) := rfl

end MPSTensor
