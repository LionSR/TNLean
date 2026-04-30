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
    A i * X = ∑ j, (physRealize A hA X) i j • A j :=
  set_option linter.unnecessarySimpa false in
  by
    simpa [physRealize] using
      (decompositionMap_sum (A := A) hA (A i * X)).symm

/-- Left-bond analogue of `physRealize`:
`physRealizeLeft A hA X` captures coefficients that rewrite each `X * A i`. -/
noncomputable def physRealizeLeft (A : MPSTensor d D) (hA : IsInjective A)
    (X : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => decompositionMap (A := A) hA (X * A i) j

/-- Defining property for the left-bond realization map. -/
theorem physRealizeLeft_spec (A : MPSTensor d D) (hA : IsInjective A)
    (X : Matrix (Fin D) (Fin D) ℂ) (i : Fin d) :
    X * A i = ∑ j, (physRealizeLeft A hA X) i j • A j :=
  set_option linter.unnecessarySimpa false in
  by
    simpa [physRealizeLeft] using
      (decompositionMap_sum (A := A) hA (X * A i)).symm

/-- `physRealize` is linear in the inserted matrix. -/
theorem physRealize_linear (A : MPSTensor d D) (hA : IsInjective A) :
    ∀ (c : ℂ) (X Y : Matrix (Fin D) (Fin D) ℂ),
      physRealize A hA (c • X + Y) = c • physRealize A hA X + physRealize A hA Y := by
  intro c X Y
  ext i j
  simp [physRealize, mul_add]

/-- Identity insertion does nothing. -/
theorem physRealize_one (A : MPSTensor d D) (hA : IsInjective A)
    (hLin : LinearIndependent ℂ A) :
    physRealize A hA 1 = 1 := by
  ext i j
  let c : Fin d → ℂ := fun k => physRealize A hA 1 i k
  have hc : Fintype.linearCombination ℂ A c = A i := by
    simpa [c, Fintype.linearCombination_apply] using (physRealize_spec A hA 1 i).symm
  have hsingle : Fintype.linearCombination ℂ A (Pi.single i (1 : ℂ)) = A i := by
    simp [Fintype.linearCombination_apply_single]
  have hc' : c = Pi.single i (1 : ℂ) :=
    hLin.fintypeLinearCombination_injective (hc.trans hsingle.symm)
  simpa [c, Matrix.one_apply, Pi.single_apply, eq_comm] using congrArg (fun f => f j) hc'

/-- `physRealize` preserves multiplication. -/
theorem physRealize_mul (A : MPSTensor d D) (hA : IsInjective A)
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    physRealize A hA (X * Y) = physRealize A hA X * physRealize A hA Y := by
  ext i k
  change decompositionMap (A := A) hA (A i * (X * Y)) k =
    (physRealize A hA X * physRealize A hA Y) i k
  have hdecomp :
      decompositionMap (A := A) hA (A i * (X * Y))
        = ∑ j, (physRealize A hA X) i j • decompositionMap (A := A) hA (A j * Y) := by
    calc
      decompositionMap (A := A) hA (A i * (X * Y))
          = decompositionMap (A := A) hA ((A i * X) * Y) := by
              simp [Matrix.mul_assoc]
      _ = decompositionMap (A := A) hA ((∑ j, (physRealize A hA X) i j • A j) * Y) := by
            rw [← physRealize_spec A hA X i]
      _ = decompositionMap (A := A) hA (∑ j, (physRealize A hA X) i j • (A j * Y)) := by
            simp [Finset.sum_mul]
      _ = ∑ j, (physRealize A hA X) i j • decompositionMap (A := A) hA (A j * Y) := by
            simp
  calc
    decompositionMap (A := A) hA (A i * (X * Y)) k
        = (∑ j, (physRealize A hA X) i j • decompositionMap (A := A) hA (A j * Y)) k := by
            simpa using congrArg (fun f => f k) hdecomp
    _ = ∑ j, (physRealize A hA X) i j * (decompositionMap (A := A) hA (A j * Y)) k := by
          simp
    _ = ∑ j, (physRealize A hA X) i j * (physRealize A hA Y) j k := by
          simp [physRealize]
    _ = (physRealize A hA X * physRealize A hA Y) i k := by
          simp [Matrix.mul_apply]

/-- Nonzero insertion gives nonzero physical operation. -/
theorem physRealize_injective (A : MPSTensor d D) (hA : IsInjective A)
    (X : Matrix (Fin D) (Fin D) ℂ) (hX : X ≠ 0) :
    physRealize A hA X ≠ 0 := by
  intro hZero
  have hAll : ∀ i : Fin d, A i * X = 0 := by
    intro i
    rw [physRealize_spec A hA X i, hZero]
    simp
  obtain ⟨c, hc⟩ := hA.exists_decomposition (1 : Matrix (Fin D) (Fin D) ℂ)
  have hX0 : X = 0 := by
    calc
      X = (1 : Matrix (Fin D) (Fin D) ℂ) * X := by simp
      _ = (∑ i, c i • A i) * X := by simp [hc]
      _ = ∑ i, c i • (A i * X) := by simp [Finset.sum_mul]
      _ = 0 := by simp [hAll]
  exact hX hX0

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
