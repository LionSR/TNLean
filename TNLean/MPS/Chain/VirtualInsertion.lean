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
`physRealizeLeft A hA X` records coefficients that rewrite each `X * A i`. -/
noncomputable def physRealizeLeft (A : MPSTensor d D) (hA : IsInjective A)
    (X : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => decompositionMap (A := A) hA (X * A i) j

/-- Defining property for the left-bond realization map. -/
theorem physRealizeLeft_spec (A : MPSTensor d D) (hA : IsInjective A)
    (X : Matrix (Fin D) (Fin D) ℂ) (i : Fin d) :
    X * A i = ∑ j, (physRealizeLeft A hA X) i j • A j := by
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
    simpa using (Fintype.linearCombination_apply_single (R := ℂ) (v := A) i (1 : ℂ))
  have hc' : c = Pi.single i (1 : ℂ) :=
    hLin.fintypeLinearCombination_injective (hc.trans hsingle.symm)
  simpa [c, Matrix.one_apply, Pi.single_apply, eq_comm] using congrArg (fun f => f j) hc'

/-- `physRealize` preserves multiplication. -/
theorem physRealize_mul (A : MPSTensor d D) (hA : IsInjective A)
    (hLin : LinearIndependent ℂ A)
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    physRealize A hA (X * Y) = physRealize A hA X * physRealize A hA Y := by
  ext i k
  let cXY : Fin d → ℂ := fun k' => physRealize A hA (X * Y) i k'
  let cProd : Fin d → ℂ := fun k' => (physRealize A hA X * physRealize A hA Y) i k'
  have hcXY : Fintype.linearCombination ℂ A cXY = A i * (X * Y) := by
    simpa [cXY, Fintype.linearCombination_apply] using (physRealize_spec A hA (X * Y) i).symm
  have hcProd : Fintype.linearCombination ℂ A cProd = A i * (X * Y) := by
    calc
      Fintype.linearCombination ℂ A cProd
          = ∑ k', cProd k' • A k' := by simp [Fintype.linearCombination_apply]
      _ = ∑ k', (∑ j, (physRealize A hA X) i j * (physRealize A hA Y) j k') • A k' := by
            simp [cProd, Matrix.mul_apply]
      _ = ∑ k', ∑ j, ((physRealize A hA X) i j * (physRealize A hA Y) j k') • A k' := by
            simp [Finset.sum_smul]
      _ = ∑ j, ∑ k', ((physRealize A hA X) i j * (physRealize A hA Y) j k') • A k' := by
            rw [Finset.sum_comm]
      _ = ∑ j, (physRealize A hA X) i j • (∑ k', (physRealize A hA Y) j k' • A k') := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [Finset.smul_sum, mul_smul, smul_assoc]
      _ = ∑ j, (physRealize A hA X) i j • (A j * Y) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simpa using congrArg (fun M => (physRealize A hA X) i j • M) (physRealize_spec A hA Y j).symm
      _ = (∑ j, (physRealize A hA X) i j • A j) * Y := by
            simp [Finset.sum_mul]
      _ = (A i * X) * Y := by simpa using congrArg (fun M => M * Y) (physRealize_spec A hA X i).symm
      _ = A i * (X * Y) := by simp [Matrix.mul_assoc]
  have hcoeff : cXY = cProd :=
    hLin.fintypeLinearCombination_injective (hcXY.trans hcProd.symm)
  simpa [cXY, cProd] using congrArg (fun f => f k) hcoeff

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
      _ = (∑ i, c i • A i) * X := by simpa [hc]
      _ = ∑ i, c i • (A i * X) := by simp [Finset.sum_mul, smul_mul_assoc]
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
