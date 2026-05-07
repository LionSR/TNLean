import TNLean.MPS.Chain.FundamentalTheorem

/-!
# Translation-invariance corollaries for injective MPS chains

For constant (translation-invariant) chains `(A, …, A)` and `(B, …, B)`,
the chain fundamental theorem reduces to a single matrix gauge:
`B^i = X · A^i · X⁻¹` with `λ = 1`.
-/

open scoped Matrix

namespace MPSChainTensor

variable {d D n : ℕ}

/-- **Single gauge for translation-invariant chains**.

If `A` is injective and the constant chains `(A, …, A)` and `(B, …, B)`
satisfy `SameMPV` on their combined tensors, there exists
`X ∈ GL(D, ℂ)` with `B^i = X · A^i · X⁻¹` for all `i`. -/
theorem ti_tensors_single_gauge
    (A B : MPSTensor d D)
    (hn : 0 < n)
    (hA : MPSTensor.IsInjective A)
    (hMPV : MPSTensor.SameMPV
      (MPSTensor.chainCombinedTensor (fun _ : Fin n => A))
      (MPSTensor.chainCombinedTensor (fun _ : Fin n => B))) :
    ∃ X : GL (Fin D) ℂ, ∀ i : Fin d,
      B i = (X : Matrix _ _ ℂ) * A i * ((X⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) := by
  let k0 : Fin n := ⟨0, hn⟩
  have hCombinedInj :
      MPSTensor.IsInjective (MPSTensor.chainCombinedTensor (fun _ : Fin n => A)) :=
    MPSTensor.chainCombinedTensor_isInjective (A := fun _ : Fin n => A) k0 hA
  obtain ⟨X, hX⟩ :=
    MPSTensor.fundamentalTheorem_singleBlock hCombinedInj hMPV
  refine ⟨X, ?_⟩
  intro i
  simpa [MPSTensor.chainCombinedTensor_apply] using hX (finProdFinEquiv (k0, i))

/-- **Translation-invariant collapse to a single gauge**.

If `A` is injective and the constant chains `(A, …, A)` and `(B, …, B)`
satisfy `SameMPV` on their combined tensors, there exist
a matrix `Z` with `IsUnit Z` and a scalar `λ : ℂ` with `λ^n = 1` such that
`B^i = λ • (Z⁻¹ * A^i * Z)` for all `i`. The proof yields `λ = 1`. -/
theorem ti_tensors_collapse_to_single_gauge
    (A B : MPSTensor d D)
    (hn : 0 < n)
    (hA : MPSTensor.IsInjective A)
    (hMPV : MPSTensor.SameMPV
      (MPSTensor.chainCombinedTensor (fun _ : Fin n => A))
      (MPSTensor.chainCombinedTensor (fun _ : Fin n => B))) :
    ∃ Z : Matrix (Fin D) (Fin D) ℂ, ∃ lam : ℂ,
      IsUnit Z ∧ lam ^ n = 1 ∧
      ∀ i : Fin d, B i = lam • (Z⁻¹ * A i * Z) := by
  obtain ⟨X, hX⟩ := ti_tensors_single_gauge A B hn hA hMPV
  refine ⟨((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ), 1, ?_, ?_, ?_⟩
  · exact (X⁻¹).isUnit
  · simp
  · intro i
    have hXi : B i =
        (X : Matrix (Fin D) (Fin D) ℂ) * A i *
          (((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := hX i
    simpa [smul_eq_mul, Matrix.mul_assoc] using hXi

end MPSChainTensor
