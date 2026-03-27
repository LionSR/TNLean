import TNLean.MPS.Chain.FundamentalTheorem

/-!
# Translation-invariance corollaries for injective MPS chains

This file packages the translation-invariant specialization of the chain
fundamental theorem as a corollary.

Because `fundamentalTheorem_injective_chain` currently yields a uniform gauge,
the translation-invariant collapse can be witnessed with scalar `λ = 1`.
The periodicity statement then follows immediately as `1 ^ n = 1`.
-/

open scoped Matrix

namespace MPSChainTensor

variable {d D n : ℕ}

/-- For translation-invariant chains `A` and `B` (constant tensors at every site),
`SameMPV` on the combined tensors yields a single matrix gauge relating the site
tensors. -/
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

/-- Corollary 1 (TI collapse to a single gauge).

For translation-invariant chains `A` and `B` (constant tensors at every site),
a chain-level fundamental-theorem hypothesis yields a single matrix gauge and a
phase `λ` with `lam ^ n = 1` such that
`B i = lam • (Z⁻¹ * A i * Z)` for all physical indices `i`.

In the current formalization this is realized by `λ = 1`. -/
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
