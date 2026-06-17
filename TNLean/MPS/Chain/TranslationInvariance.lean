import TNLean.MPS.Chain.FundamentalTheorem

/-!
# Translation-invariance corollaries for injective MPS chains

For constant (translation-invariant) chains `(A, …, A)` and `(B, …, B)`,
the chain fundamental theorem reduces to a single matrix gauge:
$B^i = X A^i X^{-1}$ with `λ = 1`.
-/

open scoped Matrix

namespace MPSChainTensor

variable {d D n : ℕ}

/-! ### Telescoping a chain against its cyclic shift -/

/-- **Telescoping a cyclic-shift gauge comparison**
(arXiv:1804.04964, Applications section, lines 1828--1862).

If a site-dependent closed chain is gauge equivalent to its cyclic shift, then
each site tensor is obtained from the first tensor by invertible matrices on
the two virtual legs.  This is the formal version of the source passage
expressing all tensors \(A_i\) in terms of \(A_1\) and the products \(L_i\),
\(R_i\). -/
theorem exists_gauge_to_first_of_cyclicShift_gaugeEquiv [NeZero n]
    {A : MPSChainTensor d D n} (hA : GaugeEquiv A (cyclicShift A)) :
    ∀ k : Fin n, ∃ L R : GL (Fin D) ℂ, ∀ i : Fin d,
      A k i = (L : Matrix (Fin D) (Fin D) ℂ) * A 0 i *
        (((R⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
  obtain ⟨Z, hZ⟩ := hA
  intro k
  induction hk : k.val generalizing k with
  | zero =>
      refine ⟨1, 1, ?_⟩
      intro i
      have hk0 : k = 0 := Fin.ext (by simpa using hk)
      subst k
      simp
  | succ m ih =>
      have hm : m < n := by
        have hklt := k.isLt
        omega
      let j : Fin n := ⟨m, hm⟩
      have hsucc : cyclicSucc j = k := by
        rw [cyclicSucc_eq_add_one]
        apply Fin.ext
        have hn2 : 2 ≤ n := by
          have hklt := k.isLt
          omega
        have hone : ((1 : Fin n).val) = 1 := by
          have h := Fin.val_one' n
          rw [h]
          exact Nat.mod_eq_of_lt (by omega)
        rw [Fin.val_add_eq_ite, hone]
        change (if n ≤ m + 1 then m + 1 - n else m + 1) = k.val
        rw [hk]
        split_ifs <;> omega
      obtain ⟨L, R, hLR⟩ := ih j rfl
      refine ⟨Z j * L, Z k * R, ?_⟩
      intro i
      have hZj := hZ j i
      change A (cyclicSucc j) i =
        (Z j : Matrix (Fin D) (Fin D) ℂ) * A j i *
          (((Z (cyclicSucc j))⁻¹ : GL (Fin D) ℂ) :
            Matrix (Fin D) (Fin D) ℂ) at hZj
      rw [← hsucc, hZj, hLR i, hsucc]
      simp [Matrix.mul_assoc, mul_inv_rev]

/-- **Single gauge for translation-invariant chains**.

If `A` is injective and the constant chains `(A, …, A)` and `(B, …, B)`
satisfy `SameMPV` on their combined tensors, there exists
`X ∈ GL(D, ℂ)` with $B^i = X A^i X^{-1}$ for all `i`. -/
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
