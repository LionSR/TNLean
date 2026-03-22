import TNLean.MPS.Chain.OneSidedInverse
import TNLean.Algebra.TracePairing

/-!
# Tensor proportionality for injective 2-site MPS (Lemma 2)

**Lemma 2** of arXiv:1804.04964: if two pairs of injective tensors yield the same
amplitudes under all virtual insertions on both bonds of a 2-site chain, the tensors
must be proportional: `A₁ = λ • B₁` and `A₂ = λ⁻¹ • B₂` for some nonzero `λ`.

## Main results

* `MPSTensor.tensor_proportional` — the main proportionality theorem.

## Proof outline

1. From the trace conditions and trace nondegeneracy, derive the matrix product
   identities `A₂ j * A₁ i = B₂ j * B₁ i` and `A₁ i * A₂ j = B₁ i * B₂ j`.

2. Using the decomposition map, extract matrices `Z` and `W` such that
   `A₁ i = Z * B₁ i` and `A₂ j = W * B₂ j`.

3. Show that `Z * M * W = M` and `W * M * Z = M` for all `M` via spanning
   arguments, yielding `Z * W = 1` and `W * Z = 1`.

4. Conclude `Z * M = M * Z` for all `M`, so `Z` lies in the center of `M_D(ℂ)`,
   which equals `ℂ · I`. Hence `Z = λ • 1` for some scalar `λ`.

5. Injectivity forces `λ ≠ 0`, completing the proof.

## References

* [arXiv:1804.04964](https://arxiv.org/abs/1804.04964), Lemma 2
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ### Helpers -/

/-- If `M * A j = 0` for every generator of an injective tensor, then `M = 0`. -/
lemma eq_zero_of_mul_injective_right {A : MPSTensor d D} (hA : IsInjective A)
    {M : Matrix (Fin D) (Fin D) ℂ} (h : ∀ j, M * A j = 0) : M = 0 := by
  have : M * 1 = 0 := by
    obtain ⟨c, hc⟩ := hA.exists_decomposition 1
    rw [hc, Finset.mul_sum]
    simp only [mul_smul_comm, h, smul_zero, Finset.sum_const_zero]
  simpa using this

/-! ### Step 1: from trace conditions to product equalities -/

/-- Internal bond trace equality implies `A₂ j * A₁ i = B₂ j * B₁ i`. -/
theorem product_eq_of_internal_trace
    (A₁ A₂ B₁ B₂ : MPSTensor d D)
    (hInt : ∀ (X : Matrix (Fin D) (Fin D) ℂ) (i j : Fin d),
      Matrix.trace (A₁ i * X * A₂ j) = Matrix.trace (B₁ i * X * B₂ j)) :
    ∀ i j, A₂ j * A₁ i = B₂ j * B₁ i := by
  intro i j
  apply sub_eq_zero.mp
  apply trace_mul_right_eq_zero
  intro N
  have h := hInt N i j
  rw [Matrix.trace_mul_cycle (A₁ i) N (A₂ j),
      Matrix.trace_mul_cycle (B₁ i) N (B₂ j)] at h
  rw [sub_mul, sub_eq_zero]
  exact h

/-- External bond trace equality implies `A₁ i * A₂ j = B₁ i * B₂ j`. -/
theorem product_eq_of_external_trace
    (A₁ A₂ B₁ B₂ : MPSTensor d D)
    (hExt : ∀ (Y : Matrix (Fin D) (Fin D) ℂ) (i j : Fin d),
      Matrix.trace (A₂ j * Y * A₁ i) = Matrix.trace (B₂ j * Y * B₁ i)) :
    ∀ i j, A₁ i * A₂ j = B₁ i * B₂ j := by
  intro i j
  apply sub_eq_zero.mp
  apply trace_mul_right_eq_zero
  intro N
  have h := hExt N j i
  rw [Matrix.trace_mul_cycle (A₂ j) N (A₁ i),
      Matrix.trace_mul_cycle (B₂ j) N (B₁ i)] at h
  rw [sub_mul, sub_eq_zero]
  exact h

/-! ### Step 2: extract right factors -/

/-- The right factor: given injective `A` with product identity, constructs `Z`
such that `A₁ i = Z * B₁ i`. -/
noncomputable def rightFactor (A : MPSTensor d D) (hA : IsInjective A)
    (B : MPSTensor d D) : Matrix (Fin D) (Fin D) ℂ :=
  Fintype.linearCombination ℂ B (decompositionMap hA 1)

/-- The right factor satisfies `A₁ i = rightFactor A₂ hA₂ B₂ * B₁ i`. -/
theorem rightFactor_spec
    (A₂ : MPSTensor d D) (hA₂ : IsInjective A₂)
    (A₁ B₁ B₂ : MPSTensor d D)
    (hProd : ∀ i j, A₂ j * A₁ i = B₂ j * B₁ i) :
    ∀ i, A₁ i = rightFactor A₂ hA₂ B₂ * B₁ i := by
  intro i
  have key : ∀ c : Fin d → ℂ,
      (Fintype.linearCombination ℂ A₂ c) * A₁ i =
      (Fintype.linearCombination ℂ B₂ c) * B₁ i := by
    intro c
    simp only [Fintype.linearCombination_apply, Finset.sum_mul, smul_mul_assoc]
    exact Finset.sum_congr rfl (fun j _ => congrArg (c j • ·) (hProd i j))
  have h := key (decompositionMap hA₂ 1)
  rw [decompositionMap_spec hA₂] at h
  simpa [rightFactor] using h

/-! ### Main theorem -/

/-- **Tensor proportionality (Lemma 2).**
Two injective 2-site tensors that agree under all virtual insertions on both bonds
must be proportional: `A₁ = λ • B₁` and `A₂ = λ⁻¹ • B₂` for some nonzero `λ`. -/
theorem tensor_proportional [NeZero D]
    (A₁ A₂ B₁ B₂ : MPSTensor d D)
    (hA₁ : IsInjective A₁) (hA₂ : IsInjective A₂)
    (hB₁ : IsInjective B₁) (hB₂ : IsInjective B₂)
    (hInt : ∀ (X : Matrix (Fin D) (Fin D) ℂ) (i j : Fin d),
      Matrix.trace (A₁ i * X * A₂ j) = Matrix.trace (B₁ i * X * B₂ j))
    (hExt : ∀ (Y : Matrix (Fin D) (Fin D) ℂ) (i j : Fin d),
      Matrix.trace (A₂ j * Y * A₁ i) = Matrix.trace (B₂ j * Y * B₁ i)) :
    ∃ (λ_ : ℂ), λ_ ≠ 0 ∧ (∀ i, A₁ i = λ_ • B₁ i) ∧ (∀ j, A₂ j = λ_⁻¹ • B₂ j) := by
  -- Step 1: product equalities
  have hProdInt := product_eq_of_internal_trace A₁ A₂ B₁ B₂ hInt
  have hProdExt := product_eq_of_external_trace A₁ A₂ B₁ B₂ hExt
  -- Step 2: extract factors
  set Z := rightFactor A₂ hA₂ B₂ with hZ_def
  set W := rightFactor A₁ hA₁ B₁ with hW_def
  have hZ : ∀ i, A₁ i = Z * B₁ i := rightFactor_spec A₂ hA₂ A₁ B₁ B₂ hProdInt
  have hW : ∀ j, A₂ j = W * B₂ j := rightFactor_spec A₁ hA₁ A₂ B₂ B₁ hProdExt
  -- Step 3a: A₂ j * Z = B₂ j
  have hA₂Z : ∀ j, A₂ j * Z = B₂ j := by
    intro j
    apply sub_eq_zero.mp
    apply eq_zero_of_mul_injective_right hB₁
    intro i
    rw [sub_mul, sub_eq_zero]
    have h := hProdInt i j
    rwa [hZ i, ← mul_assoc] at h
  -- Step 3b: A₁ i * W = B₁ i
  have hA₁W : ∀ i, A₁ i * W = B₁ i := by
    intro i
    apply sub_eq_zero.mp
    apply eq_zero_of_mul_injective_right hB₂
    intro j
    rw [sub_mul, sub_eq_zero]
    have h := hProdExt i j
    rwa [hW j, ← mul_assoc] at h
  -- Step 4: Z * M * W = M for all M
  have hZMW : ∀ M : Matrix (Fin D) (Fin D) ℂ, Z * M * W = M := by
    have hZBW : ∀ i, Z * B₁ i * W = B₁ i := fun i => by
      rw [show Z * B₁ i = A₁ i from (hZ i).symm]; exact hA₁W i
    intro M
    obtain ⟨c, hc⟩ := hB₁.exists_decomposition M
    rw [hc]
    simp_rw [Finset.mul_sum, mul_smul_comm, Finset.sum_mul, smul_mul_assoc, hZBW]
  -- Step 4': W * M * Z = M for all M
  have hWMZ : ∀ M : Matrix (Fin D) (Fin D) ℂ, W * M * Z = M := by
    have hWBZ : ∀ j, W * B₂ j * Z = B₂ j := fun j => by
      rw [show W * B₂ j = A₂ j from (hW j).symm]; exact hA₂Z j
    intro M
    obtain ⟨c, hc⟩ := hB₂.exists_decomposition M
    rw [hc]
    simp_rw [Finset.mul_sum, mul_smul_comm, Finset.sum_mul, smul_mul_assoc, hWBZ]
  -- Step 5: Z * W = 1 and W * Z = 1
  have hZW : Z * W = 1 := by simpa using hZMW 1
  have hWZ : W * Z = 1 := by simpa using hWMZ 1
  -- Step 6: Z commutes with everything
  have hZ_comm : ∀ M : Matrix (Fin D) (Fin D) ℂ, Z * M = M * Z := by
    intro M
    have h := congrArg (· * Z) (hZMW M)
    rwa [mul_assoc, hWZ, mul_one] at h
  -- Step 7: Z is scalar
  have hZ_center :
      Z ∈ Set.range (Matrix.scalar (Fin D) : ℂ →+* Matrix (Fin D) (Fin D) ℂ) := by
    rw [← Matrix.center_eq_range, Semigroup.mem_center_iff]
    exact fun M => (hZ_comm M).symm
  obtain ⟨λ_, hλ_eq⟩ := hZ_center
  rw [Matrix.scalar_apply] at hλ_eq
  have hZ_smul : Z = λ_ • 1 := by rw [← hλ_eq, ← Matrix.smul_one_eq_diagonal]
  -- Step 8: λ ≠ 0
  have hλ_ne : λ_ ≠ 0 := by
    intro hλ0
    have hZ0 : Z = 0 := by rw [hZ_smul, hλ0, zero_smul]
    exact one_ne_zero (show (1 : Matrix (Fin D) (Fin D) ℂ) = 0 from
      by rw [← hZW, hZ0, zero_mul])
  -- Step 9: W = λ⁻¹ • 1
  have hW_smul : W = λ_⁻¹ • (1 : Matrix (Fin D) (Fin D) ℂ) := by
    have h1 : λ_ • W = 1 := by
      have := hZW; rw [hZ_smul, smul_mul_assoc, one_mul] at this; exact this
    calc W = λ_⁻¹ • (λ_ • W) := by rw [smul_smul, inv_mul_cancel₀ hλ_ne, one_smul]
    _ = λ_⁻¹ • 1 := by rw [h1]
  -- Conclusion
  exact ⟨λ_, hλ_ne,
    fun i => by rw [hZ i, hZ_smul, smul_mul_assoc, one_mul],
    fun j => by rw [hW j, hW_smul, smul_mul_assoc, one_mul]⟩

end MPSTensor
