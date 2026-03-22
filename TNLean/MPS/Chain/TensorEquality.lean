import TNLean.MPS.Chain.OneSidedInverse
import TNLean.Algebra.TracePairing

/-!
# Tensor equality up to a scalar on a 2-site chain

This file formalizes the trace-pairing reduction behind Lemma 2 of
[arXiv:1804.04964](https://arxiv.org/abs/1804.04964): if two injective pairs of
local tensors agree under all virtual insertions on both bonds, then the two
pairs are proportional by inverse nonzero scalars.

The full proportionality theorem is stated as `tensor_proportional`.
The first trace-to-product reduction steps are provided as helper lemmas.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- Internal insertion trace agreement implies equality of the mixed products
`A₂ j * A₁ i = B₂ j * B₁ i` for all physical indices. -/
  lemma internal_products_eq
    (A₁ A₂ B₁ B₂ : MPSTensor d D)
    (hInt : ∀ (X : Matrix (Fin D) (Fin D) ℂ) (i j : Fin d),
      Matrix.trace (A₁ i * X * A₂ j) = Matrix.trace (B₁ i * X * B₂ j)) :
    ∀ i j, A₂ j * A₁ i = B₂ j * B₁ i := by
  intro i j
  have hzero :
      A₂ j * A₁ i - B₂ j * B₁ i = 0 := by
    apply (Matrix.trace_mul_right_eq_zero_iff (n := Fin D) (A₂ j * A₁ i - B₂ j * B₁ i)).1
    intro X
    have hX := hInt X i j
    have hcycA : Matrix.trace (A₁ i * X * A₂ j) = Matrix.trace (A₂ j * A₁ i * X) := by
      simpa [Matrix.mul_assoc] using
        (Matrix.trace_mul_cycle (A₁ i) X (A₂ j))
    have hcycB : Matrix.trace (B₁ i * X * B₂ j) = Matrix.trace (B₂ j * B₁ i * X) := by
      simpa [Matrix.mul_assoc] using
        (Matrix.trace_mul_cycle (B₁ i) X (B₂ j))
    calc
      Matrix.trace ((A₂ j * A₁ i - B₂ j * B₁ i) * X)
          = Matrix.trace (A₂ j * A₁ i * X) - Matrix.trace (B₂ j * B₁ i * X) := by
              simp [sub_mul]
      _ = Matrix.trace (A₁ i * X * A₂ j) - Matrix.trace (B₁ i * X * B₂ j) := by
            rw [hcycA, hcycB]
      _ = 0 := by simpa [hX]
  exact sub_eq_zero.mp hzero

/-- External insertion trace agreement implies equality of the mixed products
`A₁ i * A₂ j = B₁ i * B₂ j` for all physical indices. -/
  lemma external_products_eq
    (A₁ A₂ B₁ B₂ : MPSTensor d D)
    (hExt : ∀ (Y : Matrix (Fin D) (Fin D) ℂ) (i j : Fin d),
      Matrix.trace (A₂ j * Y * A₁ i) = Matrix.trace (B₂ j * Y * B₁ i)) :
    ∀ i j, A₁ i * A₂ j = B₁ i * B₂ j := by
  intro i j
  have hzero :
      A₁ i * A₂ j - B₁ i * B₂ j = 0 := by
    apply (Matrix.trace_mul_right_eq_zero_iff (n := Fin D) (A₁ i * A₂ j - B₁ i * B₂ j)).1
    intro Y
    have hY := hExt Y i j
    have hcycA : Matrix.trace (A₂ j * Y * A₁ i) = Matrix.trace (A₁ i * A₂ j * Y) := by
      simpa [Matrix.mul_assoc] using
        (Matrix.trace_mul_cycle (A₂ j) Y (A₁ i))
    have hcycB : Matrix.trace (B₂ j * Y * B₁ i) = Matrix.trace (B₁ i * B₂ j * Y) := by
      simpa [Matrix.mul_assoc] using
        (Matrix.trace_mul_cycle (B₂ j) Y (B₁ i))
    calc
      Matrix.trace ((A₁ i * A₂ j - B₁ i * B₂ j) * Y)
          = Matrix.trace (A₁ i * A₂ j * Y) - Matrix.trace (B₁ i * B₂ j * Y) := by
              simp [sub_mul]
      _ = Matrix.trace (A₂ j * Y * A₁ i) - Matrix.trace (B₂ j * Y * B₁ i) := by
            rw [hcycA, hcycB]
      _ = 0 := by simpa [hY]
  exact sub_eq_zero.mp hzero

/-- Lemma 2 of arXiv:1804.04964 (2-site case): two injective tensor pairs that
agree under all virtual insertions on both bonds are proportional. -/
theorem tensor_proportional
    (A₁ A₂ B₁ B₂ : MPSTensor d D)
    (hA₁ : IsInjective A₁) (hA₂ : IsInjective A₂)
    (hB₁ : IsInjective B₁) (hB₂ : IsInjective B₂)
    (hInt : ∀ (X : Matrix (Fin D) (Fin D) ℂ) (i j : Fin d),
      Matrix.trace (A₁ i * X * A₂ j) = Matrix.trace (B₁ i * X * B₂ j))
    (hExt : ∀ (Y : Matrix (Fin D) (Fin D) ℂ) (i j : Fin d),
      Matrix.trace (A₂ j * Y * A₁ i) = Matrix.trace (B₂ j * Y * B₁ i)) :
    ∃ (lambda_ : ℂ), lambda_ ≠ 0 ∧
      (∀ i, A₁ i = lambda_ • B₁ i) ∧ (∀ j, A₂ j = lambda_⁻¹ • B₂ j) := by
  -- Step 1 and Step 2 from the proof sketch: identify all mixed products.
  have hProdL : ∀ i j, A₂ j * A₁ i = B₂ j * B₁ i :=
    internal_products_eq A₁ A₂ B₁ B₂ hInt
  have hProdR : ∀ i j, A₁ i * A₂ j = B₁ i * B₂ j :=
    external_products_eq A₁ A₂ B₁ B₂ hExt
  -- Handle D = 0: all matrices are trivially equal (subsingleton).
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · exact ⟨1, one_ne_zero, fun i => Subsingleton.elim _ _, fun j => Subsingleton.elim _ _⟩
  haveI : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  -- Step 3: Decompose 1 in terms of A₂ to define Z, then show A₁ i = Z * B₁ i.
  set Z := ∑ j, decompositionMap hA₂ 1 j • B₂ j with hZ_def
  have hA₁_eq : ∀ i, A₁ i = Z * B₁ i := by
    intro i
    have h1 : A₁ i = (∑ j, decompositionMap hA₂ 1 j • A₂ j) * A₁ i := by
      rw [decompositionMap_sum, one_mul]
    rw [h1, Finset.sum_mul]
    simp_rw [smul_mul_assoc, hProdL i, ← smul_mul_assoc]
    rw [← Finset.sum_mul]
  -- Step 4: Decompose 1 in terms of A₁ to define W, then show A₂ j = W * B₂ j.
  set W := ∑ i, decompositionMap hA₁ 1 i • B₁ i with hW_def
  have hA₂_eq : ∀ j, A₂ j = W * B₂ j := by
    intro j
    have h1 : A₂ j = (∑ i, decompositionMap hA₁ 1 i • A₁ i) * A₂ j := by
      rw [decompositionMap_sum, one_mul]
    rw [h1, Finset.sum_mul]
    simp_rw [smul_mul_assoc, hProdR, ← smul_mul_assoc]
    rw [← Finset.sum_mul]
  -- Step 5: Show W * B₂ j * Z = B₂ j (using spanning of B₁).
  have hWBZ : ∀ j, W * B₂ j * Z = B₂ j := by
    intro j
    have h_vanish : ∀ i, (W * B₂ j * Z - B₂ j) * B₁ i = 0 := by
      intro i
      rw [sub_mul, sub_eq_zero, mul_assoc (W * B₂ j) Z (B₁ i), ← hA₂_eq j, ← hA₁_eq i]
      exact hProdL i j
    have hL : LinearMap.mulLeft ℂ (W * B₂ j * Z - B₂ j) = 0 :=
      LinearMap.ext_on_range (hv := hB₁.span_eq_top) fun i => by
        simp only [LinearMap.mulLeft_apply, LinearMap.zero_apply, h_vanish i]
    have h1 := LinearMap.congr_fun hL 1
    simp only [LinearMap.mulLeft_apply, mul_one, LinearMap.zero_apply] at h1
    exact sub_eq_zero.mp h1
  -- Step 6: Show W * M * Z = M for all M (using spanning of B₂).
  have hWMZ : ∀ M, W * M * Z = M := by
    have hL : (LinearMap.mulLeft ℂ W).comp (LinearMap.mulRight ℂ Z) = LinearMap.id :=
      LinearMap.ext_on_range (hv := hB₂.span_eq_top) fun j => by
        simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
          LinearMap.id_apply]
        rw [← mul_assoc]; exact hWBZ j
    intro M
    have := LinearMap.congr_fun hL M
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
      LinearMap.id_apply] at this
    rw [mul_assoc]; exact this
  -- Step 7: W * Z = 1 and Z * W = 1.
  have hWZ : W * Z = 1 := by simpa [mul_one] using hWMZ 1
  have hZW : Z * W = 1 := by
    have h := hWMZ (Z * W)
    have h2 : W * (Z * W) * Z = 1 := by
      rw [← mul_assoc W Z W, mul_assoc (W * Z)]
      simp only [hWZ, one_mul]
    exact h.symm.trans h2
  -- Step 8: Z commutes with all matrices.
  have hZ_comm : ∀ M, Z * M = M * Z := by
    intro M
    have h := hWMZ (Z * M)
    rw [← mul_assoc W Z M, hWZ, one_mul] at h
    exact h.symm
  -- Step 9: Z is in the center of the matrix algebra, hence scalar.
  have hZ_center : Z ∈ Set.center (Matrix (Fin D) (Fin D) ℂ) := by
    rw [Semigroup.mem_center_iff]
    exact fun M => (hZ_comm M).symm
  rw [Matrix.center_eq_range ℂ] at hZ_center
  obtain ⟨lambda_, hLam⟩ := hZ_center
  have hZ_eq : Z = lambda_ • 1 := by
    rw [← hLam, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  -- Step 10: lambda_ ≠ 0 (from W * Z = 1 and Z = lambda_ • 1).
  have hLam_ne : lambda_ ≠ 0 := by
    intro h0; have h := hWZ
    rw [hZ_eq, mul_smul_comm, mul_one, h0, zero_smul] at h
    exact zero_ne_one h
  -- Step 11: W = lambda_⁻¹ • 1.
  have hW_eq : W = lambda_⁻¹ • (1 : Matrix (Fin D) (Fin D) ℂ) := by
    have h : lambda_ • W = 1 := by
      have := hWZ; rwa [hZ_eq, mul_smul_comm, mul_one] at this
    calc W = lambda_⁻¹ • (lambda_ • W) := by
              rw [smul_smul, inv_mul_cancel₀ hLam_ne, one_smul]
      _ = lambda_⁻¹ • 1 := by rw [h]
  -- Step 12: Assemble the result.
  exact ⟨lambda_, hLam_ne,
    fun i => by rw [hA₁_eq i, hZ_eq, smul_mul_assoc, one_mul],
    fun j => by rw [hA₂_eq j, hW_eq, smul_mul_assoc, one_mul]⟩

end MPSTensor
