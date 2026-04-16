import TNLean.MPS.Chain.OneSidedInverse
import TNLean.Algebra.TracePairing
import Mathlib.Data.Matrix.Basis

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
      _ = 0 := by simp [hX]
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
      _ = 0 := by simp [hY]
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
  -- Handle D = 0: the matrix ring is trivial, all matrices are equal.
  by_cases hD : D = 0
  · subst hD
    exact ⟨1, one_ne_zero, fun i => Subsingleton.elim _ _, fun j => by
      simp [Subsingleton.elim (A₂ j) (B₂ j)]⟩
  -- Step 1: From trace conditions, derive matrix product equalities.
  have hProdL : ∀ i j, A₂ j * A₁ i = B₂ j * B₁ i :=
    internal_products_eq A₁ A₂ B₁ B₂ hInt
  have hProdR : ∀ i j, A₁ i * A₂ j = B₁ i * B₂ j :=
    external_products_eq A₁ A₂ B₁ B₂ hExt
  -- Step 2: Extract Z with A₁ i = Z * B₁ i for all i.
  -- Decompose 1 in the spanning set {A₂ j}, apply same coefficients to {B₂ j}.
  let Z := Fintype.linearCombination ℂ B₂ (decompositionMap hA₂ 1)
  have hZ : ∀ i, A₁ i = Z * B₁ i := by
    intro i
    have h : Fintype.linearCombination ℂ A₂ (decompositionMap hA₂ 1) * A₁ i =
        Fintype.linearCombination ℂ B₂ (decompositionMap hA₂ 1) * B₁ i := by
      simp only [Fintype.linearCombination_apply, Finset.sum_mul, smul_mul_assoc]
      simp_rw [hProdL i]
    rwa [decompositionMap_spec, one_mul] at h
  -- Step 3: Extract W with A₂ j = W * B₂ j for all j.
  let W := Fintype.linearCombination ℂ B₁ (decompositionMap hA₁ 1)
  have hW : ∀ j, A₂ j = W * B₂ j := by
    intro j
    have h : Fintype.linearCombination ℂ A₁ (decompositionMap hA₁ 1) * A₂ j =
        Fintype.linearCombination ℂ B₁ (decompositionMap hA₁ 1) * B₂ j := by
      simp only [Fintype.linearCombination_apply, Finset.sum_mul, smul_mul_assoc]
      simp_rw [hProdR _ j]
    rwa [decompositionMap_spec, one_mul] at h
  -- Step 4: Show Z * M * W = M for all M via spanning arguments.
  have hZMW : ∀ M : Matrix (Fin D) (Fin D) ℂ, Z * M * W = M := by
    -- First: Z * B₁ i * W = B₁ i for all i (by spanning in B₂)
    have hZBW : ∀ i, Z * B₁ i * W = B₁ i := by
      intro i
      have hvan : ∀ j, (Z * B₁ i * W - B₁ i) * B₂ j = 0 := by
        intro j
        have h := hProdR i j; rw [hZ i, hW j] at h
        rw [sub_mul, sub_eq_zero, mul_assoc]; exact h
      have hf : LinearMap.mulLeft ℂ (Z * B₁ i * W - B₁ i) = 0 :=
        LinearMap.ext_on_range (v := B₂) (hv := hB₂.span_eq_top) fun j => by
          simp only [LinearMap.mulLeft_apply, LinearMap.zero_apply]; exact hvan j
      have h := LinearMap.congr_fun hf 1
      simp only [LinearMap.mulLeft_apply, LinearMap.zero_apply, mul_one] at h
      exact sub_eq_zero.mp h
    -- Extend to all M (by spanning in B₁): Z * (M * W) = M
    have key : ∀ i, Z * (B₁ i * W) = B₁ i := fun i => by
      rw [← mul_assoc]; exact hZBW i
    have hf : (LinearMap.mulLeft ℂ Z).comp (LinearMap.mulRight ℂ W) -
        LinearMap.id = 0 :=
      LinearMap.ext_on_range (v := B₁) (hv := hB₁.span_eq_top) fun i => by
        simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
            LinearMap.sub_apply, LinearMap.id_apply, LinearMap.zero_apply, sub_eq_zero]
        exact key i
    intro M
    have h := LinearMap.congr_fun hf M
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
        LinearMap.sub_apply, LinearMap.id_apply, LinearMap.zero_apply, sub_eq_zero] at h
    rw [← mul_assoc] at h; exact h
  -- Step 5: Z * W = 1 and Z commutes with everything.
  have hZW : Z * W = 1 := by have h := hZMW 1; rwa [mul_one] at h
  have hComm : ∀ M : Matrix (Fin D) (Fin D) ℂ, Z * M = M * Z := by
    intro M
    have h := hZMW (M * Z)
    rw [mul_assoc, mul_assoc, hZW, mul_one] at h
    exact h
  -- Step 6: Z is scalar (center of M_D(ℂ) = ℂ · I for commutative ℂ).
  have hCenter : Z ∈ Set.center (Matrix (Fin D) (Fin D) ℂ) :=
    Semigroup.mem_center_iff.mpr fun g => (hComm g).symm
  rw [Matrix.center_eq_range] at hCenter
  obtain ⟨lambda_, hlambda⟩ := hCenter
  -- hlambda : Matrix.scalar (Fin D) lambda_ = Z
  -- Step 7: Z = lambda_ • 1 (connect scalar to smul)
  have hZ_eq : Z = lambda_ • (1 : Matrix (Fin D) (Fin D) ℂ) := by
    rw [← hlambda, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  -- Step 8: lambda_ ≠ 0 (since Z * W = 1 and Z = lambda_ • 1).
  have hne : lambda_ ≠ 0 := by
    intro h; rw [h, zero_smul] at hZ_eq; rw [hZ_eq, zero_mul] at hZW
    -- hZW : 0 = 1 in Matrix (Fin D) (Fin D) ℂ; D ≥ 1 so 1 ≠ 0
    have : (1 : Matrix (Fin D) (Fin D) ℂ) ≠ 0 := by
      have : NeZero D := ⟨hD⟩
      exact one_ne_zero
    exact this hZW.symm
  -- Step 9: Derive A₁ i = lambda_ • B₁ i.
  have hA₁_eq : ∀ i, A₁ i = lambda_ • B₁ i := by
    intro i; rw [hZ i, hZ_eq, smul_mul_assoc, one_mul]
  -- Step 10: Derive W = lambda_⁻¹ • 1 and A₂ j = lambda_⁻¹ • B₂ j.
  have hW_eq : W = lambda_⁻¹ • (1 : Matrix (Fin D) (Fin D) ℂ) := by
    have hsmul : lambda_ • W = 1 := by
      have := hZW; rw [hZ_eq, smul_mul_assoc, one_mul] at this; exact this
    have h1 : lambda_⁻¹ • (lambda_ • W) = lambda_⁻¹ • (1 : Matrix (Fin D) (Fin D) ℂ) := by
      rw [hsmul]
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h1
  have hA₂_eq : ∀ j, A₂ j = lambda_⁻¹ • B₂ j := by
    intro j; rw [hW j, hW_eq, smul_mul_assoc, one_mul]
  exact ⟨lambda_, hne, hA₁_eq, hA₂_eq⟩

end MPSTensor
