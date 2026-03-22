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

  -- The remaining algebraic argument (linear extension from injectivity,
  -- centrality, and center of full matrix algebra) is recorded as a TODO.
  -- It follows the standard blueprint route described in the PR thread.
  sorry

end MPSTensor
