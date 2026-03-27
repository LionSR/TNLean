/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Symmetry.Defs
import TNLean.Algebra.ScalarCommutant

/-!
# Global Symmetry Corollary (Section 5, arXiv:1804.04964)

For an injective MPS tensor `A` with on-site symmetry under a group
representation `U : G →* Matrix (Fin d) (Fin d) ℂ`, the Fundamental Theorem
provides virtual gauge matrices `X(g)` for each group element. These satisfy a
projective multiplication law up to a scalar factor.

The composition law for the twisted tensor:
`twistedTensor A U (g * h) = twistedTensor (twistedTensor A U h) U g`
combined with the gauge relations `twistedTensor A U g i = X(g) * A i * X(g)⁻¹`
gives `X(h) * X(g) * A i * X(g)⁻¹ * X(h)⁻¹ = X(g*h) * A i * X(g*h)⁻¹`,
so `X(g*h)⁻¹ * X(h) * X(g)` commutes with all `A i`, hence is scalar.

## Main results

* `gauge_ratio_commutes` — if two gauges `X, Y` both conjugate `A` to the same
  `B`, then `Y⁻¹ · X` commutes with every `A i`.
* `gauge_ratio_isScalar` — under injectivity, the ratio is a scalar matrix.
* `gaugeMatrix_projective_mul` — the gauge matrices satisfy
  `X(h) · X(g) = c(g,h) • X(g·h)` for some scalar `c(g,h)`.

## References

* [arXiv:1804.04964](https://arxiv.org/abs/1804.04964), Section 5
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {G : Type*} [Group G] {d D : ℕ}

/-! ### Scalar commutant for gauge composition -/

/-- If `X` and `Y` both conjugate `A` to the same tensor `B`, then
`Y⁻¹ · X` commutes with every `A i`. -/
theorem gauge_ratio_commutes {A B : MPSTensor d D}
    (X Y : GL (Fin D) ℂ)
    (hX : ∀ i : Fin d,
      B i = (X : Matrix _ _ ℂ) * A i * ((X⁻¹ : GL _ ℂ) : Matrix _ _ ℂ))
    (hY : ∀ i : Fin d,
      B i = (Y : Matrix _ _ ℂ) * A i * ((Y⁻¹ : GL _ ℂ) : Matrix _ _ ℂ))
    (i : Fin d) :
    ((Y⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) * (X : Matrix _ _ ℂ) * A i =
      A i * (((Y⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) * (X : Matrix _ _ ℂ)) := by
  have h : (X : Matrix _ _ ℂ) * A i * ((X⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) =
      (Y : Matrix _ _ ℂ) * A i * ((Y⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) := by
    rw [← hX i, ← hY i]
  let Xmat : Matrix (Fin D) (Fin D) ℂ := X
  let Ymat : Matrix (Fin D) (Fin D) ℂ := Y
  let Xinv : Matrix (Fin D) (Fin D) ℂ := ((X⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)
  let Yinv : Matrix (Fin D) (Fin D) ℂ := ((Y⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)
  have hXX : Xinv * Xmat = 1 := by
    simp [Xinv, Xmat]
  have hYY : Yinv * Ymat = 1 := by
    simp [Yinv, Ymat]
  have key := congr_arg
    (fun M => Yinv * M * Xmat) h
  calc
    Yinv * Xmat * A i = Yinv * Xmat * A i * 1 := by
      simp [Matrix.mul_assoc]
    _ = Yinv * Xmat * A i * (Xinv * Xmat) := by
      rw [hXX]
    _ = Yinv * ((Xmat * A i * Xinv)) * Xmat := by
      simp [Xinv, Xmat, Matrix.mul_assoc]
    _ = Yinv * ((Ymat * A i * Yinv)) * Xmat := by
      simpa [Xinv, Xmat, Yinv, Ymat] using key
    _ = (Yinv * Ymat) * A i * Yinv * Xmat := by
      simp [Yinv, Ymat, Xmat, Matrix.mul_assoc]
    _ = 1 * A i * Yinv * Xmat := by
      rw [hYY]
    _ = A i * (Yinv * Xmat) := by
      simp [Yinv, Xmat, Matrix.mul_assoc]

/-- If `X` and `Y` both conjugate an injective `A` to the same tensor `B`,
then `Y⁻¹ · X` is a scalar matrix. -/
theorem gauge_ratio_isScalar {A B : MPSTensor d D}
    (hA : IsInjective A)
    (X Y : GL (Fin D) ℂ)
    (hX : ∀ i : Fin d,
      B i = (X : Matrix _ _ ℂ) * A i * ((X⁻¹ : GL _ ℂ) : Matrix _ _ ℂ))
    (hY : ∀ i : Fin d,
      B i = (Y : Matrix _ _ ℂ) * A i * ((Y⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)) :
    ∃ c : ℂ, ((Y⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) * (X : Matrix _ _ ℂ) =
      Matrix.scalar (Fin D) c := by
  apply Matrix.isScalar_of_commute_span_eq_top _ hA.span_eq_top
  intro M hM
  obtain ⟨i, rfl⟩ := hM
  exact gauge_ratio_commutes X Y hX hY i

/-- The gauge matrices from the FT satisfy a projective multiplication law.

Given injective `A` with on-site symmetry under `U`, suppose `X(g)` witnesses
`GaugeEquiv A (twistedTensor A U g)` for each `g`. Then for all `g, h`:
`X(h) · X(g) = c(g,h) • X(g·h)` for some scalar `c(g,h)`.

The order `X(h) · X(g)` (rather than `X(g) · X(h)`) follows from the
twist composition law `twistedTensor A U (g*h) = twistedTensor (twistedTensor A U h) U g`:
applying physical `g` to the `h`-twisted tensor sandwiches the `g`-gauge
*inside* the `h`-gauge. -/
theorem gaugeMatrix_projective_mul
    (A : MPSTensor d D)
    (hA : IsInjective A)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (X : G → GL (Fin D) ℂ)
    (hX : ∀ g : G, ∀ i : Fin d,
      twistedTensor A U g i =
        (X g : Matrix _ _ ℂ) * A i * (((X g)⁻¹ : GL _ ℂ) : Matrix _ _ ℂ))
    (g h : G) :
    ∃ c : ℂ, (X h : Matrix _ _ ℂ) * (X g : Matrix _ _ ℂ) =
        c • (X (g * h)).1 := by
  let Xg := X g
  let Xh := X h
  let Xgh := X (g * h)
  -- X(h) * X(g) conjugates A to twistedTensor A U (g*h)
  let Ygl : GL (Fin D) ℂ := Xh * Xg
  have hComp : ∀ i : Fin d,
      twistedTensor A U (g * h) i =
        (Ygl : Matrix _ _ ℂ) * A i * ((Ygl⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) := by
    intro i
    -- twistedTensor A U (g*h) = twistedTensor (twistedTensor A U h) U g
    -- by composition law, and twistedTensor A U h is gauge equiv to A via Xh
    -- Use GaugeEquiv.sameMPV to show this equals Ygl conjugation
    -- Direct calculation:
    -- twistedTensor A U (g*h) i
    -- = twistedTensor (twistedTensor A U h) U g i  [by twistedTensor_mul]
    -- = ∑_j U(g)_ij (twistedTensor A U h j)       [def of twistedTensor]
    -- = ∑_j U(g)_ij (Xh A_j Xh⁻¹)                [by hX h]
    -- = Xh (∑_j U(g)_ij A_j) Xh⁻¹                 [linearity]
    -- = Xh (twistedTensor A U g i) Xh⁻¹            [def of twistedTensor]
    -- = Xh (Xg A_i Xg⁻¹) Xh⁻¹                    [by hX g]
    -- = (Xh Xg) A_i (Xg⁻¹ Xh⁻¹)                  [assoc]
    -- = Ygl A_i Ygl⁻¹                              [def of Ygl]
    have step1 : twistedTensor A U (g * h) i =
        twistedTensor (twistedTensor A U h) U g i :=
      congr_fun (twistedTensor_mul A U g h) i
    have step2 : twistedTensor (twistedTensor A U h) U g i =
        (Xh : Matrix _ _ ℂ) * twistedTensor A U g i *
          ((Xh⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) := by
      unfold twistedTensor
      -- Goal: ∑ j, U g i j • (∑ k, U h j k • A k) = Xh * (∑ j, U g i j • A j) * Xh⁻¹
      -- First replace inner sum with Xh * A j * Xh⁻¹
      have : ∀ j, (∑ k : Fin d, U h j k • A k) =
          (Xh : Matrix _ _ ℂ) * A j * ((Xh⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) := by
        intro j; exact hX h j
      simp_rw [this]
      -- Goal: ∑ j, U g i j • (Xh * A j * Xh⁻¹) = Xh * (∑ j, U g i j • A j) * Xh⁻¹
      -- Convert smul · (a * b * c) to a * (smul · b) * c
      have distrib : ∀ j, U g i j • ((Xh : Matrix _ _ ℂ) * A j *
          ((Xh⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)) =
        (Xh : Matrix _ _ ℂ) * (U g i j • A j) *
          ((Xh⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) := by
        intro j; simp [Matrix.mul_assoc]
      simp_rw [distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    rw [step1, step2, hX g i]
    simp [Xg, Xh, Ygl, Matrix.mul_assoc, mul_inv_rev]
  -- Apply scalar commutant
  obtain ⟨c, hc⟩ := gauge_ratio_isScalar hA Ygl Xgh hComp (hX (g * h))
  -- hc : Xgh⁻¹ * Ygl = scalar c
  refine ⟨c, ?_⟩
  change (Xh : Matrix _ _ ℂ) * (Xg : Matrix _ _ ℂ) = c • Xgh.1
  have hval : Ygl.1 = (Xh : Matrix _ _ ℂ) * (Xg : Matrix _ _ ℂ) := by
    simp [Ygl]
  have key : Ygl.1 = Xgh.1 * (((Xgh⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) * Ygl.1) := by
    simp
  rw [← hval, key, hc]
  simpa [Matrix.scalar_apply] using (Matrix.smul_eq_mul_diagonal (M := Xgh.1) c).symm

end MPSTensor
