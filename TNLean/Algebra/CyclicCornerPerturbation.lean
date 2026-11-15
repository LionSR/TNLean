/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.AnnihilatingPowerPerturbation
import QICLean.Channel.KrausCPTP

/-!
# Lifting an annihilating perturbation into a matrix corner

An input corner prepared in one fixed matrix and an output corner read
only through its trace allow a rectangular perturbation to be lifted
to the full matrix algebra. Its square and its two products with the
original map vanish. This is the isolated middle-corner construction in
the cyclic selection argument for arXiv:1708.00029, Theorem 4.1.
-/

open scoped Matrix

namespace Matrix

private theorem recover_isometric_corner {D r : ℕ}
    (V : Matrix (Fin D) (Fin r) ℂ) (hV : Vᴴ * V = 1)
    (Y : Matrix (Fin r) (Fin r) ℂ) : Vᴴ * (V * Y * Vᴴ) * V = Y := by
  calc
    Vᴴ * (V * Y * Vᴴ) * V = (Vᴴ * V) * Y * (Vᴴ * V) := by
      simp only [Matrix.mul_assoc]
    _ = Y := by rw [hV, Matrix.one_mul, Matrix.mul_one]

/-- A nonzero Hermitian-preserving rectangular direction that kills the
incoming prepared matrix and has zero output trace lifts to a nonzero
annihilating direction on orthogonal matrix corners. The exact incoming
and outgoing branch identities are assumed, not inferred from channel
irreducibility. This is the isolated-corner construction used in the
written argument associated with arXiv:1708.00029, Theorem 4.1. Complete
positivity of the perturbed map and its Choi-face compatibility remain
separate obligations. -/
theorem exists_annihilating_corner_perturbation {D m n : ℕ}
    (V : Matrix (Fin D) (Fin m) ℂ) (W : Matrix (Fin D) (Fin n) ℂ)
    (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1) (hOrth : Vᴴ * W = 0)
    (F : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    (L : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (hLne : L ≠ 0)
    (ρ : Matrix (Fin m) (Fin m) ℂ) (σ : Matrix (Fin D) (Fin D) ℂ)
    (φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ)
    (hIn : ∀ X, Vᴴ * F X * V = φ X • ρ)
    (hOut : ∀ Y, F (W * Y * Wᴴ) = Y.trace • σ)
    (hTrace : ∀ Y, (L Y).trace = 0) (hKill : L ρ = 0)
    (hHerm : ∀ Y, Y.IsHermitian → (L Y).IsHermitian) :
    ∃ K : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ),
      K ≠ 0 ∧ (∀ X, K X = W * L (Vᴴ * X * V) * Wᴴ) ∧
      F * K = 0 ∧ K * F = 0 ∧ K * K = 0 ∧
      (∀ X, (K X).trace = 0) ∧
      (∀ X, X.IsHermitian → (K X).IsHermitian) ∧
      (∀ p : ℕ, 2 ≤ p → (F + K) ^ p = F ^ p) := by
  let K : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    singleKrausMap W ∘ₗ L ∘ₗ singleKrausMap Vᴴ
  have hK (X : Matrix (Fin D) (Fin D) ℂ) :
      K X = W * L (Vᴴ * X * V) * Wᴴ := by
    simp only [K, LinearMap.comp_apply, singleKrausMap_apply,
      Matrix.conjTranspose_conjTranspose]
  have hExtract (Y : Matrix (Fin n) (Fin n) ℂ) :
      Vᴴ * (W * Y * Wᴴ) * V = 0 := by
    calc
      Vᴴ * (W * Y * Wᴴ) * V = (Vᴴ * W) * Y * Wᴴ * V := by
        simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hOrth, Matrix.zero_mul, Matrix.zero_mul, Matrix.zero_mul]
  have hKne : K ≠ 0 := by
    intro hZero
    apply hLne
    ext Y : 1
    change L Y = 0
    have hEval : W * L Y * Wᴴ = 0 := by
      have h := congrArg
        (fun T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) => T (V * Y * Vᴴ)) hZero
      simpa only [hK, recover_isometric_corner V hV, LinearMap.zero_apply] using h
    have h := congrArg (fun Z => Wᴴ * Z * W) hEval
    simpa only [recover_isometric_corner W hW, Matrix.mul_zero, Matrix.zero_mul] using h
  have hFK : F * K = 0 := by
    ext X : 1
    change F (K X) = 0
    rw [hK, hOut, hTrace, zero_smul]
  have hKF : K * F = 0 := by
    ext X : 1
    change K (F X) = 0
    rw [hK, hIn, map_smul, hKill, smul_zero, Matrix.mul_zero, Matrix.zero_mul]
  have hExtractK (X : Matrix (Fin D) (Fin D) ℂ) : Vᴴ * K X * V = 0 := by
    rw [hK, hExtract]
  have hKK : K * K = 0 := by
    ext X : 1
    change K (K X) = 0
    calc
      K (K X) = W * L (Vᴴ * K X * V) * Wᴴ := hK (K X)
      _ = 0 := by rw [hExtractK, map_zero, Matrix.mul_zero, Matrix.zero_mul]
  have hKtrace (X : Matrix (Fin D) (Fin D) ℂ) : (K X).trace = 0 := by
    rw [hK, Matrix.trace_mul_cycle, hW, Matrix.one_mul, hTrace]
  have hKherm (X : Matrix (Fin D) (Fin D) ℂ) (hX : X.IsHermitian) :
      (K X).IsHermitian := by
    rw [hK]
    exact Matrix.isHermitian_mul_mul_conjTranspose W
      (hHerm _ (Matrix.isHermitian_conjTranspose_mul_mul V hX))
  refine ⟨K, hKne, hK, hFK, hKF, hKK, hKtrace, hKherm, ?_⟩
  intro p hp
  exact add_pow_eq_of_annihilating_square_zero hFK hKF hKK hp

end Matrix
