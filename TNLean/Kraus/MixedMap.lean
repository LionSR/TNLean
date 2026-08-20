/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Schwarz.Basic
import TNLean.Kraus.Word

import Mathlib.LinearAlgebra.Matrix.Bilinear

/-!
# Mixed maps of finite matrix families

For two finite matrix families `A` and `B`, the mixed map is
$$
X \longmapsto \sum_i A_i X B_i^\dagger.
$$
It acts on rectangular matrices when the two families have different matrix sizes. Its iterates
are sums over pairs of word evaluations with a common word.

## Main declarations

* `Kraus.mixedMapLM` — the rectangular mixed map of two finite matrix families.
* `Kraus.mixedMapLM_pow_apply` — expansion of an iterate as a sum over words.
-/

open scoped Matrix BigOperators

namespace Kraus

variable {d D D₁ D₂ : ℕ}

/-- The mixed map associated with two finite matrix families. It sends `X` to
`∑ i, A i * X * (B i)ᴴ`. -/
noncomputable def mixedMapLM (A : Fin d → Matrix (Fin D₁) (Fin D₁) ℂ)
    (B : Fin d → Matrix (Fin D₂) (Fin D₂) ℂ) :
    Matrix (Fin D₁) (Fin D₂) ℂ →ₗ[ℂ] Matrix (Fin D₁) (Fin D₂) ℂ :=
  ∑ i : Fin d,
    (mulLeftLinearMap (n := Fin D₂) ℂ (A i)).comp
      (mulRightLinearMap (l := Fin D₁) ℂ ((B i)ᴴ))

/-- The mixed map is the sum of its left-right multiplication terms. -/
@[simp]
theorem mixedMapLM_apply (A : Fin d → Matrix (Fin D₁) (Fin D₁) ℂ)
    (B : Fin d → Matrix (Fin D₂) (Fin D₂) ℂ) (X : Matrix (Fin D₁) (Fin D₂) ℂ) :
    mixedMapLM A B X = ∑ i : Fin d, A i * X * (B i)ᴴ := by
  simp [mixedMapLM, Matrix.mul_assoc]

/-- Using the same square family on both sides gives its finite Kraus map. -/
@[simp]
theorem mixedMapLM_self (A : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    mixedMapLM A A = mapLM A := by
  ext X
  simp only [mixedMapLM_apply, mapLM_apply, map_apply]

/-- The mixed map is linear in its left matrix family. -/
theorem mixedMapLM_smul_left (c : ℂ) (A : Fin d → Matrix (Fin D₁) (Fin D₁) ℂ)
    (B : Fin d → Matrix (Fin D₂) (Fin D₂) ℂ) :
    mixedMapLM (fun i ↦ c • A i) B = c • mixedMapLM A B := by
  ext X
  simp [← Finset.smul_sum]

/-- Scaling the right matrix family conjugates the scalar. -/
theorem mixedMapLM_smul_right (c : ℂ) (A : Fin d → Matrix (Fin D₁) (Fin D₁) ℂ)
    (B : Fin d → Matrix (Fin D₂) (Fin D₂) ℂ) :
    mixedMapLM A (fun i ↦ c • B i) = starRingEnd ℂ c • mixedMapLM A B := by
  ext X
  simp [← Finset.smul_sum]

/-- Scaling both matrix families scales the mixed map by `c * conj e`. -/
theorem mixedMapLM_smul (c e : ℂ) (A : Fin d → Matrix (Fin D₁) (Fin D₁) ℂ)
    (B : Fin d → Matrix (Fin D₂) (Fin D₂) ℂ) :
    mixedMapLM (fun i ↦ c • A i) (fun i ↦ e • B i) =
      (c * starRingEnd ℂ e) • mixedMapLM A B := by
  rw [mixedMapLM_smul_left, mixedMapLM_smul_right, smul_smul]

/-- The `N`-fold iterate of a mixed map is the sum over all common words of length `N`. -/
theorem mixedMapLM_pow_apply (A : Fin d → Matrix (Fin D₁) (Fin D₁) ℂ)
    (B : Fin d → Matrix (Fin D₂) (Fin D₂) ℂ) (N : ℕ) :
    ∀ X : Matrix (Fin D₁) (Fin D₂) ℂ,
      ((mixedMapLM A B) ^ N) X =
        ∑ σ : Fin N → Fin d,
          MPSTensor.evalWord A (List.ofFn σ) * X *
            (MPSTensor.evalWord B (List.ofFn σ))ᴴ := by
  classical
  induction N with
  | zero =>
      intro X
      simp [Finset.univ_unique]
  | succ n ih =>
      intro X
      rw [pow_succ']
      change mixedMapLM A B (((mixedMapLM A B) ^ n) X) = _
      rw [ih]
      simp only [map_sum, mixedMapLM_apply]
      rw [Finset.sum_comm]
      rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin d)).sum_comp]
      rw [Fintype.sum_prod_type]
      congr 1
      funext i
      apply Finset.sum_congr rfl
      intro τ _
      simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

end Kraus
