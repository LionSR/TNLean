/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Defs
import TNLean.MPS.Core.ScaledNormality

/-!
# Proportional states with one scalar

For tensors `A`, `B` of any bond dimensions and a scalar `c`, the states satisfy
`V_N(A) = c ^ N • V_N(B)` at every positive length exactly when `A` and `c • B` have the same
states. The fundamental theorem for arbitrary tensors and its uniqueness half therefore apply
verbatim to the pair `(A, c • B)`.

An `N`-dependent constant `c_N` in place of `c ^ N` is not covered: there is a pair
with `V_N(A) = c_N • V_N(B)` for which no rescaling of `B` has the states of `A`.

## Main results

* `MPSTensor.sameMPV₂Pos_smul_iff`.
-/

namespace MPSTensor

variable {d : ℕ}

/-- **Proportional states with one scalar.** `A` and `c • B` have the same states at every positive
length exactly when every coefficient of `A` of length `N` is `c ^ N` times the corresponding
coefficient of `B`. -/
theorem sameMPV₂Pos_smul_iff {D₁ D₂ : ℕ} {A : MPSTensor d D₁} {B : MPSTensor d D₂} {c : ℂ} :
    SameMPV₂Pos A (c • B) ↔
      ∀ N, 0 < N → ∀ σ : Fin N → Fin d, mpv A σ = c ^ N * mpv B σ := by
  refine forall_congr' fun N => forall_congr' fun _ => forall_congr' fun σ => ?_
  rw [← mpv_smul c B σ]
  rfl

end MPSTensor
