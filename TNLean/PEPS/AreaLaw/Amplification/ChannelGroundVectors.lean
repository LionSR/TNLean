/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.ChannelWordObservables
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Physical channel words on a common ground vector

If every positive contraction `k i` annihilates `Ω`, evaluating its spectator
root channel on `Ω ⊗ ξ` leaves only the left action of `sqrt (1 - k i)`.
The existing chronological channel word therefore evaluates to the product
of these roots in reverse list order. No normalization of either vector or
Hermiticity of the input observable is required.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, `eq:amplification-channel-vector` and lines 218–224,
at revision `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open Matrix
open scoped Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.PEPS.AreaLaw

variable {q : ℕ} {ι κ Aux : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype Aux] [DecidableEq Aux]

private theorem kronecker_one_mulVec_product
    (A : Matrix (ι → Fin q) (ι → Fin q) ℂ) (Ω : (ι → Fin q) → ℂ) (ξ : Aux → ℂ) :
    (A ⊗ₖ (1 : Matrix Aux Aux ℂ)) *ᵥ (fun p => Ω p.1 * ξ p.2) =
      fun p => (A *ᵥ Ω) p.1 * ξ p.2 := by
  have h := Matrix.kronecker_mulVec_vec (1 : Matrix Aux Aux ℂ) (Matrix.vecMulVec ξ Ω) A
  simp only [Matrix.one_mul, Matrix.vecMulVec_mul, Matrix.vecMul_transpose] at h
  change (A ⊗ₖ (1 : Matrix Aux Aux ℂ)) *ᵥ (fun p => ξ p.2 * Ω p.1) =
    (fun p => ξ p.2 * (A *ᵥ Ω) p.1) at h
  simpa only [mul_comm] using h

/-- A physical root channel on a ground vector is left multiplication by the
complementary root, with an arbitrary spectator vector and observable.
Source: area law, `09-amplification.tex`, `eq:amplification-channel-vector`. -/
theorem spectatorRootChannel_mulVec_ground
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    {Ω : (ι → Fin q) → ℂ} (hΩ : k *ᵥ Ω = 0) (ξ : Aux → ℂ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    spectatorRootChannel k B *ᵥ (fun p => Ω p.1 * ξ p.2) =
      (CFC.sqrt (1 - k) ⊗ₖ (1 : Matrix Aux Aux ℂ)) *ᵥ
        (B *ᵥ (fun p => Ω p.1 * ξ p.2)) := by
  simp only [spectatorRootChannel, rootChannel, Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec, kronecker_one_mulVec_product,
    Matrix.sqrt_one_sub_mulVec_eq_self hk₁ hΩ, Matrix.sqrt_mulVec_eq_zero hk₀ hΩ,
    Pi.zero_apply, zero_mul, ← Pi.zero_def, Matrix.mulVec_zero, add_zero]

/-- Chronological physical channel words on a common ground vector give the
root product with the latest event on the left. This is the finite-word step
in area law, `09-amplification.tex`, lines 218–224. -/
theorem spectatorRootChannelWord_mulVec_ground
    (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1)
    {Ω : (ι → Fin q) → ℂ} (hΩ : ∀ i, k i *ᵥ Ω = 0)
    (w : List κ) (ξ : Aux → ℂ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    spectatorRootChannelWord k w B *ᵥ (fun p => Ω p.1 * ξ p.2) =
      ((w.reverse.map (fun i => CFC.sqrt (1 - k i))).prod ⊗ₖ
        (1 : Matrix Aux Aux ℂ)) *ᵥ (B *ᵥ (fun p => Ω p.1 * ξ p.2)) := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w i ih =>
    rw [spectatorRootChannelWord_append_singleton,
      spectatorRootChannel_mulVec_ground (hk₀ i) (hk₁ i) (hΩ i), ih]
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_kronecker_mul, Matrix.mul_one]
    simp only [List.reverse_append, List.reverse_singleton, List.map_append,
      List.map_singleton, List.prod_append, List.prod_singleton]

/-- A pointwise Euclidean vector bound follows from the operator-norm
difference of the two physical channel words. This is the deterministic
conversion in area law, `09-amplification.tex`, lines 218–224; no expected-norm
omission estimate is assumed or proved here. -/
theorem norm_rootProduct_sub_le_channelWord_sub
    (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1)
    {Ω : (ι → Fin q) → ℂ} (hΩ : ∀ i, k i *ᵥ Ω = 0)
    (u w : List κ) (ξ : Aux → ℂ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    ‖WithLp.toLp 2
      (((u.reverse.map (fun i => CFC.sqrt (1 - k i))).prod ⊗ₖ
          (1 : Matrix Aux Aux ℂ)) *ᵥ (B *ᵥ (fun p => Ω p.1 * ξ p.2)) -
        ((w.reverse.map (fun i => CFC.sqrt (1 - k i))).prod ⊗ₖ
          (1 : Matrix Aux Aux ℂ)) *ᵥ (B *ᵥ (fun p => Ω p.1 * ξ p.2)))‖ ≤
      ‖spectatorRootChannelWord k u B - spectatorRootChannelWord k w B‖ *
        ‖WithLp.toLp 2 (fun p : (ι → Fin q) × Aux => Ω p.1 * ξ p.2)‖ := by
  rw [← spectatorRootChannelWord_mulVec_ground k hk₀ hk₁ hΩ u ξ B,
    ← spectatorRootChannelWord_mulVec_ground k hk₀ hk₁ hΩ w ξ B,
    ← Matrix.sub_mulVec]
  exact Matrix.l2_opNorm_mulVec
    (spectatorRootChannelWord k u B - spectatorRootChannelWord k w B)
    (WithLp.toLp 2 (fun p : (ι → Fin q) × Aux => Ω p.1 * ξ p.2))

end TNLean.PEPS.AreaLaw
