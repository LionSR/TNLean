/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.ChannelGroundVectors

/-! Boundary regressions and proof-dependency guards for physical ground vectors. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open Matrix TNLean.PEPS.AreaLaw
open scoped Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace ChannelGroundVectorsTest

variable {q : ℕ} {ι κ Aux : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype Aux] [DecidableEq Aux]

-- The empty word needs no positivity, kernel, or nonzero-vector hypotheses.
example (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (Ω : (ι → Fin q) → ℂ) (ξ : Aux → ℂ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    spectatorRootChannelWord k [] B *ᵥ (fun p => Ω p.1 * ξ p.2) =
      (([].reverse.map (fun i => CFC.sqrt (1 - k i))).prod ⊗ₖ
        (1 : Matrix Aux Aux ℂ)) *ᵥ (B *ᵥ (fun p => Ω p.1 * ξ p.2)) := by
  simp

-- No inhabitedness condition on the spectator is introduced by the identity.
example (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1)
    {Ω : (ι → Fin q) → ℂ} (hΩ : ∀ i, k i *ᵥ Ω = 0) (w : List κ)
    (ξ : Empty → ℂ) (B : Matrix ((ι → Fin q) × Empty) ((ι → Fin q) × Empty) ℂ) :
    spectatorRootChannelWord k w B *ᵥ (fun p => Ω p.1 * ξ p.2) =
      ((w.reverse.map (fun i => CFC.sqrt (1 - k i))).prod ⊗ₖ
        (1 : Matrix Empty Empty ℂ)) *ᵥ (B *ᵥ (fun p => Ω p.1 * ξ p.2)) :=
  spectatorRootChannelWord_mulVec_ground k hk₀ hk₁ hΩ w ξ B

-- The common ground vector may be zero.
example (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1) (w : List κ) (ξ : Aux → ℂ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    spectatorRootChannelWord k w B *ᵥ (fun p => (0 : (ι → Fin q) → ℂ) p.1 * ξ p.2) =
      ((w.reverse.map (fun i => CFC.sqrt (1 - k i))).prod ⊗ₖ
        (1 : Matrix Aux Aux ℂ)) *ᵥ
        (B *ᵥ (fun p => (0 : (ι → Fin q) → ℂ) p.1 * ξ p.2)) :=
  spectatorRootChannelWord_mulVec_ground k hk₀ hk₁ (by simp) w ξ B

-- In a two-event word the second root multiplies on the left.
example (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1)
    {Ω : (ι → Fin q) → ℂ} (hΩ : ∀ i, k i *ᵥ Ω = 0) (i j : κ) (ξ : Aux → ℂ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    spectatorRootChannelWord k [i, j] B *ᵥ (fun p => Ω p.1 * ξ p.2) =
      ((CFC.sqrt (1 - k j) * CFC.sqrt (1 - k i)) ⊗ₖ
        (1 : Matrix Aux Aux ℂ)) *ᵥ (B *ᵥ (fun p => Ω p.1 * ξ p.2)) := by
  simpa using spectatorRootChannelWord_mulVec_ground k hk₀ hk₁ hΩ [i, j] ξ B

end ChannelGroundVectorsTest

/--
info: 'TNLean.PEPS.AreaLaw.spectatorRootChannel_mulVec_ground'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms spectatorRootChannel_mulVec_ground

/--
info: 'TNLean.PEPS.AreaLaw.spectatorRootChannelWord_mulVec_ground'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms spectatorRootChannelWord_mulVec_ground

/--
info: 'TNLean.PEPS.AreaLaw.norm_rootProduct_sub_le_channelWord_sub'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms norm_rootProduct_sub_le_channelWord_sub
