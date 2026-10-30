/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Matrix.Mul
import TNLean.Algebra.LSymbol

/-!
# L-symbols of matrix action tensors

For an onsite symmetry acting on a matrix product state with several blocks, the action on the
block `x` is moved to the virtual level by matrices `S_{g,x}`, and these satisfy

`S_{g, h • x} S_{h,x} = Lˣ_{g,h} S_{gh,x}`

for scalars `Lˣ_{g,h}` (arXiv:2502.20257, `example:z4z2`, `Papers/2502.20257/main.tex`,
lines 4363–4368, and the injective case at lines 3659–3668). Since matrix multiplication is
associative and the matrices `S_{g,x}` do not vanish, these L-symbols are compatible with the
trivial three-cochain: an onsite symmetry has no anomaly. If moreover `S_{1,x} = 1`, the
L-symbols are normalized.

## Main results

* `TNLean.Algebra.LSymbol.isCompatible_one_of_mul_eq_smul`: compatibility with the trivial
  three-cochain.
* `TNLean.Algebra.LSymbol.isNormalized_of_mul_eq_smul`: normalization.
-/

namespace TNLean.Algebra

namespace LSymbol

variable {G : Type} {X : Type*} [Group G] [MulAction G X] {n : Type*} [Fintype n]

/-- **The L-symbols of matrix action tensors are compatible with the trivial three-cochain**:
if `S_{g, h • x} S_{h,x} = Lˣ_{g,h} S_{gh,x}` for nonzero matrices `S_{g,x}`, then
`Lˣ_{g,hk} Lˣ_{h,k} = L^{k • x}_{g,h} Lˣ_{gh,k}`, the case `ω = 1` of `eq:omega_and_Ls`
(arXiv:2502.20257, lines 4363–4368 and 1920–1923). -/
theorem isCompatible_one_of_mul_eq_smul {S : G → X → Matrix n n ℂ} {L : LSymbol G X}
    (hS : ∀ g x, S g x ≠ 0)
    (hL : ∀ x g h, S g (h • x) * S h x = (L x g h : ℂ) • S (g * h) x) :
    IsCompatible L (fun _ _ _ ↦ 1) := by
  intro x g h k
  have h1 : S g (h • k • x) * S h (k • x) * S k x =
      ((L (k • x) g h : ℂ) * L x (g * h) k) • S (g * h * k) x := by
    rw [hL, Matrix.smul_mul, hL, smul_smul]
  have h2 : S g (h • k • x) * S h (k • x) * S k x =
      ((L x g (h * k) : ℂ) * L x h k) • S (g * h * k) x := by
    rw [Matrix.mul_assoc, hL, Matrix.mul_smul, ← mul_smul, hL, smul_smul, mul_assoc g h k,
      mul_comm (L x h k : ℂ)]
  have h3 := smul_left_injective ℂ (hS (g * h * k) x) (h1.symm.trans h2)
  apply Units.ext
  simpa only [one_mul, Units.val_mul] using h3.symm

/-- **Normalized action matrices give normalized L-symbols**: if
`S_{g, h • x} S_{h,x} = Lˣ_{g,h} S_{gh,x}` for nonzero matrices with `S_{1,x} = 1`, then
`Lˣ_{g,1} = Lˣ_{1,g} = 1`, the convention `eq:triv_Ls` of arXiv:2502.20257. -/
theorem isNormalized_of_mul_eq_smul [DecidableEq n] {S : G → X → Matrix n n ℂ}
    {L : LSymbol G X} (hS : ∀ g x, S g x ≠ 0) (hS₁ : ∀ x, S 1 x = 1)
    (hL : ∀ x g h, S g (h • x) * S h x = (L x g h : ℂ) • S (g * h) x) : IsNormalized L := by
  constructor
  · intro x g
    have h := hL x g 1
    rw [one_smul, hS₁, Matrix.mul_one, mul_one] at h
    exact Units.ext (smul_left_injective ℂ (hS g x) (by simpa using h.symm))
  · intro x g
    have h := hL x 1 g
    rw [hS₁, Matrix.one_mul, one_mul] at h
    exact Units.ext (smul_left_injective ℂ (hS g x) (by simpa using h.symm))

end LSymbol

end TNLean.Algebra
