/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.KleinCocycleTable
import TNLean.Algebra.LSymbolFreeAction

/-!
# The four-block Klein-four L-symbol class

For the `(1,1,1)` cocycle, every nonempty transitive compatible block action
is the regular action, and all compatible L-symbols become the regular
cocycle solution after relabeling and an action-tensor gauge.
This proves the scalar uniqueness assertion in arXiv:2203.12563, Section 6,
`Papers/2203.12563/REsubmission.tex`, line 1888.
-/

namespace TNLean.Algebra.LSymbol

open ScalarThreeCochain

/-- The last-row solution of arXiv:2203.12563, line 1888, is unique up to
relabeling the blocks and action-tensor gauge. No tensor realization is assumed
or constructed in this scalar classification. -/
theorem exists_regular_actionGaugeEquiv_of_kleinCocycleFamily_one
    {X : Type*} [MulAction (Multiplicative (ZMod 2 × ZMod 2)) X]
    [MulAction.IsPretransitive (Multiplicative (ZMod 2 × ZMod 2)) X]
    {L : LSymbol (Multiplicative (ZMod 2 × ZMod 2)) X}
    (hL : IsCompatible L (kleinCocycleFamily 1 1 1)) (x₀ : X) :
    ∃ e : Multiplicative (ZMod 2 × ZMod 2) ≃ X,
      (∀ g k, e (g * k) = g • e k) ∧
      ActionGaugeEquiv (fun x g h ↦ L (e x) g h)
        (fun x g h ↦ kleinCocycleFamily 1 1 1 g h x) := by
  let : IsCancelSMul (Multiplicative (ZMod 2 × ZMod 2)) X :=
    isCancelSMul_iff_stabilizer_eq_bot.mpr
      (stabilizer_eq_bot_of_kleinCocycleFamily_one hL)
  let e : Multiplicative (ZMod 2 × ZMod 2) ≃ X :=
    Equiv.ofBijective (fun g ↦ g • x₀)
      ⟨fun g h he ↦ IsCancelSMul.right_cancel g h x₀ he,
        MulAction.surjective_smul _ x₀⟩
  have he (g k) : e (g * k) = g • e k := mul_smul g k x₀
  refine ⟨e, he, ?_⟩
  refine actionGaugeEquiv_of_bijective_smul
    (ω := kleinCocycleFamily 1 1 1) ?_ ?_ 1 ?_
  · intro x g h k
    simpa only [smul_eq_mul, he] using hL (e x) g h k
  · simpa only [kleinCocycleFamily, ← inv_pow, inv_neg, inv_one] using
      isCompatible_regular (kleinCocycleFamily_isCocycle 1 1 1)
  · constructor
    · intro a b h
      simpa only [smul_eq_mul, mul_one] using h
    · intro a
      exact ⟨a, mul_one a⟩

end TNLean.Algebra.LSymbol
