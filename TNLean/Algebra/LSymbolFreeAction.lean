/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Cohomology.StabilizerCocycleReconstruction
import QICLean.Algebra.Cohomology.KleinCocycleTable

/-!
# L-symbols on a free transitive action

For a fixed three-cocycle, compatible scalar L-symbols on a free transitive
action are related by an action-tensor gauge. This is the trivial-stabilizer
case of arXiv:2203.12563, Section 4.1, and the uniqueness assertion used in
the four-block example of Section 6.

It also contains the following results.

* `LSymbol.exists_regular_actionGaugeEquiv_of_kleinCocycleFamily_one`,
  `LSymbol.apply_self_of_kleinCocycleFamily`: Klein-four L-symbol classes and diagonal signs.
-/

namespace LSymbol

section LSymbolFreeAction

variable {G : Type} {X : Type*} [Group G] [MulAction G X]

/-- On a free transitive action, the action gauge relates any two L-symbols
compatible with the same three-cochain. This is the trivial-stabilizer case
of arXiv:2203.12563, Section 4.1, lines 740–761. -/
theorem actionGaugeEquiv_of_bijective_smul
    {L₁ L₂ : LSymbol G X} {ω : ScalarThreeCochain G}
    (h₁ : IsCompatible L₁ ω) (h₂ : IsCompatible L₂ ω)
    (x₀ : X) (hx : Function.Bijective (fun g : G ↦ g • x₀)) :
    ActionGaugeEquiv L₁ L₂ := by
  classical
  let e : G ≃ X := Equiv.ofBijective _ hx
  refine ⟨fun g x ↦ L₂ x₀ g (e.symm x) / L₁ x₀ g (e.symm x), ?_⟩
  funext x g h
  obtain ⟨k, rfl⟩ := hx.surjective x
  have he (k : G) : e.symm (k • x₀) = k := e.symm_apply_apply k
  simp only [gauge, ← mul_smul, he, mul_one]
  have hv (L : LSymbol G X) (hL : IsCompatible L ω) :
      L (k • x₀) g h = (L x₀ g (h * k) * L x₀ h k) /
        (ω g h k * L x₀ (g * h) k) := by
    apply (eq_div_iff_mul_eq').2
    calc
      _ = ω g h k * L (k • x₀) g h * L x₀ (g * h) k := by ac_rfl
      _ = _ := (hL x₀ g h k).symm
  rw [hv L₁ h₁, hv L₂ h₂]
  apply Units.ext
  push_cast
  field_simp

/-- The regular action admits the cocycle solution from arXiv:2203.12563,
Section 6, line 1888. The inverse reflects the compatibility convention
`eq:omega_and_Ls` of arXiv:2502.20257. -/
theorem isCompatible_regular {ω : ScalarThreeCochain G} (hω : ω.IsCocycle) :
    IsCompatible (fun x g h : G ↦ (ω g h x)⁻¹) ω := by
  intro x g h k
  have he := hω g h k x
  apply Units.ext
  have he' := congrArg Units.val he
  push_cast at he' ⊢
  field_simp
  simpa only [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using he'

end LSymbolFreeAction

section KleinCocyclePhase

/-!
## Klein-four L-symbol classes and diagonal signs

For the `(1,1,1)` cocycle, every nonempty transitive compatible block action
is the regular action, and all compatible L-symbols become the regular
cocycle solution after relabeling and an action-tensor gauge.
This proves the scalar uniqueness assertion in arXiv:2203.12563, Section 6,
`Papers/2203.12563/REsubmission.tex`, line 1888.
Normalized diagonal L-symbols obey the restriction signs of every
Klein-four representative, including the two-block sign relation of line 1886.
-/

open ScalarThreeCochain Multiplicative

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

/-- For `g = ofAdd (u, v)`, the diagonal L-symbol relation
`Lˣ_{g,g} = (-1) ^ (p u + q v + r u v) L^{g • x}_{g,g}` for every row of the Klein-four table
in arXiv:2203.12563, lines 1856–1886. The type-II row at `(1,1)` gives the
opposite signs on the two blocks it exchanges (`ab` in arXiv:2203.12563,
line 1886). -/
theorem apply_self_of_kleinCocycleFamily {X : Type*}
    [MulAction (Multiplicative (ZMod 2 × ZMod 2)) X]
    {L : LSymbol (Multiplicative (ZMod 2 × ZMod 2)) X}
    {p q r : ZMod 2} (hL : IsCompatible L (kleinCocycleFamily p q r))
    (hn : IsNormalized L) (x : X) (u v : ZMod 2) :
    L x (ofAdd (u, v)) (ofAdd (u, v)) =
      (-1) ^ (p * u + q * v + r * u * v).val *
        L (ofAdd (u, v) • x) (ofAdd (u, v)) (ofAdd (u, v)) := by
  have hg : ofAdd (u, v) * ofAdd (u, v) = (1 : Multiplicative (ZMod 2 × ZMod 2)) := by
    change ofAdd (u + u, v + v) = ofAdd (0, 0)
    simp [← two_mul, show (2 : ZMod 2) = 0 from rfl]
  have hsquare (z : ZMod 2) : z * z = z := by revert z; decide
  simpa only [kleinCocycleFamily, toAdd_ofAdd, mul_assoc, hsquare] using
    hL.apply_involution hn x hg

end KleinCocyclePhase

end LSymbol
