/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ScalarThreeCocycleCyclicInvariant
import TNLean.Algebra.StabilizerCocycleLSymbol

/-!
# Reconstruction of L-symbols from stabilizer data

This file formalizes the scalar classification of L-symbols for a transitive group action in
arXiv:2203.12563, `Papers/2203.12563/REsubmission.tex` lines 740--761: the reconstruction
formula `Lexpre` (Equation (20), lines 752--759), the fact that every compatible L-symbol is of
that form up to an action-tensor gauge, and the `H²(H, ℂˣ)`-torsor structure of the gauge
classes of solutions stated at line 761.

Fix representatives `k_x` for a transitive action with basepoint `x₀`, stabilizer
`H = Stab_G(x₀)`, and transition elements `t_k(g,x) = k_(g • x)⁻¹ g k_x`. For a scalar
three-cochain `ω` on `G` and a scalar two-cochain `ψ` on `H`, Equation (20) reads
`Lˣ_{g₁,g₂} = ω(g₁g₂k_x, h₂⁻¹, h₁⁻¹) ψ(h₁,h₂) / (ω(g₁, g₂k_x, h₂⁻¹) ω(g₁,g₂,k_x))`
with `h₂ = t_k(g₂,x)` and `h₁ = t_k(g₁,g₂ • x)`.

**Local fix (fusion gauge of Equation (20)):** Equation (20) satisfies `pentagongroups`
(line 715) when `ω` is a three-cocycle equal to one at every triple of stabilizer elements; if
`ω|_H = dβ` with `β` not constant, the printed formula with a two-cocycle `ψ` is in general not
compatible. The source fixes this gauge only by the phrase "given `ω` and `β` by fixing some
gauge" at line 761. A fusion gauge making `ω` trivial on `H` always exists
(`exists_fusionGauge_eq_one_of_isTrivialGaugeClass_comap`), and in that gauge the formula is
exactly the printed one. See `docs/paper-gaps/glm23_eq20_fusion_gauge.tex`.

The torsor statement concerns action-tensor gauge classes with the fusion gauge held fixed, as
at line 761. The library gauge `LSymbol.gauge` is the reciprocal of the source's `gdgroup`
(line 718); with trivial fusion gauge this only replaces `γ` by `γ⁻¹` and defines the same
equivalence relation.

## Main definitions

* `LSymbol.ActionGaugeEquiv`: equality up to an action-tensor gauge.
* `StabilizerRepresentatives.reconstructedLSymbol`: the L-symbol of Equation (20).
* `StabilizerRepresentatives.solutionSetoid`: action-gauge classes of compatible L-symbols.
* `StabilizerRepresentatives.solutionAction`: the action of `H²(H, ℂˣ)` on solution classes by
  multiplication with induced L-symbols.
* `StabilizerRepresentatives.h2EquivSolutionClasses`: the bijection `H²(H, ℂˣ) ≃` solution
  classes determined by a base solution.

## Main results

* `ScalarThreeCochain.exists_fusionGauge_eq_one_of_isTrivialGaugeClass_comap`: a fusion gauge
  making `ω` trivial on a subgroup on which it is a coboundary.
* `StabilizerRepresentatives.reconstructedLSymbol_isCompatible`: Equation (20) is compatible,
  and `StabilizerRepresentatives.reconstructedLSymbol_base`: its basepoint restriction is `ψ`.
* `StabilizerRepresentatives.exists_actionGauge_eq_inducedLSymbol`: for `ω = 1`, every
  compatible L-symbol is an action gauge of the L-symbol induced by its basepoint restriction.
* `StabilizerRepresentatives.exists_actionGauge_eq_reconstructedLSymbol`: every compatible
  L-symbol is an action gauge of Equation (20); `exists_actionGauge_gauge_eq_reconstructedLSymbol`
  and `gauge_reconstructedLSymbol_isCompatible` transport both directions to any fusion gauge.
* `StabilizerRepresentatives.isCompatible_iff_exists_actionGauge_mul_inducedLSymbol` and
  `StabilizerRepresentatives.actionGaugeEquiv_mul_inducedLSymbol_iff`: transitivity and freeness
  of the `H²(H, ℂˣ)` action on solution classes, packaged as the bijection
  `StabilizerRepresentatives.h2EquivSolutionClasses`; the torsor laws of `solutionAction` are
  `solutionAction_mk_mk_mul` (compatibility with the product of cocycles) and
  `existsUnique_solutionAction_eq` (free and transitive).

No finiteness, normalization, or tensor assumption is used.

## References

* arXiv:2203.12563, Section 4.2, `Papers/2203.12563/REsubmission.tex` lines 740--761.
* `docs/paper-gaps/glm23_eq20_fusion_gauge.tex`.
-/

namespace TNLean.Algebra

variable {G X : Type*} [Group G] [MulAction G X]

namespace LSymbol

/-- Compatibility is multiplicative: pointwise products of compatible L-symbols are compatible
with the pointwise product of the three-cochains. -/
theorem IsCompatible.mul {L₁ L₂ : LSymbol G X} {ω₁ ω₂ : ScalarThreeCochain G}
    (h₁ : IsCompatible L₁ ω₁) (h₂ : IsCompatible L₂ ω₂) :
    IsCompatible (L₁ * L₂) (ω₁ * ω₂) := by
  intro x g h k
  simp only [Pi.mul_apply]
  calc
    _ = (L₁ x g (h * k) * L₁ x h k) * (L₂ x g (h * k) * L₂ x h k) := by ac_rfl
    _ = (ω₁ g h k * L₁ (k • x) g h * L₁ x (g * h) k) *
        (ω₂ g h k * L₂ (k • x) g h * L₂ x (g * h) k) := by rw [h₁, h₂]
    _ = _ := by ac_rfl

/-- The pointwise inverse of a compatible L-symbol is compatible with the inverse
three-cochain. -/
theorem IsCompatible.inv {L : LSymbol G X} {ω : ScalarThreeCochain G}
    (hL : IsCompatible L ω) : IsCompatible L⁻¹ ω⁻¹ := by
  intro x g h k
  simp only [Pi.inv_apply]
  rw [← mul_inv, hL x g h k, mul_inv, mul_inv]

/-- The ratio of two L-symbols compatible with the same three-cochain is compatible with the
trivial three-cochain. -/
theorem IsCompatible.mul_inv_one {L L₀ : LSymbol G X} {ω : ScalarThreeCochain G}
    (hL : IsCompatible L ω) (hL₀ : IsCompatible L₀ ω) :
    IsCompatible (L * L₀⁻¹) (fun _ _ _ ↦ 1) := by
  have h := hL.mul hL₀.inv
  rw [mul_inv_cancel] at h
  exact h

/-- An action-tensor gauge with trivial fusion gauge commutes with multiplication by a fixed
L-symbol. -/
theorem gauge_one_mul (γ : ActionTensorGauge G X) (L₁ L₂ : LSymbol G X) :
    gauge (fun _ _ ↦ 1) γ (L₁ * L₂) = L₁ * gauge (fun _ _ ↦ 1) γ L₂ := by
  funext x g h
  simp only [gauge, Pi.mul_apply]
  ac_rfl

/-- An action-tensor gauge with trivial fusion gauge preserves compatibility with the same
three-cochain. -/
theorem IsCompatible.gauge_one {L : LSymbol G X} {ω : ScalarThreeCochain G}
    (hL : IsCompatible L ω) (γ : ActionTensorGauge G X) :
    IsCompatible (LSymbol.gauge (fun _ _ ↦ 1) γ L) ω := by
  simpa only [ScalarThreeCochain.fusionGauge_one] using hL.gauge (fun _ _ ↦ 1) γ

/-- Two L-symbols are action-gauge equivalent when they differ by an action-tensor gauge and
the trivial fusion-tensor gauge. This is the equivalence relation of arXiv:2203.12563,
`gdgroup` (`REsubmission.tex` line 718), with the fusion gauge `β` fixed as at line 761. -/
def ActionGaugeEquiv (L₁ L₂ : LSymbol G X) : Prop :=
  ∃ γ : ActionTensorGauge G X, L₁ = gauge (fun _ _ ↦ 1) γ L₂

/-- Action-gauge equivalence is an equivalence relation. -/
theorem actionGaugeEquiv_equivalence : Equivalence (ActionGaugeEquiv (G := G) (X := X)) where
  refl L := ⟨fun _ _ ↦ 1, (gauge_one L).symm⟩
  symm := by
    rintro L₁ L₂ ⟨γ, rfl⟩
    refine ⟨γ⁻¹, ?_⟩
    rw [gauge_comp]
    funext x g h
    simp [gauge]
  trans := by
    rintro L₁ L₂ L₃ ⟨γ₁, rfl⟩ ⟨γ₂, rfl⟩
    refine ⟨γ₂ * γ₁, ?_⟩
    rw [gauge_comp]
    funext x g h
    simp [gauge]

/-- For an L-symbol compatible with the trivial three-cochain, its restriction to the
basepoint and to stabilizer arguments is a scalar two-cocycle. -/
theorem IsCompatible.isCocycle_restrict {L : LSymbol G X}
    (hL : IsCompatible L (fun _ _ _ ↦ 1)) (x₀ : X) :
    ScalarCocycle.IsCocycle
      (fun a b : MulAction.stabilizer G x₀ ↦ L x₀ (a : G) (b : G)) := by
  intro a b c
  have h := hL x₀ a b c
  rw [show (c : G) • x₀ = x₀ from MulAction.mem_stabilizer_iff.mp c.property, one_mul] at h
  simpa only [Subgroup.coe_mul] using h.symm

end LSymbol

namespace ScalarThreeCochain

/-- **A trivializing fusion gauge on a subgroup.** If the restriction of `ω` to a subgroup `H`
has trivial gauge class, some fusion gauge on `G` makes `ω` equal to one at every triple of
elements of `H`. The gauge extends the inverse of a trivializing two-cochain on `H` by one.

Source: arXiv:2203.12563, `REsubmission.tex` lines 744--745, where `ω|_H = dβ` is absorbed
into the gauge of the fusion tensors. -/
theorem exists_fusionGauge_eq_one_of_isTrivialGaugeClass_comap {ω : ScalarThreeCochain G}
    {H : Subgroup G} (hω : IsTrivialGaugeClass (comap H.subtype ω)) :
    ∃ β : ScalarCocycle G, ∀ a b c : H, fusionGauge β ω a b c = 1 := by
  classical
  obtain ⟨β₀, hβ₀⟩ := hω
  refine ⟨fun g h ↦ if hg : g ∈ H then if hh : h ∈ H then (β₀ ⟨g, hg⟩ ⟨h, hh⟩)⁻¹ else 1
    else 1, fun a b c ↦ ?_⟩
  have hω₀ := congrFun (congrFun (congrFun hβ₀ a) b) c
  simp only [fusionGauge, coboundary, mul_one, comap_apply, Subgroup.coe_subtype] at hω₀
  simp only [fusionGauge, coboundary, a.property, b.property, c.property,
    H.mul_mem a.property b.property, H.mul_mem b.property c.property, dite_true, ← hω₀]
  simp only [Subtype.coe_eta, ← Subgroup.coe_mul]
  apply Units.ext
  push_cast
  field_simp

end ScalarThreeCochain

namespace StabilizerRepresentatives

variable {x₀ : X}

/-- The L-symbol of arXiv:2203.12563, Equation (20) (`Lexpre`, `REsubmission.tex`
lines 752--759):

`Lˣ_{g₁,g₂} = ω(g₁g₂k_x, h₂⁻¹, h₁⁻¹) ψ(h₁,h₂) / (ω(g₁, g₂k_x, h₂⁻¹) ω(g₁,g₂,k_x))`,

where `h₂ = t_k(g₂,x)` and `h₁ = t_k(g₁,g₂ • x)` are the transition elements defined by
`g₂k_x = k_(g₂ • x) h₂` and `g₁k_(g₂ • x) = k_(g₁g₂ • x) h₁` at line 759. -/
def reconstructedLSymbol (K : StabilizerRepresentatives G X x₀) (ω : ScalarThreeCochain G)
    (ψ : ScalarCocycle (MulAction.stabilizer G x₀)) : LSymbol G X :=
  fun x g₁ g₂ ↦
    ω (g₁ * g₂ * K.k x) (K.transitionElement g₂ x : G)⁻¹
          (K.transitionElement g₁ (g₂ • x) : G)⁻¹ *
        ψ (K.transitionElement g₁ (g₂ • x)) (K.transitionElement g₂ x) /
      (ω g₁ (g₂ * K.k x) (K.transitionElement g₂ x : G)⁻¹ * ω g₁ g₂ (K.k x))

/-- Equation (20) factors as its `ψ = 1` part times the L-symbol induced by `ψ`. -/
theorem reconstructedLSymbol_eq_mul (K : StabilizerRepresentatives G X x₀)
    (ω : ScalarThreeCochain G) (ψ : ScalarCocycle (MulAction.stabilizer G x₀)) :
    K.reconstructedLSymbol ω ψ = K.reconstructedLSymbol ω 1 * K.inducedLSymbol ψ := by
  funext x g h
  simp only [reconstructedLSymbol, inducedLSymbol, Pi.mul_apply, Pi.one_apply, mul_one,
    div_eq_mul_inv]
  ac_rfl

/-- In a fusion gauge in which `ω` is one on the stabilizer, the basepoint restriction of
Equation (20) is `ψ`. This is the identification `ψ = L|_H` of arXiv:2203.12563, line 747,
with the trivializing two-cochain equal to one. -/
theorem reconstructedLSymbol_base (K : StabilizerRepresentatives G X x₀)
    {ω : ScalarThreeCochain G} (hH : ∀ a b c : MulAction.stabilizer G x₀, ω a b c = 1)
    (ψ : ScalarCocycle (MulAction.stabilizer G x₀)) (a b : MulAction.stabilizer G x₀) :
    K.reconstructedLSymbol ω ψ x₀ (a : G) (b : G) = ψ a b := by
  have hb : (b : G) • x₀ = x₀ := MulAction.mem_stabilizer_iff.mp b.property
  simp only [reconstructedLSymbol, hb, transitionElement_stabilizer, K.k_x₀, mul_one]
  have h₁ := hH (a * b) b⁻¹ a⁻¹
  have h₂ := hH a b b⁻¹
  have h₃ := hH a b 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one] at h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  simp

/-- The four-term three-cocycle identity behind the compatibility of Equation (20). Here
`p = k_x`, and `a = t_k(k,x)`, `b = t_k(h,k • x)`, `c = t_k(g,hk • x)`, so that
`k_(k • x) = k p a⁻¹`. Four instances of the three-cocycle equation, at `(g,h,k,p)`,
`(g,h,kp,a⁻¹)`, `(g,hkp,a⁻¹,b⁻¹)` and `(ghkp,a⁻¹,b⁻¹,c⁻¹)`, together with
`ω(a⁻¹,b⁻¹,c⁻¹) = 1`, give the compatibility equation. -/
private theorem reconstruction_core {ω : ScalarThreeCochain G}
    (hω : ScalarThreeCochain.IsCocycle ω) (g h k p a b c : G)
    (habc : ω a⁻¹ b⁻¹ c⁻¹ = 1) :
    ω (g * (h * (k * p))) (a⁻¹ * b⁻¹) c⁻¹ /
          (ω g (h * (k * p)) (a⁻¹ * b⁻¹) * ω g (h * k) p) *
        (ω (h * (k * p)) a⁻¹ b⁻¹ / (ω h (k * p) a⁻¹ * ω h k p)) =
      ω g h k *
          (ω (g * (h * (k * (p * a⁻¹)))) b⁻¹ c⁻¹ /
            (ω g (h * (k * (p * a⁻¹))) b⁻¹ * ω g h (k * (p * a⁻¹)))) *
        (ω (g * (h * (k * p))) a⁻¹ (b⁻¹ * c⁻¹) /
          (ω (g * h) (k * p) a⁻¹ * ω (g * h) k p)) := by
  have h₁ := hω g h k p
  have h₂ := hω g h (k * p) a⁻¹
  have h₃ := hω g (h * (k * p)) a⁻¹ b⁻¹
  have h₄ := hω (g * (h * (k * p))) a⁻¹ b⁻¹ c⁻¹
  simp only [mul_assoc] at h₁ h₂ h₃ h₄
  rw [← div_eq_one]
  calc
    _ = ω (g * h) k p * ω g h (k * p) / (ω g h k * (ω g (h * k) p * ω h k p)) *
          (ω (g * h) (k * p) a⁻¹ * ω g h (k * (p * a⁻¹)) /
            (ω g h (k * p) * (ω g (h * (k * p)) a⁻¹ * ω h (k * p) a⁻¹))) /
          ((ω (g * (h * (k * p))) a⁻¹ b⁻¹ * ω g (h * (k * p)) (a⁻¹ * b⁻¹) /
              (ω g (h * (k * p)) a⁻¹ * (ω g (h * (k * (p * a⁻¹))) b⁻¹ *
                ω (h * (k * p)) a⁻¹ b⁻¹))) *
            (ω (g * (h * (k * (p * a⁻¹)))) b⁻¹ c⁻¹ * ω (g * (h * (k * p))) a⁻¹ (b⁻¹ * c⁻¹) /
              (ω (g * (h * (k * p))) a⁻¹ b⁻¹ * (ω (g * (h * (k * p))) (a⁻¹ * b⁻¹) c⁻¹ *
                ω a⁻¹ b⁻¹ c⁻¹)))) / ω a⁻¹ b⁻¹ c⁻¹ := by
      apply Units.ext
      push_cast
      field_simp
    _ = 1 := by rw [h₁, h₂, h₃, h₄, habc]; simp

/-- **Compatibility of Equation (20) with `ψ = 1`.** If `ω` is a three-cocycle equal to one
at every triple of stabilizer elements, the L-symbol of arXiv:2203.12563, Equation (20), with
`ψ = 1` satisfies `pentagongroups` (line 715). No normalization of `ω` is needed. -/
theorem reconstructedLSymbol_one_isCompatible (K : StabilizerRepresentatives G X x₀)
    {ω : ScalarThreeCochain G} (hω : ScalarThreeCochain.IsCocycle ω)
    (hH : ∀ a b c : MulAction.stabilizer G x₀, ω a b c = 1) :
    LSymbol.IsCompatible (K.reconstructedLSymbol ω 1) ω := by
  intro x g h k
  have habc := hH (K.transitionElement k x)⁻¹ (K.transitionElement h (k • x))⁻¹
    (K.transitionElement g (h • k • x))⁻¹
  have hq : K.k (k • x) = k * (K.k x * (K.transitionElement k x : G)⁻¹) := by
    simp [coe_transitionElement, mul_assoc]
  simp only [reconstructedLSymbol, Pi.one_apply, mul_one, K.transitionElement_mul, mul_smul,
    Subgroup.coe_mul, mul_inv_rev, mul_assoc, hq, Subgroup.coe_inv] at habc ⊢
  generalize (K.transitionElement k x : G) = a at habc ⊢
  generalize (K.transitionElement h (k • x) : G) = b at habc ⊢
  generalize (K.transitionElement g (h • k • x) : G) = c at habc ⊢
  simpa only [mul_assoc] using reconstruction_core hω g h k (K.k x) a b c habc

/-- **Compatibility of Equation (20).** If `ω` is a three-cocycle equal to one at every triple
of stabilizer elements and `ψ` is a two-cocycle on the stabilizer, the L-symbol of
arXiv:2203.12563, Equation (20) (`REsubmission.tex` lines 752--759) satisfies
`pentagongroups` (line 715). The hypothesis `hH` is the fusion gauge of the local fix
recorded in the module docstring. -/
theorem reconstructedLSymbol_isCompatible (K : StabilizerRepresentatives G X x₀)
    {ω : ScalarThreeCochain G} (hω : ScalarThreeCochain.IsCocycle ω)
    (hH : ∀ a b c : MulAction.stabilizer G x₀, ω a b c = 1)
    {ψ : ScalarCocycle (MulAction.stabilizer G x₀)} (hψ : ψ.IsCocycle) :
    LSymbol.IsCompatible (K.reconstructedLSymbol ω ψ) ω := by
  rw [reconstructedLSymbol_eq_mul]
  have h := (K.reconstructedLSymbol_one_isCompatible hω hH).mul (K.inducedLSymbol_isCompatible hψ)
  rwa [show (fun _ _ _ ↦ (1 : Units ℂ)) = (1 : ScalarThreeCochain G) from rfl, mul_one] at h

/-- **Equation (20) in an arbitrary fusion gauge.** If a fusion gauge `β` makes `ω` equal to
one on the stabilizer, transporting Equation (20) for `dβ · ω` back by `β⁻¹` gives an
L-symbol compatible with `ω` itself. -/
theorem gauge_reconstructedLSymbol_isCompatible (K : StabilizerRepresentatives G X x₀)
    {ω : ScalarThreeCochain G} (hω : ScalarThreeCochain.IsCocycle ω) (β : ScalarCocycle G)
    (hβ : ∀ a b c : MulAction.stabilizer G x₀,
      ScalarThreeCochain.fusionGauge β ω a b c = 1)
    {ψ : ScalarCocycle (MulAction.stabilizer G x₀)} (hψ : ψ.IsCocycle) :
    LSymbol.IsCompatible
      (LSymbol.gauge β⁻¹ (fun _ _ ↦ 1)
        (K.reconstructedLSymbol (ScalarThreeCochain.fusionGauge β ω) ψ)) ω := by
  have h := (K.reconstructedLSymbol_isCompatible (hω.fusionGauge β) hβ hψ).gauge β⁻¹
    (fun _ _ ↦ 1)
  rwa [ScalarThreeCochain.fusionGauge_comp, mul_inv_cancel,
    show (1 : ScalarCocycle G) = fun _ _ ↦ 1 from rfl,
    ScalarThreeCochain.fusionGauge_one] at h

/-- **Surjectivity for the trivial three-cochain.** Every L-symbol `R` compatible with the
trivial three-cochain is an action gauge of the L-symbol induced by its basepoint restriction
`ψ(a,b) = R^{x₀}_{a,b}`. The gauge is
`γ_{g,x} = R^{x₀}_{k_(g • x), t_k(g,x)} / R^{x₀}_{g,k_x}`.

This is the `ω = 1` case of the classification in arXiv:2203.12563, lines 749--759. -/
theorem exists_actionGauge_eq_inducedLSymbol (K : StabilizerRepresentatives G X x₀)
    {R : LSymbol G X} (hR : LSymbol.IsCompatible R (fun _ _ _ ↦ 1)) :
    ∃ γ : ActionTensorGauge G X,
      R = LSymbol.gauge (fun _ _ ↦ 1) γ
        (K.inducedLSymbol (fun a b ↦ R x₀ (a : G) (b : G))) := by
  refine ⟨fun g x ↦ R x₀ (K.k (g • x)) (K.transitionElement g x) / R x₀ g (K.k x), ?_⟩
  funext x g h
  have hkx : K.k x • x₀ = x := K.k_smul_x₀ x
  have hfix : ∀ t : MulAction.stabilizer G x₀, (t : G) • x₀ = x₀ :=
    fun t ↦ MulAction.mem_stabilizer_iff.mp t.property
  have e₁ : h * K.k x = K.k (h • x) * K.transitionElement h x := by
    simp [coe_transitionElement, mul_assoc]
  have e₂ : g * K.k (h • x) = K.k (g • h • x) * K.transitionElement g (h • x) := by
    simp [coe_transitionElement, mul_assoc]
  have h₁ := hR x₀ g h (K.k x)
  have h₂ := hR x₀ g (K.k (h • x)) (K.transitionElement h x)
  have h₃ := hR x₀ (K.k (g • h • x)) (K.transitionElement g (h • x))
    (K.transitionElement h x)
  rw [hkx, e₁] at h₁
  rw [hfix, e₂] at h₂
  rw [hfix] at h₃
  simp only [LSymbol.gauge, inducedLSymbol, mul_one, K.transitionElement_mul, mul_smul,
    Subgroup.coe_mul]
  simp only [one_mul] at h₁ h₂ h₃
  generalize R x₀ g (K.k (h • x) * K.transitionElement h x) = A at h₁ h₂ ⊢
  generalize R x₀ (K.k (g • h • x) * K.transitionElement g (h • x))
    (K.transitionElement h x) = F at h₂ h₃ ⊢
  generalize R x g h = T at h₁ ⊢
  apply Units.ext
  have h₁' := congrArg Units.val h₁
  have h₂' := congrArg Units.val h₂
  have h₃' := congrArg Units.val h₃
  push_cast at h₁' h₂' h₃' ⊢
  field_simp
  linear_combination
    (-(R x₀ (K.k (g • h • x)) (K.transitionElement g (h • x)) : ℂ) *
        (R x₀ (K.k (h • x)) (K.transitionElement h x) : ℂ)) * h₁' +
      (R x₀ h (K.k x) : ℂ) * (R x₀ (K.k (g • h • x)) (K.transitionElement g (h • x)) : ℂ) * h₂' -
      (R x₀ g (K.k (h • x)) : ℂ) * (R x₀ h (K.k x) : ℂ) * h₃'

/-- **Transitivity of the `H²` action.** Let `L₀` be compatible with `ω`. An L-symbol is
compatible with `ω` exactly when it is an action gauge of `L₀` times the L-symbol induced by a
two-cocycle on the stabilizer. No cocycle hypothesis on `ω` is needed.

This is the statement "the solutions of `L|_H` are a `𝒢`-torsor" of arXiv:2203.12563,
`REsubmission.tex` line 761, in the part asserting that any two solutions are related by an
element of `H²(H, ℂˣ)`. -/
theorem isCompatible_iff_exists_actionGauge_mul_inducedLSymbol
    (K : StabilizerRepresentatives G X x₀) {ω : ScalarThreeCochain G} {L₀ : LSymbol G X}
    (hL₀ : LSymbol.IsCompatible L₀ ω) (L : LSymbol G X) :
    LSymbol.IsCompatible L ω ↔
      ∃ ψ : ScalarCocycle (MulAction.stabilizer G x₀), ψ.IsCocycle ∧
        ∃ γ : ActionTensorGauge G X,
          L = LSymbol.gauge (fun _ _ ↦ 1) γ (L₀ * K.inducedLSymbol ψ) := by
  constructor
  · intro hL
    have hR := hL.mul_inv_one hL₀
    obtain ⟨γ, hγ⟩ := K.exists_actionGauge_eq_inducedLSymbol hR
    refine ⟨_, hR.isCocycle_restrict x₀, γ, ?_⟩
    rw [LSymbol.gauge_one_mul, ← hγ]
    simp
  · rintro ⟨ψ, hψ, γ, rfl⟩
    have h := hL₀.mul (K.inducedLSymbol_isCompatible hψ)
    rw [show (fun _ _ _ ↦ (1 : Units ℂ)) = (1 : ScalarThreeCochain G) from rfl, mul_one] at h
    exact h.gauge_one γ

/-- **Freeness of the `H²` action.** Multiplying a fixed L-symbol by the L-symbols induced by
two stabilizer two-cochains gives action-gauge equivalent results exactly when the two-cochains
are cohomologous.

This is the part of arXiv:2203.12563, line 761, identifying distinct solutions with distinct
elements of `H²(H, ℂˣ)`. -/
theorem actionGaugeEquiv_mul_inducedLSymbol_iff (K : StabilizerRepresentatives G X x₀)
    (L₀ : LSymbol G X) (ψ₁ ψ₂ : ScalarCocycle (MulAction.stabilizer G x₀)) :
    LSymbol.ActionGaugeEquiv (L₀ * K.inducedLSymbol ψ₁) (L₀ * K.inducedLSymbol ψ₂) ↔
      ScalarCocycle.CohomologousTo ψ₁ ψ₂ := by
  rw [K.cohomologousTo_iff_exists_actionGauge_inducedLSymbol_eq]
  simp only [LSymbol.ActionGaugeEquiv, LSymbol.gauge_one_mul, mul_right_inj]

/-- **Classification in a trivializing fusion gauge.** If `ω` is a three-cocycle equal to one at
every triple of stabilizer elements, every L-symbol compatible with `ω` is an action gauge of
the L-symbol of Equation (20) for some two-cocycle `ψ` on the stabilizer.

Source: arXiv:2203.12563, `REsubmission.tex` lines 749--759. -/
theorem exists_actionGauge_eq_reconstructedLSymbol (K : StabilizerRepresentatives G X x₀)
    {ω : ScalarThreeCochain G} (hω : ScalarThreeCochain.IsCocycle ω)
    (hH : ∀ a b c : MulAction.stabilizer G x₀, ω a b c = 1) {L : LSymbol G X}
    (hL : LSymbol.IsCompatible L ω) :
    ∃ ψ : ScalarCocycle (MulAction.stabilizer G x₀), ψ.IsCocycle ∧
      ∃ γ : ActionTensorGauge G X,
        L = LSymbol.gauge (fun _ _ ↦ 1) γ (K.reconstructedLSymbol ω ψ) := by
  obtain ⟨ψ, hψ, γ, hγ⟩ :=
    (K.isCompatible_iff_exists_actionGauge_mul_inducedLSymbol
      (K.reconstructedLSymbol_one_isCompatible hω hH) L).1 hL
  exact ⟨ψ, hψ, γ, by rw [hγ, K.reconstructedLSymbol_eq_mul ω ψ]⟩

/-- **Classification in an arbitrary fusion gauge.** If a fusion gauge `β` makes the
three-cocycle `ω` equal to one on the stabilizer, then for every L-symbol `L` compatible with
`ω`, its fusion-gauge transform by `β` is an action gauge of Equation (20) for `dβ · ω`. -/
theorem exists_actionGauge_gauge_eq_reconstructedLSymbol
    (K : StabilizerRepresentatives G X x₀) {ω : ScalarThreeCochain G}
    (hω : ScalarThreeCochain.IsCocycle ω) (β : ScalarCocycle G)
    (hβ : ∀ a b c : MulAction.stabilizer G x₀,
      ScalarThreeCochain.fusionGauge β ω a b c = 1)
    {L : LSymbol G X} (hL : LSymbol.IsCompatible L ω) :
    ∃ ψ : ScalarCocycle (MulAction.stabilizer G x₀), ψ.IsCocycle ∧
      ∃ γ : ActionTensorGauge G X,
        LSymbol.gauge β (fun _ _ ↦ 1) L =
          LSymbol.gauge (fun _ _ ↦ 1) γ
            (K.reconstructedLSymbol (ScalarThreeCochain.fusionGauge β ω) ψ) :=
  K.exists_actionGauge_eq_reconstructedLSymbol (hω.fusionGauge β) hβ
    (hL.gauge β (fun _ _ ↦ 1))

/-- The action-gauge classes of L-symbols compatible with a fixed three-cochain `ω`, with the
fusion gauge held fixed as in arXiv:2203.12563, line 761. -/
def solutionSetoid (ω : ScalarThreeCochain G) :
    Setoid {L : LSymbol G X // LSymbol.IsCompatible L ω} where
  r L₁ L₂ := LSymbol.ActionGaugeEquiv L₁.1 L₂.1
  iseqv := ⟨fun L ↦ LSymbol.actionGaugeEquiv_equivalence.refl L.1,
    fun h ↦ LSymbol.actionGaugeEquiv_equivalence.symm h,
    fun h₁₂ h₂₃ ↦ LSymbol.actionGaugeEquiv_equivalence.trans h₁₂ h₂₃⟩

/-- **The torsor of solutions.** A base solution `L₀` compatible with `ω` determines a
bijection from `H²(H, ℂˣ)` onto the action-gauge classes of L-symbols compatible with `ω`,
sending the class of `ψ` to the class of `L₀ · L[ψ]`, where `L[ψ]` is the induced L-symbol.
This is the torsor statement with the base point `L₀`: the action of `H²(H, ℂˣ)` by
multiplication with induced L-symbols is free and transitive on solution classes.

Source: arXiv:2203.12563, `REsubmission.tex` line 761. -/
noncomputable def h2EquivSolutionClasses (K : StabilizerRepresentatives G X x₀)
    {ω : ScalarThreeCochain G} {L₀ : LSymbol G X} (hL₀ : LSymbol.IsCompatible L₀ ω) :
    H2 (MulAction.stabilizer G x₀) ≃ Quotient (solutionSetoid (X := X) ω) :=
  Equiv.ofBijective
    (Quotient.map (sa := ScalarCocycle.IsCocycle.instSetoid) (sb := solutionSetoid ω)
      (fun ψ ↦ ⟨L₀ * K.inducedLSymbol ψ.1,
        ((K.isCompatible_iff_exists_actionGauge_mul_inducedLSymbol hL₀ _).2
          ⟨ψ.1, ψ.2, fun _ _ ↦ 1, (LSymbol.gauge_one _).symm⟩)⟩)
      (fun _ _ h ↦ (K.actionGaugeEquiv_mul_inducedLSymbol_iff L₀ _ _).2 h))
    ⟨by
      rintro ⟨ψ₁⟩ ⟨ψ₂⟩ h
      exact Quotient.sound ((K.actionGaugeEquiv_mul_inducedLSymbol_iff L₀ _ _).1
        (Quotient.exact h)),
    by
      rintro ⟨L⟩
      obtain ⟨ψ, hψ, γ, hγ⟩ :=
        (K.isCompatible_iff_exists_actionGauge_mul_inducedLSymbol hL₀ L.1).1 L.2
      exact ⟨Quotient.mk _ ⟨ψ, hψ⟩, Quotient.sound ⟨γ⁻¹, by
        rw [hγ, LSymbol.gauge_comp]
        funext x g h
        simp [LSymbol.gauge]⟩⟩⟩

/-- The bijection `h2EquivSolutionClasses` sends the class of `ψ` to the class of
`L₀ · L[ψ]`. -/
theorem h2EquivSolutionClasses_mk (K : StabilizerRepresentatives G X x₀)
    {ω : ScalarThreeCochain G} {L₀ : LSymbol G X} (hL₀ : LSymbol.IsCompatible L₀ ω)
    (ψ : {ψ : ScalarCocycle (MulAction.stabilizer G x₀) // ψ.IsCocycle}) :
    K.h2EquivSolutionClasses hL₀ (Quotient.mk _ ψ) =
      Quotient.mk (solutionSetoid ω) ⟨L₀ * K.inducedLSymbol ψ.1,
        ((K.isCompatible_iff_exists_actionGauge_mul_inducedLSymbol hL₀ _).2
          ⟨ψ.1, ψ.2, fun _ _ ↦ 1, (LSymbol.gauge_one _).symm⟩)⟩ :=
  rfl

/-- The action of a stabilizer cohomology class on action-gauge classes of solutions:
`[ψ] · [L] = [L · L[ψ]]`, where `L[ψ]` is the induced L-symbol. This is the action of
`𝒢 = H²(H, ℂˣ)` in arXiv:2203.12563, `REsubmission.tex` line 761. -/
def solutionAction (K : StabilizerRepresentatives G X x₀) {ω : ScalarThreeCochain G} :
    H2 (MulAction.stabilizer G x₀) → Quotient (solutionSetoid (X := X) ω) →
      Quotient (solutionSetoid (X := X) ω) :=
  Quotient.map₂ (sa := ScalarCocycle.IsCocycle.instSetoid) (sb := solutionSetoid ω)
    (sc := solutionSetoid ω)
    (fun ψ L ↦ ⟨L.1 * K.inducedLSymbol ψ.1, by
      have h := L.2.mul (K.inducedLSymbol_isCompatible ψ.2)
      rwa [show (fun _ _ _ ↦ (1 : Units ℂ)) = (1 : ScalarThreeCochain G) from rfl,
        mul_one] at h⟩)
    (by
      rintro ψ₁ ψ₂ hψ L₁ L₂ ⟨γ₁, hγ₁⟩
      obtain ⟨γ₂, hγ₂⟩ :=
        (K.cohomologousTo_iff_exists_actionGauge_inducedLSymbol_eq ψ₁.1 ψ₂.1).1 hψ
      refine ⟨γ₁ * γ₂, ?_⟩
      change L₁.1 * K.inducedLSymbol ψ₁.1 = _
      rw [hγ₁, hγ₂]
      funext x g h
      simp only [LSymbol.gauge, Pi.mul_apply, mul_one]
      apply Units.ext
      push_cast
      field_simp)

/-- The action on representatives: `[ψ] · [L] = [L · L[ψ]]`. -/
theorem solutionAction_mk (K : StabilizerRepresentatives G X x₀) {ω : ScalarThreeCochain G}
    (ψ : {ψ : ScalarCocycle (MulAction.stabilizer G x₀) // ψ.IsCocycle})
    (L : {L : LSymbol G X // LSymbol.IsCompatible L ω}) :
    K.solutionAction (Quotient.mk _ ψ) (Quotient.mk (solutionSetoid ω) L) =
      Quotient.mk (solutionSetoid ω) ⟨L.1 * K.inducedLSymbol ψ.1, by
        have h := L.2.mul (K.inducedLSymbol_isCompatible ψ.2)
        rwa [show (fun _ _ _ ↦ (1 : Units ℂ)) = (1 : ScalarThreeCochain G) from rfl,
          mul_one] at h⟩ :=
  rfl

/-- **Action law.** Acting by `[ψ₂]` and then by `[ψ₁]` is acting by the class of the pointwise
product `ψ₁ψ₂`, which is the product in `H²(H, ℂˣ)`. -/
theorem solutionAction_mk_mk_mul (K : StabilizerRepresentatives G X x₀)
    {ω : ScalarThreeCochain G}
    (ψ₁ ψ₂ : {ψ : ScalarCocycle (MulAction.stabilizer G x₀) // ψ.IsCocycle})
    (hψ : (ψ₁.1 * ψ₂.1).IsCocycle) (c : Quotient (solutionSetoid (X := X) ω)) :
    K.solutionAction (Quotient.mk _ ψ₁) (K.solutionAction (Quotient.mk _ ψ₂) c) =
      K.solutionAction (Quotient.mk _ ⟨ψ₁.1 * ψ₂.1, hψ⟩) c := by
  induction c using Quotient.ind with
  | _ L =>
    simp only [solutionAction_mk]
    congr 2
    funext x g h
    simp only [inducedLSymbol, Pi.mul_apply]
    ac_rfl

/-- **The torsor property.** The action of `H²(H, ℂˣ)` on action-gauge classes of L-symbols
compatible with `ω` is free and transitive: for any two classes there is exactly one
cohomology class carrying the first to the second.

Source: arXiv:2203.12563, `REsubmission.tex` line 761, "the solutions of `L|_H` are a
`𝒢`-torsor" with `𝒢 = H²(H, ℂˣ)`, for action-tensor gauge classes with the fusion gauge fixed. -/
theorem existsUnique_solutionAction_eq (K : StabilizerRepresentatives G X x₀)
    {ω : ScalarThreeCochain G} (c₁ c₂ : Quotient (solutionSetoid (X := X) ω)) :
    ∃! a : H2 (MulAction.stabilizer G x₀), K.solutionAction a c₁ = c₂ := by
  induction c₁ using Quotient.ind with
  | _ L₀ =>
  have hmap : ∀ a, K.solutionAction a (Quotient.mk _ L₀) = K.h2EquivSolutionClasses L₀.2 a := by
    intro a
    induction a using Quotient.ind with
    | _ ψ =>
      rw [solutionAction_mk, h2EquivSolutionClasses_mk]
  simp only [hmap]
  exact (K.h2EquivSolutionClasses L₀.2).bijective.existsUnique c₂

end StabilizerRepresentatives

end TNLean.Algebra
