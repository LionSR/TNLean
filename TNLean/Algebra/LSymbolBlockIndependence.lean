/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.LSymbol

/-!
# Block independence for scalar L-symbols

This file formalizes arXiv:2502.20257, Proposition `prop:technical01`
(lines 6965–7027), by explicit scalar gauges. No finiteness, transitivity,
or cocyclicity assumption is used.

The proof first factors a block-independent compatible L-symbol as
`Lˣ_{g,h} = A(g,h) q(x)`. Compatibility then shows that
`q(g • x) / q(x)` is a character. The resulting forward gauge multiplier is
exactly `L`, so the pointwise inverse gauges trivialize it.

**Local fixes (source algebra):** The proof follows the paper-gap notes in
issue #7268 for `prop:technical01`: line 6990 needs `γ_h` in the second denominator factor;
line 6996 requires division by `ell_{g,h;h}`; line 7016 therefore contains its
reciprocal; and the displayed factor is a forward gauge multiplier, whose
inverse gauges trivialize `L`.

## Main definitions

* `LSymbol.ell`: the scalar factor `ellˣ_{a,b;g}`.
* `LSymbol.IsBlockIndependentEll`, `IsBlockConstant`, and `IsTrivialEll`:
  the three raw conditions.
* `LSymbol.HasTrivialGauge`, `HasBlockConstantGauge`,
  `HasTrivialEllGauge`, and `IsBlockIndependent`: the four gauge-existential
  formulations in `prop:technical01`.

## Main results

* `LSymbol.factorization_of_isBlockIndependentEll`: corrected factorization.
* `LSymbol.relativeCharacter_mul`: the relative block scalar is a character.
* `LSymbol.exists_gauge_eq_one_of_isBlockIndependentEll`: explicit inverse
  gauges trivialize a block-independent compatible L-symbol.
* `LSymbol.hasTrivialGauge_iff_*`: the four conditions are equivalent.
-/

namespace TNLean.Algebra

variable {G X : Type*} [Group G] [MulAction G X]

namespace LSymbol

/-- The scalar factor
`ellˣ_{a,b;g} = Lˣ_{ag,g⁻¹b} / Lˣ_{a,b}` from arXiv:2502.20257,
Appendix `app:block_indep`. -/
def ell (L : LSymbol G X) (x : X) (a b g : G) : Units ℂ :=
  L x (a * g) (g⁻¹ * b) / L x a b

/-- The raw block-independence condition for `ell`, before choosing a gauge.
This is the condition preceding arXiv:2502.20257, `prop:technical01`. -/
def IsBlockIndependentEll (L : LSymbol G X) : Prop :=
  ∀ x y a b g, ell L x a b g = ell L y a b g

/-- L-symbols are block-constant when they do not depend on the block label.
This is the raw condition in item 2 of arXiv:2502.20257,
`prop:technical01`. -/
def IsBlockConstant (L : LSymbol G X) : Prop :=
  ∀ x y g h, L x g h = L y g h

/-- The raw condition that every scalar factor `ellˣ_{a,b;g}` is one.
This is item 3 of arXiv:2502.20257, `prop:technical01`, before choosing a
gauge. -/
def IsTrivialEll (L : LSymbol G X) : Prop :=
  ∀ x a b g, ell L x a b g = 1

/-- The raw condition that all L-symbols are one. -/
def IsTrivial (L : LSymbol G X) : Prop :=
  ∀ x g h, L x g h = 1

/-- Item 1 of arXiv:2502.20257, `prop:technical01`: some joint scalar gauge
trivializes every L-symbol. -/
def HasTrivialGauge (L : LSymbol G X) : Prop :=
  ∃ β : ScalarCocycle G, ∃ γ : ActionTensorGauge G X, IsTrivial (gauge β γ L)

/-- Item 2 of arXiv:2502.20257, `prop:technical01`: some joint scalar gauge
makes the L-symbols block-constant. -/
def HasBlockConstantGauge (L : LSymbol G X) : Prop :=
  ∃ β : ScalarCocycle G, ∃ γ : ActionTensorGauge G X,
    IsBlockConstant (gauge β γ L)

/-- Item 3 of arXiv:2502.20257, `prop:technical01`: some joint scalar gauge
makes every `ell` equal to one. -/
def HasTrivialEllGauge (L : LSymbol G X) : Prop :=
  ∃ β : ScalarCocycle G, ∃ γ : ActionTensorGauge G X,
    IsTrivialEll (gauge β γ L)

/-- Item 4 of arXiv:2502.20257, `prop:technical01`: the block-independence
condition holds after some joint scalar gauge. -/
def IsBlockIndependent (L : LSymbol G X) : Prop :=
  ∃ β : ScalarCocycle G, ∃ γ : ActionTensorGauge G X,
    IsBlockIndependentEll (gauge β γ L)

/-- The identity fusion and action gauges leave an L-symbol unchanged. -/
@[simp]
theorem gauge_one (L : LSymbol G X) :
    gauge (fun _ _ ↦ 1) (fun _ _ ↦ 1) L = L := by
  funext x g h
  simp [gauge]

/-- Successive joint scalar gauges multiply both cochains pointwise. -/
theorem gauge_comp (β₁ β₂ : ScalarCocycle G)
    (γ₁ γ₂ : ActionTensorGauge G X) (L : LSymbol G X) :
    gauge β₂ γ₂ (gauge β₁ γ₁ L) = gauge (β₁ * β₂) (γ₁ * γ₂) L := by
  funext x g h
  simp only [gauge, Pi.mul_apply]
  (apply Units.ext; push_cast; field_simp)

omit [MulAction G X] in
/-- Block-constant L-symbols have block-independent `ell`. -/
theorem IsBlockConstant.isBlockIndependentEll {L : LSymbol G X}
    (hL : IsBlockConstant L) : IsBlockIndependentEll L := by
  intro x y a b g
  simp only [ell]
  rw [hL x y, hL x y]

omit [MulAction G X] in
/-- Trivial `ell` is block-independent. -/
theorem IsTrivialEll.isBlockIndependentEll {L : LSymbol G X}
    (hL : IsTrivialEll L) : IsBlockIndependentEll L := by
  intro x y a b g
  rw [hL x, hL y]

omit [Group G] [MulAction G X] in
/-- Trivial L-symbols are block-constant. -/
theorem IsTrivial.isBlockConstant {L : LSymbol G X}
    (hL : IsTrivial L) : IsBlockConstant L := by
  intro x y g h
  rw [hL x, hL y]

omit [MulAction G X] in
/-- Trivial L-symbols have trivial `ell`. -/
theorem IsTrivial.isTrivialEll {L : LSymbol G X}
    (hL : IsTrivial L) : IsTrivialEll L := by
  intro x a b g
  rw [ell, hL x, hL x]
  simp

/-- Compatibility at `(g,1,1)` gives
`Lˣ_{g,1} = Lˣ_{1,1} / ω(g,1,1)`.
This is arXiv:2502.20257, `eq:aux1`. -/
theorem IsCompatible.apply_right_one {L : LSymbol G X}
    {ω : ScalarThreeCochain G} (hL : IsCompatible L ω) (x : X) (g : G) :
    L x g 1 = L x 1 1 / ω g 1 1 := by
  have h := hL x g 1 1
  simp only [mul_one, one_smul] at h
  calc
    L x g 1 = (ω g 1 1 * L x g 1 * L x g 1) /
        (ω g 1 1 * L x g 1) := by simp [div_eq_mul_inv]
    _ = (L x g 1 * L x 1 1) / (ω g 1 1 * L x g 1) := by rw [← h]
    _ = L x 1 1 / ω g 1 1 := by
      (apply Units.ext; push_cast; field_simp)

/-- Compatibility at `(1,1,g)` gives
`Lˣ_{1,g} = ω(1,1,g) L^{g • x}_{1,1}`.
This is arXiv:2502.20257, `eq:aux2`. -/
theorem IsCompatible.apply_left_one {L : LSymbol G X}
    {ω : ScalarThreeCochain G} (hL : IsCompatible L ω) (x : X) (g : G) :
    L x 1 g = ω 1 1 g * L (g • x) 1 1 := by
  have h := hL x 1 1 g
  simp only [one_mul] at h
  apply (mul_right_cancel (b := L x 1 g))
  simpa [mul_assoc] using h

/-- The block-independent scalar factor, evaluated at a chosen base block. -/
def blockFactor (L : LSymbol G X) (ω : ScalarThreeCochain G) (x₀ : X)
    (g h : G) : Units ℂ :=
  (ω (g * h) 1 1 * ell L x₀ g h h)⁻¹

/-- Corrected factorization of a compatible block-independent L-symbol:
`Lˣ_{g,h} = A(g,h) Lˣ_{1,1}`, where
`A(g,h) = (ω(gh,1,1) ell^{x₀}_{g,h;h})⁻¹`.

This is arXiv:2502.20257, `eq:Lfact`, with the division by `ell` required by
its definition. -/
theorem factorization_of_isBlockIndependentEll {L : LSymbol G X}
    {ω : ScalarThreeCochain G} (hCompat : IsCompatible L ω)
    (hBI : IsBlockIndependentEll L) (x₀ x : X) (g h : G) :
    L x g h = blockFactor L ω x₀ g h * L x 1 1 := by
  have hRight := hCompat.apply_right_one x (g * h)
  calc
    L x g h = L x (g * h) 1 / ell L x g h h := by
      simp only [ell, inv_mul_cancel]
      simp [div_eq_mul_inv, mul_comm, mul_left_comm]
    _ = L x (g * h) 1 / ell L x₀ g h h := by rw [hBI x x₀]
    _ = blockFactor L ω x₀ g h * L x 1 1 := by
      rw [hRight]
      simp only [blockFactor]
      simp [div_eq_mul_inv, mul_assoc, mul_comm]

/-- The relative scalar appearing in arXiv:2502.20257, `eq:defrho`.
With the corrected factorization it is
`ρ(g) = (ell^{x₀}_{1,g;g} ω(g,1,1) ω(1,1,g))⁻¹`. -/
def relativeCharacter (L : LSymbol G X) (ω : ScalarThreeCochain G) (x₀ : X)
    (g : G) : Units ℂ :=
  (ell L x₀ 1 g g * ω g 1 1 * ω 1 1 g)⁻¹

/-- The relative block scalar transports `Lˣ_{1,1}` along the action:
`L^{g • x}_{1,1} = ρ(g) Lˣ_{1,1}`.

This is arXiv:2502.20257, `eq:defrho`, with the reciprocal `ell` forced by the
corrected `eq:Lfact`. -/
theorem relativeCharacter_mul_base {L : LSymbol G X}
    {ω : ScalarThreeCochain G} (hCompat : IsCompatible L ω)
    (hBI : IsBlockIndependentEll L) (x₀ x : X) (g : G) :
    L (g • x) 1 1 = relativeCharacter L ω x₀ g * L x 1 1 := by
  have hFactor := factorization_of_isBlockIndependentEll hCompat hBI x₀ x 1 g
  have hLeft := hCompat.apply_left_one x g
  rw [hLeft] at hFactor
  calc
    L (g • x) 1 1 =
        (blockFactor L ω x₀ 1 g * L x 1 1) / ω 1 1 g := by
      rw [← hFactor]
      simp [div_eq_mul_inv, mul_assoc, mul_comm]
    _ = relativeCharacter L ω x₀ g * L x 1 1 := by
      simp only [blockFactor, relativeCharacter, one_mul]
      (apply Units.ext; push_cast; field_simp)

/-- The relative scalar is multiplicative, hence a one-dimensional character.
No transitivity or finiteness of the action is needed. -/
theorem relativeCharacter_mul {L : LSymbol G X}
    {ω : ScalarThreeCochain G} (hCompat : IsCompatible L ω)
    (hBI : IsBlockIndependentEll L) (x₀ : X) (g h : G) :
    relativeCharacter L ω x₀ (g * h) =
      relativeCharacter L ω x₀ g * relativeCharacter L ω x₀ h := by
  have hgh := relativeCharacter_mul_base hCompat hBI x₀ x₀ (g * h)
  have hh := relativeCharacter_mul_base hCompat hBI x₀ x₀ h
  have hg := relativeCharacter_mul_base hCompat hBI x₀ (h • x₀) g
  have hEq : relativeCharacter L ω x₀ (g * h) * L x₀ 1 1 =
      relativeCharacter L ω x₀ g *
        (relativeCharacter L ω x₀ h * L x₀ 1 1) := by
    calc
      _ = L ((g * h) • x₀) 1 1 := hgh.symm
      _ = L (g • h • x₀) 1 1 := by rw [mul_smul]
      _ = relativeCharacter L ω x₀ g * L (h • x₀) 1 1 := hg
      _ = _ := by rw [hh]
  apply (mul_right_cancel (b := L x₀ 1 1))
  simpa only [mul_assoc] using hEq

/-- The forward fusion cochain whose joint gauge multiplier equals `L`. -/
def factorFusionGauge (L : LSymbol G X) (ω : ScalarThreeCochain G) (x₀ : X) :
    ScalarCocycle G :=
  fun g h ↦ blockFactor L ω x₀ g h / relativeCharacter L ω x₀ h

/-- The forward action cochain whose joint gauge multiplier equals `L`. -/
def factorActionGauge (L : LSymbol G X) : ActionTensorGauge G X :=
  fun g x ↦ (L (g • x) 1 1)⁻¹

/-- The corrected factorization is exactly a forward joint gauge multiplier:
applying the factor gauges to the trivial L-symbol produces `L`.

The inverse gauges, not these forward gauges, therefore trivialize `L`. -/
theorem gauge_one_eq_of_isBlockIndependentEll {L : LSymbol G X}
    {ω : ScalarThreeCochain G} (hCompat : IsCompatible L ω)
    (hBI : IsBlockIndependentEll L) (x₀ : X) :
    gauge (factorFusionGauge L ω x₀) (factorActionGauge L)
      (fun _ _ _ ↦ 1) = L := by
  funext x g h
  simp only [gauge, factorFusionGauge, factorActionGauge, mul_one]
  rw [factorization_of_isBlockIndependentEll hCompat hBI x₀ x]
  rw [relativeCharacter_mul_base hCompat hBI x₀ x h]
  simp only [mul_smul]
  (apply Units.ext; push_cast; field_simp)

/-- Direct trivializing gauges for a block-independent compatible L-symbol.
They are the pointwise inverses of the forward factor gauges. -/
theorem gauge_inv_eq_one_of_isBlockIndependentEll {L : LSymbol G X}
    {ω : ScalarThreeCochain G} (hCompat : IsCompatible L ω)
    (hBI : IsBlockIndependentEll L) (x₀ : X) :
    gauge (factorFusionGauge L ω x₀)⁻¹ (factorActionGauge L)⁻¹ L =
      (fun _ _ _ ↦ 1) := by
  calc
    gauge (factorFusionGauge L ω x₀)⁻¹ (factorActionGauge L)⁻¹ L =
        gauge (factorFusionGauge L ω x₀)⁻¹ (factorActionGauge L)⁻¹
          (gauge (factorFusionGauge L ω x₀) (factorActionGauge L)
            (fun _ _ _ ↦ 1)) := by
      rw [gauge_one_eq_of_isBlockIndependentEll hCompat hBI x₀]
    _ = gauge (factorFusionGauge L ω x₀ * (factorFusionGauge L ω x₀)⁻¹)
        (factorActionGauge L * (factorActionGauge L)⁻¹)
        (fun _ _ _ ↦ 1) := gauge_comp _ _ _ _ _
    _ = (fun _ _ _ ↦ 1) := by
      funext x g h
      simp [gauge]

/-- A compatible block-independent L-symbol admits a trivializing gauge.
The only set-theoretic assumption is that a base block exists. -/
theorem hasTrivialGauge_of_isBlockIndependentEll [Nonempty X]
    {L : LSymbol G X} {ω : ScalarThreeCochain G} (hCompat : IsCompatible L ω)
    (hBI : IsBlockIndependentEll L) : HasTrivialGauge L := by
  let x₀ : X := Classical.choice ‹Nonempty X›
  refine ⟨(factorFusionGauge L ω x₀)⁻¹, (factorActionGauge L)⁻¹, ?_⟩
  intro x g h
  exact congrFun (congrFun (congrFun
    (gauge_inv_eq_one_of_isBlockIndependentEll hCompat hBI x₀) x) g) h

/-- Item 1 implies item 2 of arXiv:2502.20257, `prop:technical01`. -/
theorem HasTrivialGauge.hasBlockConstantGauge {L : LSymbol G X}
    (hL : HasTrivialGauge L) : HasBlockConstantGauge L := by
  obtain ⟨β, γ, h⟩ := hL
  exact ⟨β, γ, h.isBlockConstant⟩

/-- Item 1 implies item 3 of arXiv:2502.20257, `prop:technical01`. -/
theorem HasTrivialGauge.hasTrivialEllGauge {L : LSymbol G X}
    (hL : HasTrivialGauge L) : HasTrivialEllGauge L := by
  obtain ⟨β, γ, h⟩ := hL
  exact ⟨β, γ, h.isTrivialEll⟩

/-- Item 2 implies item 4 of arXiv:2502.20257, `prop:technical01`. -/
theorem HasBlockConstantGauge.isBlockIndependent {L : LSymbol G X}
    (hL : HasBlockConstantGauge L) : IsBlockIndependent L := by
  obtain ⟨β, γ, h⟩ := hL
  exact ⟨β, γ, h.isBlockIndependentEll⟩

/-- Item 3 implies item 4 of arXiv:2502.20257, `prop:technical01`. -/
theorem HasTrivialEllGauge.isBlockIndependent {L : LSymbol G X}
    (hL : HasTrivialEllGauge L) : IsBlockIndependent L := by
  obtain ⟨β, γ, h⟩ := hL
  exact ⟨β, γ, h.isBlockIndependentEll⟩

/-- Item 4 implies item 1 of arXiv:2502.20257, `prop:technical01`.
Compatibility is transported through the witnessing gauge and the two gauges
are then composed. -/
theorem IsBlockIndependent.hasTrivialGauge [Nonempty X]
    {L : LSymbol G X} {ω : ScalarThreeCochain G} (hCompat : IsCompatible L ω)
    (hL : IsBlockIndependent L) : HasTrivialGauge L := by
  obtain ⟨β, γ, hBI⟩ := hL
  obtain ⟨δ, ε, hTriv⟩ :=
    hasTrivialGauge_of_isBlockIndependentEll (hCompat.gauge β γ) hBI
  refine ⟨β * δ, γ * ε, ?_⟩
  rw [← gauge_comp]
  exact hTriv

/-- Capstone equivalence of items 1 and 2 in arXiv:2502.20257,
`prop:technical01`. -/
theorem hasTrivialGauge_iff_hasBlockConstantGauge [Nonempty X]
    {L : LSymbol G X} {ω : ScalarThreeCochain G} (hCompat : IsCompatible L ω) :
    HasTrivialGauge L ↔ HasBlockConstantGauge L := by
  constructor
  · exact HasTrivialGauge.hasBlockConstantGauge
  · exact fun h ↦ (h.isBlockIndependent).hasTrivialGauge hCompat

/-- Capstone equivalence of items 1 and 3 in arXiv:2502.20257,
`prop:technical01`. -/
theorem hasTrivialGauge_iff_hasTrivialEllGauge [Nonempty X]
    {L : LSymbol G X} {ω : ScalarThreeCochain G} (hCompat : IsCompatible L ω) :
    HasTrivialGauge L ↔ HasTrivialEllGauge L := by
  constructor
  · exact HasTrivialGauge.hasTrivialEllGauge
  · exact fun h ↦ (h.isBlockIndependent).hasTrivialGauge hCompat

/-- Capstone equivalence of items 1 and 4 in arXiv:2502.20257,
`prop:technical01`. -/
theorem hasTrivialGauge_iff_isBlockIndependent [Nonempty X]
    {L : LSymbol G X} {ω : ScalarThreeCochain G} (hCompat : IsCompatible L ω) :
    HasTrivialGauge L ↔ IsBlockIndependent L := by
  constructor
  · exact fun h ↦ h.hasBlockConstantGauge.isBlockIndependent
  · exact IsBlockIndependent.hasTrivialGauge hCompat

end LSymbol

end TNLean.Algebra
