/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import TNLean.Algebra.ProjectiveRepresentation

/-!
# Scalar 2-cocycles and Mathlib's `H²(G, ℂˣ)`

The factor system `ω : G × G → ℂˣ` of a projective representation satisfies the
multiplicative 2-cocycle equation.  Its class lives in Mathlib's degree-two group
cohomology `groupCohomology.H2 (Rep.ofMulDistribMulAction G ℂˣ)`, for the trivial
action of `G` on `ℂˣ`; the class of a cocycle `ω` is
`groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂ hω)`.

The trivial action is the scoped instance
`TNLean.Algebra.ScalarCohomology.trivialMulDistribMulAction`; Mathlib defines no
action of an arbitrary group on `ℂˣ`.  Open it with
`open scoped TNLean.Algebra.ScalarCohomology`.

## Main definitions

* `groupCohomology.IsMulCocycle₂` : the multiplicative 2-cocycle condition
* `groupCohomology.IsMulCoboundary₂` : the multiplicative 2-coboundary condition
* `ScalarCohomology.trivialMulDistribMulAction` : the trivial action of `G` on `ℂˣ`
* `scalarRepresentationRes` : restriction of the trivial representation on `ℂˣ`
  along a group homomorphism, the coefficient map of Mathlib's restriction
* `ScalarCocycle.commPhase` : the commutator phase `ω(g,h) ω(h,g)⁻¹`

## Main results

* `isMulCocycle₂_iff` : the scalar cocycle equation in the source orientation
* `H2π_eq_iff_isMulCoboundary₂_div` : two cocycles have the same class in
  Mathlib's `H²(G, ℂˣ)` iff their ratio is a coboundary
* `ScalarCocycle.exists_H2π_eq` : every class of `H²(G, ℂˣ)` is the class of a
  scalar cocycle
* `ScalarCocycle.H2π_ne_zero_of_commPhase_ne_one` : a non-trivial commutator phase
  of a cocycle at a commuting pair forces a non-zero class in `H²(G, ℂˣ)`

## References

* Pérez-García et al., *String order and symmetries in quantum spin lattices*,
  arXiv:0802.0447
* Chen, Gu, Wen, *Classification of gapped symmetric phases in one-dimensional
  spin systems*, Phys. Rev. B 83, 035107 (2011)
* Franco-Rubio, Bochniak, Cirac, *Symmetry defects and gauging for quantum states
  with matrix product unitary symmetries*, arXiv:2502.20257, lines 1927--1931
-/

namespace TNLean.Algebra

variable {G : Type} [Group G]
variable {D : ℕ}

namespace ScalarCohomology

set_option warn.classDefReducibility false in
/-- The trivial action of `G` on the scalar coefficient group `ℂˣ`, so that
`Rep.ofMulDistribMulAction G ℂˣ` is the coefficient module of `H²(G, ℂˣ)` and
`H³(G, ℂˣ)`.  It is scoped: other actions of particular groups on `ℂˣ` exist. -/
scoped instance trivialMulDistribMulAction : MulDistribMulAction G (Units ℂ) where
  smul _ z := z
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

/-- The group acts trivially on the scalar coefficient module. -/
theorem ofMulDistribMulAction_ρ_apply (a : G) (x : Rep.ofMulDistribMulAction G ℂˣ) :
    (Rep.ofMulDistribMulAction G ℂˣ).ρ a x = x :=
  rfl

end ScalarCohomology

open scoped ScalarCohomology

/-- Mathlib's scalar two-cocycle equation, written in the source's order of factors.
The action on `ℂˣ` is trivial, as in arXiv:2502.20257, lines 1927–1931. -/
theorem isMulCocycle₂_iff (ω : ScalarCocycle G) :
    groupCohomology.IsMulCocycle₂ ω ↔
      ∀ g h k : G, ω (g, h) * ω (g * h, k) = ω (g, h * k) * ω (h, k) := by
  constructor <;> intro h g k j
  · have h' := h g k j
    change ω (g * k, j) * ω (g, k) = ω (k, j) * ω (g, k * j) at h'
    simpa only [mul_comm] using h'
  · change ω (g * k, j) * ω (g, k) = ω (k, j) * ω (g, k * j)
    simpa only [mul_comm] using h g k j

/-! ### Cocycle and coboundary equations -/

/-- The source-oriented scalar coboundary formula, with the same witness. -/
theorem isMulCoboundary₂_div_iff (ω₁ ω₂ : G × G → ℂˣ) :
    groupCohomology.IsMulCoboundary₂ (ω₁ / ω₂) ↔
      ∃ φ : G → ℂˣ, ∀ g h, ω₁ (g, h) = φ g * φ h * (φ (g * h))⁻¹ * ω₂ (g, h) := by
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, fun g h ↦ ?_⟩
    have h' := hφ g h
    change φ h / φ (g * h) * φ g = ω₁ (g, h) / ω₂ (g, h) at h'
    rw [eq_div_iff_mul_eq'] at h'
    rw [← h', div_mul_eq_mul_div, mul_comm (φ h), div_eq_mul_inv]
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, fun g h ↦ ?_⟩
    change φ h / φ (g * h) * φ g = ω₁ (g, h) / ω₂ (g, h)
    rw [hφ g h, mul_div_cancel_right, div_mul_eq_mul_div, mul_comm (φ h), div_eq_mul_inv]

/-- Adding a coboundary to a scalar cocycle preserves the cocycle condition. -/
theorem isMulCocycle₂_of_isMulCoboundary₂_div {ω₁ ω₂ : G × G → ℂˣ}
    (h₂ : groupCohomology.IsMulCocycle₂ ω₂)
    (h : groupCohomology.IsMulCoboundary₂ (ω₁ / ω₂)) :
    groupCohomology.IsMulCocycle₂ ω₁ := by
  have hd := groupCohomology.coboundaries₂_le_cocycles₂
    (Rep.ofMulDistribMulAction G ℂˣ)
    (groupCohomology.coboundariesOfIsMulCoboundary₂ h).property
  have hs := (groupCohomology.cocycles₂ (Rep.ofMulDistribMulAction G ℂˣ)).add_mem hd
    (groupCohomology.cocyclesOfIsMulCocycle₂ h₂).property
  apply groupCohomology.isMulCocycle₂_of_mem_cocycles₂ (G := G) (M := ℂˣ)
    ((@Additive.ofMul ℂˣ) ∘ ω₁)
  have heq :
      (groupCohomology.coboundariesOfIsMulCoboundary₂ h :
          G × G → Rep.ofMulDistribMulAction G ℂˣ) +
        (groupCohomology.cocyclesOfIsMulCocycle₂ h₂ :
          G × G → Rep.ofMulDistribMulAction G ℂˣ) = ((@Additive.ofMul ℂˣ) ∘ ω₁) := by
    funext p
    change Additive.ofMul (ω₁ p / ω₂ p * ω₂ p) = Additive.ofMul (ω₁ p)
    rw [div_mul_cancel]
  exact (congrArg (fun f : G × G → Rep.ofMulDistribMulAction G ℂˣ ↦
    f ∈ groupCohomology.cocycles₂ (Rep.ofMulDistribMulAction G ℂˣ)) heq).mp hs

/-- Every projective representation of positive bond dimension has a genuine 2-cocycle
as factor system.  This is the `Units ℂ`-level lift of
`ProjectiveRepresentation.cocycle_of_assoc`: associativity of matrix multiplication
forces the multiplicative 2-cocycle identity on `ω`. -/
theorem ScalarCocycle.isMulCocycle₂_of_projRep
    {ω : ScalarCocycle G} (ρ : ProjectiveRepresentation (D := D) ω) (hD : 0 < D) :
    groupCohomology.IsMulCocycle₂ ω := by
  apply (isMulCocycle₂_iff _).mpr
  intro g h k
  have hℂ : (ω (g, h) : ℂ) * (ω (g * h, k) : ℂ) = (ω (g, h * k) : ℂ) * (ω (h, k) : ℂ) :=
    ρ.cocycle_of_assoc (D := D) hD g h k
  have hUcoe : ((ω (g, h) * ω (g * h, k) : Units ℂ) : ℂ) =
      ((ω (g, h * k) * ω (h, k) : Units ℂ) : ℂ) := by
    push_cast; exact hℂ
  exact Units.ext hUcoe

/-! ### Mathlib's degree-two group cohomology with coefficients `ℂˣ`

The coefficient group in `Papers/2502.20257/main.tex:1927--1931` is `ℂˣ` with the
trivial group action.  Mathlib's low-degree comparison theorems place the
coefficient ring and the acting group in the same universe, so the cocycle-bearing
modules use `G : Type` throughout. -/

/-- Restricting the trivial representation on `ℂˣ` along `f : K →* G` gives the trivial
representation of `K`; this is the identity on `Additive ℂˣ` as a representation morphism, the
coefficient map for Mathlib's restriction `groupCohomology.cochainsMap f` and
`groupCohomology.map f`. -/
def scalarRepresentationRes {K : Type} [Group K] (f : K →* G) :
    Rep.res f (Rep.ofMulDistribMulAction G ℂˣ) ⟶
      Rep.ofMulDistribMulAction K ℂˣ := by
  apply Rep.ofHom
  refine ⟨LinearMap.id, ?_⟩
  intro g
  rfl

/-- Two arbitrary scalar two-cochains differ by a coboundary precisely when
their images in the quotient of all two-cochains by two-coboundaries agree.
No cocycle condition is required: this quotient is not `H²(G, ℂˣ)`. -/
theorem isMulCoboundary₂_div_iff_quotient_mk_eq (ω₁ ω₂ : G × G → ℂˣ) :
    groupCohomology.IsMulCoboundary₂ (ω₁ / ω₂) ↔
      (Submodule.Quotient.mk ((@Additive.ofMul ℂˣ) ∘ ω₁) :
        (G × G → Rep.ofMulDistribMulAction G ℂˣ) ⧸
          groupCohomology.coboundaries₂ (Rep.ofMulDistribMulAction G ℂˣ)) =
        Submodule.Quotient.mk ((@Additive.ofMul ℂˣ) ∘ ω₂) := by
  constructor
  · intro h
    exact (Submodule.Quotient.eq _).mpr
      (groupCohomology.coboundariesOfIsMulCoboundary₂ h).property
  · intro h
    exact groupCohomology.isMulCoboundary₂_of_mem_coboundaries₂
      (G := G) (M := ℂˣ) _ ((Submodule.Quotient.eq _).mp h)

/-- Every scalar cochain has a coboundary self-ratio, without a cocycle hypothesis. -/
theorem isMulCoboundary₂_div_self (ω : G × G → ℂˣ) :
    groupCohomology.IsMulCoboundary₂ (ω / ω) :=
  (isMulCoboundary₂_div_iff_quotient_mk_eq ω ω).mpr rfl

/-- Symmetry uses equality in the upstream cochain quotient, not a local relation. -/
theorem isMulCoboundary₂_div_symm {ω₁ ω₂ : G × G → ℂˣ}
    (h : groupCohomology.IsMulCoboundary₂ (ω₁ / ω₂)) :
    groupCohomology.IsMulCoboundary₂ (ω₂ / ω₁) :=
  (isMulCoboundary₂_div_iff_quotient_mk_eq ω₂ ω₁).mpr
    ((isMulCoboundary₂_div_iff_quotient_mk_eq ω₁ ω₂).mp h).symm

/-- Transitivity uses equality in the upstream cochain quotient. -/
theorem isMulCoboundary₂_div_trans {ω₁ ω₂ ω₃ : G × G → ℂˣ}
    (h₁₂ : groupCohomology.IsMulCoboundary₂ (ω₁ / ω₂))
    (h₂₃ : groupCohomology.IsMulCoboundary₂ (ω₂ / ω₃)) :
    groupCohomology.IsMulCoboundary₂ (ω₁ / ω₃) :=
  (isMulCoboundary₂_div_iff_quotient_mk_eq ω₁ ω₃).mpr
    (((isMulCoboundary₂_div_iff_quotient_mk_eq ω₁ ω₂).mp h₁₂).trans
      ((isMulCoboundary₂_div_iff_quotient_mk_eq ω₂ ω₃).mp h₂₃))

/-- Genuine scalar cocycles have equal `H²` classes exactly when their ratio is a coboundary. -/
theorem H2π_eq_iff_isMulCoboundary₂_div {ω₁ ω₂ : G × G → ℂˣ}
    (h₁ : groupCohomology.IsMulCocycle₂ ω₁) (h₂ : groupCohomology.IsMulCocycle₂ ω₂) :
    groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
        (groupCohomology.cocyclesOfIsMulCocycle₂ h₁) =
      groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
        (groupCohomology.cocyclesOfIsMulCocycle₂ h₂) ↔
      groupCohomology.IsMulCoboundary₂ (ω₁ / ω₂) := by
  rw [groupCohomology.H2π_eq_iff]
  constructor
  · intro h
    exact groupCohomology.isMulCoboundary₂_of_mem_coboundaries₂
      (G := G) (M := ℂˣ) _ h
  · intro h
    exact (groupCohomology.coboundariesOfIsMulCoboundary₂ h).property

/-- The class of the constant cocycle `1` is zero. -/
theorem ScalarCocycle.H2π_one
    (h : groupCohomology.IsMulCocycle₂ (1 : ScalarCocycle G)) :
    groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
      (groupCohomology.cocyclesOfIsMulCocycle₂ h) = 0 := by
  have : groupCohomology.cocyclesOfIsMulCocycle₂ h = 0 := rfl
  rw [this, map_zero]

/-- The native zero-class criterion needs no constant-cocycle comparison. -/
theorem H2π_eq_zero_iff_isMulCoboundary₂ {ω : G × G → ℂˣ}
    (hω : groupCohomology.IsMulCocycle₂ ω) :
    groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
        (groupCohomology.cocyclesOfIsMulCocycle₂ hω) = 0 ↔
      groupCohomology.IsMulCoboundary₂ ω := by
  rw [groupCohomology.H2π_eq_zero_iff]
  constructor
  · intro h
    exact groupCohomology.isMulCoboundary₂_of_mem_coboundaries₂
      (G := G) (M := ℂˣ) _ h
  · intro h
    exact (groupCohomology.coboundariesOfIsMulCoboundary₂ h).property

/-- Every class of Mathlib's `H²(G, ℂˣ)`, for the trivial action, is the class of a
scalar cocycle. -/
theorem ScalarCocycle.exists_H2π_eq
    (x : groupCohomology.H2 (Rep.ofMulDistribMulAction G ℂˣ)) :
    ∃ (ω : ScalarCocycle G) (hω : groupCohomology.IsMulCocycle₂ ω),
      groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂ hω) = x := by
  induction x using groupCohomology.H2_induction_on with
  | h α =>
    refine ⟨fun p ↦ Additive.toMul (α p),
      (groupCohomology.isMulCocycle₂_of_mem_cocycles₂ (G := G) (M := Units ℂ)
          (fun p ↦ α p) α.property), ?_⟩
    rfl

/-! ### Commutator phase and non-triviality of a cohomology class

For a pair of commuting group elements `g`, `h`, the *commutator phase*
`ω(g,h) · ω(h,g)⁻¹` of an `ℂˣ`-valued 2-cocycle is invariant under the
coboundary action and so descends to the cohomology class.  When the phase
differs from `1` the class is non-zero.  This is the standard discrete
invariant detecting the non-trivial element of `H²(Z₂ × Z₂, ℂˣ) = Z₂`. -/

/-- The commutator phase `ω(g,h) · ω(h,g)⁻¹` of a scalar 2-cocycle. -/
def ScalarCocycle.commPhase (ω : ScalarCocycle G) (g h : G) : Units ℂ :=
  ω (g, h) * (ω (h, g))⁻¹

omit [Group G] in
/-- The trivial cocycle has commutator phase `1`. -/
lemma ScalarCocycle.commPhase_one (g h : G) :
    ScalarCocycle.commPhase (G := G) 1 g h = 1 := by
  simp [ScalarCocycle.commPhase]

/-- Commutator phases are invariant under a coboundary, without a cocycle hypothesis. -/
theorem ScalarCocycle.commPhase_eq_of_isMulCoboundary₂_div {ω₁ ω₂ : G × G → ℂˣ}
    (H : groupCohomology.IsMulCoboundary₂ (ω₁ / ω₂))
    {g k : G} (hgk : g * k = k * g) :
    ScalarCocycle.commPhase ω₁ g k = ScalarCocycle.commPhase ω₂ g k := by
  obtain ⟨φ, hφ⟩ := (isMulCoboundary₂_div_iff ω₁ ω₂).mp H
  simp only [ScalarCocycle.commPhase, hφ g k, hφ k g, hgk]
  apply Units.ext
  push_cast
  field_simp

/-- A non-trivial commutator phase at a commuting pair forces a non-zero class in
Mathlib's `H²(G, ℂˣ)`. -/
theorem ScalarCocycle.H2π_ne_zero_of_commPhase_ne_one {ω : ScalarCocycle G}
    (hω : groupCohomology.IsMulCocycle₂ ω) {g h : G} (hgh : g * h = h * g)
    (hne : ScalarCocycle.commPhase ω g h ≠ 1) :
    groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
      (groupCohomology.cocyclesOfIsMulCocycle₂ hω) ≠ 0 := by
  intro H
  apply hne
  have hB : groupCohomology.IsMulCoboundary₂ (ω / (1 : G × G → ℂˣ)) := by
    simpa only [div_one] using (H2π_eq_zero_iff_isMulCoboundary₂ hω).mp H
  rw [ScalarCocycle.commPhase_eq_of_isMulCoboundary₂_div hB hgh,
    ScalarCocycle.commPhase_one]

end TNLean.Algebra
