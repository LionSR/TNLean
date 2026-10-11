/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import TNLean.Algebra.CocycleCohomology
import TNLean.Algebra.ScalarThreeCocycle

/-!
# Scalar three-cocycles as degree-three group cohomology

This file identifies the multiplicative scalar three-cocycles of
arXiv:2502.20257, `eq:3-cocycle`, and their fusion-gauge classes from
`eq:omegagauge`, with Mathlib's degree-three group cohomology
`groupCohomology A 3` of the trivial representation `A` of `G` on `ℂˣ`.

The representation is `scalarH2Representation G`, already used for the
degree-two comparison in `TNLean.Algebra.CocycleCohomology`: its underlying
module is `Additive ℂˣ` with the trivial action. A scalar three-cochain `ω`
corresponds to the inhomogeneous cochain `(g₀, g₁, g₂) ↦ ω(g₀, g₁, g₂)`. With the
trivial action, Mathlib's differential in degree three is

`(df)(a, b, c, e) = f(b, c, e) - f(ab, c, e) + f(a, bc, e) - f(a, b, ce) + f(a, b, c)`,

which is the additive form of the scalar three-cocycle equation, and its
differential in degree two is the additive form of the three-coboundary of
`eq:omegagauge`. No normalization is involved on either side: fusion gauges by
arbitrary scalar two-cochains correspond to arbitrary Mathlib coboundaries.

## Main definitions

* `ScalarThreeCochain.toInhomogeneousCochain`: a scalar three-cochain as an
  inhomogeneous three-cochain of the trivial representation on `ℂˣ`.
* `ScalarThreeCochain.cocyclesEquiv`: scalar three-cocycles are Mathlib's
  three-cocycles.
* `ScalarThreeCochain.anomalyClass`: the degree-three cohomology class of a scalar
  three-cocycle.
* `scalarRepresentationRes`: restriction of the trivial representation on `ℂˣ` along a group
  homomorphism, as a representation morphism.

## Main results

* `ScalarCocycle.toInhomogeneousCochain_comap`,
  `ScalarThreeCochain.toInhomogeneousCochain_comap`: restriction of scalar cochains along a
  homomorphism is Mathlib's `groupCohomology.cochainsMap`.
* `ScalarThreeCochain.isCocycle_iff_d_eq_zero`: the three-cocycle equation is
  the vanishing of Mathlib's differential.
* `ScalarCocycle.d_toInhomogeneousCochain`: Mathlib's degree-two differential is
  the three-coboundary of `eq:omegagauge`.
* `ScalarThreeCochain.cohomologousTo_iff_anomalyClass_eq`: fusion-gauge
  equivalence is equality of degree-three cohomology classes.
* `ScalarThreeCochain.isTrivialGaugeClass_iff_anomalyClass_eq_zero`: trivial
  gauge class is the vanishing of the degree-three cohomology class.
* `ScalarThreeCochain.anomalyClass_surjective`: every degree-three class is
  represented by a scalar three-cocycle.

## References

* Franco-Rubio, Bochniak, Cirac, *Symmetry defects and gauging for quantum states
  with matrix product unitary symmetries*, arXiv:2502.20257, `eq:3-cocycle` and
  `eq:omegagauge`
* Mathlib, `Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic`
-/

noncomputable section

open CategoryTheory groupCohomology

namespace TNLean.Algebra

universe u

/-- A cocycle of positive degree `n + 1` has zero class in Mathlib's group
cohomology exactly when it is the differential of an inhomogeneous `n`-cochain. -/
theorem groupCohomology_π_eq_zero_iff {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (n : ℕ) (x : cocycles A (n + 1)) :
    π A (n + 1) x = 0 ↔
      ∃ y : (Fin n → G) → A, inhomogeneousCochains.d A n y = iCocycles A (n + 1) x := by
  let S : ShortComplex (ModuleCat k) :=
    ShortComplex.mk ((inhomogeneousCochains A).toCycles n (n + 1)) (π A (n + 1))
      ((inhomogeneousCochains A).toCycles_comp_homologyπ n (n + 1))
  have hS : S.Exact := S.exact_of_g_is_cokernel
    ((inhomogeneousCochains A).homologyIsCokernel n (n + 1) (by simp))
  have hi : ∀ y : (Fin n → G) → A,
      iCocycles A (n + 1) ((inhomogeneousCochains A).toCycles n (n + 1) y) =
        inhomogeneousCochains.d A n y := by
    intro y
    rw [← inhomogeneousCochains.d_def]
    exact ConcreteCategory.congr_hom ((inhomogeneousCochains A).toCycles_i n (n + 1)) y
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff S).mp hS x hx
    exact ⟨y, by rw [← hi y]; exact congrArg _ hy⟩
  · rintro ⟨y, hy⟩
    have hxy : (inhomogeneousCochains A).toCycles n (n + 1) y = x := by
      apply (ModuleCat.mono_iff_injective (iCocycles A (n + 1))).1 inferInstance
      rw [hi y, hy]
    rw [← hxy]
    exact ConcreteCategory.congr_hom
      ((inhomogeneousCochains A).toCycles_comp_homologyπ n (n + 1)) y

variable {G : Type} [Group G]

/-- The underlying additive group of the trivial representation on `ℂˣ`
(notation for `Units ℂ`) is `Additive ℂˣ`. -/
def scalarRepresentationEquiv (G : Type) [Group G] :
    Additive (Units ℂ) ≃+ scalarH2Representation G :=
  (@Rep.toAdditive G (Units ℂ) _ _ (ScalarCocycle.trivialMulDistribMulAction (G := G))).symm

/-- The group acts trivially on the scalar representation. -/
theorem scalarH2Representation_ρ_apply (a : G) (x : scalarH2Representation G) :
    (scalarH2Representation G).ρ a x = x :=
  rfl

@[simp]
theorem scalarRepresentationEquiv_ofMul_eq_zero_iff (z : Units ℂ) :
    scalarRepresentationEquiv G (Additive.ofMul z) = 0 ↔ z = 1 := by
  rw [AddEquivClass.map_eq_zero_iff, ofMul_eq_zero]

/-- Restricting the trivial representation on `ℂˣ` along `f : K →* G` gives the trivial
representation of `K`; this is the identity on `Additive ℂˣ` as a representation morphism, the
coefficient map for Mathlib's restriction `groupCohomology.cochainsMap f`. -/
def scalarRepresentationRes {K : Type} [Group K] (f : K →* G) :
    Rep.res f (scalarH2Representation G) ⟶ scalarH2Representation K := by
  apply Rep.ofHom
  refine ⟨LinearMap.id, ?_⟩
  intro g
  rfl

namespace ScalarCocycle

/-- A scalar two-cochain as an inhomogeneous two-cochain of the trivial
representation on `ℂˣ`. -/
def toInhomogeneousCochain (β : ScalarCocycle G) :
    (Fin 2 → G) → scalarH2Representation G :=
  fun g ↦ scalarRepresentationEquiv G (Additive.ofMul (β (g 0) (g 1)))

/-- An inhomogeneous two-cochain of the trivial representation on `ℂˣ` as a
scalar two-cochain. -/
def ofInhomogeneousCochain (f : (Fin 2 → G) → scalarH2Representation G) :
    ScalarCocycle G :=
  fun g h ↦ ((scalarRepresentationEquiv G).symm (f ![g, h])).toMul

@[simp]
theorem toInhomogeneousCochain_ofInhomogeneousCochain
    (f : (Fin 2 → G) → scalarH2Representation G) :
    toInhomogeneousCochain (ofInhomogeneousCochain f) = f := by
  funext g
  simp only [toInhomogeneousCochain, ofInhomogeneousCochain, ofMul_toMul,
    AddEquiv.apply_symm_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Restriction `ScalarCocycle.comap f` is Mathlib's restriction of inhomogeneous two-cochains,
`groupCohomology.cochainsMap f`, with the identity coefficient map. -/
theorem toInhomogeneousCochain_comap {K : Type} [Group K] (f : K →* G) (β : ScalarCocycle G) :
    toInhomogeneousCochain (β.comap f) =
      ((cochainsMap f (scalarRepresentationRes f)).f 2).hom (toInhomogeneousCochain β) :=
  rfl

end ScalarCocycle

namespace ScalarThreeCochain

/-- A scalar three-cochain as an inhomogeneous three-cochain of the trivial
representation on `ℂˣ`. -/
def toInhomogeneousCochain (ω : ScalarThreeCochain G) :
    (Fin 3 → G) → scalarH2Representation G :=
  fun g ↦ scalarRepresentationEquiv G (Additive.ofMul (ω (g 0) (g 1) (g 2)))

/-- An inhomogeneous three-cochain of the trivial representation on `ℂˣ` as a
scalar three-cochain. -/
def ofInhomogeneousCochain (f : (Fin 3 → G) → scalarH2Representation G) :
    ScalarThreeCochain G :=
  fun g h k ↦ ((scalarRepresentationEquiv G).symm (f ![g, h, k])).toMul

@[simp]
theorem ofInhomogeneousCochain_toInhomogeneousCochain (ω : ScalarThreeCochain G) :
    ofInhomogeneousCochain (toInhomogeneousCochain ω) = ω := by
  funext g h k
  simp [ofInhomogeneousCochain, toInhomogeneousCochain]

@[simp]
theorem toInhomogeneousCochain_ofInhomogeneousCochain
    (f : (Fin 3 → G) → scalarH2Representation G) :
    toInhomogeneousCochain (ofInhomogeneousCochain f) = f := by
  funext g
  simp only [toInhomogeneousCochain, ofInhomogeneousCochain, ofMul_toMul,
    AddEquiv.apply_symm_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Restriction `ScalarThreeCochain.comap f` is Mathlib's restriction of inhomogeneous
three-cochains, `groupCohomology.cochainsMap f`, with the identity coefficient map. -/
theorem toInhomogeneousCochain_comap {K : Type} [Group K] (f : K →* G)
    (ω : ScalarThreeCochain G) :
    toInhomogeneousCochain (comap f ω) =
      ((cochainsMap f (scalarRepresentationRes f)).f 3).hom (toInhomogeneousCochain ω) :=
  rfl

/-- Mathlib's degree-three differential of a scalar three-cochain, for the
trivial action on `ℂˣ`, is the ratio of the two sides of the three-cocycle
equation of arXiv:2502.20257, `eq:3-cocycle`. -/
theorem d_toInhomogeneousCochain (ω : ScalarThreeCochain G) (g : Fin 4 → G) :
    inhomogeneousCochains.d (scalarH2Representation G) 3 (toInhomogeneousCochain ω) g =
      scalarRepresentationEquiv G (Additive.ofMul
        (ω (g 1) (g 2) (g 3) / ω (g 0 * g 1) (g 2) (g 3) * ω (g 0) (g 1 * g 2) (g 3) /
          ω (g 0) (g 1) (g 2 * g 3) * ω (g 0) (g 1) (g 2))) := by
  apply (scalarRepresentationEquiv G).symm.injective
  rw [inhomogeneousCochains.d_hom_apply, Fin.sum_univ_four, scalarH2Representation_ρ_apply]
  simp only [toInhomogeneousCochain, Fin.contractNth, map_add, AddEquiv.symm_apply_apply]
  simp [ofMul_div, ofMul_mul]
  abel_nf
  rfl

omit [Group G] in
private theorem five_term_eq_one_iff {M : Type*} [CommGroup M] (a b c d e : M) :
    a / b * c / d * e = 1 ↔ b * d = e * c * a := by
  have key : a / b * c / d * e = a * c * e / (b * d) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ac_rfl
  rw [key, div_eq_one, eq_comm, show e * c * a = a * c * e by ac_rfl]

/-- The scalar three-cocycle equation of arXiv:2502.20257, `eq:3-cocycle`, is the
vanishing of Mathlib's degree-three differential for the trivial action on
`ℂˣ`. -/
theorem isCocycle_iff_d_eq_zero (ω : ScalarThreeCochain G) :
    IsCocycle ω ↔
      inhomogeneousCochains.d (scalarH2Representation G) 3 (toInhomogeneousCochain ω) = 0 := by
  constructor
  · intro h
    funext g
    rw [d_toInhomogeneousCochain, Pi.zero_apply, scalarRepresentationEquiv_ofMul_eq_zero_iff,
      five_term_eq_one_iff]
    exact h (g 0) (g 1) (g 2) (g 3)
  · intro h a b c e
    have := congrFun h ![a, b, c, e]
    rw [d_toInhomogeneousCochain, Pi.zero_apply, scalarRepresentationEquiv_ofMul_eq_zero_iff,
      five_term_eq_one_iff] at this
    simpa using this

end ScalarThreeCochain

namespace ScalarCocycle

/-- Mathlib's degree-two differential of a scalar two-cochain, for the trivial
action on `ℂˣ`, is the alternating product of its four face values. -/
theorem d_toInhomogeneousCochain_apply (β : ScalarCocycle G) (g : Fin 3 → G) :
    inhomogeneousCochains.d (scalarH2Representation G) 2 (toInhomogeneousCochain β) g =
      scalarRepresentationEquiv G (Additive.ofMul
        (β (g 1) (g 2) / β (g 0 * g 1) (g 2) * β (g 0) (g 1 * g 2) / β (g 0) (g 1))) := by
  apply (scalarRepresentationEquiv G).symm.injective
  rw [inhomogeneousCochains.d_hom_apply, Fin.sum_univ_three, scalarH2Representation_ρ_apply]
  simp only [toInhomogeneousCochain, Fin.contractNth, map_add, AddEquiv.symm_apply_apply]
  simp [ofMul_div, ofMul_mul]
  abel_nf
  rfl

/-- Mathlib's degree-two differential of a scalar two-cochain, for the trivial
action on `ℂˣ`, is its multiplicative three-coboundary from arXiv:2502.20257,
`eq:omegagauge`. -/
theorem d_toInhomogeneousCochain (β : ScalarCocycle G) :
    inhomogeneousCochains.d (scalarH2Representation G) 2 (toInhomogeneousCochain β) =
      ScalarThreeCochain.toInhomogeneousCochain (ScalarThreeCochain.coboundary β) := by
  funext g
  rw [d_toInhomogeneousCochain_apply]
  simp only [ScalarThreeCochain.toInhomogeneousCochain, ScalarThreeCochain.coboundary]
  congr 2
  simp only [div_eq_mul_inv, mul_inv_rev]
  ac_rfl

end ScalarCocycle

namespace ScalarThreeCochain

/-- Passing to inhomogeneous cochains turns pointwise quotients into
differences. -/
theorem toInhomogeneousCochain_div (ω η : ScalarThreeCochain G) :
    toInhomogeneousCochain (ω / η) = toInhomogeneousCochain ω - toInhomogeneousCochain η := by
  funext g
  simp [toInhomogeneousCochain, ofMul_div]

/-- The constant scalar three-cochain one is the zero inhomogeneous cochain. -/
@[simp]
theorem toInhomogeneousCochain_one :
    toInhomogeneousCochain (fun _ _ _ ↦ (1 : Units ℂ)) =
      (0 : (Fin 3 → G) → scalarH2Representation G) := by
  funext g
  simp [toInhomogeneousCochain]

theorem toInhomogeneousCochain_injective :
    Function.Injective (toInhomogeneousCochain (G := G)) :=
  Function.LeftInverse.injective ofInhomogeneousCochain_toInhomogeneousCochain

/-- A fusion gauge carries `η` to `ω` exactly when the three-coboundary of the
gauge is the pointwise quotient `ω / η`. -/
theorem fusionGauge_eq_iff (β : ScalarCocycle G) (ω η : ScalarThreeCochain G) :
    fusionGauge β η = ω ↔ coboundary β = ω / η := by
  rw [eq_div_iff_mul_eq']
  rfl

/-- Two scalar three-cochains are cohomologous in the sense of arXiv:2502.20257,
`eq:omegagauge`, exactly when the difference of their inhomogeneous cochains is
a Mathlib three-coboundary. No normalization is imposed on either side. -/
theorem cohomologousTo_iff_exists_d_eq (ω η : ScalarThreeCochain G) :
    CohomologousTo ω η ↔
      ∃ y : (Fin 2 → G) → scalarH2Representation G,
        inhomogeneousCochains.d (scalarH2Representation G) 2 y =
          toInhomogeneousCochain ω - toInhomogeneousCochain η := by
  constructor
  · rintro ⟨β, hβ⟩
    refine ⟨β.toInhomogeneousCochain, ?_⟩
    rw [ScalarCocycle.d_toInhomogeneousCochain, ← toInhomogeneousCochain_div,
      (fusionGauge_eq_iff β ω η).1 hβ]
  · rintro ⟨y, hy⟩
    refine ⟨ScalarCocycle.ofInhomogeneousCochain y, (fusionGauge_eq_iff _ ω η).2 ?_⟩
    apply toInhomogeneousCochain_injective
    rw [← ScalarCocycle.d_toInhomogeneousCochain,
      ScalarCocycle.toInhomogeneousCochain_ofInhomogeneousCochain, hy,
      toInhomogeneousCochain_div]

/-! ### Cocycles and cohomology classes -/

/-- A scalar three-cocycle as a Mathlib three-cocycle of the trivial
representation on `ℂˣ`. -/
def toCocycles (ω : {ω : ScalarThreeCochain G // IsCocycle ω}) :
    cocycles (scalarH2Representation G) 3 :=
  cocyclesMk (toInhomogeneousCochain ω.1) ((isCocycle_iff_d_eq_zero ω.1).1 ω.2)

@[simp]
theorem iCocycles_toCocycles (ω : {ω : ScalarThreeCochain G // IsCocycle ω}) :
    iCocycles (scalarH2Representation G) 3 (toCocycles ω) = toInhomogeneousCochain ω.1 :=
  iCocycles_mk _ ((isCocycle_iff_d_eq_zero ω.1).1 ω.2)

/-- A Mathlib three-cocycle of the trivial representation on `ℂˣ` as a scalar
three-cocycle. -/
def ofCocycles (x : cocycles (scalarH2Representation G) 3) :
    {ω : ScalarThreeCochain G // IsCocycle ω} :=
  ⟨ofInhomogeneousCochain (iCocycles (scalarH2Representation G) 3 x), by
    rw [isCocycle_iff_d_eq_zero, toInhomogeneousCochain_ofInhomogeneousCochain,
      ← inhomogeneousCochains.d_def]
    exact ConcreteCategory.congr_hom
      ((inhomogeneousCochains (scalarH2Representation G)).iCycles_d 3 4) x⟩

/-- Scalar three-cocycles in the sense of arXiv:2502.20257, `eq:3-cocycle`, are
Mathlib's three-cocycles of the trivial representation on `ℂˣ`. -/
def cocyclesEquiv :
    {ω : ScalarThreeCochain G // IsCocycle ω} ≃ cocycles (scalarH2Representation G) 3 where
  toFun := toCocycles
  invFun := ofCocycles
  left_inv ω := by
    apply Subtype.ext
    change ofInhomogeneousCochain (iCocycles (scalarH2Representation G) 3 (toCocycles ω)) = ω.1
    rw [iCocycles_toCocycles, ofInhomogeneousCochain_toInhomogeneousCochain]
  right_inv x := by
    apply (ModuleCat.mono_iff_injective (iCocycles (scalarH2Representation G) 3)).1
      inferInstance
    rw [iCocycles_toCocycles, ofCocycles, toInhomogeneousCochain_ofInhomogeneousCochain]

/-- The class of a scalar three-cocycle in Mathlib's degree-three group
cohomology `H³(G, ℂˣ)` of the trivial representation on `ℂˣ`. -/
def anomalyClass (ω : {ω : ScalarThreeCochain G // IsCocycle ω}) :
    groupCohomology (scalarH2Representation G) 3 :=
  π (scalarH2Representation G) 3 (toCocycles ω)

/-- Fusion-gauge equivalence of scalar three-cocycles, arXiv:2502.20257,
`eq:omegagauge`, is equality of their classes in `H³(G, ℂˣ)`. -/
theorem cohomologousTo_iff_anomalyClass_eq (ω η : {ω : ScalarThreeCochain G // IsCocycle ω}) :
    CohomologousTo ω.1 η.1 ↔ anomalyClass ω = anomalyClass η := by
  rw [anomalyClass, anomalyClass, ← sub_eq_zero, ← map_sub,
    groupCohomology_π_eq_zero_iff (scalarH2Representation G) 2, map_sub,
    iCocycles_toCocycles, iCocycles_toCocycles, cohomologousTo_iff_exists_d_eq]

/-- A scalar three-cocycle has trivial fusion-gauge class exactly when its class
in `H³(G, ℂˣ)` vanishes. -/
theorem isTrivialGaugeClass_iff_anomalyClass_eq_zero
    (ω : {ω : ScalarThreeCochain G // IsCocycle ω}) :
    IsTrivialGaugeClass ω.1 ↔ anomalyClass ω = 0 := by
  rw [IsTrivialGaugeClass, cohomologousTo_iff_exists_d_eq, toInhomogeneousCochain_one,
    sub_zero, anomalyClass, groupCohomology_π_eq_zero_iff (scalarH2Representation G) 2,
    iCocycles_toCocycles]

/-- Every class in `H³(G, ℂˣ)` is the class of a scalar three-cocycle. -/
theorem anomalyClass_surjective : Function.Surjective (anomalyClass (G := G)) := by
  intro c
  induction c using groupCohomology_induction_on with
  | h x => exact ⟨ofCocycles x, congrArg _ ((cocyclesEquiv (G := G)).apply_symm_apply x)⟩

end ScalarThreeCochain

end TNLean.Algebra
