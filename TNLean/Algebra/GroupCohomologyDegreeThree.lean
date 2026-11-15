/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Degree-three group cohomology

This extends Mathlib's low-degree interface to degree three. All cocycles and
cohomology classes are computed by Mathlib's inhomogeneous cochain complex.
Coefficients may have a nontrivial action; no normalization is imposed.

## Main definitions

* `groupCohomology.d₃₄`: the differential on functions on triples.
* `groupCohomology.cocycles₃`, `groupCohomology.coboundaries₃`: its kernel
  and the image of Mathlib's `groupCohomology.d₂₃`.
* `groupCohomology.IsMulCocycle₃`: the multiplicative three-cocycle equation.
* `groupCohomology.H3π`: the projection to Mathlib's third cohomology.

## Main results

* `groupCohomology.H3π_eq_iff`: two cocycles have the same class exactly when
  their difference is a coboundary.
* `groupCohomology.d₂₃_toMul`: the multiplicative formula for a coboundary.

## References

* Mathlib, `Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree`.
* TNLean issue #8319, the degree-three foundation for the Mathlib migration.
-/

noncomputable section

universe u

open CategoryTheory Limits Representation

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

/-! ### Cochains and differentials -/

/-- Four inhomogeneous coordinates written as a tuple. -/
def cochainsIso₄ : (inhomogeneousCochains A).X 4 ≅ ↧(G × G × G × G → A) :=
  (LinearEquiv.funCongrLeft k A ((Fin.consEquiv _).symm.trans
    ((Equiv.refl G).prodCongr ((Fin.consEquiv _).symm.trans
      ((Equiv.refl G).prodCongr (piFinTwoEquiv fun _ ↦ G)))))).toModuleIso.symm

/-- The third differential, written on triples rather than functions on `Fin 3`. -/
@[simps!]
def d₃₄ : ModuleCat.of k (G × G × G → A) ⟶ ModuleCat.of k (G × G × G × G → A) :=
  ModuleCat.ofHom
  { toFun f g :=
      A.ρ g.1 (f g.2) - f (g.1 * g.2.1, g.2.2) +
        f (g.1, g.2.1 * g.2.2.1, g.2.2.2) -
        f (g.1, g.2.1, g.2.2.1 * g.2.2.2) + f (g.1, g.2.1, g.2.2.1)
    map_add' f h := by
      ext g
      dsimp
      rw [map_add]
      abel
    map_smul' r f := by
      ext g
      dsimp
      simp only [map_smul, smul_add, smul_sub] }

/-- The tuple differential is the differential of Mathlib's cochain complex. -/
theorem comp_d₃₄_eq :
    (cochainsIso₃ A).hom ≫ d₃₄ A =
      (inhomogeneousCochains A).d 3 4 ≫ (cochainsIso₄ A).hom := by
  ext x y
  change A.ρ y.1 (x _) - x _ + x _ - x _ + x _ = _ + _
  dsimp
  rw [Fin.sum_univ_four]
  simp only [sub_eq_add_neg, add_assoc, Fin.val_zero, Fin.val_one, Fin.val_two,
    show (3 : Fin 4).val = 3 from rfl, Nat.reduceAdd, pow_succ', pow_zero,
    mul_neg_one, neg_neg, mul_one, one_mul, neg_smul, one_smul]
  rcongr i <;> fin_cases i <;> rfl

@[reassoc, elementwise]
theorem eq_d₃₄_comp_inv :
    (cochainsIso₃ A).inv ≫ (inhomogeneousCochains A).d 3 4 =
      d₃₄ A ≫ (cochainsIso₄ A).inv :=
  (CommSq.horiz_inv ⟨comp_d₃₄_eq A⟩).w

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem d₂₃_comp_d₃₄ : d₂₃ A ≫ d₃₄ A = 0 := by
  ext f g
  simp [mul_assoc, Pi.zero_apply (M := fun _ ↦ A)]
  abel

/-- The short complex calculating cohomology in degree three in tuple coordinates. -/
@[simps! -isSimp f g]
def shortComplexH3 : ShortComplex (ModuleCat k) :=
  ShortComplex.mk (d₂₃ A) (d₃₄ A) (d₂₃_comp_d₃₄ A)

/-! ### Cocycles and coboundaries -/

/-- Three-cocycles as the kernel of the third differential. -/
def cocycles₃ : Submodule k (G × G × G → A) := LinearMap.ker (d₃₄ A).hom

/-- Three-coboundaries as the image of the second differential. -/
def coboundaries₃ : Submodule k (G × G × G → A) := LinearMap.range (d₂₃ A).hom

variable {A}

@[macro_inline]
instance : FunLike (cocycles₃ A) (G × G × G) A := ⟨Subtype.val, Subtype.val_injective⟩

@[simp]
theorem cocycles₃.coe_mk (f : G × G × G → A) (hf) :
    ((⟨f, hf⟩ : cocycles₃ A) : G × G × G → A) = f := rfl

@[simp]
theorem cocycles₃.val_eq_coe (f : cocycles₃ A) : f.1 = f := rfl

@[ext]
theorem cocycles₃_ext {f h : cocycles₃ A}
    (hfh : ∀ a b c : G, f (a, b, c) = h (a, b, c)) : f = h :=
  DFunLike.ext f h (Prod.forall.mpr fun a ↦ Prod.forall.mpr (hfh a))

theorem mem_cocycles₃_def (f : G × G × G → A) :
    f ∈ cocycles₃ A ↔ ∀ a b c d : G,
      A.ρ a (f (b, c, d)) - f (a * b, c, d) + f (a, b * c, d) -
        f (a, b, c * d) + f (a, b, c) = 0 :=
  LinearMap.mem_ker.trans <| by
    simp_rw [funext_iff, d₃₄_hom_apply, Prod.forall]
    rfl

/-- The additive three-cocycle equation. -/
theorem mem_cocycles₃_iff (f : G × G × G → A) :
    f ∈ cocycles₃ A ↔ ∀ a b c d : G,
      f (a * b, c, d) + f (a, b, c * d) =
        A.ρ a (f (b, c, d)) + f (a, b * c, d) + f (a, b, c) := by
  rw [mem_cocycles₃_def]
  refine forall_congr' fun a ↦ forall_congr' fun b ↦
    forall_congr' fun c ↦ forall_congr' fun d ↦ ?_
  rw [show A.ρ a (f (b, c, d)) - f (a * b, c, d) + f (a, b * c, d) -
      f (a, b, c * d) + f (a, b, c) =
      (A.ρ a (f (b, c, d)) + f (a, b * c, d) + f (a, b, c)) -
        (f (a * b, c, d) + f (a, b, c * d)) by abel, sub_eq_zero, eq_comm]

theorem d₂₃_apply_mem_cocycles₃ (f : G × G → A) :
    d₂₃ A f ∈ cocycles₃ A :=
  d₂₃_comp_d₃₄_apply _ _

@[simp]
theorem cocycles₃.d₃₄_apply (f : cocycles₃ A) : d₃₄ A f = 0 := f.2

variable (A) in
theorem coboundaries₃_le_cocycles₃ : coboundaries₃ A ≤ cocycles₃ A := by
  rintro _ ⟨f, rfl⟩
  exact d₂₃_apply_mem_cocycles₃ f

/-! ### Multiplicative coefficients -/

section

variable {G M : Type*} [Mul G] [CommGroup M] [SMul G M]

/-- The multiplicative three-cocycle equation with the specified coefficient action. -/
def IsMulCocycle₃ (f : G × G × G → M) : Prop :=
  ∀ a b c d : G, f (a * b, c, d) * f (a, b, c * d) =
    a • f (b, c, d) * f (a, b * c, d) * f (a, b, c)

/-- A three-cochain is a coboundary if it is the differential of a two-cochain. -/
def IsMulCoboundary₃ (f : G × G × G → M) : Prop :=
  ∃ β : G × G → M, ∀ a b c : G,
    a • β (b, c) / β (a * b, c) * β (a, b * c) / β (a, b) = f (a, b, c)

end

section

variable {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]

/-- A multiplicative three-cocycle is a cocycle of the induced additive representation. -/
@[simps]
def cocyclesOfIsMulCocycle₃ {f : G × G × G → M} (hf : IsMulCocycle₃ f) :
    cocycles₃ (Rep.ofMulDistribMulAction G M) :=
  ⟨Additive.ofMul ∘ f, (mem_cocycles₃_iff (A := Rep.ofMulDistribMulAction G M) f).2 hf⟩

theorem isMulCocycle₃_of_mem_cocycles₃ (f : G × G × G → M)
    (hf : f ∈ cocycles₃ (Rep.ofMulDistribMulAction G M)) :
    IsMulCocycle₃ (Additive.toMul ∘ f) :=
  (mem_cocycles₃_iff (A := Rep.ofMulDistribMulAction G M) f).1 hf

/-- Mathlib's second differential is the alternating multiplicative coboundary. -/
theorem d₂₃_toMul (β : G × G → M) (a b c : G) :
    Additive.toMul
      (d₂₃ (Rep.ofMulDistribMulAction G M) (Additive.ofMul ∘ β) (a, b, c)) =
        a • β (b, c) / β (a * b, c) * β (a, b * c) / β (a, b) := rfl

/-- A multiplicative coboundary is a coboundary of the induced additive representation. -/
def coboundariesOfIsMulCoboundary₃ {f : G × G × G → M} (hf : IsMulCoboundary₃ f) :
    coboundaries₃ (Rep.ofMulDistribMulAction G M) :=
  ⟨Additive.ofMul ∘ f, hf.choose,
    funext fun g ↦ hf.choose_spec g.1 g.2.1 g.2.2⟩

theorem isMulCoboundary₃_of_mem_coboundaries₃ (f : G × G × G → M)
    (hf : f ∈ coboundaries₃ (Rep.ofMulDistribMulAction G M)) :
    IsMulCoboundary₃ (Additive.toMul ∘ f) := by
  rcases hf with ⟨β, rfl⟩
  exact ⟨β, fun _ _ _ ↦ rfl⟩

end

/-! ### Comparison with the inhomogeneous complex -/

open ShortComplex

variable (A)

set_option backward.isDefEq.respectTransparency.types false in
/-- The third short complex in tuple coordinates is Mathlib's third short complex. -/
@[simps! hom inv]
def isoShortComplexH3 :
    (inhomogeneousCochains A).sc 3 ≅ shortComplexH3 A :=
  (inhomogeneousCochains A).isoSc' 2 3 4 (by simp) (by simp) ≪≫
    isoMk (cochainsIso₂ A) (cochainsIso₃ A) (cochainsIso₄ A)
      (comp_d₂₃_eq A) (comp_d₃₄_eq A)

/-- Tuple three-cocycles are the cycles of Mathlib's inhomogeneous cochain complex. -/
def isoCocycles₃ : cocycles A 3 ≅ ↧(cocycles₃ A) :=
  cyclesMapIso' (isoShortComplexH3 A) _ (shortComplexH3 A).moduleCatLeftHomologyData

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem isoCocycles₃_hom_comp_i :
    (isoCocycles₃ A).hom ≫ (shortComplexH3 A).moduleCatLeftHomologyData.i =
      iCocycles A 3 ≫ (cochainsIso₃ A).hom := by
  simp [isoCocycles₃, iCocycles, HomologicalComplex.iCycles, iCycles]

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem isoCocycles₃_inv_comp_iCocycles :
    (isoCocycles₃ A).inv ≫ iCocycles A 3 =
      (shortComplexH3 A).moduleCatLeftHomologyData.i ≫ (cochainsIso₃ A).inv :=
  (CommSq.horiz_inv ⟨isoCocycles₃_hom_comp_i A⟩).w

/-! ### Third cohomology -/

/-- Mathlib's third group cohomology. -/
abbrev H3 := groupCohomology A 3

/-- The projection from tuple three-cocycles to Mathlib's third cohomology. -/
def H3π : ↧(cocycles₃ A) ⟶ H3 A :=
  (isoCocycles₃ A).inv ≫ π A 3

set_option backward.isDefEq.respectTransparency false in
instance : Epi (H3π A) := inferInstanceAs <| Epi (_ ≫ _)

variable {A}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A three-cocycle has zero class exactly when it is a coboundary. -/
theorem H3π_eq_zero_iff (x : cocycles₃ A) : H3π A x = 0 ↔ ⇑x ∈ coboundaries₃ A := by
  have h := leftHomologyπ_naturality'_assoc (isoShortComplexH3 A).inv
    (shortComplexH3 A).moduleCatLeftHomologyData (leftHomologyData _)
    ((inhomogeneousCochains A).sc 3).leftHomologyIso.hom
  simp only [H3π, isoCocycles₃, π, HomologicalComplex.homologyπ, homologyπ,
    cyclesMapIso'_inv, leftHomologyπ, ← h, ← leftHomologyMapIso'_inv, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply, map_eq_zero_iff _
    ((ModuleCat.mono_iff_injective _).1 inferInstance)]
  simp [LinearMap.range_codRestrict, coboundaries₃, shortComplexH3, cocycles₃]

/-- Two three-cocycles have equal classes exactly when their difference is a coboundary. -/
theorem H3π_eq_iff (x y : cocycles₃ A) :
    H3π A x = H3π A y ↔ ⇑x - ⇑y ∈ coboundaries₃ A := by
  rw [← sub_eq_zero, ← map_sub, H3π_eq_zero_iff]
  rfl

@[elab_as_elim]
theorem H3_induction_on {C : H3 A → Prop} (x : H3 A)
    (h : ∀ y : cocycles₃ A, C (H3π A y)) : C x :=
  groupCohomology_induction_on x fun y ↦ by simpa [H3π] using h ((isoCocycles₃ A).hom y)

end groupCohomology
