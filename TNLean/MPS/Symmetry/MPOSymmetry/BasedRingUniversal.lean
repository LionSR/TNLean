/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Symmetry.MPOSymmetry.BasedRing

/-!
# Universal property of the integer fusion ring

Project results: basis values determine a ring homomorphism uniquely, and
ring-valued fusion characters correspond to ring homomorphisms. The faithful
regular action identifies the abstract ring operations with the prescribed
integer basis expansion. Targets may be noncommutative rings.
-/

noncomputable section

namespace MPOTensor.FusionRing

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The regular representation as a unital ring homomorphism. -/
def regularHom (F : FusionRing ι) : F.Carrier →+* Matrix ι ι ℤ :=
  F.nimRepHom F.constants F.laws.isNIMRep (fun x y ↦ by
    simpa only [eq_comm] using (F.laws.isFusionUnit x y).1)

/-- The basis matrices of the regular representation are the fusion matrices. -/
@[simp]
theorem regularHom_basis (F : FusionRing ι) (a : ι) :
    F.regularHom (F.basis a) = integerNIMRepMatrix F.constants a :=
  F.nimRepHom_basis _ _ _ a

/-- The regular representation is faithful. -/
theorem regularHom_injective (F : FusionRing ι) : Function.Injective F.regularHom := by
  change Function.Injective (integerNIMRepEval F.constants)
  exact F.laws.integerNIMRepEval_injective

/-- Products of basis elements have the prescribed natural structure constants. -/
theorem basis_mul (F : FusionRing ι) (a b : ι) :
    F.basis a * F.basis b = ∑ c, (F.constants a b c : ℤ) • F.basis c := by
  apply F.regularHom_injective
  simp only [map_mul, map_sum, map_zsmul, regularHom_basis]
  exact F.laws.isNIMRep.integerNIMRepMatrix_mul a b

/-- Every element is the integer combination of its basis coefficients. -/
theorem sum_smul_basis (F : FusionRing ι) (u : F.Carrier) :
    (∑ a, u a • F.basis a) = u := by
  apply F.regularHom_injective
  simp only [map_sum, map_zsmul, regularHom_basis]
  rfl

/-- Ring homomorphisms from a fusion ring are determined by their basis values. -/
theorem hom_ext (F : FusionRing ι) {R : Type*} [Ring R]
    {f g : F.Carrier →+* R} (h : ∀ a, f (F.basis a) = g (F.basis a)) : f = g := by
  apply RingHom.ext
  intro u
  calc
    f u = f (∑ a, u a • F.basis a) := congrArg f (F.sum_smul_basis u).symm
    _ = ∑ a, u a • f (F.basis a) := by simp only [map_sum, map_zsmul]
    _ = ∑ a, u a • g (F.basis a) := by simp only [h]
    _ = g (∑ a, u a • F.basis a) := by simp only [map_sum, map_zsmul]
    _ = g u := congrArg g (F.sum_smul_basis u)

/-- The extension of a compatible unital family is unique. -/
theorem lift_unique (F : FusionRing ι) {R : Type*} [Ring R] (f : ι → R)
    (hunit : f F.unit = 1)
    (hmul : ∀ a b, f a * f b = ∑ c, (F.constants a b c : ℤ) • f c)
    (g : F.Carrier →+* R) (hg : ∀ a, g (F.basis a) = f a) :
    g = F.lift f hunit hmul := by
  apply F.hom_ext
  intro a
  simpa only [lift_basis] using hg a

/-- Restricting a ring homomorphism to the fusion basis gives a character. -/
theorem isFusionCharacter_basis (F : FusionRing ι) {R : Type*} [Ring R]
    (f : F.Carrier →+* R) :
    IsFusionCharacter F.constants F.unit (fun a ↦ f (F.basis a)) := by
  constructor
  · simp only [basis_unit, map_one]
  · intro a b
    calc
      f (F.basis a) * f (F.basis b) = f (F.basis a * F.basis b) := (map_mul f _ _).symm
      _ = ∑ c, (F.constants a b c : ℤ) • f (F.basis c) := by
        rw [basis_mul, map_sum]
        simp only [map_zsmul]
      _ = ∑ c, (F.constants a b c : R) * f (F.basis c) := by
        simp only [← Int.cast_smul_eq_zsmul R, Int.cast_natCast, smul_eq_mul]

/-- Ring-valued fusion characters correspond exactly to unital ring homomorphisms.
The target is a ring; semiring-valued characters require a separate scalar extension. -/
def characterEquiv (F : FusionRing ι) {R : Type*} [Ring R] :
    (F.Carrier →+* R) ≃ {χ : ι → R // IsFusionCharacter F.constants F.unit χ} where
  toFun f := ⟨fun a ↦ f (F.basis a), F.isFusionCharacter_basis f⟩
  invFun χ := F.characterHom χ.1 χ.2
  left_inv f := by
    apply F.hom_ext
    intro a
    exact F.characterHom_basis _ _ a
  right_inv χ := by
    apply Subtype.ext
    funext a
    exact F.characterHom_basis χ.1 χ.2 a

/-- A unital NIM-representation has a unique RingHom with the specified basis images.
The unit condition remains explicit, and the matrices use output rows and input columns. -/
theorem nimRepHom_unique (F : FusionRing ι) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : ι → κ → κ → ℕ) (hM : IsNIMRep F.constants M)
    (hunit : ∀ x y, M F.unit x y = if x = y then 1 else 0)
    (g : F.Carrier →+* Matrix κ κ ℤ)
    (hg : ∀ a, g (F.basis a) = integerNIMRepMatrix M a) :
    g = F.nimRepHom M hM hunit := by
  apply F.hom_ext
  intro a
  simpa only [nimRepHom_basis] using hg a

end MPOTensor.FusionRing
