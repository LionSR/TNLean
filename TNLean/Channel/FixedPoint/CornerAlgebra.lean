/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Peripheral.CyclicDecomposition.Basic
import Mathlib.RingTheory.Idempotents

/-!
# Complex-algebra and star structures on the idempotent corner

Mathlib's `IsIdempotentElem.Corner` already provides the `Semiring` / `Ring` structure on the
subsemigroup `Set.range (P * · * P)` for an idempotent `P`, with unit `P`. For the matrix
corners appearing in the support-projection route for Wolf Cor. 6.6 we additionally need:

* a `ℂ`-module and `ℂ`-algebra structure on the corner;
* star, `StarRing`, and `StarModule ℂ` structures when `P` is self-adjoint;
* a `ℂ`-linear equivalence with the repository's
  `cornerSubmodule P = {X | P * X * P = X}`.

This file supplies those instances for `P : Matrix (Fin D) (Fin D) ℂ` and the linear
equivalence `cornerSubmodule P ≃ₗ[ℂ] IsIdempotentElem.Corner hP`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Cor. 6.6].
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix

namespace MatrixCorner

variable {D : ℕ} {P : Matrix (Fin D) (Fin D) ℂ}

private lemma mem_corner_iff_matrix (hP : IsIdempotentElem P)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    X ∈ Subsemigroup.corner P ↔ P * X = X ∧ X * P = X :=
  Subsemigroup.mem_corner_iff hP

/-! ### `ℂ`-linear structure -/

instance instSMulComplexCorner (hP : IsIdempotentElem P) : SMul ℂ hP.Corner where
  smul c X := ⟨c • X.1, by
    obtain ⟨hL, hR⟩ := (mem_corner_iff_matrix hP X.1).mp X.2
    refine (mem_corner_iff_matrix hP _).mpr ⟨?_, ?_⟩
    · rw [Matrix.mul_smul, hL]
    · rw [smul_mul_assoc, hR]⟩

@[simp] lemma smul_val (hP : IsIdempotentElem P) (c : ℂ) (X : hP.Corner) :
    (c • X).1 = c • X.1 := rfl

instance instMulActionComplexCorner (hP : IsIdempotentElem P) : MulAction ℂ hP.Corner where
  one_smul X := Subtype.ext (one_smul ℂ X.1)
  mul_smul c d X := Subtype.ext (mul_smul c d X.1)

instance instDistribMulActionComplexCorner (hP : IsIdempotentElem P) :
    DistribMulAction ℂ hP.Corner where
  smul_zero c := Subtype.ext (smul_zero c)
  smul_add c X Y := Subtype.ext (smul_add c X.1 Y.1)

instance instModuleComplexCorner (hP : IsIdempotentElem P) : Module ℂ hP.Corner where
  add_smul c d X := Subtype.ext (add_smul c d X.1)
  zero_smul X := Subtype.ext (zero_smul ℂ X.1)

/-- The algebra map `ℂ → hP.Corner` sending `c` to `c • P`. -/
noncomputable def cornerAlgebraMap (hP : IsIdempotentElem P) : ℂ →+* hP.Corner where
  toFun c := ⟨c • P, by
    refine (mem_corner_iff_matrix hP _).mpr ⟨?_, ?_⟩
    · rw [Matrix.mul_smul, hP.eq]
    · rw [smul_mul_assoc, hP.eq]⟩
  map_one' := Subtype.ext (one_smul ℂ P)
  map_mul' c d := Subtype.ext <| by
    change (c * d) • P = (c • P) * (d • P)
    rw [smul_mul_smul_comm, hP.eq]
  map_zero' := Subtype.ext (zero_smul ℂ P)
  map_add' c d := Subtype.ext (add_smul c d P)

@[simp] lemma cornerAlgebraMap_apply_val (hP : IsIdempotentElem P) (c : ℂ) :
    (cornerAlgebraMap hP c).1 = c • P := rfl

noncomputable instance instAlgebraComplexCorner (hP : IsIdempotentElem P) :
    Algebra ℂ hP.Corner where
  algebraMap := cornerAlgebraMap hP
  commutes' c X := by
    apply Subtype.ext
    obtain ⟨hL, hR⟩ := (mem_corner_iff_matrix hP X.1).mp X.2
    change (c • P) * X.1 = X.1 * (c • P)
    rw [smul_mul_assoc, Matrix.mul_smul, hL, hR]
  smul_def' c X := by
    apply Subtype.ext
    obtain ⟨hL, _⟩ := (mem_corner_iff_matrix hP X.1).mp X.2
    change c • X.1 = (c • P) * X.1
    rw [smul_mul_assoc, hL]

/-! ### Star structure for a self-adjoint idempotent

The `Star`, `InvolutiveStar`, `StarMul`, `StarAddMonoid`, `StarRing`, and `StarModule ℂ` instances
on `hP.Corner` require the self-adjointness hypothesis `Pᴴ = P`. Because this hypothesis is
data-level, the structures below are given as `def`s rather than global `instance`s; callers
should introduce them locally with `letI` at each use site.
-/

section Star

variable (hP : IsIdempotentElem P) (hPstar : Pᴴ = P)

/-- Star on `hP.Corner` given self-adjointness of `P`. -/
@[reducible] noncomputable def cornerStar : Star hP.Corner where
  star X := ⟨X.1ᴴ, by
    obtain ⟨hL, hR⟩ := (mem_corner_iff_matrix hP X.1).mp X.2
    refine (mem_corner_iff_matrix hP _).mpr ⟨?_, ?_⟩
    · calc P * X.1ᴴ = Pᴴ * X.1ᴴ := by rw [hPstar]
        _ = (X.1 * P)ᴴ := by rw [← Matrix.conjTranspose_mul]
        _ = X.1ᴴ := by rw [hR]
    · calc X.1ᴴ * P = X.1ᴴ * Pᴴ := by rw [hPstar]
        _ = (P * X.1)ᴴ := by rw [← Matrix.conjTranspose_mul]
        _ = X.1ᴴ := by rw [hL]⟩

@[simp] lemma cornerStar_val
    (X : hP.Corner) :
    letI : Star hP.Corner := cornerStar hP hPstar
    (Star.star X).1 = X.1ᴴ := rfl

/-- `InvolutiveStar` structure on `hP.Corner` given self-adjointness of `P`. -/
@[reducible] noncomputable def cornerInvolutiveStar : InvolutiveStar hP.Corner :=
  letI : Star hP.Corner := cornerStar hP hPstar
  { star := Star.star
    star_involutive := fun X => Subtype.ext (Matrix.conjTranspose_conjTranspose X.1) }

/-- `StarMul` structure on `hP.Corner` given self-adjointness of `P`. -/
@[reducible] noncomputable def cornerStarMul : StarMul hP.Corner :=
  letI : InvolutiveStar hP.Corner := cornerInvolutiveStar hP hPstar
  { star_involutive := InvolutiveStar.star_involutive
    star_mul := fun X Y => Subtype.ext (Matrix.conjTranspose_mul X.1 Y.1) }

/-- `StarAddMonoid` structure on `hP.Corner` given self-adjointness of `P`. -/
@[reducible] noncomputable def cornerStarAddMonoid : StarAddMonoid hP.Corner :=
  letI : InvolutiveStar hP.Corner := cornerInvolutiveStar hP hPstar
  { star_involutive := InvolutiveStar.star_involutive
    star_add := fun X Y => Subtype.ext (Matrix.conjTranspose_add X.1 Y.1) }

/-- `StarRing` structure on `hP.Corner` given self-adjointness of `P`. -/
@[reducible] noncomputable def cornerStarRing : StarRing hP.Corner :=
  letI : StarMul hP.Corner := cornerStarMul hP hPstar
  letI : StarAddMonoid hP.Corner := cornerStarAddMonoid hP hPstar
  { star := Star.star
    star_involutive := InvolutiveStar.star_involutive
    star_mul := StarMul.star_mul
    star_add := StarAddMonoid.star_add }

/-- `StarModule ℂ` on `hP.Corner` given self-adjointness of `P`. -/
@[reducible] noncomputable def cornerStarModuleComplex :
    letI : Star hP.Corner := cornerStar hP hPstar
    StarModule ℂ hP.Corner :=
  letI : Star hP.Corner := cornerStar hP hPstar
  { star_smul := fun c X => Subtype.ext <| by
      change (c • X.1)ᴴ = Star.star c • X.1ᴴ
      exact Matrix.conjTranspose_smul c X.1 }

end Star

/-! ### Identification with the repository's `cornerSubmodule` -/

section CornerSubmoduleIdentification

/-- For an idempotent `P`, `cornerSubmodule P = {X | P * X * P = X}` has the same underlying set
as `Subsemigroup.corner P = Set.range (P * · * P)`. -/
lemma cornerSubmodule_mem_iff_mem_corner
    (hP : IsIdempotentElem P) (X : Matrix (Fin D) (Fin D) ℂ) :
    X ∈ cornerSubmodule P ↔ X ∈ Subsemigroup.corner P := by
  constructor
  · intro h
    have h' : P * X * P = X := h
    exact ⟨X, by simp [h']⟩
  · intro h
    obtain ⟨hL, hR⟩ := (mem_corner_iff_matrix hP X).mp h
    change P * X * P = X
    rw [Matrix.mul_assoc, hR, hL]

/-- The `ℂ`-linear equivalence `cornerSubmodule P ≃ₗ[ℂ] IsIdempotentElem.Corner hP` for an
idempotent matrix `P`, given by the identity on underlying matrices. -/
def cornerSubmoduleCornerEquiv (hP : IsIdempotentElem P) :
    cornerSubmodule P ≃ₗ[ℂ] hP.Corner where
  toFun X := ⟨X.1, (cornerSubmodule_mem_iff_mem_corner hP X.1).mp X.2⟩
  invFun X := ⟨X.1, (cornerSubmodule_mem_iff_mem_corner hP X.1).mpr X.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma cornerSubmoduleCornerEquiv_apply_val
    (hP : IsIdempotentElem P) (X : cornerSubmodule P) :
    (cornerSubmoduleCornerEquiv hP X).1 = X.1 := rfl

@[simp] lemma cornerSubmoduleCornerEquiv_symm_apply_val
    (hP : IsIdempotentElem P) (X : hP.Corner) :
    ((cornerSubmoduleCornerEquiv hP).symm X).1 = X.1 := rfl

end CornerSubmoduleIdentification

end MatrixCorner
