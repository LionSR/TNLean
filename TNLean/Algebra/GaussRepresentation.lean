/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Complex.Basic
import TNLean.Algebra.UnitaryFactorizationComparison

/-!
# Local Gauss representation from unitary factorization comparisons

For a finite group `G`, the gauge labels transform by

`T_g(a,b) = (a * g⁻¹, g * b)`.

Given unitary matter operators `R a b`, the corresponding local Gauss operator
has the block from `(a,b)` to `T_g(a,b)` equal to

`(R (T_g(a,b)))⁻¹ * R a b`.

This is the representation part of FBC25, Proposition `prop:gausslaws` and
Equation `eq:mcG` (arXiv:2502.20257, lines 3380--3387). Gauged-tensor
invariance and placement on a chain are not treated here.
-/

noncomputable section

namespace TNLean.Algebra

variable {G n : Type*} [Group G]

/-- The two-leg gauge-label permutation
`T_g(a,b) = (a * g⁻¹, g * b)` from FBC25, Equation `eq:mcG`
(arXiv:2502.20257, lines 3380--3387). -/
def gaussLegAction (g : G) : G × G ≃ G × G where
  toFun p := (p.1 * g⁻¹, g * p.2)
  invFun p := (p.1 * g, g⁻¹ * p.2)
  left_inv p := by simp
  right_inv p := by simp

@[simp]
theorem gaussLegAction_apply (g : G) (a b : G) :
    gaussLegAction g (a, b) = (a * g⁻¹, g * b) :=
  rfl

@[simp]
theorem gaussLegAction_one : gaussLegAction (1 : G) = 1 := by
  ext p <;> simp [gaussLegAction]

/-- The paper's label permutations compose in representation order:
`T_g ∘ T_h = T_{g * h}`. -/
theorem gaussLegAction_mul (g h : G) :
    gaussLegAction g * gaussLegAction h = gaussLegAction (g * h) := by
  ext p <;> simp [gaussLegAction, mul_assoc]

variable [Fintype n] [DecidableEq n]

/-- The local Gauss operator whose unique nonzero gauge block in column
`(a,b)` lies in row `T_g(a,b)` and equals
`(R (T_g(a,b)))⁻¹ R(a,b)`.

This is exactly
`G_g = ∑_{a,b} λ_{a,b}^{a g⁻¹,g b} ⊗ |a g⁻¹,g b⟩⟨a,b|`
from FBC25, Equation `eq:mcG` (arXiv:2502.20257, lines 3380--3387), with
`λ` supplied by `Matrix.unitaryFactorizationComparison`. -/
def gaussOperator (R : G → G → Matrix.unitaryGroup n ℂ) (g : G) :
    Matrix (n × (G × G)) (n × (G × G)) ℂ := by
  classical
  exact fun x y ↦
    if x.2 = gaussLegAction g y.2 then
      (Matrix.unitaryFactorizationComparison R y.2.1 y.2.2 x.2.1 x.2.2 :
        Matrix n n ℂ) x.1 y.1
    else 0

/-- The nonzero block of the Gauss operator is the factorization comparison
specified in FBC25, Equation `eq:mcG`. -/
@[simp]
theorem gaussOperator_apply_target
    (R : G → G → Matrix.unitaryGroup n ℂ) (g a b : G) (i j : n) :
    gaussOperator R g (i, gaussLegAction g (a, b)) (j, (a, b)) =
      (Matrix.unitaryFactorizationComparison R a b (a * g⁻¹) (g * b) :
        Matrix n n ℂ) i j := by
  classical
  simp [gaussOperator]

/-- Every other gauge block in a fixed column of the Gauss operator vanishes. -/
@[simp]
theorem gaussOperator_apply_of_ne
    (R : G → G → Matrix.unitaryGroup n ℂ) (g : G)
    (x y : n × (G × G)) (hxy : x.2 ≠ gaussLegAction g y.2) :
    gaussOperator R g x y = 0 := by
  classical
  simp [gaussOperator, hxy]

variable [Fintype G]

/-- Local Gauss operators multiply according to the group law. This is the
first conclusion of FBC25, Proposition `prop:gausslaws`
(arXiv:2502.20257, lines 3380--3387). -/
theorem gaussOperator_mul
    (R : G → G → Matrix.unitaryGroup n ℂ) (g h : G) :
    gaussOperator R g * gaussOperator R h = gaussOperator R (g * h) := by
  classical
  ext x y
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
  rw [Fintype.sum_eq_single (gaussLegAction h y.2)]
  · have hcomp : gaussLegAction g (gaussLegAction h y.2) =
        gaussLegAction (g * h) y.2 := by
      simp [gaussLegAction, mul_assoc]
    by_cases hxy : x.2 = gaussLegAction (g * h) y.2
    · have hx : x.2 = gaussLegAction g (gaussLegAction h y.2) :=
        hxy.trans hcomp.symm
      simp only [gaussOperator, hx, hcomp, ite_true]
      rw [← Matrix.mul_apply]
      exact (congrFun₂ (congrArg Subtype.val
        (Matrix.unitaryFactorizationComparison_trans R y.2.1 y.2.2
          (gaussLegAction h y.2).1 (gaussLegAction h y.2).2
          (gaussLegAction (g * h) y.2).1 (gaussLegAction (g * h) y.2).2)) x.1 y.1).symm
    · have hx : x.2 ≠ gaussLegAction g (gaussLegAction h y.2) := fun heq ↦
        hxy (heq.trans hcomp)
      simp [gaussOperator, hx, hxy]
  · intro q hq
    simp [gaussOperator, hq]

variable [DecidableEq G]

omit [Fintype G] in
/-- The Gauss operator of the identity group element is the identity matrix. -/
@[simp]
theorem gaussOperator_one (R : G → G → Matrix.unitaryGroup n ℂ) :
    gaussOperator R 1 = 1 := by
  classical
  ext x y
  by_cases hxy : x.2 = y.2
  · by_cases hij : x.1 = y.1
    · have hfull : x = y := Prod.ext hij hxy
      subst y
      simp [gaussOperator]
    · have hfull : x ≠ y := fun h ↦ hij (congrArg Prod.fst h)
      simp [gaussOperator, hxy, hij, hfull]
  · have hfull : x ≠ y := fun h ↦ hxy (congrArg Prod.snd h)
    simp [gaussOperator, hxy, hfull]

omit [Fintype G] [DecidableEq G] in
/-- The adjoint of a local Gauss operator is the operator for the inverse group
element. -/
theorem star_gaussOperator
    (R : G → G → Matrix.unitaryGroup n ℂ) (g : G) :
    star (gaussOperator R g) = gaussOperator R g⁻¹ := by
  classical
  ext x y
  rw [Matrix.star_apply]
  by_cases hxy : y.2 = gaussLegAction g x.2
  · have hyx : x.2 = gaussLegAction g⁻¹ y.2 := by
      rw [hxy]
      simp [gaussLegAction]
    rw [gaussOperator, ite_eq_left hxy, gaussOperator, ite_eq_left hyx]
    change star ((Matrix.unitaryFactorizationComparison R x.2.1 x.2.2
      y.2.1 y.2.2 : Matrix n n ℂ) y.1 x.1) = _
    rw [← Matrix.star_apply]
    change ((Matrix.unitaryFactorizationComparison R x.2.1 x.2.2
      y.2.1 y.2.2)⁻¹ : Matrix.unitaryGroup n ℂ) x.1 y.1 = _
    rw [Matrix.unitaryFactorizationComparison_inv]
  · have hyx : x.2 ≠ gaussLegAction g⁻¹ y.2 := by
      intro heq
      apply hxy
      rw [heq]
      simp [gaussLegAction]
    rw [gaussOperator, ite_eq_right hxy, gaussOperator, ite_eq_right hyx]
    exact star_zero ℂ

/-- Every local Gauss operator is unitary. -/
theorem gaussOperator_mem_unitaryGroup
    (R : G → G → Matrix.unitaryGroup n ℂ) (g : G) :
    gaussOperator R g ∈ Matrix.unitaryGroup (n × (G × G)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_gaussOperator, gaussOperator_mul]
  simp

/-- The local Gauss operators form a unitary representation of `G`. This is
the representation part of FBC25, Proposition `prop:gausslaws`
(arXiv:2502.20257, lines 3380--3387), isolated from the proposition's separate
gauged-tensor invariance statement. -/
def gaussRepresentation (R : G → G → Matrix.unitaryGroup n ℂ) :
    G →* Matrix.unitaryGroup (n × (G × G)) ℂ where
  toFun g := ⟨gaussOperator R g, gaussOperator_mem_unitaryGroup R g⟩
  map_one' := Subtype.ext (gaussOperator_one R)
  map_mul' g h := Subtype.ext (gaussOperator_mul R g h).symm

@[simp]
theorem gaussRepresentation_coe
    (R : G → G → Matrix.unitaryGroup n ℂ) (g : G) :
    (gaussRepresentation R g : Matrix (n × (G × G)) (n × (G × G)) ℂ) =
      gaussOperator R g :=
  rfl

end TNLean.Algebra
