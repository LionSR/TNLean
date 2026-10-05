/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GInjectiveTorusProjector
import TNLean.Algebra.RepresentationDelta

/-!
# Matching representations on the eight bonds of the four-block torus

Representations belong to individual oriented bonds, not to vertices or to
unordered adjacent vertex pairs. Both endpoints read the same bond's matrix:
a head reads `U(g)`, and a tail reads `transpose U(g⁻¹)`. The four-leg action
therefore matches across every bond, including parallel bonds at period two.

This is the representation data in SCP10, Definition 5.1 and Theorem 5.5.
Representations may vary independently from bond to bond. This module uses a
common finite coordinate alphabet; varying bond dimensions remain a separate
generalization. No closure-spanning claim is made here.
-/

open scoped Kronecker

namespace TNLean.PEPS

variable {G V : Type*} [Group G] [Fintype V] [DecidableEq V]
variable {width height : ℕ}

/-- The local action from the four actual incident bonds. Top and left are
incoming; right and down are outgoing. Each bond representation is shared by
its two endpoints, even when another bond joins the same pair of vertices. -/
def torusMatchedLegMatrix
    (Uh Uv : TorusVertex width height → G →* Matrix V V ℂ)
    (v : TorusVertex width height) :
    G →* Matrix (V × V × V × V) (V × V × V × V) ℂ where
  toFun g := Uv v g ⊗ₖ ((Uh v g⁻¹).transpose ⊗ₖ
    ((Uv (v.1, v.2 - 1) g⁻¹).transpose ⊗ₖ Uh (v.1 - 1, v.2) g))
  map_one' := by simp
  map_mul' g h := by
    simp only [mul_inv_rev, map_mul, Matrix.transpose_mul, Matrix.mul_kronecker_mul]

/-- The coefficient-space representation induced by the matching bond data. -/
noncomputable def torusMatchedLegRep
    (Uh Uv : TorusVertex width height → G →* Matrix V V ℂ)
    (v : TorusVertex width height) :
    Representation ℂ G ((V × V × V × V) → ℂ) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp (torusMatchedLegMatrix Uh Uv v)

/-- A uniform bond family recovers the existing native four-leg action. -/
@[simp]
theorem torusMatchedLegRep_const (U : G →* Matrix V V ℂ)
    (v : TorusVertex width height) :
    torusMatchedLegRep (fun _ ↦ U) (fun _ ↦ U) v = torusLegRep U := rfl

/-- Unitarity, separately from algebraic semi-regularity, is assumed for
every individual bond in the source's Definition 5.1. -/
def IsUnitaryTorusBondFamily
    (Uh Uv : TorusVertex width height → G →* Matrix V V ℂ) : Prop :=
  (∀ v g, Uh v g ∈ Matrix.unitaryGroup V ℂ) ∧
    ∀ v g, Uv v g ∈ Matrix.unitaryGroup V ℂ

variable [Fintype G]

/-- Algebraic semi-regularity is a condition on every actual bond
representation, rather than an assumption only on the four-leg product. Together with
`IsUnitaryTorusBondFamily`, this is the source's bond hypothesis. -/
def IsSemiRegularTorusBondFamily
    (Uh Uv : TorusVertex width height → G →* Matrix V V ℂ) : Prop :=
  (∀ v, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (Uh v))) ∧
    ∀ v, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (Uv v))

attribute [local instance] Representation.invertibleFintypeCardComplex

/-- The canonical local averaging tensor for any specified four-leg action. -/
noncomputable def representationAveragingSite
    (ρ : Representation ℂ G ((V × V × V × V) → ℂ))
    (t r b l : V) (s : V × V × V × V) : ℂ :=
  LinearMap.toMatrix' ρ.averageMap s (t, r, b, l)

/-- Its actual site map is the local invariant projector. -/
theorem siteMap_representationAveragingSite
    (ρ : Representation ℂ G ((V × V × V × V) → ℂ)) :
    siteMap (representationAveragingSite ρ) = ρ.averageMap := by
  apply LinearMap.toMatrix'.injective
  rw [toMatrix_siteMap_regular]
  rfl

/-- Uniform matching bond data recover the existing averaging tensor. -/
@[simp]
theorem representationAveragingSite_torusLegRep (U : G →* Matrix V V ℂ) :
    representationAveragingSite (torusLegRep U) = averagingSite U := rfl

end TNLean.PEPS
