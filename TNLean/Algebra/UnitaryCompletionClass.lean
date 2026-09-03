/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.GaussRepresentation

/-!
# Prescribed defect maps and their full unitary completion class

When the fusion scalars of a non-injective invariant matrix product state are
not block independent, the state-level construction of FBC25 prescribes the
modified fusion operators only on physical defect subspaces: for every ordered
pair `(a, b)` of gauge labels there is a defect subspace `K a b` of the matter
space and an isometry `D a b` defined on it. The operator used on the whole
matter space is any unitary agreeing with `D a b` on `K a b`, and the closing
sentence of the modified-fusion lemma of FBC25 (arXiv:2502.20257,
lines 4215--4260) records that such an extension is not unique. A completion is
therefore the whole family `(U a b)`, not one selected operator.

The matter operators are represented here as elements of
`Matrix.unitaryGroup n ℂ`, the family type consumed by the local Gauss operator
`TNLean.Algebra.gaussOperator`, so that a completion is literally an admissible
argument of that operator and its gauge block
`(U (T g (a, b)))⁻¹ * U a b` is the unitary factorization comparison
`Matrix.unitaryFactorizationComparison`. Defect subspaces are submodules of
`n → ℂ` and a prescribed isometry is given by an ambient matrix, whose
restriction to the defect subspace carries all the mathematical content.

The three transport results follow the derivation of the modified Gauss law in
FBC25 (arXiv:2502.20257, lines 4325--4335) in the order it must be taken:
agreement on the defect subspace, then an equality of images in the whole
matter space, and only then multiplication by the adjoint of the target
completion. No step asserts that the adjoint of a completion restricts to the
adjoint of a prescribed defect map, which is false for a general completion.
-/

noncomputable section

open scoped Matrix

namespace TNLean.Algebra

variable {G n : Type*} [Fintype n] [DecidableEq n]

/-- Prescribed defect maps: for every ordered pair `(a, b)` of gauge labels, a
defect subspace `domain a b` of the matter space and a matrix whose restriction
to it is the prescribed isometry `D a b`.

This is the defect subspace `K_{a,b}` together with the isometry
`D_{a,b} : K_{a,b} → H_m` of the state-level fusion construction of FBC25
(arXiv:2502.20257, lines 4215--4260 and 4325--4335). -/
structure DefectMaps (G n : Type*) [Fintype n] where
  /-- The defect subspace of the matter space attached to the labels `(a, b)`. -/
  domain : G → G → Submodule ℂ (n → ℂ)
  /-- A matrix whose restriction to `domain a b` is the prescribed defect
  isometry. -/
  prescribed : G → G → Matrix n n ℂ
  /-- The prescribed map is an isometry on its defect subspace. -/
  isometry_on_domain : ∀ a b, ∀ ξ ∈ domain a b,
    (star (prescribed a b) * prescribed a b) *ᵥ ξ = ξ

namespace DefectMaps

variable (D : DefectMaps G n)

/-- A family of unitary matter operators is a completion of the prescribed
defect maps when every member agrees with the prescribed map on its defect
subspace.

This is the membership condition of the full completion class attached to the
modified fusion operators of FBC25 (arXiv:2502.20257, lines 4215--4260). -/
def IsCompletion (R : G → G → Matrix.unitaryGroup n ℂ) : Prop :=
  ∀ a b, ∀ ξ ∈ D.domain a b,
    (R a b : Matrix n n ℂ) *ᵥ ξ = D.prescribed a b *ᵥ ξ

/-- The full completion class of the prescribed defect maps, whose members are
whole families of unitary matter operators.

This is the completion class of the modified fusion operators of FBC25
(arXiv:2502.20257, lines 4215--4260); no single pair of labels is singled
out. -/
def completionClass : Set (G → G → Matrix.unitaryGroup n ℂ) :=
  {R | D.IsCompletion R}

@[simp]
theorem mem_completionClass_iff {R : G → G → Matrix.unitaryGroup n ℂ} :
    R ∈ D.completionClass ↔ D.IsCompletion R :=
  Iff.rfl

variable {D}

/-- A completion agrees with the prescribed defect map on its defect subspace.
This is the first step of the transport derivation of FBC25
(arXiv:2502.20257, lines 4325--4335). -/
theorem IsCompletion.mulVec_eq_prescribed
    {R : G → G → Matrix.unitaryGroup n ℂ} (hR : D.IsCompletion R) {a b : G}
    {ξ : n → ℂ} (hξ : ξ ∈ D.domain a b) :
    (R a b : Matrix n n ℂ) *ᵥ ξ = D.prescribed a b *ᵥ ξ :=
  hR a b ξ hξ

/-- Covariance of the prescribed defect maps on their defect subspaces implies
the same covariance for every completion, as an equality of images in the whole
matter space. This is the second step of the transport derivation of FBC25
(arXiv:2502.20257, lines 4325--4335). -/
theorem IsCompletion.mulVec_eq_mulVec
    {R : G → G → Matrix.unitaryGroup n ℂ} (hR : D.IsCompletion R)
    {a b c d : G} {ξ η : n → ℂ} (hξ : ξ ∈ D.domain a b)
    (hη : η ∈ D.domain c d)
    (hcov : D.prescribed a b *ᵥ ξ = D.prescribed c d *ᵥ η) :
    (R a b : Matrix n n ℂ) *ᵥ ξ = (R c d : Matrix n n ℂ) *ᵥ η := by
  rw [hR.mulVec_eq_prescribed hξ, hR.mulVec_eq_prescribed hη, hcov]

/-- The transport identity: the gauge block of a completion carries a defect
vector to the covariant one. This is the third step of the transport derivation
of FBC25 (arXiv:2502.20257, lines 4325--4335); the adjoint of the target
completion is applied only after the equality of images in the whole matter
space is available. -/
theorem IsCompletion.unitaryFactorizationComparison_mulVec
    {R : G → G → Matrix.unitaryGroup n ℂ} (hR : D.IsCompletion R)
    {a b c d : G} {ξ η : n → ℂ} (hξ : ξ ∈ D.domain a b)
    (hη : η ∈ D.domain c d)
    (hcov : D.prescribed a b *ᵥ ξ = D.prescribed c d *ᵥ η) :
    (Matrix.unitaryFactorizationComparison R a b c d : Matrix n n ℂ) *ᵥ ξ = η := by
  rw [Matrix.unitaryFactorizationComparison_coe, ← Matrix.mulVec_mulVec,
    hR.mulVec_eq_mulVec hξ hη hcov, Matrix.mulVec_mulVec,
    Matrix.UnitaryGroup.star_mul_self, Matrix.one_mulVec]

variable [Group G]

/-- The transport identity for the two gauge labels moved by the Gauss leg
action. This is the exact defect-covariance identity used for the modified
Gauss law of FBC25 (arXiv:2502.20257, lines 4325--4335). -/
theorem IsCompletion.unitaryFactorizationComparison_gaussLegAction_mulVec
    {R : G → G → Matrix.unitaryGroup n ℂ} (hR : D.IsCompletion R) (g : G)
    {a b : G} {ξ η : n → ℂ} (hξ : ξ ∈ D.domain a b)
    (hη : η ∈ D.domain (a * g⁻¹) (g * b))
    (hcov : D.prescribed a b *ᵥ ξ = D.prescribed (a * g⁻¹) (g * b) *ᵥ η) :
    (Matrix.unitaryFactorizationComparison R a b (a * g⁻¹) (g * b) :
        Matrix n n ℂ) *ᵥ ξ = η :=
  hR.unitaryFactorizationComparison_mulVec hξ hη hcov

end DefectMaps

end TNLean.Algebra
