/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ProjectiveRepresentation
import TNLean.Algebra.SymmetryParity
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Conjugate-projective representations

Time reversal and reflection act by complex conjugation on the virtual
factor system. The coefficient action below is a `MulDistribMulAction`, so
both cocycles and their classes are Mathlib's group-cohomology objects.
There is no separate cohomology quotient. Associativity of the semilinear
matrix action gives the twisted two-cocycle equation; rephasing changes the
factor system by its twisted coboundary.

Source: arXiv:2011.12127, Section III.A, `TN-Review-main.tex` lines 1120–1130.
The parity for virtual gauges is time reversal plus reflection, whereas the
parity for the one-cocycle is time reversal alone.
-/

open scoped Matrix

namespace TNLean.Algebra

variable {G : Type} [Group G]

set_option warn.classDefReducibility false in
/-- The scalar action by identity or conjugation specified by a symmetry parity.
Extension to nonzero complex scalars of the U(1) action in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1122 and 1129. -/
noncomputable def parityUnitsAction (α : G →* SymmetryParity) :
    MulDistribMulAction G (Units ℂ) where
  smul g z := Units.map (parityConj (α g)).toMonoidHom z
  one_smul z := Units.ext (by
    change parityConj (α 1) (z : ℂ) = z
    simp)
  mul_smul g h z := Units.ext (by
    change parityConj (α (g * h)) (z : ℂ) =
      parityConj (α g) (parityConj (α h) (z : ℂ))
    rw [map_mul, parityConj_mul])
  smul_one g := Units.ext (by
    change parityConj (α g) 1 = 1
    exact map_one _)
  smul_mul g z w := Units.ext (by
    change parityConj (α g) ((z : ℂ) * (w : ℂ)) =
      parityConj (α g) (z : ℂ) * parityConj (α g) (w : ℂ)
    exact _root_.map_mul _ _ _)

/-- Scalar multiplication in the coefficient module is the chosen conjugation.
Supporting algebra for arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1122 and 1129. -/
@[simp] theorem parityUnitsAction_coe_smul (α : G →* SymmetryParity) (g : G)
    (z : Units ℂ) :
    letI := parityUnitsAction α
    ((g • z : Units ℂ) : ℂ) = parityConj (α g) (z : ℂ) := rfl

/-- A unitary virtual action with conjugate-projective multiplication law.
Multiplicative form of the virtual law in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1120 and 1124–1129. -/
structure ConjugateProjectiveRepresentation (α : G →* SymmetryParity)
    (ω : ScalarCocycle G) {D : ℕ} where
  /-- Invertible virtual symmetry matrices.
  Source: arXiv:2011.12127,
  `Papers/2011.12127/TN-Review-main.tex`, lines 1084–1090 and 1120. -/
  X : G → GL (Fin D) ℂ
  /-- The virtual symmetry matrices are unitary.
  Source: arXiv:2011.12127,
  `Papers/2011.12127/TN-Review-main.tex`, lines 1084–1090. -/
  unitary : ∀ g, (X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup (Fin D) ℂ
  /-- Composition of virtual symmetries, with conjugation on the second matrix.
  Multiplicative form of the virtual law in arXiv:2011.12127,
  `Papers/2011.12127/TN-Review-main.tex`, lines 1120 and 1124–1129. -/
  map_mul' : ∀ g h,
    (X g : Matrix (Fin D) (Fin D) ℂ) *
        parityConjMatrix (α g) (X h : Matrix (Fin D) (Fin D) ℂ) =
      (ω g h : ℂ) • (X (g * h) : Matrix (Fin D) (Fin D) ℂ)

namespace ConjugateProjectiveRepresentation

variable {α : G →* SymmetryParity} {ω : ScalarCocycle G} {D : ℕ}
variable (ρ : ConjugateProjectiveRepresentation α ω (D := D))

include ρ

/-- The conjugate-projective multiplication law.
Multiplicative form of the virtual law in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1120 and 1124–1129. -/
theorem map_mul (g h : G) :
    (ρ.X g : Matrix (Fin D) (Fin D) ℂ) *
        parityConjMatrix (α g) (ρ.X h : Matrix (Fin D) (Fin D) ℂ) =
      (ω g h : ℂ) • (ρ.X (g * h) : Matrix (Fin D) (Fin D) ℂ) :=
  ρ.map_mul' g h

omit ρ in
/-- A scalar multiple of a nonempty unitary matrix is unitary only if the
scalar lies on the unit circle.
Supporting algebra for arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1084–1086 and 1129. -/
private theorem scalar_unitary_of_smul (hD : 0 < D) (c : ℂ)
    (M : Matrix (Fin D) (Fin D) ℂ)
    (hM : M ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hcM : c • M ∈ Matrix.unitaryGroup (Fin D) ℂ) : star c * c = 1 := by
  have h := (Matrix.mem_unitaryGroup_iff').1 hcM
  rw [star_smul, Matrix.smul_mul, Matrix.mul_smul,
    (Matrix.mem_unitaryGroup_iff').1 hM, smul_smul] at h
  have heq := congrFun (congrFun h (⟨0, hD⟩ : Fin D)) (⟨0, hD⟩ : Fin D)
  simpa using heq

/-- Unitarity of the virtual matrices forces their factor system to be
U(1)-valued. This supplies the source's coefficient group rather than adding
unit modulus as a separate representation hypothesis.
Supporting algebra for arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1124–1129. -/
theorem factor_unitary (hD : 0 < D) (g h : G) :
    star (ω g h : ℂ) * (ω g h : ℂ) = 1 := by
  have hconj : parityConjMatrix (α g) (ρ.X h : Matrix (Fin D) (Fin D) ℂ) ∈
      Matrix.unitaryGroup (Fin D) ℂ := by
    rcases symmetryParity_cases (α g) with hp | hp
    · simpa [hp] using ρ.unitary h
    · simpa [hp] using Matrix.map_star_mem_unitaryGroup_iff.mpr (ρ.unitary h)
  have hprod := (Matrix.unitaryGroup (Fin D) ℂ).mul_mem (ρ.unitary g) hconj
  rw [ρ.map_mul] at hprod
  exact scalar_unitary_of_smul hD (ω g h : ℂ) (ρ.X (g * h)) (ρ.unitary _) hprod

/-- A scalar relating two unitary choices of a virtual gauge lies in U(1).
Supporting algebra for arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1084–1086 and 1129. -/
theorem rephase_unitary {ω' : ScalarCocycle G}
    (ρ' : ConjugateProjectiveRepresentation α ω' (D := D)) (hD : 0 < D)
    (ξ : G → Units ℂ)
    (hξ : ∀ g, (ρ'.X g : Matrix (Fin D) (Fin D) ℂ) =
      (ξ g : ℂ) • (ρ.X g : Matrix (Fin D) (Fin D) ℂ)) (g : G) :
    star (ξ g : ℂ) * (ξ g : ℂ) = 1 := by
  apply scalar_unitary_of_smul hD (ξ g : ℂ) (ρ.X g) (ρ.unitary g)
  rw [← hξ]
  exact ρ'.unitary g

/-- Associativity derives the twisted scalar cocycle equation, without any
normalization assumption.
Multiplicative form of the associativity equation in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1124–1129. -/
theorem cocycle_of_assoc (hD : 0 < D) (g h k : G) :
    (ω (g * h) k : ℂ) * (ω g h : ℂ) =
      parityConj (α g) (ω h k : ℂ) * (ω g (h * k) : ℂ) := by
  have hassoc :
      ((ρ.X g : Matrix (Fin D) (Fin D) ℂ) *
          parityConjMatrix (α g) (ρ.X h : Matrix (Fin D) (Fin D) ℂ)) *
          parityConjMatrix (α (g * h)) (ρ.X k : Matrix (Fin D) (Fin D) ℂ) =
        (ρ.X g : Matrix (Fin D) (Fin D) ℂ) *
          parityConjMatrix (α g)
            ((ρ.X h : Matrix (Fin D) (Fin D) ℂ) *
              parityConjMatrix (α h) (ρ.X k : Matrix (Fin D) (Fin D) ℂ)) := by
    rw [parityConjMatrix_mul, parityConjMatrix_comp, ← _root_.map_mul, Matrix.mul_assoc]
  rw [ρ.map_mul, Matrix.smul_mul, ρ.map_mul, ρ.map_mul,
    parityConjMatrix_smul, Matrix.mul_smul, ρ.map_mul] at hassoc
  have hscalar := ProjectiveRepresentation.smul_eq_smul_cancel (D := D) hD
    (hM := (ρ.X (g * (h * k))).isUnit)
    (by simpa only [smul_smul, mul_assoc] using hassoc)
  simpa only [mul_comm] using hscalar

/-- The factor system is a Mathlib multiplicative two-cocycle for the
conjugation action.
Multiplicative form of the two-cocycle equation in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1124–1129. -/
theorem isMulCocycle₂ (hD : 0 < D) :
    letI := parityUnitsAction α
    groupCohomology.IsMulCocycle₂ (Function.uncurry ω) := by
  intro g h k
  apply Units.ext
  exact ρ.cocycle_of_assoc hD g h k

/-- Rephasing the virtual matrices changes the factor system by precisely
the twisted coboundary.
Multiplicative form of the coboundary formula in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, line 1129. -/
theorem factorSystem_rephase {ω' : ScalarCocycle G}
    (ρ' : ConjugateProjectiveRepresentation α ω' (D := D)) (hD : 0 < D)
    (ξ : G → Units ℂ)
    (hξ : ∀ g, (ρ'.X g : Matrix (Fin D) (Fin D) ℂ) =
      (ξ g : ℂ) • (ρ.X g : Matrix (Fin D) (Fin D) ℂ)) (g h : G) :
    ω' g h = ξ g * Units.map (parityConj (α g)).toMonoidHom (ξ h) /
      ξ (g * h) * ω g h := by
  have heq := ρ'.map_mul g h
  simp only [hξ, parityConjMatrix_smul, Matrix.smul_mul, Matrix.mul_smul,
    ρ.map_mul, smul_smul] at heq
  have hscalar := ProjectiveRepresentation.smul_eq_smul_cancel (D := D) hD
    (hM := (ρ.X (g * h)).isUnit) heq
  apply Units.ext
  simp only [Units.val_mul, Units.val_div_eq_div_val, Units.coe_map]
  change (ω' g h : ℂ) = (ξ g : ℂ) * parityConj (α g) (ξ h : ℂ) /
    (ξ (g * h) : ℂ) * (ω g h : ℂ)
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (ξ (g * h)).ne_zero).2
  calc
    (ω' g h : ℂ) * (ξ (g * h) : ℂ) =
        (ξ g : ℂ) * (parityConj (α g) (ξ h : ℂ) * (ω g h : ℂ)) := by
          simpa only [mul_left_comm] using hscalar.symm
    _ = _ := by ring

end ConjugateProjectiveRepresentation

/-! ## Unit-circle coefficients

The source's U(1) is the existing group `unitary ℂ`. Its cohomology is used
directly below; the larger coefficient group of all complex units is not
identified with the circle.
-/

/-- Identity or conjugation on the unit circle, regarded as `unitary ℂ`.
Source: arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1122 and 1129. -/
noncomputable def parityUnitary (p : SymmetryParity) (z : unitary ℂ) : unitary ℂ :=
  if p = 1 then z else star z

/-- The unit-circle action is the restriction of scalar parity conjugation.
Supporting algebra for arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1122 and 1129. -/
@[simp] theorem parityUnitary_coe (p : SymmetryParity) (z : unitary ℂ) :
    (parityUnitary p z : ℂ) = parityConj p (z : ℂ) := by
  rcases symmetryParity_cases p with rfl | rfl <;> simp [parityUnitary]

set_option warn.classDefReducibility false in
/-- The source's conjugation action on U(1), rather than on all complex units.
Source: arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1122 and 1129. -/
noncomputable def parityUnitaryAction (α : G →* SymmetryParity) :
    MulDistribMulAction G (unitary ℂ) where
  smul g z := parityUnitary (α g) z
  one_smul z := by
    change parityUnitary (α 1) z = z
    ext
    simp
  mul_smul g h z := by
    change parityUnitary (α (g * h)) z = parityUnitary (α g) (parityUnitary (α h) z)
    ext
    simp [parityConj_mul]
  smul_one g := by
    change parityUnitary (α g) 1 = 1
    ext
    simp
  smul_mul g z w := by
    change parityUnitary (α g) (z * w) = parityUnitary (α g) z * parityUnitary (α g) w
    ext
    simp

/-- The U(1) coefficient representation used in the SPT classification.
Coefficient representation for the cohomology groups in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1122 and 1129. -/
noncomputable abbrev parityUnitaryCoefficientRepresentation
    (α : G →* SymmetryParity) : Rep ℤ G :=
  @Rep.ofMulDistribMulAction G (unitary ℂ) _ _ (parityUnitaryAction α)

/-- A U(1)-valued one-cocycle determines its actual circle-coefficient class.
Source: arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, line 1122. -/
noncomputable def parityUnitaryH1Class (β : G →* SymmetryParity) (φ : G → unitary ℂ)
    (hφ : letI := parityUnitaryAction β; groupCohomology.IsMulCocycle₁ φ) :
    groupCohomology.H1 (parityUnitaryCoefficientRepresentation β) :=
  letI := parityUnitaryAction β
  groupCohomology.H1π _ (groupCohomology.cocyclesOfIsMulCocycle₁ hφ)

/-- A U(1)-valued two-cocycle determines its actual circle-coefficient class.
Source: arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, line 1129. -/
noncomputable def parityUnitaryH2Class (α : G →* SymmetryParity)
    (ω : G → G → unitary ℂ)
    (hω : letI := parityUnitaryAction α;
      groupCohomology.IsMulCocycle₂ (Function.uncurry ω)) :
    groupCohomology.H2 (parityUnitaryCoefficientRepresentation α) :=
  letI := parityUnitaryAction α
  groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂ hω)

/-- The inclusion of U(1) into complex units commutes with parity conjugation.
Supporting algebra for arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1122 and 1129. -/
@[simp] theorem parityUnitary_toUnits (p : SymmetryParity) (z : unitary ℂ) :
    Unitary.toUnits (parityUnitary p z) =
      Units.map (parityConj p).toMonoidHom (Unitary.toUnits z) :=
  Units.ext (parityUnitary_coe p z)

/-- The inclusion of U(1) into complex units preserves twisted cocycles.
Supporting algebra for arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1124–1129. -/
theorem isMulCocycle₂_toUnits (α : G →* SymmetryParity) (ω : G → G → unitary ℂ)
    (hω : letI := parityUnitaryAction α;
      groupCohomology.IsMulCocycle₂ (Function.uncurry ω)) :
    letI := parityUnitsAction α
    groupCohomology.IsMulCocycle₂ (fun p : G × G => Unitary.toUnits (ω p.1 p.2)) := by
  intro g h k
  change Unitary.toUnits (ω (g * h) k) * Unitary.toUnits (ω g h) =
    Units.map (parityConj (α g)).toMonoidHom (Unitary.toUnits (ω h k)) *
      Unitary.toUnits (ω g (h * k))
  have heq := congrArg Unitary.toUnits (hω g h k)
  change Unitary.toUnits (ω (g * h) k * ω g h) =
    Unitary.toUnits (parityUnitary (α g) (ω h k) * ω g (h * k)) at heq
  simpa only [map_mul, parityUnitary_toUnits] using heq

/-- A unit-modulus complex unit, regarded as an element of U(1).
Supporting algebra for arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, line 1129. -/
def unitaryScalar (z : Units ℂ) (hz : star (z : ℂ) * (z : ℂ) = 1) : unitary ℂ :=
  ⟨z, z.isUnit.mem_unitary_of_star_mul_self hz⟩

/-- The corresponding unit-circle element has the same complex value.
Supporting algebra for arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, line 1129. -/
@[simp] theorem unitaryScalar_coe (z : Units ℂ) (hz : star (z : ℂ) * (z : ℂ) = 1) :
    (unitaryScalar z hz : ℂ) = z := rfl

/-- Circle-valued twisted coboundaries identify the same U(1) cohomology class.
Source: arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, line 1129. -/
theorem parityUnitaryH2Class_eq_of_isMulCoboundary₂ (α : G →* SymmetryParity)
    (ω ω' : G → G → unitary ℂ)
    (hω : letI := parityUnitaryAction α;
      groupCohomology.IsMulCocycle₂ (Function.uncurry ω))
    (hω' : letI := parityUnitaryAction α;
      groupCohomology.IsMulCocycle₂ (Function.uncurry ω'))
    (h : letI := parityUnitaryAction α;
      groupCohomology.IsMulCoboundary₂ (Function.uncurry (ω / ω'))) :
    parityUnitaryH2Class α ω hω = parityUnitaryH2Class α ω' hω' := by
  let := parityUnitaryAction α
  apply (groupCohomology.H2π_eq_iff _ _).2
  exact (groupCohomology.coboundariesOfIsMulCoboundary₂ h).property

/-- Circle-valued one-coboundaries identify the same U(1) cohomology class.
Source: arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, line 1122. -/
theorem parityUnitaryH1Class_eq_of_isMulCoboundary₁ (β : G →* SymmetryParity)
    (φ φ' : G → unitary ℂ)
    (hφ : letI := parityUnitaryAction β; groupCohomology.IsMulCocycle₁ φ)
    (hφ' : letI := parityUnitaryAction β; groupCohomology.IsMulCocycle₁ φ')
    (h : letI := parityUnitaryAction β; groupCohomology.IsMulCoboundary₁ (φ / φ')) :
    parityUnitaryH1Class β φ hφ = parityUnitaryH1Class β φ' hφ' := by
  let := parityUnitaryAction β
  apply (groupCohomology.H1π_eq_iff _ _).2
  exact (groupCohomology.coboundariesOfIsMulCoboundary₁ h).property

namespace ConjugateProjectiveRepresentation

variable {α : G →* SymmetryParity} {D : ℕ}

/-- A scalar rephasing of unitary virtual matrices gives a coboundary in
U(1). The scalar's unit modulus is derived from the matrix relation.
Multiplicative form of the rephasing relation in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, line 1129. -/
theorem isMulCoboundary₂_unitary_of_rephase {ω ω' : G → G → _root_.unitary ℂ}
    (ρ : ConjugateProjectiveRepresentation α (fun g h => Unitary.toUnits (ω g h))
      (D := D))
    (ρ' : ConjugateProjectiveRepresentation α (fun g h => Unitary.toUnits (ω' g h))
      (D := D)) (hD : 0 < D) (ξ : G → Units ℂ)
    (hξ : ∀ g, (ρ'.X g : Matrix (Fin D) (Fin D) ℂ) =
      (ξ g : ℂ) • (ρ.X g : Matrix (Fin D) (Fin D) ℂ)) :
    letI := parityUnitaryAction α
    groupCohomology.IsMulCoboundary₂ (Function.uncurry (ω' / ω)) := by
  let ξu : G → _root_.unitary ℂ := fun g => unitaryScalar (ξ g) (ρ.rephase_unitary ρ' hD ξ hξ g)
  have hξu (g : G) : Unitary.toUnits (ξu g) = ξ g := Units.ext rfl
  refine ⟨ξu, fun g h => ?_⟩
  change parityUnitary (α g) (ξu h) / ξu (g * h) * ξu g = ω' g h / ω g h
  apply Unitary.toUnits_injective
  simp only [_root_.map_mul, map_div, parityUnitary_toUnits, hξu]
  rw [ρ.factorSystem_rephase ρ' hD ξ hξ]
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- Pointwise scalar gauge equivalence preserves the actual U(1)-valued
second cohomology class. No unit-modulus assumption on the supplied scalars
is needed, since both virtual representations are unitary.
Source: arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, line 1129. -/
theorem parityUnitaryH2Class_eq_of_rephase {ω ω' : G → G → _root_.unitary ℂ}
    (ρ : ConjugateProjectiveRepresentation α (fun g h => Unitary.toUnits (ω g h))
      (D := D))
    (ρ' : ConjugateProjectiveRepresentation α (fun g h => Unitary.toUnits (ω' g h))
      (D := D)) (hD : 0 < D) (ξ : G → Units ℂ)
    (hξ : ∀ g, (ρ'.X g : Matrix (Fin D) (Fin D) ℂ) =
      (ξ g : ℂ) • (ρ.X g : Matrix (Fin D) (Fin D) ℂ))
    (hω : letI := parityUnitaryAction α;
      groupCohomology.IsMulCocycle₂ (Function.uncurry ω))
    (hω' : letI := parityUnitaryAction α;
      groupCohomology.IsMulCocycle₂ (Function.uncurry ω')) :
    parityUnitaryH2Class α ω' hω' = parityUnitaryH2Class α ω hω :=
  parityUnitaryH2Class_eq_of_isMulCoboundary₂ α ω' ω hω' hω
    (ρ.isMulCoboundary₂_unitary_of_rephase ρ' hD ξ hξ)

end ConjugateProjectiveRepresentation

end TNLean.Algebra
