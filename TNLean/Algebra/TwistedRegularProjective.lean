/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.TwistedRegularRepresentation
import TNLean.Algebra.ProjectiveRepresentation
import Mathlib.LinearAlgebra.Matrix.Reindex
import QICLean.Algebra.MatrixReindexUnitary

/-!
# Invertible twisted regular matrices

The cocycle-twisted regular matrices are unitary and therefore invertible.
This packages the projective multiplication law at the level of invertible
matrices, as needed for fixed-point MPS constructions. The regular matrices
are those of arXiv:2502.20257, lines 412–418; the fixed-point use follows
Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.F.2.
-/

open scoped Matrix

namespace TNLean.Algebra
namespace ScalarCocycle

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Pointwise inverse of a scalar two-cochain. -/
def inverse (ω : ScalarCocycle G) : ScalarCocycle G :=
  fun g h => (ω g h)⁻¹

omit [Fintype G] [DecidableEq G] in
/-- Inverting a genuine scalar two-cocycle gives another cocycle. -/
theorem inverse_isCocycle {ω : ScalarCocycle G}
    (hω : ω.IsCocycle) : (inverse ω).IsCocycle := by
  intro g h k
  simpa only [inverse, mul_inv_rev, mul_comm] using
    congrArg Inv.inv (hω g h k)

omit [Group G] [Fintype G] [DecidableEq G] in
/-- The circle-valued phase of the inverse cochain is the inverse of the
original circle phase. -/
theorem inverse_circlePhaseInclusion (ω : ScalarCocycle G) (g h : G) :
    (inverse ω).circlePhaseInclusion g h =
      (ω.circlePhaseInclusion g h)⁻¹ := by
  simp [inverse, ScalarCocycle.circlePhaseInclusion,
    ScalarCocycle.circlePhase, map_inv]

/-- The cocycle-twisted left regular matrix, regarded as an invertible
matrix. -/
noncomputable def twistedLeftRegularGL (ω : ScalarCocycle G) (g : G) : GL G ℂ :=
  Unitary.toUnits ⟨twistedLeftRegular ω g, twistedLeftRegular_mem_unitaryGroup ω g⟩

@[simp]
theorem twistedLeftRegularGL_coe (ω : ScalarCocycle G) (g : G) :
    (twistedLeftRegularGL ω g : Matrix G G ℂ) = twistedLeftRegular ω g := rfl

/-- The invertible twisted regular matrices obey the projective law with
factor system `ω.circlePhaseInclusion⁻¹`. -/
theorem twistedLeftRegularGL_mul {ω : ScalarCocycle G}
    (hω : ω.IsCocycle) (g h : G) :
    twistedLeftRegularGL ω g * twistedLeftRegularGL ω h =
      Matrix.GeneralLinearGroup.scalar G (ω.circlePhaseInclusion g h)⁻¹ *
        twistedLeftRegularGL ω (g * h) := by
  apply Units.ext
  simp only [Units.val_mul, twistedLeftRegularGL_coe,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul, Units.val_inv_eq_inv_val]
  exact twistedLeftRegular_mul hω g h

/-- Every genuine cocycle of a finite group gives a unitary projective
representation on the regular bond space. Its factor system is the inverse
of the canonical circle representative of the input cocycle, following the
left-regular convention of arXiv:2502.20257, lines 412–415. -/
noncomputable def twistedLeftRegularProjective
    (ω : ScalarCocycle G) (hω : ω.IsCocycle) :
    ProjectiveRepresentation (D := Fintype.card G)
      (fun g h => (ω.circlePhaseInclusion g h)⁻¹) where
  X g := Units.map
    (Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin G)).toMonoidHom
    (ω.twistedLeftRegularGL g)
  map_mul' g h := by
    change (Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin G))
        (ω.twistedLeftRegular g) *
      (Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin G))
        (ω.twistedLeftRegular h) =
      (((ω.circlePhaseInclusion g h)⁻¹ : Units ℂ) : ℂ) •
        (Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin G))
          (ω.twistedLeftRegular (g * h))
    rw [← _root_.map_mul, ← map_smul]
    congr 1
    simpa [ScalarCocycle.circlePhaseInclusion, ScalarCocycle.phase,
      Units.val_inv_eq_inv_val] using ω.twistedLeftRegular_mul hω g h

/-- The regular projective representation has unitary virtual matrices. -/
theorem twistedLeftRegularProjective_mem_unitaryGroup
    (ω : ScalarCocycle G) (hω : ω.IsCocycle) (g : G) :
    (((ω.twistedLeftRegularProjective hω).X g : GL (Fin (Fintype.card G)) ℂ) :
      Matrix (Fin (Fintype.card G)) (Fin (Fintype.card G)) ℂ) ∈
      Matrix.unitaryGroup (Fin (Fintype.card G)) ℂ := by
  change Matrix.reindex (Fintype.equivFin G) (Fintype.equivFin G)
    (ω.twistedLeftRegular g) ∈ _
  exact Matrix.reindex_mem_unitaryGroup _ _
    (ω.twistedLeftRegular_mem_unitaryGroup g)

/-- Using the inverse input cocycle cancels the inverse convention in the
twisted left-regular matrices. The resulting factor system is the canonical
circle representative of the requested class. -/
noncomputable def regularProjectiveForClass
    (ω : ScalarCocycle G) (hω : ω.IsCocycle) :
    ProjectiveRepresentation (D := Fintype.card G) ω.circlePhaseInclusion :=
  let σ := (inverse ω).twistedLeftRegularProjective (inverse_isCocycle hω)
  { X := σ.X
    map_mul' := by
      intro g h
      simpa [σ, inverse_circlePhaseInclusion] using σ.map_mul g h }

/-- The virtual matrices of `regularProjectiveForClass` are unitary. -/
theorem regularProjectiveForClass_mem_unitaryGroup
    (ω : ScalarCocycle G) (hω : ω.IsCocycle) (g : G) :
    ((ω.regularProjectiveForClass hω).X g :
      Matrix (Fin (Fintype.card G)) (Fin (Fintype.card G)) ℂ) ∈
      Matrix.unitaryGroup (Fin (Fintype.card G)) ℂ := by
  exact (inverse ω).twistedLeftRegularProjective_mem_unitaryGroup
    (inverse_isCocycle hω) g

end ScalarCocycle
end TNLean.Algebra
