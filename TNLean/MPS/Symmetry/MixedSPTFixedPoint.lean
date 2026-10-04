/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.SPTFixedPoint
import TNLean.MPS.Symmetry.MixedSymmetry
import TNLean.Algebra.ConjugateRegularRepresentation

/-!
# Dimer SPT fixed points with time reversal and reflection

The physical dimer matrix units already form a complete operator basis. A
virtual conjugate-projective representation therefore determines the physical
symmetry coefficients uniquely. Time reversal conjugates scalar coefficients;
reflection swaps the two physical dimer factors and reverses site order.
The virtual factor system cancels from the physical action.

Source: arXiv:2011.12127, Section III.A, `Papers/2011.12127/TN-Review-main.tex`
lines 1120–1130 and 1147–1157. We retain the corrected dimer tensor of
`SPTFixedPoint`, not the erroneous displayed source tensor discussed in
`docs/paper-gaps/rmp_spt_fixed_point_tensor.tex`.
-/

open scoped Matrix Kronecker
open TNLean.Algebra

namespace MPSTensor

variable {D : ℕ}

/-- Identify the physical dimer factors, swapping them for reflection. -/
def sptPairingEquiv (r : SymmetryParity) : Fin D × Fin D ≃ Fin (D * D) :=
  (if r = 1 then Equiv.refl _ else Equiv.prodComm _ _).trans finProdFinEquiv

/-- The physical symmetry matrix of a dimer: `φ (X̄ ⊗ X)`, followed by the
swap of physical factors when the symmetry reflects the chain. -/
noncomputable def mixedSptMatrix (X : Matrix (Fin D) (Fin D) ℂ)
    (φ : ℂ) (r : SymmetryParity) : Matrix (Fin (D * D)) (Fin (D * D)) ℂ :=
  φ • Matrix.reindex finProdFinEquiv (sptPairingEquiv r) (X.map star ⊗ₖ X)

/-- The mixed action on the dimer letters has precisely the prescribed virtual
gauge and phase. This coefficient identity holds even before imposing the
unitarity and group laws on the virtual matrices. -/
theorem mixedTensorAction_sptFixedPointTensor
    (X : Matrix (Fin D) (Fin D) ℂ) (φ : ℂ) (t r : SymmetryParity)
    (i : Fin (D * D)) :
    mixedTensorAction (sptFixedPointTensor D) (mixedSptMatrix X φ r) t r i =
      φ • (Xᴴ * sptFixedPointTensor D i * X) := by
  classical
  rcases symmetryParity_cases t with rfl | rfl <;>
    rcases symmetryParity_cases r with rfl | rfl <;>
      ext x y <;>
      simp only [mixedTensorAction, mixedSptMatrix, sptPairingEquiv,
        symmetryLetter_trivial, symmetryLetter_timeReversal, symmetryLetter_reflection,
        symmetryLetter_both, Matrix.reindex_apply, Matrix.submatrix_apply,
        Matrix.smul_apply, Matrix.sum_apply, sptFixedPointTensor,
        smul_eq_mul, Matrix.single_apply, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
        Matrix.map_apply] <;>
      rw [← finProdFinEquiv.sum_comp] <;>
      simp [sptPair, sptScale, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
        ite_and, apply_ite, mul_comm, mul_left_comm]

/-- The dimer letters determine every coefficient of a mixed physical action. -/
theorem eq_of_mixedTensorAction_sptFixedPointTensor_eq [NeZero D]
    {U V : Matrix (Fin (D * D)) (Fin (D * D)) ℂ} (t r : SymmetryParity)
    (h : mixedTensorAction (sptFixedPointTensor D) U t r =
      mixedTensorAction (sptFixedPointTensor D) V t r) : U = V := by
  ext i j
  have hsum := congrArg (symmetryLetter t r) (congrFun h i)
  simp only [mixedTensorAction, symmetryLetter_sum, symmetryLetter_smul,
    symmetryLetter_self] at hsum
  have hc := congrFun (eq_of_sum_smul_sptFixedPointTensor_eq hsum) j
  exact (parityConj t).injective hc

/-- The virtual projective phase cancels between the two dimer factors. Thus
the physical multiplication is twisted only by time reversal, not reflection. -/
theorem mixedSptMatrix_mul [NeZero D]
    (X Y Z : Matrix (Fin D) (Fin D) ℂ) (z w c : ℂ)
    (t r s : SymmetryParity)
    (hXY : X * parityConjMatrix (t * r) Y = c • Z)
    (hc : star c * c = 1) :
    mixedSptMatrix X z r * parityConjMatrix t (mixedSptMatrix Y w s) =
      mixedSptMatrix Z (z * parityConj t w) (r * s) := by
  apply eq_of_mixedTensorAction_sptFixedPointTensor_eq t (r * s)
  funext i
  have hcomp := congrFun
    (mixedTensorAction_comp (sptFixedPointTensor D)
      (mixedSptMatrix X z r) (mixedSptMatrix Y w s) t r 1 s) i
  simp only [mul_one] at hcomp
  rw [← hcomp]
  have hY : mixedTensorAction (sptFixedPointTensor D) (mixedSptMatrix Y w s) 1 s =
      fun j => w • (Yᴴ * sptFixedPointTensor D j * Y) := by
    funext j
    exact mixedTensorAction_sptFixedPointTensor Y w 1 s j
  rw [hY, mixedTensorAction_conjugation,
    mixedTensorAction_sptFixedPointTensor,
    mixedTensorAction_sptFixedPointTensor]
  calc
    _ = (z * parityConj t w) •
        ((X * parityConjMatrix (t * r) Y)ᴴ * sptFixedPointTensor D i *
          (X * parityConjMatrix (t * r) Y)) := by
      simp [Matrix.conjTranspose_mul, Matrix.mul_assoc, smul_smul, mul_comm]
    _ = _ := by
      rw [hXY]
      have hc' : c * star c = 1 := by simpa only [mul_comm] using hc
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
        smul_smul, mul_assoc, hc', mul_one]

/-- Unitary virtual matrices and a unitary phase give a unitary physical action,
including the reflection swap. -/
theorem mixedSptMatrix_mem_unitaryGroup
    (X : Matrix (Fin D) (Fin D) ℂ) (φ : ℂ) (r : SymmetryParity)
    (hX : X ∈ Matrix.unitaryGroup (Fin D) ℂ) (hφ : φ ∈ unitary ℂ) :
    mixedSptMatrix X φ r ∈ Matrix.unitaryGroup (Fin (D * D)) ℂ := by
  apply Unitary.smul_mem_of_mem hφ
  rw [← Matrix.isUnitaryBetween_iff_mem_unitaryGroup]
  apply Matrix.IsUnitaryBetween.reindex
  rw [Matrix.isUnitaryBetween_iff_mem_unitaryGroup]
  exact Matrix.kronecker_mem_unitary (Matrix.map_star_mem_unitaryGroup_iff.mpr hX) hX

section Group

variable {G : Type} [Group G] (t r : G →* SymmetryParity)
variable {ω : ScalarCocycle G}
variable (ρ : ConjugateProjectiveRepresentation (t * r) ω (D := D))
variable (φ : G → unitary ℂ)

/-- The physical action realizing a virtual conjugate-projective representation
and a prescribed time-reversal-twisted character. -/
noncomputable def mixedSptAction (g : G) :
    Matrix (Fin (D * D)) (Fin (D * D)) ℂ :=
  mixedSptMatrix (ρ.X g) (φ g) (r g)

/-- Every physical symmetry matrix is unitary, even for an antiunitary symmetry
whose complex conjugation is implemented separately. -/
theorem mixedSptAction_unitary (g : G) :
    mixedSptAction t r ρ φ g ∈ Matrix.unitaryGroup (Fin (D * D)) ℂ :=
  mixedSptMatrix_mem_unitaryGroup _ _ _ (ρ.unitary g) (φ g).property

/-- The dimer tensor has the prescribed time-reversal/reflection symmetry. -/
theorem sptFixedPointTensor_isMixedSymmetric :
    IsMixedSymmetric (sptFixedPointTensor D) t r (mixedSptAction t r ρ φ)
      (fun g => (φ g : ℂ)) (fun g => (ρ.X g : Matrix (Fin D) (Fin D) ℂ)) :=
  fun _g i => mixedTensorAction_sptFixedPointTensor _ _ _ _ i

/-- The physical action is a genuine time-reversal-semilinear representation:
the virtual two-cocycle disappears from its multiplication law. -/
theorem mixedSptAction_mul [NeZero D]
    (hφ : letI := parityUnitaryAction t; groupCohomology.IsMulCocycle₁ φ)
    (g h : G) :
    mixedSptAction t r ρ φ (g * h) =
      mixedSptAction t r ρ φ g * parityConjMatrix (t g) (mixedSptAction t r ρ φ h) := by
  have hphase : (φ (g * h) : ℂ) = (φ g : ℂ) * parityConj (t g) (φ h : ℂ) := by
    have hu : φ (g * h) = parityUnitary (t g) (φ h) * φ g := hφ g h
    have hc := congrArg (fun z : unitary ℂ => (z : ℂ)) hu
    simpa only [Submonoid.coe_mul, parityUnitary_coe, mul_comm] using hc
  simp only [mixedSptAction, map_mul, hphase]
  exact (mixedSptMatrix_mul _ _ _ _ _ (ω g h : ℂ) _ _ _
    (ρ.map_mul g h) (ρ.factor_unitary (Nat.pos_of_ne_zero (NeZero.ne D)) g h)).symm

/-- The identity symmetry acts identically on the physical dimer. -/
theorem mixedSptAction_one [NeZero D]
    (hφ : letI := parityUnitaryAction t; groupCohomology.IsMulCocycle₁ φ) :
    mixedSptAction t r ρ φ 1 = 1 := by
  have h := mixedSptAction_mul t r ρ φ hφ 1 1
  simp only [one_mul, map_one, parityConjMatrix_one] at h
  have hu := Unitary.mul_star_self_of_mem (mixedSptAction_unitary t r ρ φ 1)
  have heq := congrArg (fun M => M * star (mixedSptAction t r ρ φ 1)) h
  simpa only [Matrix.mul_assoc, hu, Matrix.mul_one] using heq.symm

/-- The physical action on an N-site periodic wavefunction has the prescribed
phase to the Nth power, with actual conjugation and site-order reversal. -/
theorem mixedSptAction_mpv (g : G) {N : ℕ}
    (σ : Fin N → Fin (D * D)) :
    (∑ τ : Fin N → Fin (D * D),
      (∏ n, mixedSptAction t r ρ φ g (σ n) (τ n)) *
        parityConj (t g) (mpv (sptFixedPointTensor D)
          (if r g = 1 then τ else τ ∘ Fin.rev))) =
      (φ g : ℂ) ^ N * mpv (sptFixedPointTensor D) σ := by
  rw [← mpv_mixedTensorAction]
  have hX := Matrix.coe_gl_inv_eq_conjTranspose_of_mem_unitaryGroup
    (ρ.X g) (ρ.unitary g)
  have hfamily : mixedTensorAction (sptFixedPointTensor D)
      (mixedSptAction t r ρ φ g) (t g) (r g) =
      fun i => (φ g : ℂ) • ((ρ.X g : Matrix (Fin D) (Fin D) ℂ)ᴴ *
        sptFixedPointTensor D i * (ρ.X g : Matrix (Fin D) (Fin D) ℂ)) := by
    funext i
    exact sptFixedPointTensor_isMixedSymmetric t r ρ φ g i
  have hgauge : GaugeEquiv (sptFixedPointTensor D)
      (fun i => (ρ.X g : Matrix (Fin D) (Fin D) ℂ)ᴴ *
        sptFixedPointTensor D i * (ρ.X g : Matrix (Fin D) (Fin D) ℂ)) :=
    ⟨(ρ.X g)⁻¹, fun i => by simp only [inv_inv, hX]⟩
  rw [hfamily]
  calc
    _ = (φ g : ℂ) ^ N * mpv
        (fun i => (ρ.X g : Matrix (Fin D) (Fin D) ℂ)ᴴ *
          sptFixedPointTensor D i * (ρ.X g : Matrix (Fin D) (Fin D) ℂ)) σ := by
      simp [mpv, coeff, Kraus.evalWord_smul, Matrix.trace_smul]
    _ = _ := by rw [← hgauge.sameMPV N σ]

/-- Any other virtual action implementing the same symmetry of the dimer differs
pointwise only by scalar phases. This uses the actual injectivity of its letters. -/
theorem exists_rephase_of_mixedSptSymmetry [NeZero D]
    {ω' : ScalarCocycle G}
    (ρ' : ConjugateProjectiveRepresentation (t * r) ω' (D := D))
    (hρ' : IsMixedSymmetric (sptFixedPointTensor D) t r (mixedSptAction t r ρ φ)
      (fun g => (φ g : ℂ)) (fun g => (ρ'.X g : Matrix (Fin D) (Fin D) ℂ))) :
    ∃ ξ : G → Units ℂ, ∀ g, (ρ'.X g : Matrix (Fin D) (Fin D) ℂ) =
      (ξ g : ℂ) • (ρ.X g : Matrix (Fin D) (Fin D) ℂ) := by
  classical
  have hscalar (g : G) : ∃ ξ : Units ℂ,
      (ρ'.X g : Matrix (Fin D) (Fin D) ℂ) =
        (ξ : ℂ) • (ρ.X g : Matrix (Fin D) (Fin D) ℂ) := by
    have hsame (i) : (ρ.X g : Matrix (Fin D) (Fin D) ℂ)ᴴ *
        sptFixedPointTensor D i * (ρ.X g : Matrix (Fin D) (Fin D) ℂ) =
        (ρ'.X g : Matrix (Fin D) (Fin D) ℂ)ᴴ *
          sptFixedPointTensor D i * (ρ'.X g : Matrix (Fin D) (Fin D) ℂ) := by
      exact smul_right_injective (M := Matrix (Fin D) (Fin D) ℂ)
        (Unitary.toUnits (φ g)).ne_zero
        ((sptFixedPointTensor_isMixedSymmetric t r ρ φ g i).symm.trans (hρ' g i))
    have hX := Matrix.coe_gl_inv_eq_conjTranspose_of_mem_unitaryGroup
      (ρ.X g) (ρ.unitary g)
    have hY := Matrix.coe_gl_inv_eq_conjTranspose_of_mem_unitaryGroup
      (ρ'.X g) (ρ'.unitary g)
    obtain ⟨u, hu⟩ := gauge_unique_up_to_scalar sptFixedPointTensor_isInjective
      (X := (ρ.X g)⁻¹) (Y := (ρ'.X g)⁻¹)
      (B := fun i => (ρ.X g : Matrix (Fin D) (Fin D) ℂ)ᴴ *
        sptFixedPointTensor D i * (ρ.X g : Matrix (Fin D) (Fin D) ℂ))
      (fun i => by simp only [inv_inv, hX])
      (fun i => by simpa only [inv_inv, hY] using hsame i)
    have hv : (ρ.X g : Matrix (Fin D) (Fin D) ℂ) =
        (u : ℂ) • (ρ'.X g : Matrix (Fin D) (Fin D) ℂ) := by
      calc
        _ = (ρ'.X g : Matrix (Fin D) (Fin D) ℂ) *
            ((ρ'.X g)⁻¹ : GL (Fin D) ℂ) * (ρ.X g : Matrix (Fin D) (Fin D) ℂ) := by
          simp
        _ = (ρ'.X g : Matrix (Fin D) (Fin D) ℂ) *
            ((u : ℂ) • (((ρ.X g)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) *
              (ρ.X g : Matrix (Fin D) (Fin D) ℂ) := by rw [hu]
        _ = _ := by simp [Matrix.mul_assoc]
    refine ⟨u⁻¹, ?_⟩
    rw [hv, smul_smul]
    simp
  choose ξ hξ using hscalar
  exact ⟨ξ, hξ⟩

end Group

/-- The virtual U(1) cohomology class of the mixed dimer symmetry is independent
of the unitary gauge implementing it. -/
theorem parityUnitaryH2Class_eq_of_mixedSptSymmetry
    {G : Type} [Group G] [NeZero D] (t r : G →* SymmetryParity)
    {ω ω' : G → G → unitary ℂ}
    (ρ : ConjugateProjectiveRepresentation (t * r)
      (fun g h => Unitary.toUnits (ω g h)) (D := D))
    (ρ' : ConjugateProjectiveRepresentation (t * r)
      (fun g h => Unitary.toUnits (ω' g h)) (D := D))
    (φ : G → unitary ℂ)
    (hω : letI := parityUnitaryAction (t * r);
      groupCohomology.IsMulCocycle₂ (Function.uncurry ω))
    (hω' : letI := parityUnitaryAction (t * r);
      groupCohomology.IsMulCocycle₂ (Function.uncurry ω'))
    (hρ' : IsMixedSymmetric (sptFixedPointTensor D) t r (mixedSptAction t r ρ φ)
      (fun g => (φ g : ℂ)) (fun g => (ρ'.X g : Matrix (Fin D) (Fin D) ℂ))) :
    parityUnitaryH2Class (t * r) ω' hω' = parityUnitaryH2Class (t * r) ω hω := by
  obtain ⟨ξ, hξ⟩ := exists_rephase_of_mixedSptSymmetry t r ρ φ ρ' hρ'
  exact ρ.parityUnitaryH2Class_eq_of_rephase ρ'
    (Nat.pos_of_ne_zero (NeZero.ne D)) ξ hξ hω hω'

/-- Every pair of genuine twisted U(1) cocycles of a finite symmetry group has
an injective dimer fixed point with a rank-one idempotent transfer map. The
physical action is unitary and time-reversal-semilinear; its tensor symmetry
has exactly the prescribed character and virtual factor system. -/
theorem exists_mixed_spt_fixedPoint {G : Type} [Group G] [Fintype G]
    (t r : G →* SymmetryParity) (ω : G → G → unitary ℂ) (φ : G → unitary ℂ)
    (hω : letI := parityUnitaryAction (t * r);
      groupCohomology.IsMulCocycle₂ (Function.uncurry ω))
    (hφ : letI := parityUnitaryAction t; groupCohomology.IsMulCocycle₁ φ) :
    ∃ ρ : ConjugateProjectiveRepresentation (t * r)
        (fun g h => Unitary.toUnits (ω g h)) (D := Fintype.card G),
      Kraus.IsInjective (sptFixedPointTensor (Fintype.card G)) ∧
      IsTransferIdempotent (sptFixedPointTensor (Fintype.card G)) ∧
      Module.finrank ℂ (LinearMap.range
        (Kraus.transferMap (sptFixedPointTensor (Fintype.card G)))) = 1 ∧
      (∀ g, mixedSptAction t r ρ φ g ∈
        Matrix.unitaryGroup (Fin (Fintype.card G * Fintype.card G)) ℂ) ∧
      (∀ g h, mixedSptAction t r ρ φ (g * h) =
        mixedSptAction t r ρ φ g * parityConjMatrix (t g) (mixedSptAction t r ρ φ h)) ∧
      IsMixedSymmetric (sptFixedPointTensor (Fintype.card G)) t r
        (mixedSptAction t r ρ φ) (fun g => (φ g : ℂ))
        (fun g => (ρ.X g : Matrix (Fin (Fintype.card G)) (Fin (Fintype.card G)) ℂ)) := by
  classical
  let : NeZero (Fintype.card G) := ⟨Fintype.card_ne_zero⟩
  let ρ := conjugateRegularUnitaryRepresentation (t * r) ω hω
  exact ⟨ρ, sptFixedPointTensor_isInjective, sptFixedPointTensor_isTransferIdempotent,
    finrank_range_transferMap_sptFixedPointTensor, mixedSptAction_unitary t r ρ φ,
    mixedSptAction_mul t r ρ φ hφ, sptFixedPointTensor_isMixedSymmetric t r ρ φ⟩

end MPSTensor
