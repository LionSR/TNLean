/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.PolarUniqueness
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Continuous local frames of projection families

This module supplies auxiliary finite-dimensional ingredients for the
support comparison in Schuch–Pérez-García–Cirac, arXiv:1010.3732,
Appendix C, lines 2653–2717. Continuity of the projection family is explicit;
it is not inferred here from a physical gap or an ambient tensor path.
The outstanding canonical-support construction is recorded in
`docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.
-/

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology

namespace Matrix

/-- The positive polar factor of a continuous rectangular matrix family is
continuous. Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem continuous_polarPos_family
    {T m n : Type*} [TopologicalSpace T]
    [Fintype m] [Fintype n] [DecidableEq n]
    (M : T → Matrix m n ℂ) (hM : Continuous M) :
    Continuous fun t => polarPos (M t) := by
  classical
  have hGram : Continuous fun t => (M t)ᴴ * M t := hM.matrix_conjTranspose.matrix_mul hM
  have hsqrt : Continuous fun t => cfc Real.sqrt ((M t)ᴴ * M t) :=
    Continuous.cfc_of_mem_nhdsSet Real.sqrt (s := Set.univ) (by simp) hGram
      (fun t => isHermitian_conjTranspose_mul_self (M t)) Real.continuous_sqrt.continuousOn
  convert hsqrt using 1
  funext t
  rw [polarPos, CFC.sqrt_eq_real_sqrt _ (posSemidef_conjTranspose_mul_self (M t)).nonneg,
    cfcₙ_eq_cfc]

/-- On an injective rectangular matrix the polar isometry is obtained by
inverting its positive factor. Source context: arXiv:1010.3732,
Appendix C, lines 2653–2717. -/
theorem polarIso_eq_mul_inv_polarPos_of_injective
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℂ) (hM : Function.Injective M.mulVec) :
    polarIso M = M * (polarPos M)⁻¹ := by
  classical
  have hunit := (posDef_polarPos_of_injective M hM).isUnit
  calc
    polarIso M = polarIso M * (polarPos M * (polarPos M)⁻¹) := by
      rw [mul_nonsing_inv (A := polarPos M)
        ((polarPos M).isUnit_iff_isUnit_det.mp hunit), Matrix.mul_one]
    _ = M * (polarPos M)⁻¹ := by rw [← Matrix.mul_assoc, polarIso_mul_polarPos]

/-- Polar isometries vary continuously in a continuous family of injective
rectangular matrices. Source context: arXiv:1010.3732, Appendix C,
lines 2653–2717. -/
theorem continuous_polarIso_family_of_injective
    {T m n : Type*} [TopologicalSpace T]
    [Fintype m] [Fintype n] [DecidableEq n]
    (M : T → Matrix m n ℂ) (hM : Continuous M)
    (hInj : ∀ t, Function.Injective (M t).mulVec) :
    Continuous fun t => polarIso (M t) := by
  classical
  have hPos := continuous_polarPos_family M hM
  have hInv : Continuous fun t => Ring.inverse (polarPos (M t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hAt : ContinuousAt Ring.inverse (polarPos (M t)) := by
      obtain ⟨u, hu⟩ := (posDef_polarPos_of_injective (M t) (hInj t)).isUnit
      rw [← hu]
      exact NormedRing.inverse_continuousAt u
    exact hAt.comp' (f := fun t => polarPos (M t)) hPos.continuousAt
  have h := hM.matrix_mul hInv
  simpa only [polarIso_eq_mul_inv_polarPos_of_injective _ (hInj _),
    nonsing_inv_eq_ringInverse] using h

/-- The projected base frame has invertible Gram matrix near the base
parameter. Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem exists_open_projected_frame_injective
    {T m n : Type*} [TopologicalSpace T]
    [Fintype m] [Fintype n] [DecidableEq n]
    (P : T → Matrix m m ℂ) (hP : Continuous P) (t₀ : T)
    (J₀ : Matrix m n ℂ) (hJ₀ : J₀.IsIsometry) (hbase : P t₀ = J₀ * J₀ᴴ) :
    ∃ S : Set T, IsOpen S ∧ t₀ ∈ S ∧
      ∀ t ∈ S, Function.Injective (P t * J₀).mulVec := by
  classical
  let M := fun t => P t * J₀
  have hM : Continuous M := hP.matrix_mul continuous_const
  have hGram : Continuous fun t => (M t)ᴴ * M t := hM.matrix_conjTranspose.matrix_mul hM
  have hJ : J₀ᴴ * J₀ = 1 := hJ₀
  have hMbase : M t₀ = J₀ := by
    simp only [M, hbase, Matrix.mul_assoc, hJ, Matrix.mul_one]
  let S := {t | IsUnit ((M t)ᴴ * M t)}
  refine ⟨S, Units.isOpen.preimage hGram, ?_, ?_⟩
  · change IsUnit ((M t₀)ᴴ * M t₀)
    rw [hMbase, hJ]
    exact isUnit_one
  · intro t ht a b hab
    apply (mulVec_injective_iff_isUnit.mpr ht)
    simpa only [mulVec_mulVec] using congrArg ((M t)ᴴ *ᵥ ·) hab

/-- The polar frame selected by projecting a base frame is continuous and
isometric locally, and lies in the prescribed projection range. Source
context: arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem exists_local_continuous_isometric_projected_frame
    {T m n : Type*} [TopologicalSpace T]
    [Fintype m] [Fintype n] [DecidableEq n]
    (P : T → Matrix m m ℂ) (hP : Continuous P) (hid : ∀ t, P t * P t = P t)
    (t₀ : T) (J₀ : Matrix m n ℂ) (hJ₀ : J₀.IsIsometry) (hbase : P t₀ = J₀ * J₀ᴴ) :
    ∃ S : Set T, IsOpen S ∧ t₀ ∈ S ∧
      ContinuousOn (fun t => polarIso (P t * J₀)) S ∧
      ∀ t ∈ S, (polarIso (P t * J₀)).IsIsometry ∧
        P t * polarIso (P t * J₀) = polarIso (P t * J₀) := by
  classical
  obtain ⟨S, hS, ht₀, hInj⟩ := exists_open_projected_frame_injective P hP t₀ J₀ hJ₀ hbase
  refine ⟨S, hS, ht₀, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    exact continuous_polarIso_family_of_injective (fun t : S => P t * J₀)
      ((hP.comp continuous_subtype_val).matrix_mul continuous_const)
      (fun t => hInj t t.property)
  · intro t ht
    refine ⟨isIsometry_polarIso_of_injective _ (hInj t ht), ?_⟩
    obtain ⟨R, hR⟩ := exists_polarIso_eq_mul (P t * J₀)
    rw [hR, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hid t]

/-- An isometric frame contained in a projection range exhausts that range
when their ranks agree. Source context: arXiv:1010.3732, Appendix C,
lines 2653–2717. -/
theorem range_eq_of_isometric_frame_of_rank_eq
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (P : Matrix m m ℂ) (J : Matrix m n ℂ) (hJ : J.IsIsometry)
    (hPJ : P * J = J) (hrank : P.rank = Fintype.card n) :
    LinearMap.range J.mulVecLin = LinearMap.range P.mulVecLin := by
  classical
  have hle : LinearMap.range J.mulVecLin ≤ LinearMap.range P.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    refine ⟨J *ᵥ v, ?_⟩
    change P *ᵥ (J *ᵥ v) = J *ᵥ v
    rw [mulVec_mulVec, hPJ]
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hJrank := J.rank_eq_finrank_range_toLin (Pi.basisFun ℂ m) (Pi.basisFun ℂ n)
  have hPrank := P.rank_eq_finrank_range_toLin (Pi.basisFun ℂ m) (Pi.basisFun ℂ m)
  rw [toLin_eq_toLin', toLin'_apply'] at hJrank hPrank
  rw [← hJrank, ← hPrank, hJ.rank_eq_card J, hrank]

/-- A Hermitian projection is recovered from any full isometric frame in
its range. Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem frame_mul_conjTranspose_eq_of_rank_eq
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (P : Matrix m m ℂ) (hP : P.IsHermitian) (J : Matrix m n ℂ) (hJ : J.IsIsometry)
    (hPJ : P * J = J) (hrank : P.rank = Fintype.card n) : J * Jᴴ = P := by
  classical
  obtain ⟨R, hR⟩ := exists_mul_eq_of_range_le
    (range_eq_of_isometric_frame_of_rank_eq P J hJ hPJ hrank).ge
  have hAdj : Jᴴ * P = Jᴴ := by
    simpa only [conjTranspose_mul, hP.eq] using congrArg conjTranspose hPJ
  have hJR : J * Jᴴ * P = P := by
    rw [← hR, Matrix.mul_assoc, ← Matrix.mul_assoc Jᴴ, hJ, Matrix.one_mul]
  simpa only [Matrix.mul_assoc, hAdj] using hJR

/-- A continuous fixed-rank orthogonal projection family admits continuous
isometric frames locally near a prescribed base frame. Source context:
arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem exists_local_continuous_projection_frame
    {T m n : Type*} [TopologicalSpace T]
    [Fintype m] [Fintype n] [DecidableEq n]
    (P : T → Matrix m m ℂ) (hP : Continuous P)
    (hHerm : ∀ t, (P t).IsHermitian) (hid : ∀ t, P t * P t = P t)
    (hrank : ∀ t, (P t).rank = Fintype.card n)
    (t₀ : T) (J₀ : Matrix m n ℂ) (hJ₀ : J₀.IsIsometry) (hbase : P t₀ = J₀ * J₀ᴴ) :
    ∃ S : Set T, IsOpen S ∧ t₀ ∈ S ∧
      ContinuousOn (fun t => polarIso (P t * J₀)) S ∧
      ∀ t ∈ S, (polarIso (P t * J₀)).IsIsometry ∧
        polarIso (P t * J₀) * (polarIso (P t * J₀))ᴴ = P t := by
  classical
  obtain ⟨S, hS, ht₀, hcont, hFrame⟩ :=
    exists_local_continuous_isometric_projected_frame P hP hid t₀ J₀ hJ₀ hbase
  refine ⟨S, hS, ht₀, hcont, ?_⟩
  intro t ht
  obtain ⟨hIso, hContained⟩ := hFrame t ht
  exact ⟨hIso, frame_mul_conjTranspose_eq_of_rank_eq (P t) (hHerm t)
    (polarIso (P t * J₀)) hIso hContained (hrank t)⟩

end Matrix
