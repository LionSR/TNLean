/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.TwoProjectionCompression
import TNLean.MPS.ParentHamiltonian.FNWAggregateOrthogonality
import TNLean.MPS.ParentHamiltonian.SpectatorBoundaryGram
import TNLean.Wielandt.Primitivity.StronglyIrreducibleToFullRank

/-!
# FNW projector defect

This module completes the Hilbert-space geometry in Fannes--Nachtergaele--Werner,
*Communications in Mathematical Physics* 144 (1992), Lemma 6.2. The two overlap
ranges contain the full boundary range. The source-coordinate overlap estimate
therefore controls the relative defect of their orthogonal projections. A global
physical reversal then identifies these three ranges with the two overlapping
boundary ranges and the full ground space in reversed block order.
-/

open scoped BigOperators ComplexOrder Matrix

namespace MPSTensor

noncomputable section

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- The full FNW boundary range lies in the left-overlap range. -/
private theorem fnwBoundaryRange_le_leftOverlapRange
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    fnwBoundaryRange ρ hρ A ((ℓ + m) + r) ≤
      LinearMap.range (fnwLeftOverlapMap ρ hρ A ℓ m r) := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  rintro x ⟨B, rfl⟩
  exact ⟨fnwLeftFullGroundFamily A r B,
    fnwLeftOverlapMap_fullGroundFamily ρ hρ A ℓ m r B⟩

/-- The full FNW boundary range lies in the right-overlap range. -/
private theorem fnwBoundaryRange_le_rightOverlapRange
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    fnwBoundaryRange ρ hρ A ((ℓ + m) + r) ≤
      LinearMap.range (fnwRightOverlapMap ρ hρ A ℓ m r) := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  rintro x ⟨B, rfl⟩
  exact ⟨fnwRightFullGroundFamily A ℓ B,
    fnwRightOverlapMap_fullGroundFamily ρ hρ A ℓ m r B⟩

/-- The source-coordinate form of the FNW relative projector defect. The
coefficient is kept as the separate linear and quadratic contributions from
Lemma 6.2. -/
private theorem norm_fnwOverlapRange_projector_defect_le [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    (hρfix : Kraus.transferMap A ρ = ρ) (ℓ m r : ℕ)
    (hminus : 0 < fnwLowerBoundaryConstant ρ hρ A m) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    ‖(LinearMap.range (fnwLeftOverlapMap ρ hρ A ℓ m r)).starProjection ∘L
          (LinearMap.range (fnwRightOverlapMap ρ hρ A ℓ m r)).starProjection -
        (fnwBoundaryRange ρ hρ A ((ℓ + m) + r)).starProjection‖ ≤
      fnwMixingQuantity ρ hρ A htr m /
          fnwLowerBoundaryConstant ρ hρ A m +
        fnwMixingQuantity ρ hρ A htr m ^ 2 /
          fnwLowerBoundaryConstant ρ hρ A m := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let U := LinearMap.range (fnwLeftOverlapMap ρ hρ A ℓ m r)
  let V := LinearMap.range (fnwRightOverlapMap ρ hρ A ℓ m r)
  let W := fnwBoundaryRange ρ hρ A ((ℓ + m) + r)
  let η := fnwMixingQuantity ρ hρ A htr m /
      fnwLowerBoundaryConstant ρ hρ A m +
    fnwMixingQuantity ρ hρ A htr m ^ 2 /
      fnwLowerBoundaryConstant ρ hρ A m
  have ha : 0 ≤ fnwMixingQuantity ρ hρ A htr m :=
    mul_nonneg (fnwTraceInverseFactor_pos hρ).le (norm_nonneg _)
  have hη : 0 ≤ η := by
    dsimp only [η]
    positivity
  apply Submodule.norm_starProjection_comp_sub_starProjection_le_of_relative_overlap
    U V W
  · exact fnwBoundaryRange_le_leftOverlapRange ρ hρ A ℓ m r
  · exact fnwBoundaryRange_le_rightOverlapRange ρ hρ A ℓ m r
  · exact hη
  · intro x hxU hxW y hyV hyW
    obtain ⟨Φ, rfl⟩ := hxU
    obtain ⟨Ψ, rfl⟩ := hyV
    exact norm_inner_fnwOverlapMaps_le_linear_add_quadratic
      ρ hρ htr A hA hρfix ℓ m r Φ Ψ hxW hyW hminus

private theorem cfg_comp_rev_comp_rev (N : ℕ) (μ : Cfg d N) :
    (μ ∘ Fin.rev) ∘ Fin.rev = μ := by
  ext i
  simp

private theorem physicalSiteReverseConfigEquiv_apply_cfg
    (N : ℕ) (μ : Cfg d N) :
    physicalSiteReverseConfigEquiv d N μ = μ ∘ Fin.rev := rfl

private theorem physicalSiteReverseConfigEquiv_apply_apply_cfg
    (N : ℕ) (μ : Cfg d N) :
    physicalSiteReverseConfigEquiv d N
        (physicalSiteReverseConfigEquiv d N μ) = μ := by
  ext i
  simp [physicalSiteReverseConfigEquiv, Equiv.arrowCongr, Function.comp_def]

/-- Reversal and reordering of the three separate configuration blocks. -/
private def fnwReverseThreeBlocksEquiv (d ℓ m r : ℕ) :
    ((Cfg d ℓ × Cfg d m) × Cfg d r) ≃ ((Cfg d r × Cfg d m) × Cfg d ℓ) where
  toFun blocks :=
    ((physicalSiteReverseConfigEquiv d r blocks.2,
        physicalSiteReverseConfigEquiv d m blocks.1.2),
      physicalSiteReverseConfigEquiv d ℓ blocks.1.1)
  invFun blocks :=
    ((physicalSiteReverseConfigEquiv d ℓ blocks.2,
        physicalSiteReverseConfigEquiv d m blocks.1.2),
      physicalSiteReverseConfigEquiv d r blocks.1.1)
  left_inv := by
    rintro ⟨⟨μℓ, μm⟩, μr⟩
    simp only [physicalSiteReverseConfigEquiv_apply_apply_cfg]
  right_inv := by
    rintro ⟨⟨μr, μm⟩, μℓ⟩
    simp only [physicalSiteReverseConfigEquiv_apply_apply_cfg]

/-- Global physical reversal sends the source block order \(\ell,m,r\) to
the whole-increment order \(r,m,\ell\), reversing the sites inside each
block. -/
private def fnwGlobalPhysicalReverseConfigEquiv (d ℓ m r : ℕ) :
    Cfg d ((ℓ + m) + r) ≃ Cfg d (r + m + ℓ) :=
  (fnwThreeBlockConfigEquiv d ℓ m r).symm |>.trans
    (fnwReverseThreeBlocksEquiv d ℓ m r) |>.trans
      (fnwThreeBlockConfigEquiv d r m ℓ)

/-- The exact Hilbert-space equivalence implementing global physical reversal
between the FNW source coordinates and the whole-increment coordinates. -/
private noncomputable def fnwGlobalPhysicalReverseES (d ℓ m r : ℕ) :
    EuclideanSpace ℂ (Cfg d ((ℓ + m) + r)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Cfg d (r + m + ℓ)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (fnwGlobalPhysicalReverseConfigEquiv d ℓ m r)

private theorem fnwGlobalPhysicalReverseES_apply_append
    (ℓ m r : ℕ) (ψ : EuclideanSpace ℂ (Cfg d ((ℓ + m) + r)))
    (μr : Cfg d r) (μm : Cfg d m) (μℓ : Cfg d ℓ) :
    fnwGlobalPhysicalReverseES d ℓ m r ψ
        (Fin.append (Fin.append μr μm) μℓ) =
      ψ (Fin.append
        (Fin.append (μℓ ∘ Fin.rev) (μm ∘ Fin.rev)) (μr ∘ Fin.rev)) := by
  simp [fnwGlobalPhysicalReverseES, fnwGlobalPhysicalReverseConfigEquiv,
    fnwReverseThreeBlocksEquiv, physicalSiteReverseConfigEquiv_apply_cfg,
    Equiv.piCongrLeft']

/-- Extensionality in the three separate configuration blocks. -/
private theorem euclideanSpace_threeBlock_ext
    (r m ℓ : ℕ) {x y : EuclideanSpace ℂ (Cfg d (r + m + ℓ))}
    (h : ∀ μr : Cfg d r, ∀ μm : Cfg d m, ∀ μℓ : Cfg d ℓ,
      x (Fin.append (Fin.append μr μm) μℓ) =
        y (Fin.append (Fin.append μr μm) μℓ)) :
    x = y := by
  apply PiLp.ext
  intro σ
  rw [← (fnwThreeBlockConfigEquiv d r m ℓ).apply_symm_apply σ]
  obtain ⟨⟨μr, μm⟩, μℓ⟩ := (fnwThreeBlockConfigEquiv d r m ℓ).symm σ
  exact h μr μm μℓ

private theorem reassocTailBoundaryMapES_apply_threeBlock
    (A : MPSTensor d D) (r m ℓ : ℕ)
    (y : BoundaryFamilySpace (D := D) (Cfg d r))
    (μr : Cfg d r) (μm : Cfg d m) (μℓ : Cfg d ℓ) :
    reassocTailBoundaryMapES A r m ℓ y
        (Fin.append (Fin.append μr μm) μℓ) =
      groundSpaceMap A (m + ℓ)
        (boundaryFamilyEquiv (D := D) (Cfg d r) y μr)
        (Fin.append μm μℓ) := by
  change tailBoundaryMapES A r (m + ℓ) y
      (((finCongr (Nat.add_assoc r m ℓ)).arrowCongr
        (Equiv.refl (Fin d))) (Fin.append (Fin.append μr μm) μℓ)) = _
  have hcfg :
      ((finCongr (Nat.add_assoc r m ℓ)).arrowCongr
        (Equiv.refl (Fin d))) (Fin.append (Fin.append μr μm) μℓ) =
        Fin.append μr (Fin.append μm μℓ) := by
    rw [Fin.append_assoc]
    rfl
  rw [hcfg]
  change tailBoundaryMap A r (m + ℓ)
      (boundaryFamilyEquiv (D := D) (Cfg d r) y)
      (Fin.append μr (Fin.append μm μℓ)) = _
  exact tailBoundaryMap_append A r (m + ℓ)
    (boundaryFamilyEquiv (D := D) (Cfg d r) y) μr (Fin.append μm μℓ)

/-- Global physical reversal carries the left FNW overlap range to the
reassociated tail boundary range. -/
private theorem fnwGlobalPhysicalReverseES_map_leftOverlapRange
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    (LinearMap.range (fnwLeftOverlapMap ρ hρ A ℓ m r)).map
        (fnwGlobalPhysicalReverseES d ℓ m r).toLinearEquiv.toLinearMap =
      (reassocTailBoundaryMapES A r m ℓ).range := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  ext x
  constructor
  · rintro ⟨v, ⟨Φ, rfl⟩, rfl⟩
    let Y : Cfg d r → Mat := fun μr => Φ.ofLp (μr ∘ Fin.rev)
    let y : BoundaryFamilySpace (D := D) (Cfg d r) :=
      (boundaryFamilyEquiv (D := D) (Cfg d r)).symm Y
    refine ⟨y, ?_⟩
    apply euclideanSpace_threeBlock_ext r m ℓ
    intro μr μm μℓ
    change reassocTailBoundaryMapES A r m ℓ y
        (Fin.append (Fin.append μr μm) μℓ) =
      fnwGlobalPhysicalReverseES d ℓ m r
        (fnwLeftOverlapMap ρ hρ A ℓ m r Φ)
        (Fin.append (Fin.append μr μm) μℓ)
    rw [reassocTailBoundaryMapES_apply_threeBlock,
      fnwGlobalPhysicalReverseES_apply_append,
      fnwLeftOverlapMap_apply_append]
    simp only [Y, y, LinearEquiv.apply_symm_apply,
      fnwBoundaryMapCLM_apply, fnwBoundaryMap_apply, groundSpaceMap_apply,
      List.ofFn_fin_append, Kraus.evalWord_append,
      Kraus.evalWord_conjTranspose, List.ofFn_reverse,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      cfg_comp_rev_comp_rev]
    exact Matrix.trace_mul_comm
      (Kraus.evalWord A (List.ofFn μm) * Kraus.evalWord A (List.ofFn μℓ))
      (Φ.ofLp (μr ∘ Fin.rev))
  · rintro ⟨y, rfl⟩
    let Y := boundaryFamilyEquiv (D := D) (Cfg d r) y
    let Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r) :=
      WithLp.toLp 2 fun μr => Y (μr ∘ Fin.rev)
    refine ⟨fnwLeftOverlapMap ρ hρ A ℓ m r Φ, ⟨Φ, rfl⟩, ?_⟩
    apply euclideanSpace_threeBlock_ext r m ℓ
    intro μr μm μℓ
    change fnwGlobalPhysicalReverseES d ℓ m r
        (fnwLeftOverlapMap ρ hρ A ℓ m r Φ)
        (Fin.append (Fin.append μr μm) μℓ) =
      reassocTailBoundaryMapES A r m ℓ y
        (Fin.append (Fin.append μr μm) μℓ)
    rw [reassocTailBoundaryMapES_apply_threeBlock,
      fnwGlobalPhysicalReverseES_apply_append,
      fnwLeftOverlapMap_apply_append]
    simp only [Y, Φ, boundaryFamilyEquiv_apply_apply,
      fnwBoundaryMapCLM_apply, fnwBoundaryMap_apply, groundSpaceMap_apply,
      List.ofFn_fin_append, Kraus.evalWord_append,
      Kraus.evalWord_conjTranspose, List.ofFn_reverse,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      cfg_comp_rev_comp_rev]
    exact Matrix.trace_mul_comm
      (boundaryFamilyEquiv (D := D) (Cfg d r) y μr)
      (Kraus.evalWord A (List.ofFn μm) * Kraus.evalWord A (List.ofFn μℓ))

private theorem leftBoundaryMapES_apply_threeBlock
    (A : MPSTensor d D) (r m ℓ : ℕ)
    (y : BoundaryFamilySpace (D := D) (Cfg d ℓ))
    (μr : Cfg d r) (μm : Cfg d m) (μℓ : Cfg d ℓ) :
    leftBoundaryMapES A (r + m) ℓ y
        (Fin.append (Fin.append μr μm) μℓ) =
      groundSpaceMap A (r + m)
        (boundaryFamilyEquiv (D := D) (Cfg d ℓ) y μℓ)
        (Fin.append μr μm) := by
  change leftBoundaryMap A (r + m) ℓ
      (boundaryFamilyEquiv (D := D) (Cfg d ℓ) y)
      (Fin.append (Fin.append μr μm) μℓ) = _
  exact leftBoundaryMap_append A (r + m) ℓ
    (boundaryFamilyEquiv (D := D) (Cfg d ℓ) y) (Fin.append μr μm) μℓ

/-- Global physical reversal carries the right FNW overlap range to the left
boundary range in whole-increment coordinates. -/
private theorem fnwGlobalPhysicalReverseES_map_rightOverlapRange
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    (LinearMap.range (fnwRightOverlapMap ρ hρ A ℓ m r)).map
        (fnwGlobalPhysicalReverseES d ℓ m r).toLinearEquiv.toLinearMap =
      (leftBoundaryMapES A (r + m) ℓ).range := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  ext x
  constructor
  · rintro ⟨v, ⟨Ψ, rfl⟩, rfl⟩
    let Z : Cfg d ℓ → Mat := fun μℓ => Ψ.ofLp (μℓ ∘ Fin.rev)
    let z : BoundaryFamilySpace (D := D) (Cfg d ℓ) :=
      (boundaryFamilyEquiv (D := D) (Cfg d ℓ)).symm Z
    refine ⟨z, ?_⟩
    apply euclideanSpace_threeBlock_ext r m ℓ
    intro μr μm μℓ
    change leftBoundaryMapES A (r + m) ℓ z
        (Fin.append (Fin.append μr μm) μℓ) =
      fnwGlobalPhysicalReverseES d ℓ m r
        (fnwRightOverlapMap ρ hρ A ℓ m r Ψ)
        (Fin.append (Fin.append μr μm) μℓ)
    rw [leftBoundaryMapES_apply_threeBlock,
      fnwGlobalPhysicalReverseES_apply_append,
      fnwRightOverlapMap_apply_append]
    simp only [Z, z, LinearEquiv.apply_symm_apply,
      fnwBoundaryMapCLM_apply, fnwBoundaryMap_apply, groundSpaceMap_apply,
      List.ofFn_fin_append, Kraus.evalWord_append,
      Kraus.evalWord_conjTranspose, List.ofFn_reverse,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      cfg_comp_rev_comp_rev]
    exact Matrix.trace_mul_comm
      (Kraus.evalWord A (List.ofFn μr) * Kraus.evalWord A (List.ofFn μm))
      (Ψ.ofLp (μℓ ∘ Fin.rev))
  · rintro ⟨z, rfl⟩
    let Z := boundaryFamilyEquiv (D := D) (Cfg d ℓ) z
    let Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ) :=
      WithLp.toLp 2 fun μℓ => Z (μℓ ∘ Fin.rev)
    refine ⟨fnwRightOverlapMap ρ hρ A ℓ m r Ψ, ⟨Ψ, rfl⟩, ?_⟩
    apply euclideanSpace_threeBlock_ext r m ℓ
    intro μr μm μℓ
    change fnwGlobalPhysicalReverseES d ℓ m r
        (fnwRightOverlapMap ρ hρ A ℓ m r Ψ)
        (Fin.append (Fin.append μr μm) μℓ) =
      leftBoundaryMapES A (r + m) ℓ z
        (Fin.append (Fin.append μr μm) μℓ)
    rw [leftBoundaryMapES_apply_threeBlock,
      fnwGlobalPhysicalReverseES_apply_append,
      fnwRightOverlapMap_apply_append]
    simp only [Z, Ψ, boundaryFamilyEquiv_apply_apply,
      fnwBoundaryMapCLM_apply, fnwBoundaryMap_apply, groundSpaceMap_apply,
      List.ofFn_fin_append, Kraus.evalWord_append,
      Kraus.evalWord_conjTranspose, List.ofFn_reverse,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      cfg_comp_rev_comp_rev]
    exact Matrix.trace_mul_comm
      (boundaryFamilyEquiv (D := D) (Cfg d ℓ) z μℓ)
      (Kraus.evalWord A (List.ofFn μr) * Kraus.evalWord A (List.ofFn μm))

/-- Global physical reversal sends a full FNW boundary vector to the
corresponding full-ground-space vector. -/
private theorem fnwGlobalPhysicalReverseES_fnwBoundaryMapCLM
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ) (B : Mat) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    fnwGlobalPhysicalReverseES d ℓ m r
        (fnwBoundaryMapCLM ρ hρ A ((ℓ + m) + r) B) =
      groundSpaceMapES A (r + m + ℓ)
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) B) := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  apply euclideanSpace_threeBlock_ext r m ℓ
  intro μr μm μℓ
  change fnwGlobalPhysicalReverseES d ℓ m r
      (fnwBoundaryMapCLM ρ hρ A ((ℓ + m) + r) B)
      (Fin.append (Fin.append μr μm) μℓ) =
    groundSpaceMap A (r + m + ℓ) B (Fin.append (Fin.append μr μm) μℓ)
  simp only [fnwGlobalPhysicalReverseES_apply_append, fnwBoundaryMapCLM_apply,
    fnwBoundaryMap_apply, groundSpaceMap_apply, List.ofFn_fin_append,
    Kraus.evalWord_append, Kraus.evalWord_conjTranspose, List.ofFn_reverse,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    cfg_comp_rev_comp_rev]
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm B
    ((Kraus.evalWord A (List.ofFn μr) * Kraus.evalWord A (List.ofFn μm)) *
      Kraus.evalWord A (List.ofFn μℓ))

/-- Global physical reversal carries the full FNW boundary range to the
full ground space. -/
private theorem fnwGlobalPhysicalReverseES_map_boundaryRange
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    (fnwBoundaryRange ρ hρ A ((ℓ + m) + r)).map
        (fnwGlobalPhysicalReverseES d ℓ m r).toLinearEquiv.toLinearMap =
      groundSpaceES A (r + m + ℓ) := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  ext x
  constructor
  · rintro ⟨v, ⟨B, rfl⟩, rfl⟩
    rw [mem_groundSpaceES_iff]
    change (WithLp.linearEquiv 2 ℂ (NSiteSpace d (r + m + ℓ)))
      (fnwGlobalPhysicalReverseES d ℓ m r
        (fnwBoundaryMapCLM ρ hρ A ((ℓ + m) + r) B)) ∈
      groundSpace A (r + m + ℓ)
    rw [fnwGlobalPhysicalReverseES_fnwBoundaryMapCLM,
      groundSpaceMapES_frobeniusEquivEuclidean_apply,
      LinearEquiv.apply_symm_apply]
    exact LinearMap.mem_range_self (groundSpaceMap A (r + m + ℓ)) B
  · intro hx
    rw [mem_groundSpaceES_iff] at hx
    obtain ⟨B, hB⟩ := hx
    refine ⟨fnwBoundaryMapCLM ρ hρ A ((ℓ + m) + r) B, ⟨B, rfl⟩, ?_⟩
    change fnwGlobalPhysicalReverseES d ℓ m r
        (fnwBoundaryMapCLM ρ hρ A ((ℓ + m) + r) B) = x
    rw [fnwGlobalPhysicalReverseES_fnwBoundaryMapCLM,
      groundSpaceMapES_frobeniusEquivEuclidean_apply]
    apply (WithLp.linearEquiv 2 ℂ (NSiteSpace d (r + m + ℓ))).injective
    rw [LinearEquiv.apply_symm_apply]
    exact hB

/-- The source-coordinate projector defect and the whole-increment
defect have equal operator norm under global physical reversal. -/
private theorem norm_fnwOverlapRange_projector_defect_eq_wholeIncrement
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    ‖(LinearMap.range (fnwLeftOverlapMap ρ hρ A ℓ m r)).starProjection ∘L
          (LinearMap.range (fnwRightOverlapMap ρ hρ A ℓ m r)).starProjection -
        (fnwBoundaryRange ρ hρ A ((ℓ + m) + r)).starProjection‖ =
      ‖(reassocTailBoundaryMapES A r m ℓ).range.starProjection ∘L
          (leftBoundaryMapES A (r + m) ℓ).range.starProjection -
        (groundSpaceES A (r + m + ℓ)).starProjection‖ := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let E := fnwGlobalPhysicalReverseES d ℓ m r
  let U := LinearMap.range (fnwLeftOverlapMap ρ hρ A ℓ m r)
  let V := LinearMap.range (fnwRightOverlapMap ρ hρ A ℓ m r)
  let W := fnwBoundaryRange ρ hρ A ((ℓ + m) + r)
  let X := U.starProjection ∘L V.starProjection - W.starProjection
  have hU : U.map E.toLinearEquiv.toLinearMap =
      (reassocTailBoundaryMapES A r m ℓ).range :=
    fnwGlobalPhysicalReverseES_map_leftOverlapRange ρ hρ A ℓ m r
  have hV : V.map E.toLinearEquiv.toLinearMap =
      (leftBoundaryMapES A (r + m) ℓ).range :=
    fnwGlobalPhysicalReverseES_map_rightOverlapRange ρ hρ A ℓ m r
  have hW : W.map E.toLinearEquiv.toLinearMap = groundSpaceES A (r + m + ℓ) :=
    fnwGlobalPhysicalReverseES_map_boundaryRange ρ hρ A ℓ m r
  have hconj :
      E.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (X.comp E.symm.toContinuousLinearEquiv.toContinuousLinearMap) =
      (reassocTailBoundaryMapES A r m ℓ).range.starProjection ∘L
          (leftBoundaryMapES A (r + m) ℓ).range.starProjection -
        (groundSpaceES A (r + m + ℓ)).starProjection := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, X, sub_apply]
    have hUp := Submodule.starProjection_map_apply E U v
    have hVp := Submodule.starProjection_map_apply E V v
    have hWp := Submodule.starProjection_map_apply E W v
    have hUp' : (reassocTailBoundaryMapES A r m ℓ).range.starProjection v =
        E (U.starProjection (E.symm v)) := by
      simpa only [hU] using hUp
    have hVp' : (leftBoundaryMapES A (r + m) ℓ).range.starProjection v =
        E (V.starProjection (E.symm v)) := by
      simpa only [hV] using hVp
    have hWp' : (groundSpaceES A (r + m + ℓ)).starProjection v =
        E (W.starProjection (E.symm v)) := by
      simpa only [hW] using hWp
    rw [hVp', hWp', map_sub]
    have hUpV := Submodule.starProjection_map_apply E U
      (E (V.starProjection (E.symm v)))
    have hUpV' : (reassocTailBoundaryMapES A r m ℓ).range.starProjection
        (E (V.starProjection (E.symm v))) =
      E (U.starProjection (E.symm (E (V.starProjection (E.symm v))))) := by
      simpa only [hU] using hUpV
    rw [hUpV', E.symm_apply_apply]
    rfl
  rw [← hconj]
  let Y := E.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (X.comp E.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  change ‖X‖ = ‖Y‖
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Y)
    intro v
    calc
      ‖X v‖ = ‖Y (E v)‖ := by simp [Y]
      _ ≤ ‖Y‖ * ‖E v‖ :=
        ContinuousLinearMap.le_of_opNorm_le Y le_rfl (E v)
      _ = ‖Y‖ * ‖v‖ := by rw [E.norm_map]
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg X)
    intro v
    calc
      ‖Y v‖ = ‖X (E.symm v)‖ := by simp [Y, E.norm_map]
      _ ≤ ‖X‖ * ‖E.symm v‖ :=
        ContinuousLinearMap.le_of_opNorm_le X le_rfl (E.symm v)
      _ = ‖X‖ * ‖v‖ := by rw [E.symm.norm_map]

/-- Fixed-length FNW Lemma 6.2 in whole-increment coordinates. The positivity
hypotheses on the interaction and spectator lengths retain the source statement;
the Hilbert-space estimate also holds at the zero endpoints. The right-hand side
displays the separate linear and quadratic source terms. -/
theorem wholeIncrement_groundProjection_defect_le_fnw [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    (hρfix : Kraus.transferMap A ρ = ρ) {L m : ℕ}
    (hInj : Kraus.IsNBlkInjective A L) (_hL : 0 < L) (hLm : L ≤ m)
    (r ℓ : ℕ) (_hr : 0 < r) (_hℓ : 0 < ℓ) :
    ‖(reassocTailBoundaryMapES A r m ℓ).range.starProjection ∘L
          (leftBoundaryMapES A (r + m) ℓ).range.starProjection -
        (groundSpaceES A (r + m + ℓ)).starProjection‖ ≤
      fnwMixingQuantity ρ hρ A htr m /
          fnwLowerBoundaryConstant ρ hρ A m +
        fnwMixingQuantity ρ hρ A htr m ^ 2 /
          fnwLowerBoundaryConstant ρ hρ A m := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  have hminus := fnwLowerBoundaryConstant_pos_of_isNBlkInjective_of_le
    ρ hρ A hρfix hInj hLm
  rw [← norm_fnwOverlapRange_projector_defect_eq_wholeIncrement ρ hρ A ℓ m r]
  exact norm_fnwOverlapRange_projector_defect_le
    ρ hρ htr A hA hρfix ℓ m r hminus

/-- The factored coefficient in FNW 1992, Lemma 6.2. -/
theorem wholeIncrement_groundProjection_defect_le_fnw_factored [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    (hρfix : Kraus.transferMap A ρ = ρ) {L m : ℕ}
    (hInj : Kraus.IsNBlkInjective A L) (hL : 0 < L) (hLm : L ≤ m)
    (r ℓ : ℕ) (hr : 0 < r) (hℓ : 0 < ℓ) :
    ‖(reassocTailBoundaryMapES A r m ℓ).range.starProjection ∘L
          (leftBoundaryMapES A (r + m) ℓ).range.starProjection -
        (groundSpaceES A (r + m + ℓ)).starProjection‖ ≤
      fnwMixingQuantity ρ hρ A htr m *
          (1 + fnwMixingQuantity ρ hρ A htr m) /
        fnwLowerBoundaryConstant ρ hρ A m := by
  rw [show fnwMixingQuantity ρ hρ A htr m *
      (1 + fnwMixingQuantity ρ hρ A htr m) /
        fnwLowerBoundaryConstant ρ hρ A m =
      fnwMixingQuantity ρ hρ A htr m /
          fnwLowerBoundaryConstant ρ hρ A m +
        fnwMixingQuantity ρ hρ A htr m ^ 2 /
          fnwLowerBoundaryConstant ρ hρ A m by ring]
  exact wholeIncrement_groundProjection_defect_le_fnw
    ρ hρ htr A hA hρfix hInj hL hLm r ℓ hr hℓ

/-- A primitive MPS admits a positive interaction length after which the
fixed-length FNW Lemma 6.2 estimate holds for every positive middle and
spectator length. -/
theorem IsPrimitiveMPS.exists_wholeIncrement_groundProjection_defect_le_fnw
    [NeZero D] {ρ : Mat} {A : MPSTensor d D} (hP : IsPrimitiveMPS A ρ)
    (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1) :
    ∃ L : ℕ, 0 < L ∧ ∀ m : ℕ, L ≤ m → ∀ r ℓ : ℕ,
      0 < r → 0 < ℓ →
      ‖(reassocTailBoundaryMapES A r m ℓ).range.starProjection ∘L
            (leftBoundaryMapES A (r + m) ℓ).range.starProjection -
          (groundSpaceES A (r + m + ℓ)).starProjection‖ ≤
        fnwMixingQuantity ρ hρ A htr m /
            fnwLowerBoundaryConstant ρ hρ A m +
          fnwMixingQuantity ρ hρ A htr m ^ 2 /
            fnwLowerBoundaryConstant ρ hρ A m := by
  obtain ⟨L, hL, hInj⟩ := isNormal_of_isPrimitiveMPS_with_posDef hP hρ
  refine ⟨L, hL, fun m hLm r ℓ hr hℓ ↦ ?_⟩
  exact wholeIncrement_groundProjection_defect_le_fnw
    ρ hρ htr A hP.norm hP.fixedPoint_is_fixed hInj hL hLm r ℓ hr hℓ

end

end MPSTensor
