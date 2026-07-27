/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.MPDO.SectorCompressionSeparation
import TNLean.MPS.MPDO.VerticalSpectral

/-!
# Grouping vertical normal sectors into BNT representatives

This file performs the gauge-phase grouping step in the proof of the vertical
canonical form for matrix product density operators.  Starting from the
spectrally normalized physical corners, it chooses one normal tensor from each
matrix-product-vector phase class.  Every original corner is expressed using
an invertible conjugation and a scalar of unit modulus, with the scalar of the
chosen representative equal to one.  The physical isometries are retained
unchanged, so all reducing identities and the literal reconstruction of every
vertical letter survive the regrouping.

This is the phase-class decomposition and positivity argument of
arXiv:1606.00608, lines 1898--1902.  It combines the BNT characterization at
lines 1135--1148 with the preceding isometry-preserving vertical sector
theorem.  For every grouped sector it constructs the physical selector, proves
the corresponding loop identity, finds a nonzero finite-chain compression,
and deduces that the grouped coefficient is positive.  The positive-diagonal
isometry asserted at lines 1895--1896 and the gauge normalization and final
coisometry argument at lines 1903--1921 are not included.

The grouping assumes normalized BNT-refined horizontal form, which is stronger
than the literal CPSV canonical form.

## Main statement

* `IsHorizontalCF.exists_verticalBNTGrouping_with_isometry`: the normalized
  vertical corners grouped into BNT representatives, with the physical
  isometries and literal reconstruction retained.

## References

* Cirac--Pérez-García--Schuch--Verstraete, arXiv:1606.00608, Proposition
  `prop:vertical`, lines 1873--1921.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- A nonzero vertical corner of a tensor in normalized BNT-refined horizontal
form has a nonzero first-site sector compression at some chain length.

This is the separation assertion used in the proof of Proposition 4.13 of
arXiv:1606.00608, line 1898.  It follows from Lemma L for the BNT-refined
horizontal form, Appendix C.3, lines 1835--1858.

**Scope restriction (BNT-refined horizontal form):** `IsHorizontalCF` is
stronger than the literal CPSV canonical form; see
`docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`. -/
theorem IsHorizontalCF.exists_sectorCompression_ne_zero_of_corner
    (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M)
    (P : Matrix (Fin d) (Fin d) ℂ)
    (hcorner : ∃ v, P * verticalTensor M v * P ≠ 0) :
    ∃ N, sectorCompression M P N ≠ 0 := by
  exact exists_sectorCompression_ne_zero_of_corner_of_insertedTensor_eq M
    (hHorizontal.insertedTensor_eq_of_firstSiteActionAgree M) P hcorner

/-- A nonzero normal representative gives a nonzero physical range corner
through an exact gauge-corner identity.

Source context: arXiv:1606.00608, Proposition 4.13, line 1898, where
$P_{\alpha,k}$ selects a nonzero normal sector of the vertical direct sum.
The present lemma isolates the algebraic nonvanishing implication from the
exact gauge-corner identity. -/
theorem exists_rangeProjection_corner_ne_zero
    {n : ℕ} [NeZero n] (M : MPOTensor d D) (A : MPSTensor (D * D) n)
    (hA : A.IsNormalTensor) (V : Matrix (Fin d) (Fin n) ℂ)
    (hV : Vᴴ * V = 1) (X : GL (Fin n) ℂ) (ω : ℂ) (hω : ω ≠ 0)
    (hcorner : ∀ v,
      ω • ((X : Matrix (Fin n) (Fin n) ℂ) * A v *
        (↑(X⁻¹) : Matrix (Fin n) (Fin n) ℂ)) =
          Vᴴ * verticalTensor M v * V) :
    ∃ v, (V * Vᴴ) * verticalTensor M v * (V * Vᴴ) ≠ 0 := by
  obtain ⟨v, hv⟩ := hA.exists_apply_ne_zero
  refine ⟨v, ?_⟩
  have hconj : (X : Matrix (Fin n) (Fin n) ℂ) * A v *
      (↑(X⁻¹) : Matrix (Fin n) (Fin n) ℂ) ≠ 0 := by
    intro hzero
    apply hv
    have hcancel := congrArg
      (fun Z : Matrix (Fin n) (Fin n) ℂ =>
        (↑(X⁻¹) : Matrix (Fin n) (Fin n) ℂ) * Z *
          (X : Matrix (Fin n) (Fin n) ℂ)) hzero
    simpa [Matrix.mul_assoc] using hcancel
  have hsmall : Vᴴ * verticalTensor M v * V ≠ 0 := by
    rw [← hcorner v]
    exact smul_ne_zero hω hconj
  intro hzero
  apply hsmall
  have hcancel := congrArg
    (fun Z : Matrix (Fin d) (Fin d) ℂ => Vᴴ * Z * V) hzero
  rw [show Vᴴ * ((V * Vᴴ) * verticalTensor M v * (V * Vᴴ)) * V =
      Vᴴ * verticalTensor M v * V by
    simp only [← Matrix.mul_assoc, hV, Matrix.one_mul]
    rw [Matrix.mul_assoc (Vᴴ * verticalTensor M v * V) Vᴴ V,
      hV, Matrix.mul_one]] at hcancel
  simpa using hcancel

/-- Group normalized vertical corners by gauge-phase class from a normal-corner
decomposition and finite-chain separation of nonzero physical corners.

For each class `j` and copy `q`, the original normalized corner is

`blocks (enum j q) = ζ j q · X j q · blocks (repr j) · (X j q)⁻¹`.

The scalar `ζ j q` has unit norm, and it is one for the chosen representative.
The gauge `X j q` is also the identity for the chosen representative.
Consequently the coefficient `μ (enum j q) * ζ j q` in the literal vertical
decomposition is positive.  The representatives form a basis of normal tensors
for the corresponding weighted block tensor and are pairwise gauge-phase
distinct.  Each physical range projector satisfies the representative-loop
identity and has a nonzero finite-chain compression.

Source: the phase-class decomposition and positivity argument in
arXiv:1606.00608, lines 1898--1902, using the BNT characterization at lines
1135--1148 and the preceding isometry-preserving vertical sector theorem.  The
positive-diagonal isometry asserted at lines 1895--1896 and the subsequent
gauge normalization and coisometry argument at lines 1903--1921 are not
included.

The hypotheses isolate exactly the two inputs used by the common argument:
an isometry-preserving normal vertical decomposition and finite-chain
separation for every nonzero physical corner. -/
theorem exists_verticalBNTGrouping_with_isometry_of_decomposition
    (M : MPOTensor d D) (hM : IsMPDO M)
    (hDecomp :
      ∃ (r : ℕ) (dim : Fin r → ℕ) (μ : Fin r → ℂ)
        (blocks : (k : Fin r) → MPSTensor (D * D) (dim k))
        (V : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ),
        (∀ k, 0 < dim k) ∧
        (∀ k, (0 : ℂ) < μ k) ∧
        (∀ k, MPSTensor.IsNormalTensor (blocks k)) ∧
        (∀ k, (V k)ᴴ * V k = 1) ∧
        (∀ k l, k ≠ l → (V k)ᴴ * V l = 0) ∧
        (∀ k v, verticalTensor M v * V k = V k * (μ k • blocks k v)) ∧
        (∀ k v, (V k)ᴴ * verticalTensor M v = (μ k • blocks k v) * (V k)ᴴ) ∧
        (∀ k v, μ k • blocks k v = (V k)ᴴ * verticalTensor M v * V k) ∧
        ∀ v, verticalTensor M v =
          ∑ k, V k * (μ k • blocks k v) * (V k)ᴴ)
    (hSeparate : ∀ P : Matrix (Fin d) (Fin d) ℂ,
      (∃ v, P * verticalTensor M v * P ≠ 0) →
        ∃ N, sectorCompression M P N ≠ 0) :
    ∃ (r : ℕ) (dim : Fin r → ℕ) (μ : Fin r → ℂ)
      (blocks : (k : Fin r) → MPSTensor (D * D) (dim k))
      (V : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ),
      (∀ k, 0 < dim k) ∧
      (∀ k, (0 : ℂ) < μ k) ∧
      (∀ k, MPSTensor.IsNormalTensor (blocks k)) ∧
      (∀ k, (V k)ᴴ * V k = 1) ∧
      (∀ k l, k ≠ l → (V k)ᴴ * V l = 0) ∧
      (∀ k v, verticalTensor M v * V k = V k * (μ k • blocks k v)) ∧
      (∀ k v, (V k)ᴴ * verticalTensor M v = (μ k • blocks k v) * (V k)ᴴ) ∧
      (∀ k v, μ k • blocks k v = (V k)ᴴ * verticalTensor M v * V k) ∧
      (∀ v, verticalTensor M v = ∑ k, V k * (μ k • blocks k v) * (V k)ᴴ) ∧
      let classes := MPSTensor.mpvPhaseClassData blocks
      ∃ (hdim : ∀ j q,
          dim (classes.repr j) = dim (classes.enum j q))
        (X : (j : Fin classes.g) → (q : Fin (classes.copies j)) →
          GL (Fin (dim (classes.enum j q))) ℂ)
        (ζ : (j : Fin classes.g) → Fin (classes.copies j) → ℂ),
        (∀ j q, ‖ζ j q‖ = 1) ∧
        (∀ j q, ζ j q ≠ 0) ∧
        (∀ j, X j ⟨0, classes.copies_pos j⟩ = 1) ∧
        (∀ j, ζ j ⟨0, classes.copies_pos j⟩ = 1) ∧
        (∀ j q v,
          blocks (classes.enum j q) v =
            ζ j q •
              ((X j q : Matrix (Fin (dim (classes.enum j q)))
                  (Fin (dim (classes.enum j q))) ℂ) *
                (cast (congr_arg (MPSTensor (D * D)) (hdim j q))
                  (blocks (classes.repr j))) v *
                (↑((X j q)⁻¹) : Matrix (Fin (dim (classes.enum j q)))
                  (Fin (dim (classes.enum j q))) ℂ))) ∧
        MPSTensor.IsCPSVBasisOfNormalTensors
          (MPSTensor.toTensorFromBlocks (d := D * D) (μ := μ) blocks)
          (fun j => ⟨dim (classes.repr j), blocks (classes.repr j)⟩) ∧
        MPSTensor.BlocksNotGaugePhaseEquiv
          (d := D * D) (fun j => blocks (classes.repr j)) ∧
        (∀ j q, μ (classes.enum j q) * ζ j q ≠ 0) ∧
        (∀ j q, SectorProjectorData M
          (V (classes.enum j q) * (V (classes.enum j q))ᴴ)
          (μ (classes.enum j q) * ζ j q)
          (representativeLoop (blocks (classes.repr j)))) ∧
        (∀ j q, ∃ N, sectorCompression M
          (V (classes.enum j q) * (V (classes.enum j q))ᴴ) N ≠ 0) ∧
        (∀ j q, (0 : ℂ) < μ (classes.enum j q) * ζ j q) ∧
        (∀ j q, (V (classes.enum j q))ᴴ * V (classes.enum j q) = 1) ∧
        (∀ j q l p, classes.enum j q ≠ classes.enum l p →
          (V (classes.enum j q))ᴴ * V (classes.enum l p) = 0) ∧
        (∀ j q v,
          verticalTensor M v * V (classes.enum j q) =
            V (classes.enum j q) *
              ((μ (classes.enum j q) * ζ j q) •
                ((X j q : Matrix (Fin (dim (classes.enum j q)))
                    (Fin (dim (classes.enum j q))) ℂ) *
                  (cast (congr_arg (MPSTensor (D * D)) (hdim j q))
                    (blocks (classes.repr j))) v *
                  (↑((X j q)⁻¹) : Matrix (Fin (dim (classes.enum j q)))
                    (Fin (dim (classes.enum j q))) ℂ)))) ∧
        (∀ j q v,
          (V (classes.enum j q))ᴴ * verticalTensor M v =
            ((μ (classes.enum j q) * ζ j q) •
                ((X j q : Matrix (Fin (dim (classes.enum j q)))
                    (Fin (dim (classes.enum j q))) ℂ) *
                  (cast (congr_arg (MPSTensor (D * D)) (hdim j q))
                    (blocks (classes.repr j))) v *
                  (↑((X j q)⁻¹) : Matrix (Fin (dim (classes.enum j q)))
                    (Fin (dim (classes.enum j q))) ℂ))) *
              (V (classes.enum j q))ᴴ) ∧
        (∀ j q v,
          (μ (classes.enum j q) * ζ j q) •
              ((X j q : Matrix (Fin (dim (classes.enum j q)))
                  (Fin (dim (classes.enum j q))) ℂ) *
                (cast (congr_arg (MPSTensor (D * D)) (hdim j q))
                  (blocks (classes.repr j))) v *
                (↑((X j q)⁻¹) : Matrix (Fin (dim (classes.enum j q)))
                  (Fin (dim (classes.enum j q))) ℂ)) =
            (V (classes.enum j q))ᴴ * verticalTensor M v * V (classes.enum j q)) ∧
        ∀ v, verticalTensor M v =
          ∑ j : Fin classes.g, ∑ q : Fin (classes.copies j),
            V (classes.enum j q) *
              ((μ (classes.enum j q) * ζ j q) •
                ((X j q : Matrix (Fin (dim (classes.enum j q)))
                    (Fin (dim (classes.enum j q))) ℂ) *
                  (cast (congr_arg (MPSTensor (D * D)) (hdim j q))
                    (blocks (classes.repr j))) v *
                  (↑((X j q)⁻¹) : Matrix (Fin (dim (classes.enum j q)))
                    (Fin (dim (classes.enum j q))) ℂ))) *
              (V (classes.enum j q))ᴴ := by
  classical
  obtain ⟨r, dim, μ, blocks, V, hdimPos, hμPos, hNormal, hIso, hOrth,
    hInt, hIntStar, hCorner, hReconstruct⟩ :=
    hDecomp
  let classes := MPSTensor.mpvPhaseClassData blocks
  haveI : ∀ k, NeZero (dim k) := fun k => ⟨(hdimPos k).ne'⟩
  have hClassGauge : ∀ j q,
      ∃ (hdim : dim (classes.repr j) = dim (classes.enum j q))
        (X : GL (Fin (dim (classes.enum j q))) ℂ) (ζ : ℂ),
        ‖ζ‖ = 1 ∧ ζ ≠ 0 ∧
        (∀ v, blocks (classes.enum j q) v =
          ζ • ((X : Matrix (Fin (dim (classes.enum j q)))
              (Fin (dim (classes.enum j q))) ℂ) *
            (cast (congr_arg (MPSTensor (D * D)) hdim)
              (blocks (classes.repr j))) v *
            (↑(X⁻¹) : Matrix (Fin (dim (classes.enum j q)))
              (Fin (dim (classes.enum j q))) ℂ))) ∧
        (q = ⟨0, classes.copies_pos j⟩ → X = 1 ∧ ζ = 1) := by
    intro j q
    by_cases hq : q = ⟨0, classes.copies_pos j⟩
    · have hEnum : classes.enum j q = classes.repr j := by
        rw [hq]
        exact MPSTensor.mpvPhaseClassData_enum_zero_eq_repr blocks j
      have hdim : dim (classes.repr j) = dim (classes.enum j q) :=
        congrArg dim hEnum.symm
      refine ⟨hdim, 1, 1, norm_one, one_ne_zero, ?_, fun _ => ⟨rfl, rfl⟩⟩
      have hcast : cast (congr_arg (MPSTensor (D * D)) hdim)
          (blocks (classes.repr j)) = blocks (classes.enum j q) := by
        rw [cast_eq_iff_heq]
        exact hEnum.symm.rec HEq.rfl
      intro v
      calc
        blocks (classes.enum j q) v =
            (cast (congr_arg (MPSTensor (D * D)) hdim)
              (blocks (classes.repr j))) v := congrFun hcast.symm v
        _ = (1 : ℂ) •
            ((1 : Matrix (Fin (dim (classes.enum j q)))
                (Fin (dim (classes.enum j q))) ℂ) *
              (cast (congr_arg (MPSTensor (D * D)) hdim)
                (blocks (classes.repr j))) v *
              (1 : Matrix (Fin (dim (classes.enum j q)))
                (Fin (dim (classes.enum j q))) ℂ)) := by
          rw [Matrix.one_mul, Matrix.mul_one, one_smul]
    · obtain ⟨hdim, hGaugePhase⟩ :=
        MPSTensor.MPVBlockPhaseEquiv.dim_eq_and_gaugePhaseEquiv_of_isNormalTensor
          (hNormal (classes.repr j)) (hNormal (classes.enum j q))
          (classes.enum_phase j q)
      obtain ⟨X, ζ, hζNe, hGauge⟩ := hGaugePhase
      refine ⟨hdim, X, ζ, ?_, hζNe, hGauge, fun h => (hq h).elim⟩
      exact MPSTensor.norm_eq_one_of_gaugePhase_cast_of_isNormalTensor
        (hNormal (classes.repr j)) (hNormal (classes.enum j q)) hdim hGauge
  choose hdim X ζ hζNorm hζNe hGauge hDist using hClassGauge
  have hXDist : ∀ j, X j ⟨0, classes.copies_pos j⟩ = 1 := by
    intro j
    exact (hDist j ⟨0, classes.copies_pos j⟩ rfl).1
  have hζDist' : ∀ j, ζ j ⟨0, classes.copies_pos j⟩ = 1 := by
    intro j
    exact (hDist j ⟨0, classes.copies_pos j⟩ rfl).2
  have hCornerEq : ∀ j q v,
      μ (classes.enum j q) • blocks (classes.enum j q) v =
        (μ (classes.enum j q) * ζ j q) •
          ((X j q : Matrix _ _ ℂ) *
            (cast (congr_arg (MPSTensor (D * D)) (hdim j q))
              (blocks (classes.repr j))) v *
            (((X j q)⁻¹ : GL (Fin (dim (classes.enum j q))) ℂ) :
              Matrix _ _ ℂ)) := by
    intro j q v
    rw [hGauge j q v, smul_smul]
  have hGroupedCorner : ∀ j q v,
      (μ (classes.enum j q) * ζ j q) •
          ((X j q : Matrix (Fin (dim (classes.enum j q)))
              (Fin (dim (classes.enum j q))) ℂ) *
            (cast (congr_arg (MPSTensor (D * D)) (hdim j q))
              (blocks (classes.repr j))) v *
            (↑((X j q)⁻¹) : Matrix (Fin (dim (classes.enum j q)))
              (Fin (dim (classes.enum j q))) ℂ)) =
        (V (classes.enum j q))ᴴ * verticalTensor M v * V (classes.enum j q) := by
    intro j q v
    rw [← hCornerEq j q v]
    exact hCorner (classes.enum j q) v
  have hSector : ∀ j q, SectorProjectorData M
      (V (classes.enum j q) * (V (classes.enum j q))ᴴ)
      (μ (classes.enum j q) * ζ j q)
      (representativeLoop (blocks (classes.repr j))) := by
    intro j q
    have hs := sectorProjectorData_of_gauge_corner M
      (cast (congr_arg (MPSTensor (D * D)) (hdim j q))
        (blocks (classes.repr j)))
      (V (classes.enum j q)) (hIso (classes.enum j q)) (X j q)
      (μ (classes.enum j q) * ζ j q) (hGroupedCorner j q)
    rw [representativeLoop_cast (hdim j q)] at hs
    exact hs
  have hCompression : ∀ j q, ∃ N, sectorCompression M
      (V (classes.enum j q) * (V (classes.enum j q))ᴴ) N ≠ 0 := by
    intro j q
    have hNormalCast : MPSTensor.IsNormalTensor
        (cast (congr_arg (MPSTensor (D * D)) (hdim j q))
          (blocks (classes.repr j))) :=
      (MPSTensor.isNormalTensor_cast_iff (hdim j q)
        (blocks (classes.repr j))).2 (hNormal (classes.repr j))
    have hRange := exists_rangeProjection_corner_ne_zero M
      (cast (congr_arg (MPSTensor (D * D)) (hdim j q))
        (blocks (classes.repr j))) hNormalCast
      (V (classes.enum j q)) (hIso (classes.enum j q)) (X j q)
      (μ (classes.enum j q) * ζ j q)
      (mul_ne_zero (hμPos (classes.enum j q)).ne' (hζNe j q))
      (hGroupedCorner j q)
    exact hSeparate _ hRange
  have hCoeffPos : ∀ j q, (0 : ℂ) < μ (classes.enum j q) * ζ j q := by
    intro j q
    let q₀ : Fin (classes.copies j) := ⟨0, classes.copies_pos j⟩
    have hRefPos : (0 : ℂ) < μ (classes.enum j q₀) * ζ j q₀ := by
      rw [hζDist' j]
      simp only [mul_one, q₀]
      exact hμPos (classes.repr j)
    obtain ⟨N, hne⟩ := hCompression j q
    exact sector_weight_pos hM (hSector j q₀) hRefPos (hSector j q) N hne
  have hBNT : MPSTensor.IsCPSVBasisOfNormalTensors
      (MPSTensor.toTensorFromBlocks (d := D * D) (μ := μ) blocks)
      (fun j => ⟨dim (classes.repr j), blocks (classes.repr j)⟩) := by
    refine ⟨fun j => hNormal (classes.repr j), ?_, ?_⟩
    · intro N _hN
      let phase : (j : Fin classes.g) → Fin (classes.copies j) → ℂ :=
        fun j q => (classes.enum_phase j q).choose
      refine ⟨fun j => ∑ q : Fin (classes.copies j),
        (μ (classes.enum j q) * phase j q) ^ N, ?_⟩
      intro w
      calc
        MPSTensor.mpv
            (MPSTensor.toTensorFromBlocks (d := D * D) (μ := μ) blocks) w =
            ∑ k : Fin r, (μ k) ^ N * MPSTensor.mpv (blocks k) w := by
              simpa [smul_eq_mul] using
                (MPSTensor.mpv_toTensorFromBlocks_eq_sum
                  (d := D * D) μ blocks w)
        _ = ∑ j : Fin classes.g, ∑ q : Fin (classes.copies j),
            (μ (classes.enum j q)) ^ N *
              MPSTensor.mpv (blocks (classes.enum j q)) w :=
              (classes.regroup fun k => (μ k) ^ N * MPSTensor.mpv (blocks k) w).symm
        _ = ∑ j : Fin classes.g, ∑ q : Fin (classes.copies j),
            (μ (classes.enum j q) * phase j q) ^ N *
              MPSTensor.mpv (blocks (classes.repr j)) w := by
              refine Finset.sum_congr rfl fun j _ =>
                Finset.sum_congr rfl fun q _ => ?_
              rw [(classes.enum_phase j q).choose_spec.2 N _hN w, mul_pow]
              ring
        _ = ∑ j : Fin classes.g,
            (∑ q : Fin (classes.copies j),
              (μ (classes.enum j q) * phase j q) ^ N) *
                MPSTensor.mpv (blocks (classes.repr j)) w := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.sum_mul]
    · exact
        MPSTensor.exists_eventually_linearIndependent_of_normalTensor_blocks_not_gaugePhaseEquiv
          (fun j => blocks (classes.repr j))
          (fun j => hNormal (classes.repr j)) classes.blocks_not_equiv
  refine ⟨r, dim, μ, blocks, V, hdimPos, hμPos, hNormal, hIso, hOrth,
    hInt, hIntStar, hCorner, hReconstruct, hdim, X, ζ, hζNorm, hζNe,
    hXDist, hζDist', hGauge, hBNT, classes.blocks_not_equiv, ?_, hSector, hCompression,
    hCoeffPos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j q
    exact mul_ne_zero (hμPos (classes.enum j q)).ne' (hζNe j q)
  · intro j q
    exact hIso (classes.enum j q)
  · intro j q l p hne
    exact hOrth (classes.enum j q) (classes.enum l p) hne
  · intro j q v
    rw [← hCornerEq j q v]
    exact hInt (classes.enum j q) v
  · intro j q v
    rw [← hCornerEq j q v]
    exact hIntStar (classes.enum j q) v
  · intro j q v
    rw [← hCornerEq j q v]
    exact hCorner (classes.enum j q) v
  · intro v
    calc
      verticalTensor M v =
          ∑ k : Fin r, V k * (μ k • blocks k v) * (V k)ᴴ := hReconstruct v
      _ = ∑ j : Fin classes.g, ∑ q : Fin (classes.copies j),
          V (classes.enum j q) *
            (μ (classes.enum j q) • blocks (classes.enum j q) v) *
              (V (classes.enum j q))ᴴ := by
            exact (classes.regroup_matrix fun k =>
              V k * (μ k • blocks k v) * (V k)ᴴ).symm
      _ = ∑ j : Fin classes.g, ∑ q : Fin (classes.copies j),
          V (classes.enum j q) *
            ((μ (classes.enum j q) * ζ j q) •
              ((X j q : Matrix _ _ ℂ) *
                (cast (congr_arg (MPSTensor (D * D)) (hdim j q))
                  (blocks (classes.repr j))) v *
                (((X j q)⁻¹ : GL (Fin (dim (classes.enum j q))) ℂ) :
                  Matrix _ _ ℂ))) *
            (V (classes.enum j q))ᴴ := by
              refine Finset.sum_congr rfl fun j _ =>
                Finset.sum_congr rfl fun q _ => ?_
              rw [hCornerEq j q v]


/-- Group the normalized vertical corners of an MPDO in normalized BNT-refined
horizontal form by their gauge-phase classes while retaining the physical
reducing isometries. This is the phase-class decomposition and positivity
argument of arXiv:1606.00608, Proposition 4.13, lines 1898--1902. -/
theorem IsHorizontalCF.exists_verticalBNTGrouping_with_isometry
    (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    ∃ (r : ℕ) (dim : Fin r → ℕ) (μ : Fin r → ℂ)
      (blocks : (k : Fin r) → MPSTensor (D * D) (dim k))
      (V : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ),
      (∀ k, 0 < dim k) ∧
      (∀ k, (0 : ℂ) < μ k) ∧
      (∀ k, MPSTensor.IsNormalTensor (blocks k)) ∧
      (∀ k, (V k)ᴴ * V k = 1) ∧
      (∀ k l, k ≠ l → (V k)ᴴ * V l = 0) ∧
      (∀ k v, verticalTensor M v * V k = V k * (μ k • blocks k v)) ∧
      (∀ k v, (V k)ᴴ * verticalTensor M v = (μ k • blocks k v) * (V k)ᴴ) ∧
      (∀ k v, μ k • blocks k v = (V k)ᴴ * verticalTensor M v * V k) ∧
      (∀ v, verticalTensor M v = ∑ k, V k * (μ k • blocks k v) * (V k)ᴴ) ∧
      let classes := MPSTensor.mpvPhaseClassData blocks
      ∃ (hdim : ∀ j q,
          dim (classes.repr j) = dim (classes.enum j q))
        (X : (j : Fin classes.g) → (q : Fin (classes.copies j)) →
          GL (Fin (dim (classes.enum j q))) ℂ)
        (ζ : (j : Fin classes.g) → Fin (classes.copies j) → ℂ),
        (∀ j q, ‖ζ j q‖ = 1) ∧
        (∀ j q, ζ j q ≠ 0) ∧
        (∀ j, X j ⟨0, classes.copies_pos j⟩ = 1) ∧
        (∀ j, ζ j ⟨0, classes.copies_pos j⟩ = 1) ∧
        (∀ j q v,
          blocks (classes.enum j q) v =
            ζ j q •
              ((X j q : Matrix (Fin (dim (classes.enum j q)))
                  (Fin (dim (classes.enum j q))) ℂ) *
                (cast (congr_arg (MPSTensor (D * D)) (hdim j q))
                  (blocks (classes.repr j))) v *
                (↑((X j q)⁻¹) : Matrix (Fin (dim (classes.enum j q)))
                  (Fin (dim (classes.enum j q))) ℂ))) ∧
        MPSTensor.IsCPSVBasisOfNormalTensors
          (MPSTensor.toTensorFromBlocks (d := D * D) (μ := μ) blocks)
          (fun j => ⟨dim (classes.repr j), blocks (classes.repr j)⟩) ∧
        MPSTensor.BlocksNotGaugePhaseEquiv
          (d := D * D) (fun j => blocks (classes.repr j)) ∧
        (∀ j q, μ (classes.enum j q) * ζ j q ≠ 0) ∧
        (∀ j q, SectorProjectorData M
          (V (classes.enum j q) * (V (classes.enum j q))ᴴ)
          (μ (classes.enum j q) * ζ j q)
          (representativeLoop (blocks (classes.repr j)))) ∧
        (∀ j q, ∃ N, sectorCompression M
          (V (classes.enum j q) * (V (classes.enum j q))ᴴ) N ≠ 0) ∧
        (∀ j q, (0 : ℂ) < μ (classes.enum j q) * ζ j q) ∧
        (∀ j q, (V (classes.enum j q))ᴴ * V (classes.enum j q) = 1) ∧
        (∀ j q l p, classes.enum j q ≠ classes.enum l p →
          (V (classes.enum j q))ᴴ * V (classes.enum l p) = 0) ∧
        (∀ j q v,
          verticalTensor M v * V (classes.enum j q) =
            V (classes.enum j q) *
              ((μ (classes.enum j q) * ζ j q) •
                ((X j q : Matrix (Fin (dim (classes.enum j q)))
                    (Fin (dim (classes.enum j q))) ℂ) *
                  (cast (congr_arg (MPSTensor (D * D)) (hdim j q))
                    (blocks (classes.repr j))) v *
                  (↑((X j q)⁻¹) : Matrix (Fin (dim (classes.enum j q)))
                    (Fin (dim (classes.enum j q))) ℂ)))) ∧
        (∀ j q v,
          (V (classes.enum j q))ᴴ * verticalTensor M v =
            ((μ (classes.enum j q) * ζ j q) •
                ((X j q : Matrix (Fin (dim (classes.enum j q)))
                    (Fin (dim (classes.enum j q))) ℂ) *
                  (cast (congr_arg (MPSTensor (D * D)) (hdim j q))
                    (blocks (classes.repr j))) v *
                  (↑((X j q)⁻¹) : Matrix (Fin (dim (classes.enum j q)))
                    (Fin (dim (classes.enum j q))) ℂ))) *
              (V (classes.enum j q))ᴴ) ∧
        (∀ j q v,
          (μ (classes.enum j q) * ζ j q) •
              ((X j q : Matrix (Fin (dim (classes.enum j q)))
                  (Fin (dim (classes.enum j q))) ℂ) *
                (cast (congr_arg (MPSTensor (D * D)) (hdim j q))
                  (blocks (classes.repr j))) v *
                (↑((X j q)⁻¹) : Matrix (Fin (dim (classes.enum j q)))
                  (Fin (dim (classes.enum j q))) ℂ)) =
            (V (classes.enum j q))ᴴ * verticalTensor M v * V (classes.enum j q)) ∧
        ∀ v, verticalTensor M v =
          ∑ j : Fin classes.g, ∑ q : Fin (classes.copies j),
            V (classes.enum j q) *
              ((μ (classes.enum j q) * ζ j q) •
                ((X j q : Matrix (Fin (dim (classes.enum j q)))
                    (Fin (dim (classes.enum j q))) ℂ) *
                  (cast (congr_arg (MPSTensor (D * D)) (hdim j q))
                    (blocks (classes.repr j))) v *
                  (↑((X j q)⁻¹) : Matrix (Fin (dim (classes.enum j q)))
                    (Fin (dim (classes.enum j q))) ℂ))) *
              (V (classes.enum j q))ᴴ := by
  exact exists_verticalBNTGrouping_with_isometry_of_decomposition M hM
    (hHorizontal.exists_normal_verticalBlockDecomp_with_isometry M hM)
    (fun P hRange =>
      hHorizontal.exists_sectorCompression_ne_zero_of_corner M P hRange)

end MPOTensor
