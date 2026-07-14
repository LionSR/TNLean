/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.MPDO.VerticalSpectral

/-!
# Grouping vertical normal sectors into BNT representatives

This file performs the gauge-phase grouping step in the proof of the vertical
canonical form for matrix product density operators.  Starting from the
spectrally normalized physical corners, it chooses one normal tensor from each
matrix-product-vector phase class.  Every original corner is expressed as a
nonzero complex scalar times an invertible conjugate of its representative.
The physical isometries are retained unchanged, so all reducing identities and
the literal reconstruction of every vertical letter survive the regrouping.

This is the algebraic phase-class decomposition invoked in the first sentence
of arXiv:1606.00608, line 1898.  It combines the BNT characterization at lines
1135--1148 with the preceding isometry-preserving vertical sector theorem.  It
does not prove the positive-diagonal isometry asserted at lines 1895--1896.  No
positivity of the grouped coefficients and no unitarity of the gauges is
asserted here; those are consequences of the subsequent MPDO argument at lines
1898--1921.

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

/-- Group the normalized vertical corners of a horizontally canonical MPDO by
their gauge-phase classes while retaining the physical reducing isometries.

For each class `j` and copy `q`, the original normalized corner is

`blocks (enum j q) = ζ j q · X j q · blocks (repr j) · (X j q)⁻¹`.

Consequently its coefficient in the literal vertical decomposition is the
nonzero complex number `μ (enum j q) * ζ j q`.  The representatives form a
basis of normal tensors for the corresponding weighted block tensor and are
pairwise gauge-phase distinct.

Source: the algebraic phase-class decomposition in the first sentence of
arXiv:1606.00608, line 1898, using the BNT characterization at lines
1135--1148 and the preceding isometry-preserving vertical sector theorem.  The
positive-diagonal isometry asserted at lines 1895--1896 is not included. -/
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
        (∀ j q, ζ j q ≠ 0) ∧
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
    hHorizontal.exists_normal_verticalBlockDecomp_with_isometry M hM
  let classes := MPSTensor.mpvPhaseClassData blocks
  haveI : ∀ k, NeZero (dim k) := fun k => ⟨(hdimPos k).ne'⟩
  have hClassGauge : ∀ j q,
      ∃ hdim : dim (classes.repr j) = dim (classes.enum j q),
        MPSTensor.GaugePhaseEquiv
          (cast (congr_arg (MPSTensor (D * D)) hdim) (blocks (classes.repr j)))
          (blocks (classes.enum j q)) := by
    intro j q
    exact MPSTensor.MPVBlockPhaseEquiv.dim_eq_and_gaugePhaseEquiv_of_isNormalTensor
      (hNormal (classes.repr j)) (hNormal (classes.enum j q))
      (classes.enum_phase j q)
  choose hdim hGaugePhase using hClassGauge
  choose X ζ hζNe hGauge using hGaugePhase
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
  have hBNT : MPSTensor.IsCPSVBasisOfNormalTensors
      (MPSTensor.toTensorFromBlocks (d := D * D) (μ := μ) blocks)
      (fun j => ⟨dim (classes.repr j), blocks (classes.repr j)⟩) := by
    refine ⟨fun j => hNormal (classes.repr j), ?_, ?_⟩
    · intro N
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
              rw [(classes.enum_phase j q).choose_spec.2 N w, mul_pow]
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
    hInt, hIntStar, hCorner, hReconstruct, hdim, X, ζ, hζNe, hGauge, hBNT,
    classes.blocks_not_equiv, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

end MPOTensor
