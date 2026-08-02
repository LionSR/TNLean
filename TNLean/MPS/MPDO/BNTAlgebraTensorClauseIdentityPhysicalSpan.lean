/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTAlgebraTensorClauseCorner

/-!
# Identity-dressed physical-letter span for exact two-site sectors

The gauge-dressed physical corner of an exact matched two-site sector gives
two oblique physical maps.  In one orientation their compression is the raw
algebra-side representative; in the opposite orientation it is the
Gram-dressed representative.  The first orientation expresses every
identity-dressed horizontal slice as a linear combination of physical letters
of the two-site blocking.

The two physical maps need not coincide.  Consequently this construction is
not a positive physical corner and does not identify the raw and Gram-dressed
reflected marked chains.

## Main results

* `TwoSiteExactSectorGauge.exists_blockTwo_identity_oblique_compression`
  constructs both orientations of the oblique two-site compression.
* `TwoSiteExactSectorGauge.exists_identity_physical_letter_coefficients`
  constructs the identity-dressed physical-letter coefficients.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition 4.13, Figures 7--8, lines 1909--1919, and Appendix C.4,
  lines 2048--2057
-/

open scoped Matrix ComplexOrder

noncomputable section

namespace MPOTensor

variable {d D : ℕ}

namespace BNTAlgebraTensorClause.TwoSiteExactSectorGauge

variable {M : MPOTensor d D} {H : BNTAlgebraTensorClause M}

/-- The gauge-dressed physical corner of a matched two-site sector determines
two oblique maps.  If `V` is the isometric corner, `X` is the exact sector
gauge, and

`L = V * (X⁻¹)ᴴ`, `R = V * X`,

then the `L,R` compression is the raw representative, while the reversed
`R,L` compression is its Gram dressing.

The maps `L` and `R` need not coincide.  Thus the conclusion is not a positive
physical corner and supplies no common reflected target for the two marked
chains.

Source comparison: arXiv:1606.00608, Proposition 4.13, Figures 7--8 and
lines 1909--1919, applied in Appendix C.4, lines 2048--2057. -/
theorem exists_blockTwo_identity_oblique_compression
    (S : TwoSiteExactSectorGauge H) (γ : Fin H.labelCount) :
    ∃ (V : Matrix (Fin (d * d))
        (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ) (c : ℂ)
      (L R : Matrix (Fin (d * d))
        (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ),
      Vᴴ * V = 1 ∧ (0 : ℂ) < c ∧
        L = V *
          ((↑((S.gauge γ)⁻¹) : Matrix
            (Fin (S.decomposition.bondDim (S.relabel γ)))
            (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ))ᴴ ∧
        R = V * (S.gauge γ : Matrix
          (Fin (S.decomposition.bondDim (S.relabel γ)))
          (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ) ∧
        (∀ v : Fin (D * D),
          Lᴴ * verticalTensor (blockTwo M) v * R =
            c • (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
              (H.tensor γ)) v) ∧
        (∀ v : Fin (D * D),
          Rᴴ * verticalTensor (blockTwo M) v * L =
            c • gramDressing (S.gauge γ)
              (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
                (H.tensor γ)) v) := by
  obtain ⟨V, c, hV, hc, hcorner⟩ := S.exists_blockTwo_gauge_sector_corner γ
  let L := V *
    ((↑((S.gauge γ)⁻¹) : Matrix
      (Fin (S.decomposition.bondDim (S.relabel γ)))
      (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ))ᴴ
  let R := V * (S.gauge γ : Matrix
    (Fin (S.decomposition.bondDim (S.relabel γ)))
    (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)
  refine ⟨V, c, L, R, hV, hc, rfl, rfl, ?_, ?_⟩
  · intro v
    dsimp only [L, R]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    calc
      (↑((S.gauge γ)⁻¹) : Matrix
            (Fin (S.decomposition.bondDim (S.relabel γ)))
            (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ) *
          (Vᴴ * (verticalTensor (blockTwo M) v *
            (V * (S.gauge γ : Matrix
              (Fin (S.decomposition.bondDim (S.relabel γ)))
              (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)))) =
        (↑((S.gauge γ)⁻¹) : Matrix
            (Fin (S.decomposition.bondDim (S.relabel γ)))
            (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ) *
          (Vᴴ * verticalTensor (blockTwo M) v * V) *
            (S.gauge γ : Matrix
              (Fin (S.decomposition.bondDim (S.relabel γ)))
              (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ) := by
        simp only [Matrix.mul_assoc]
      _ = (↑((S.gauge γ)⁻¹) : Matrix
            (Fin (S.decomposition.bondDim (S.relabel γ)))
            (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ) *
          (c • ((S.gauge γ : Matrix
              (Fin (S.decomposition.bondDim (S.relabel γ)))
              (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ) *
            (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
              (H.tensor γ)) v *
            (↑((S.gauge γ)⁻¹) : Matrix
              (Fin (S.decomposition.bondDim (S.relabel γ)))
              (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ))) *
          (S.gauge γ : Matrix
            (Fin (S.decomposition.bondDim (S.relabel γ)))
            (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ) := by
        rw [hcorner v]
      _ = c • (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
          (H.tensor γ)) v := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc]
        rw [← Units.val_mul]
        simp
  · intro v
    dsimp only [L, R]
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    calc
      (S.gauge γ : Matrix
            (Fin (S.decomposition.bondDim (S.relabel γ)))
            (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)ᴴ *
          (Vᴴ * (verticalTensor (blockTwo M) v *
            (V * (↑((S.gauge γ)⁻¹) : Matrix
              (Fin (S.decomposition.bondDim (S.relabel γ)))
              (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)ᴴ))) =
        (S.gauge γ : Matrix
            (Fin (S.decomposition.bondDim (S.relabel γ)))
            (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)ᴴ *
          (Vᴴ * verticalTensor (blockTwo M) v * V) *
            (↑((S.gauge γ)⁻¹) : Matrix
              (Fin (S.decomposition.bondDim (S.relabel γ)))
              (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)ᴴ := by
        simp only [Matrix.mul_assoc]
      _ = (S.gauge γ : Matrix
            (Fin (S.decomposition.bondDim (S.relabel γ)))
            (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)ᴴ *
          (c • ((S.gauge γ : Matrix
              (Fin (S.decomposition.bondDim (S.relabel γ)))
              (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ) *
            (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
              (H.tensor γ)) v *
            (↑((S.gauge γ)⁻¹) : Matrix
              (Fin (S.decomposition.bondDim (S.relabel γ)))
              (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ))) *
          (↑((S.gauge γ)⁻¹) : Matrix
            (Fin (S.decomposition.bondDim (S.relabel γ)))
            (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)ᴴ := by
        rw [hcorner v]
      _ = c • gramDressing (S.gauge γ)
          (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
            (H.tensor γ)) v := by
        symm
        dsimp only [gramDressing]
        rw [Matrix.coe_units_inv, Matrix.mul_inv_rev,
          Matrix.conjTranspose_nonsing_inv]
        simp only [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul]

/-- Every exact matched two-site sector has coefficients whose physical-letter
linear combinations are the horizontal slices of the identity-dressed raw
representative.

This is only the physical-letter-span part of the comparison.  It gives no
positive corner and no equality with the common reflected target required to
identify the raw and Gram-dressed representatives.

Source comparison: arXiv:1606.00608, Proposition 4.13, Figures 7--8 and
lines 1909--1919, applied in Appendix C.4, lines 2048--2057. -/
theorem exists_identity_physical_letter_coefficients
    (S : TwoSiteExactSectorGauge H) (γ : Fin H.labelCount) :
    ∃ fId : Fin (S.decomposition.bondDim (S.relabel γ) *
          S.decomposition.bondDim (S.relabel γ)) →
        Fin ((d * d) * (d * d)) → ℂ,
      ∀ u,
        MPSTensor.linearMarkedTensor fId (blockTwo M).toMPSTensor u =
          horizontalSlice
            (gramDressing
              (1 : GL (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)
              (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
                (H.tensor γ))) u.divNat u.modNat := by
  obtain ⟨V, c, L, R, _hV, hc, _hL, _hR, hcompression, _hreverse⟩ :=
    S.exists_blockTwo_identity_oblique_compression γ
  refine ⟨twoSidedCompressionCoefficients L R c, ?_⟩
  intro u
  have hPhysical := linearMarkedTensor_twoSidedCompressionCoefficients
    (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ)) (H.tensor γ))
    L R c (ne_of_gt hc) hcompression u
  have hOne : gramDressing
      (1 : GL (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)
      (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
        (H.tensor γ)) =
      cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
        (H.tensor γ) := by
    funext v
    simp only [gramDressing, Units.val_one, Matrix.conjTranspose_one,
      Matrix.one_mul, inv_one, Matrix.mul_one]
  rw [hOne]
  exact hPhysical

end BNTAlgebraTensorClause.TwoSiteExactSectorGauge

end MPOTensor
