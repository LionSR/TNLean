/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.AmbientSectorMaps.BNTAlgebraTensorClauseSpectrum
import TNLean.MPS.MPDO.Vertical.FigureEightPairwise
import TNLean.MPS.MPDO.Fusion.VerticalCopyBlocks

/-!
# Physical corners of the exact two-site sector gauge

The distinguished copies in the one-site and two-site vertical decompositions
give isometric physical inclusions for the raw and exact gauge-dressed
algebra-side sectors.  The Gram-dressed marked chain of the latter therefore
has the reflected form appearing on the right-hand side of Figures 7--8.

These corner identities alone do not prove the common-target Gram identity
required for the unitary gauge conclusion.  The mixed one-site/two-site
marked comparison in `BNTAlgebraTensorClauseReflectedTarget` supplies the
additional argument.

## Main results

* `TwoSiteExactSectorGauge.exists_oneSite_raw_sector_corner`
* `TwoSiteExactSectorGauge.exists_blockTwo_gauge_sector_corner`
* `TwoSiteExactSectorGauge.markedChainCoefficient_gauge_eq_reflectedAdjoint`

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition 4.13, Figures 7--8, lines 1909--1919, and Appendix C.4,
  lines 2048--2057

## Identity-dressed physical-letter span for exact two-site sectors

The gauge-dressed physical corner of an exact matched two-site sector gives
two oblique physical maps.  In one orientation their compression is the raw
algebra-side representative; in the opposite orientation it is the
Gram-dressed representative.  The first orientation expresses every
identity-dressed horizontal slice as a linear combination of physical letters
of the two-site blocking.

The two physical maps need not coincide.  Consequently this construction is
not a positive physical corner and does not identify the raw and Gram-dressed
reflected marked chains.

### Main results

* `TwoSiteExactSectorGauge.exists_blockTwo_identity_oblique_compression`
  constructs both orientations of the oblique two-site compression.
* `TwoSiteExactSectorGauge.exists_identity_physical_letter_coefficients`
  constructs the identity-dressed physical-letter coefficients.

### References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition 4.13, Figures 7--8, lines 1909--1919, and Appendix C.4,
  lines 2048--2057
-/

section

open scoped Matrix ComplexOrder

noncomputable section

namespace MPOTensor

namespace BNTAlgebraTensorClause.TwoSiteExactSectorGauge

variable {d D : ℕ} {M : MPOTensor d D} {H : BNTAlgebraTensorClause M}

/-- Every algebra-side sector has an isometric one-site physical corner whose
compression is a positive scalar multiple of the raw representative,
transported to the bond dimension of its matched two-site sector.

The construction uses the distinguished first copy in the one-site vertical
decomposition and does not assume any normalization of the matched two-site
gauge.

Source: arXiv:1606.00608, Proposition 4.13, statement lines 943--951 and proof
lines 1898--1921, and Appendix C.4, lines 2048--2057. -/
theorem exists_oneSite_raw_sector_corner
    (S : TwoSiteExactSectorGauge H) (γ : Fin H.labelCount) :
    ∃ (W : Matrix (Fin d)
        (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ) (c : ℂ),
      Wᴴ * W = 1 ∧ (0 : ℂ) < c ∧
        ∀ v : Fin (D * D),
          Wᴴ * verticalTensor M v * W =
            c • (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
              (H.tensor γ)) v := by
  classical
  let p : (α : Fin H.labelCount) × Fin (H.multiplicity α) :=
    ⟨γ, ⟨0, H.multiplicity_pos γ⟩⟩
  let E := verticalCopyBlockInclusion H.bondDim H.multiplicity p
  let W₀ := H.verticalCoisometryᴴ * E
  let c := H.weight γ ⟨0, H.multiplicity_pos γ⟩
  have hW₀ : W₀ᴴ * W₀ = 1 := by
    calc
      W₀ᴴ * W₀ = Eᴴ * H.verticalCoisometry *
          (H.verticalCoisometryᴴ * E) := by
        simp only [W₀, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = Eᴴ * (H.verticalCoisometry * H.verticalCoisometryᴴ) * E := by
        simp only [Matrix.mul_assoc]
      _ = Eᴴ * E := by rw [H.coisometry, Matrix.mul_one]
      _ = 1 := verticalCopyBlockInclusion_isometry H.bondDim H.multiplicity p
  have hCorner₀ : ∀ v : Fin (D * D),
      W₀ᴴ * verticalTensor M v * W₀ = c • H.tensor γ v := by
    intro v
    calc
      W₀ᴴ * verticalTensor M v * W₀ =
          Eᴴ * (H.verticalCoisometry * verticalTensor M v *
            H.verticalCoisometryᴴ) * E := by
        simp only [W₀, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = Eᴴ * verticalAssembledTensor H.bondDim H.multiplicity
          H.weight H.tensor v * E := by rw [H.forward v]
      _ = c • H.tensor γ v := by
        exact (verticalCopyBlockInclusion_compression H.bondDim H.multiplicity
          H.weight H.tensor p v).symm
  let W : Matrix (Fin d)
      (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ :=
    cast (congrArg (fun n ↦ Matrix (Fin d) (Fin n) ℂ) (S.bondDim_eq γ)) W₀
  refine ⟨W, c, ?_, ?_, ?_⟩
  · have cast_isometry {m n : ℕ} (V : Matrix (Fin d) (Fin m) ℂ)
        (hV : Vᴴ * V = 1) (h : m = n) :
        let V' := cast (congrArg (fun k ↦ Matrix (Fin d) (Fin k) ℂ) h) V
        V'ᴴ * V' = 1 := by
      cases h
      simpa using hV
    exact cast_isometry W₀ hW₀ (S.bondDim_eq γ)
  · exact H.weight_pos γ ⟨0, H.multiplicity_pos γ⟩
  · intro v
    have cast_compression {m n : ℕ} (A : MPSTensor (D * D) m)
        (V : Matrix (Fin d) (Fin m) ℂ)
        (hCorner : ∀ u, Vᴴ * verticalTensor M u * V = c • A u)
        (h : m = n) (u : Fin (D * D)) :
        let A' := cast (congrArg (MPSTensor (D * D)) h) A
        let V' := cast (congrArg (fun k ↦ Matrix (Fin d) (Fin k) ℂ) h) V
        V'ᴴ * verticalTensor M u * V' = c • A' u := by
      cases h
      simpa using hCorner u
    exact cast_compression (H.tensor γ) W₀ hCorner₀ (S.bondDim_eq γ) v

/-- Every matched two-site sector has an isometric physical corner whose
compression is a positive scalar multiple of the exact gauge-dressed
algebra-side representative.

This is the gauge-dressed half of the marked sector comparison in CPSV16,
Proposition 4.13, Figures 7--8, lines 1909--1919, applied to the two-site
decomposition in Appendix C.4, lines 2048--2057.

**Scope restriction (gauge-dressed corner):** This theorem alone does not
construct an identity-dressed corner or prove the common-target Gram identity.
The mixed-prefix comparison that supplies the latter is documented in
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

Source: arXiv:1606.00608, Proposition 4.13, lines 1909--1919, and Appendix C.4,
lines 2048--2057. -/
theorem exists_blockTwo_gauge_sector_corner
    (S : TwoSiteExactSectorGauge H) (γ : Fin H.labelCount) :
    ∃ (V : Matrix (Fin (d * d))
        (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ) (c : ℂ),
      Vᴴ * V = 1 ∧ (0 : ℂ) < c ∧
        ∀ v : Fin (D * D),
          Vᴴ * verticalTensor (blockTwo M) v * V =
            c • ((S.gauge γ : Matrix
                (Fin (S.decomposition.bondDim (S.relabel γ)))
                (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ) *
              (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
                (H.tensor γ)) v *
              (↑((S.gauge γ)⁻¹) : Matrix
                (Fin (S.decomposition.bondDim (S.relabel γ)))
                (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)) := by
  classical
  let V := blockedReferenceInclusion S.decomposition.bondDim
    S.decomposition.multiplicity S.decomposition.multiplicity_pos
    S.decomposition.verticalCoisometry (S.relabel γ)
  let c := S.decomposition.weight (S.relabel γ)
    ⟨0, S.decomposition.multiplicity_pos (S.relabel γ)⟩
  refine ⟨V, c, ?_, ?_, ?_⟩
  · exact blockedReferenceInclusion_isometry S.decomposition.bondDim
      S.decomposition.multiplicity S.decomposition.multiplicity_pos
      S.decomposition.verticalCoisometry S.decomposition.coisometry (S.relabel γ)
  · exact S.decomposition.weight_pos (S.relabel γ)
      ⟨0, S.decomposition.multiplicity_pos (S.relabel γ)⟩
  · intro v
    rw [← S.tensor_eq γ v]
    exact (blockedReference_compression M S.decomposition.bondDim
      S.decomposition.multiplicity S.decomposition.multiplicity_pos
      S.decomposition.weight S.decomposition.tensor
      S.decomposition.verticalCoisometry S.decomposition.coisometry
      S.decomposition.reconstruction (S.relabel γ) v).symm

/-- The marked chain of the exact gauge-dressed algebra-side sector equals
the reflected-adjoint marked chain of the same representative in the adjoint
two-site blocking.

This is the gauge-dressed Figure 7 identity used on one side of Figure 8 in
CPSV16, Proposition 4.13, lines 1909--1919, for the sector matching of
Appendix C.4, lines 2048--2057.

**Scope restriction (gauge-dressed corner):** This theorem alone does not
compare the expression with the identity-dressed algebra-side representative.
The mixed-prefix comparison that proves the common-target Gram identity is
documented in
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

Source: arXiv:1606.00608, Proposition 4.13, lines 1909--1919, and Appendix C.4,
lines 2048--2057. -/
theorem markedChainCoefficient_gauge_eq_reflectedAdjoint
    (S : TwoSiteExactSectorGauge H) (hM : IsMPDO M)
    (γ : Fin H.labelCount) (N : ℕ)
    (r s : Fin (S.decomposition.bondDim (S.relabel γ)))
    (σ τ : Fin N → Fin (d * d)) :
    markedChainCoefficient
        (gramDressing (S.gauge γ)
          (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
            (H.tensor γ)))
        (blockTwo M) r s (List.ofFn σ) (List.ofFn τ) =
      markedChainCoefficient
        (reflectedAdjoint
          (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
            (H.tensor γ)))
        (adjointTensor (blockTwo M)) r s
        (List.ofFn σ).reverse (List.ofFn τ).reverse := by
  obtain ⟨V, c, _, hc, hcorner⟩ := S.exists_blockTwo_gauge_sector_corner γ
  exact hM.blockTwo.markedChainCoefficient_gramDressing_eq_reflectedAdjoint
    (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ)) (H.tensor γ))
    V (S.gauge γ) c hc hcorner N r s σ τ

end BNTAlgebraTensorClause.TwoSiteExactSectorGauge

end MPOTensor
end

end

section

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
end

end
