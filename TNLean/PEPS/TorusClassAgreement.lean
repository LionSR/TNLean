import TNLean.PEPS.TorusTINormalGauge

/-!
# Class agreement from per-edge transfer-map covariance on the torus

The translation-invariant gauge reduction needs the **class-agreement input** of the capstone
`isTorusOrientationUniformGaugeFamilyModScalar_of_translationInvariant`: that on each orientation
class every per-edge gauge agrees, up to a nonzero scalar, with the reference orientation matrix
transported to that edge.

This file derives that agreement from per-edge transfer-map covariance.  The per-edge gauge `X e`
realizes a forward per-edge transfer (conjugation) on the bond matrices of `A.bondDim e`.  Two
invertible matrices realizing the same conjugation differ by a nonzero scalar
(`edgeGauge_unique_scalar`, the center of the full matrix algebra is the scalars).  So once the
conjugation of `X e` coincides with the conjugation of the transported reference matrix --- the
covariance that the region-insertion transfer map satisfies under translation
(`TNLean/PEPS/RegionTransferCovariance.lean`) --- the per-edge agreement holds with the scalar
`edgeGauge_unique_scalar` supplies.  Gathering the two orientation classes gives the
orientation-uniform-up-to-scalar family the capstone consumes.

The covariance hypothesis `hcovH`/`hcovV` is the conjugation form of the transfer-map covariance:
the conjugation by `X e` on every bond matrix equals the conjugation by the transported reference
matrix.  It is what the determinacy of the region-insertion transfer map
(`regionInsertedCoeff_transferMap_unique`) and the translation covariance of the coefficient
identity (`regionInsertedCoeff_translate_coeffIdentity`) establish for the per-edge gauges of a
translation-invariant pair; supplying it here as a hypothesis isolates the algebraic
class-agreement assembly from that geometric covariance.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- **Per-edge class agreement from conjugation covariance.**

If, on every horizontal (vertical) edge `e`, the conjugation by the per-edge gauge `X e` on every
bond matrix coincides with the conjugation by the transported reference matrix
`glReindex (huni.horizontal he).symm Xh` (`glReindex (huni.vertical he).symm Xv`), then the whole
gauge family `X` is orientation uniform up to per-edge scalars.

The conjugation coincidence forces, edge by edge, the per-edge gauge to be the transported
reference matrix up to a nonzero scalar (`edgeGauge_unique_scalar`, the quotient lies in the
center of the full matrix algebra, hence is a scalar).  These per-edge scalars are exactly the
residual freedom recorded in the orientation-uniform-up-to-scalar family.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isTorusOrientationUniformGaugeFamilyModScalar_of_conjCovariance
    {bondDim : Edge (torusGraph width height) → ℕ} {Dh Dv : ℕ}
    (huni : TorusUniformBondDim bondDim Dh Dv)
    (X : (e : Edge (torusGraph width height)) → GL (Fin (bondDim e)) ℂ)
    (Xh : GL (Fin Dh) ℂ) (Xv : GL (Fin Dv) ℂ)
    (hcovH : ∀ (e : Edge (torusGraph width height)) (he : IsHorizontalTorusEdge e)
      (N : Matrix (Fin (bondDim e)) (Fin (bondDim e)) ℂ),
      (X e : Matrix (Fin (bondDim e)) (Fin (bondDim e)) ℂ) * N *
          (↑(X e)⁻¹ : Matrix (Fin (bondDim e)) (Fin (bondDim e)) ℂ) =
        (glReindex (huni.horizontal he).symm Xh :
            Matrix (Fin (bondDim e)) (Fin (bondDim e)) ℂ) * N *
          (↑(glReindex (huni.horizontal he).symm Xh)⁻¹ :
            Matrix (Fin (bondDim e)) (Fin (bondDim e)) ℂ))
    (hcovV : ∀ (e : Edge (torusGraph width height)) (he : IsVerticalTorusEdge e)
      (N : Matrix (Fin (bondDim e)) (Fin (bondDim e)) ℂ),
      (X e : Matrix (Fin (bondDim e)) (Fin (bondDim e)) ℂ) * N *
          (↑(X e)⁻¹ : Matrix (Fin (bondDim e)) (Fin (bondDim e)) ℂ) =
        (glReindex (huni.vertical he).symm Xv :
            Matrix (Fin (bondDim e)) (Fin (bondDim e)) ℂ) * N *
          (↑(glReindex (huni.vertical he).symm Xv)⁻¹ :
            Matrix (Fin (bondDim e)) (Fin (bondDim e)) ℂ)) :
    IsTorusOrientationUniformGaugeFamilyModScalar huni X := by
  classical
  -- On each orientation class, the conjugation coincidence gives the per-edge scalar.
  have hH : ∀ (e : Edge (torusGraph width height)) (he : IsHorizontalTorusEdge e),
      ∃ c : ℂˣ, (X e : Matrix (Fin (bondDim e)) (Fin (bondDim e)) ℂ) =
        (c : ℂ) • (glReindex (huni.horizontal he).symm Xh :
          Matrix (Fin (bondDim e)) (Fin (bondDim e)) ℂ) := by
    intro e he
    -- Apply `gl_conj_unique_scalar` to `X e` and the transported reference, with the roles of
    -- `Z`/`Z'` arranged so the scalar relates `X e` to the reference.
    obtain ⟨c, hc⟩ := gl_conj_unique_scalar (glReindex (huni.horizontal he).symm Xh) (X e)
      (fun N => (hcovH e he N).symm)
    exact ⟨c, hc⟩
  have hV : ∀ (e : Edge (torusGraph width height)) (he : IsVerticalTorusEdge e),
      ∃ c : ℂˣ, (X e : Matrix (Fin (bondDim e)) (Fin (bondDim e)) ℂ) =
        (c : ℂ) • (glReindex (huni.vertical he).symm Xv :
          Matrix (Fin (bondDim e)) (Fin (bondDim e)) ℂ) := by
    intro e he
    obtain ⟨c, hc⟩ := gl_conj_unique_scalar (glReindex (huni.vertical he).symm Xv) (X e)
      (fun N => (hcovV e he N).symm)
    exact ⟨c, hc⟩
  -- Choose the per-edge scalars and assemble through the class-agreement selection.
  refine isTorusOrientationUniformGaugeFamilyModScalar_of_classAgreement huni X Xh Xv
    (fun e => if he : IsHorizontalTorusEdge e then (hH e he).choose else 1)
    (fun e => if he : IsVerticalTorusEdge e then (hV e he).choose else 1)
    (fun e he => ?_) (fun e he => ?_)
  · simp only [dif_pos he]; exact (hH e he).choose_spec
  · simp only [dif_pos he]; exact (hV e he).choose_spec

end PEPS
end TNLean
