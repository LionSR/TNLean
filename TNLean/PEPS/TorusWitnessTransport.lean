import TNLean.PEPS.TorusRectangleGauge
import TNLean.PEPS.TorusConjCovarianceFamily

/-!
# Transport of a conjugation coefficient identity along a torus translation

The torus assembly consumes, at every edge of an orientation class, an
`EdgeCoeffIdentityWitness` whose reference field demands that the *transported* reference gauge
realize the region-insertion coefficient identity at that edge.  This file supplies the
matrix-algebra transport that produces that reference identity from the one at the class's
reference edge: a coefficient identity realized at a reference boundary edge `f` by conjugation
with `Z` transports, for a translation-invariant pair, to the same identity at the translated
boundary edge realized by conjugation with the transported gauge `glReindex h Z`.

The translation covariance of the bare coefficient identity is
`regionInsertedCoeff_translate_coeffIdentity`; specializing its abstract transfer map to a
conjugation `M ↦ Z · (reindex M) · Z⁻¹` and rewriting the nested bond-dimension reindexings with
`reindexAlgEquiv_gaugeConj` identifies the transported transfer with conjugation by the
reindexed gauge.  No new geometry enters: this is the cast bookkeeping that aligns the
translated reference identity with the conjugation form the witness interface expects.

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

/-- The bond dimension of a translation-invariant tensor at the translated boundary edge of a
region equals its bond dimension at the reference boundary edge, packaged for the inserted matrix
at the translated edge. -/
theorem bondDim_boundaryEdgeMap_translate_eq
    {A : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A)
    (a : ZMod width) (b : ZMod height) (R : Finset (TorusVertex width height))
    (f : {f : Edge (torusGraph width height) //
      IsRegionBoundaryEdge (G := torusGraph width height) R f}) :
    A.bondDim (boundaryEdgeMap (translate a b) R f).1 = A.bondDim f.1 :=
  bondDim_boundaryEdgeMap_translate hA a b R f

/-- **Transport of a conjugation coefficient identity along a torus translation.**

For translation-invariant tensors `A`, `B` on the torus with matched bond dimensions on the
reference boundary edge `f` of `R`, a coefficient identity realized by conjugation with an
invertible gauge `Z` over `B`'s bond on `f` transports to the translated boundary edge
`boundaryEdgeMap (translate a b) R f` of the translated region `Region.map (translate a b) R`,
realized by conjugation with the transported gauge `glReindex hbond Z` over `B`'s bond on the
translated edge.

The translation covariance `regionInsertedCoeff_translate_coeffIdentity` carries the bare identity
with its transfer map; specializing the transfer to the conjugation `M ↦ Z · (reindex M) · Z⁻¹`
and collapsing the nested reindexings with `reindexAlgEquiv_gaugeConj` and
`reindexAlgEquiv_finCongr_symm_round` identifies the transported map with conjugation by
`glReindex hbond Z`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_translate_coeffIdentity_conj
    {A B : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (hB : IsTorusTranslationInvariant B)
    (a : ZMod width) (b : ZMod height) (R : Finset (TorusVertex width height))
    (f : {f : Edge (torusGraph width height) //
      IsRegionBoundaryEdge (G := torusGraph width height) R f})
    (hE : A.bondDim f.1 = B.bondDim f.1)
    (Z : GL (Fin (B.bondDim f.1)) ℂ)
    (hid : ∀ (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
      (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) R)
      (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) (Finset.univ \ R)),
      regionInsertedCoeff (G := torusGraph width height) A R f M σ τ =
        regionInsertedCoeff (G := torusGraph width height) B R f
          ((Z : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE) M *
            (↑Z⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)) σ τ)
    (hE' : A.bondDim (boundaryEdgeMap (translate a b) R f).1 =
        B.bondDim (boundaryEdgeMap (translate a b) R f).1)
    (Z' : GL (Fin (B.bondDim (boundaryEdgeMap (translate a b) R f).1)) ℂ)
    (hZ' : Z' = glReindex (bondDim_boundaryEdgeMap_translate hB a b R f).symm Z)
    (M' : Matrix (Fin (A.bondDim (boundaryEdgeMap (translate a b) R f).1))
      (Fin (A.bondDim (boundaryEdgeMap (translate a b) R f).1)) ℂ)
    (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) R)
    (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := torusGraph width height) A
        (Region.map (translate a b) R) (boundaryEdgeMap (translate a b) R f) M'
        (regionPhysicalConfigMap (translate a b) R σ)
        (regionPhysicalConfigCongr (d := d) (Region_map_compl (translate a b) R)
          (regionPhysicalConfigMap (translate a b) (Finset.univ \ R) τ)) =
      regionInsertedCoeff (G := torusGraph width height) B
        (Region.map (translate a b) R) (boundaryEdgeMap (translate a b) R f)
        ((Z' : Matrix (Fin (B.bondDim (boundaryEdgeMap (translate a b) R f).1))
              (Fin (B.bondDim (boundaryEdgeMap (translate a b) R f).1)) ℂ) *
            Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE') M' *
          (↑Z'⁻¹ : Matrix (Fin (B.bondDim (boundaryEdgeMap (translate a b) R f).1))
              (Fin (B.bondDim (boundaryEdgeMap (translate a b) R f).1)) ℂ))
        (regionPhysicalConfigMap (translate a b) R σ)
        (regionPhysicalConfigCongr (d := d) (Region_map_compl (translate a b) R)
          (regionPhysicalConfigMap (translate a b) (Finset.univ \ R) τ)) := by
  -- The conjugation transfer map at the reference edge.
  set g : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ →
      Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ :=
    fun M => (Z : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE) M *
      (↑Z⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) with hg
  -- Substitute the transported gauge.
  subst hZ'
  -- Transport the bare coefficient identity with this transfer map.
  rw [regionInsertedCoeff_translate_coeffIdentity hA hB a b R f g hid M' σ τ]
  -- It remains to align the transported transfer with conjugation by `glReindex hbB.symm Z`.
  congr 1
  -- Abbreviate the two bond-dimension reindexings.
  set hbA := bondDim_boundaryEdgeMap_translate hA a b R f with hbAdef
  set hbB := bondDim_boundaryEdgeMap_translate hB a b R f with hbBdef
  -- Expand `g`, then pull the conjugation through the bond-dimension reindexing.
  simp only [hg]
  rw [reindexAlgEquiv_gaugeConj hbB.symm Z]
  -- The two inner reindexings of `M'` agree by proof irrelevance of the bond casts: the nested
  -- triple reindexing and the single reindexing across `hE'` both reindex `M'` by the composite
  -- finite-index cast, which is the same cast up to proof irrelevance.
  congr 1

end PEPS
end TNLean
