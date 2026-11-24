/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.FundamentalTheorem.Torus.TorusRectangleGauge
import TNLean.PEPS.FundamentalTheorem.Torus.TorusEdgeGaugeCovariance

/-!
# Transport of a conjugation coefficient identity along a torus translation

The torus construction requires, at every edge of an orientation class, an
`EdgeCoeffIdentityWitness` whose reference identity states that the *transported* reference gauge
realizes the region-insertion coefficient identity at that edge.  This file supplies the
matrix-algebra transport that produces that reference identity from the one at the class's
reference edge: a coefficient identity realized at a reference boundary edge `f` by conjugation
with `Z` transports, for a translation-invariant pair, to the same identity at the translated
boundary edge realized by conjugation with the transported gauge `glReindex h Z`.

The translation covariance of the bare coefficient identity is
`regionInsertedCoeff_translate_coeffIdentity`; specializing its abstract transfer map to a
conjugation `M ↦ Z · (reindex M) · Z⁻¹` and using the reindexing algebra equivalence
identifies the transported transfer with conjugation by the reindexed gauge.  No new geometry
enters: the reindexing along the bond-dimension equalities aligns the translated reference
identity with the required conjugation form.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)

## The translated coefficient-identity witness on the torus

The torus construction requires an `EdgeCoeffIdentityWitness` at every edge of each
orientation class.  This file produces such a witness at a translate `Edge.map (translate a b) f.1`
of a reference boundary edge `f`, against the *transported* reference gauge.

The region is the image `Region.map (translate a b) R` of the reference region `R`; both the
second tensor's region block and its host block are blocked-tensor injective there, by transport
of the reference injectivities for the translation-invariant second tensor.  The reference
coefficient identity transports to the image region realized by the transported reference gauge
(`regionInsertedCoeff_translate_coeffIdentity_conj`), giving the witness's reference identity.  The
per-edge gauge's own identity on the image region is supplied as the hypothesis `hidX`; an
arbitrary region/complement physical configuration is preimaged through the configuration
transport equivalences (`regionPhysicalConfigMapEquiv`, `regionPhysicalConfigCongr`) before the
transported identities apply, which aligns the image-region configurations
with the translated ones.

### References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1572 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

section

open ManyBody (Edge)

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- **Transport of a conjugation coefficient identity along a torus translation.**

For translation-invariant tensors `A`, `B` on the torus with matched bond dimensions on the
reference boundary edge `f` of `R`, a coefficient identity realized by conjugation with an
invertible gauge `Z` over `B`'s bond on `f` transports to the translated boundary edge
`boundaryEdgeMap (translate a b) R f` of the translated region `Region.map (translate a b) R`,
realized by conjugation with the transported gauge `glReindex hbond Z` over `B`'s bond on the
translated edge.

The translation covariance `regionInsertedCoeff_translate_coeffIdentity` carries the bare
identity with its transfer map; specializing the transfer to the conjugation
`M ↦ Z · (reindex M) · Z⁻¹`
and using multiplicativity of the matrix reindexing equivalence identifies the transported map
with conjugation by `glReindex hbond Z`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_translate_coeffIdentity_conj
    {A B : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (hB : IsTorusTranslationInvariant B)
    (a : ZMod width) (b : ZMod height) (R : Finset (TorusVertex width height))
    (f : {f : Edge (torusGraph width height) //
      ManyBody.IsRegionBoundaryEdge (G := torusGraph width height) R f})
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
  rw [map_mul, map_mul, glReindex_coe,
    show (glReindex hbB.symm Z)⁻¹ = glReindex hbB.symm Z⁻¹ from
      (map_inv (glReindex hbB.symm) Z).symm,
    glReindex_coe]
  -- The two inner reindexings of `M'` agree by proof irrelevance of the bond-dimension equalities:
  -- triple reindexing and the single reindexing across `hE'` both reindex `M'` by the composite
  -- finite-index equivalence.
  congr 1

end PEPS
end TNLean

end

section

open ManyBody (Edge)

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- Every region/complement physical-configuration pair on the image region of a translation is the
transport of a unique pair on the original region: the configuration transport equivalences are
bijections, so any image configuration is the image of its preimage. -/
theorem exists_regionPhysicalConfig_translate_preimage
    (a : ZMod width) (b : ZMod height) (R : Finset (TorusVertex width height))
    (σ' : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (Region.map (translate a b) R))
    (τ' : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (Finset.univ \ Region.map (translate a b) R)) :
    ∃ (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) R)
      (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) (Finset.univ \ R)),
      σ' = regionPhysicalConfigMap (translate a b) R σ ∧
      τ' = regionPhysicalConfigCongr (d := d) (Region_map_compl (translate a b) R)
        (regionPhysicalConfigMap (translate a b) (Finset.univ \ R) τ) := by
  refine ⟨(regionPhysicalConfigMapEquiv (d := d) (translate a b) R).symm σ',
    (regionPhysicalConfigMapEquiv (d := d) (translate a b) (Finset.univ \ R)).symm
      ((regionPhysicalConfigCongr (d := d) (Region_map_compl (translate a b) R)).symm τ'), ?_, ?_⟩
  · exact ((regionPhysicalConfigMapEquiv (d := d) (translate a b) R).apply_symm_apply σ').symm
  · rw [show regionPhysicalConfigMap (translate a b) (Finset.univ \ R)
        ((regionPhysicalConfigMapEquiv (d := d) (translate a b) (Finset.univ \ R)).symm
          ((regionPhysicalConfigCongr (d := d) (Region_map_compl (translate a b) R)).symm τ')) =
        (regionPhysicalConfigMapEquiv (d := d) (translate a b) (Finset.univ \ R))
          ((regionPhysicalConfigMapEquiv (d := d) (translate a b) (Finset.univ \ R)).symm
            ((regionPhysicalConfigCongr (d := d) (Region_map_compl (translate a b) R)).symm τ'))
        from rfl,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **The translated coefficient-identity witness on the torus.**

For translation-invariant tensors `A`, `B` with matched bond dimensions on the reference boundary
edge `f` of `R`, positive bonds, and `B`'s reference region and host blocks blocked-tensor
injective, suppose the reference coefficient identity at `f` is realized by conjugation with a gauge
`Z`, and a per-edge gauge `X` realizes the coefficient identity over the image region
`Region.map (translate a b) R` at the translated boundary edge.  Then the translated edge carries an
`EdgeCoeffIdentityWitness` whose per-edge gauge is `X` and whose reference gauge is the transported
gauge `glReindex _ Z`.

The reference identity transports by `regionInsertedCoeff_translate_coeffIdentity_conj`; an
arbitrary image-region configuration pair is preimaged through the configuration transport
equivalences before the transported identity applies.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 377--457 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def edgeCoeffIdentityWitness_translate
    {A B : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (hB : IsTorusTranslationInvariant B)
    (a : ZMod width) (b : ZMod height) (R : Finset (TorusVertex width height))
    (f : {f : Edge (torusGraph width height) //
      ManyBody.IsRegionBoundaryEdge (G := torusGraph width height) R f})
    (hE : A.bondDim f.1 = B.bondDim f.1)
    (Z : GL (Fin (B.bondDim f.1)) ℂ)
    (hposB : ∀ g : Edge (torusGraph width height), 0 < B.bondDim g)
    (hRB : RegionBlockedTensorInjective (G := torusGraph width height) B R)
    (hCB : RegionBlockedTensorInjective (G := torusGraph width height) B (Finset.univ \ R))
    (hid : ∀ (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
      (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) R)
      (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) (Finset.univ \ R)),
      regionInsertedCoeff (G := torusGraph width height) A R f M σ τ =
        regionInsertedCoeff (G := torusGraph width height) B R f
          ((Z : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE) M *
            (↑Z⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)) σ τ)
    (X : GL (Fin (B.bondDim (boundaryEdgeMap (translate a b) R f).1)) ℂ)
    (hEX : A.bondDim (boundaryEdgeMap (translate a b) R f).1 =
      B.bondDim (boundaryEdgeMap (translate a b) R f).1)
    (hidX : ∀ (M : Matrix (Fin (A.bondDim (boundaryEdgeMap (translate a b) R f).1))
        (Fin (A.bondDim (boundaryEdgeMap (translate a b) R f).1)) ℂ)
      (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
        (Region.map (translate a b) R))
      (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
        (Finset.univ \ Region.map (translate a b) R)),
      regionInsertedCoeff (G := torusGraph width height) A (Region.map (translate a b) R)
          (boundaryEdgeMap (translate a b) R f) M σ τ =
        regionInsertedCoeff (G := torusGraph width height) B (Region.map (translate a b) R)
          (boundaryEdgeMap (translate a b) R f)
          ((X : Matrix (Fin (B.bondDim (boundaryEdgeMap (translate a b) R f).1))
                (Fin (B.bondDim (boundaryEdgeMap (translate a b) R f).1)) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr hEX) M *
            (↑X⁻¹ : Matrix (Fin (B.bondDim (boundaryEdgeMap (translate a b) R f).1))
                (Fin (B.bondDim (boundaryEdgeMap (translate a b) R f).1)) ℂ)) σ τ) :
    EdgeCoeffIdentityWitness A B (boundaryEdgeMap (translate a b) R f).1 X
      (glReindex (bondDim_boundaryEdgeMap_translate hB a b R f).symm Z) hEX where
  region := Region.map (translate a b) R
  isBoundary := (boundaryEdgeMap (translate a b) R f).2
  hRB := regionBlockedTensorInjective_translate hB a b R hRB
  hCB := by
    rw [show Finset.univ \ Region.map (translate a b) R =
        Region.map (translate a b) (Finset.univ \ R) from (Region_map_compl (translate a b) R).symm]
    exact regionBlockedTensorInjective_translate hB a b _ hCB
  hposB := hposB
  hidZ := hidX
  hidZref := by
    intro M σ' τ'
    obtain ⟨σ, τ, rfl, rfl⟩ :=
      exists_regionPhysicalConfig_translate_preimage (d := d) a b R σ' τ'
    exact regionInsertedCoeff_translate_coeffIdentity_conj hA hB a b R f hE Z hid hEX
      (glReindex (bondDim_boundaryEdgeMap_translate hB a b R f).symm Z) rfl M σ τ

end PEPS
end TNLean

end
