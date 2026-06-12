import TNLean.PEPS.TorusWitnessTransport

/-!
# The translated coefficient-identity witness on the torus

The torus assembly consumes an `EdgeCoeffIdentityWitness` at every edge of each
orientation class.  This file produces such a witness at a translate `Edge.map (translate a b) f.1`
of a reference boundary edge `f`, against the *transported* reference gauge.

The region is the image `Region.map (translate a b) R` of the reference region `R`; both the
second tensor's region block and its host block are blocked-tensor injective there, by transport
of the reference injectivities for the translation-invariant second tensor.  The reference
coefficient identity transports to the image region realized by the transported reference gauge
(`regionInsertedCoeff_translate_coeffIdentity_conj`), giving the witness's reference field.  The
per-edge gauge's own identity on the image region is supplied as the hypothesis `hidX`; an
arbitrary region/complement physical configuration is preimaged through the configuration
transport equivalences (`regionPhysicalConfigMapEquiv`, `regionPhysicalConfigCongr`) before the
transported identities apply, the cast bookkeeping that aligns the image-region configurations
with the translated ones.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1572 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

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
      IsRegionBoundaryEdge (G := torusGraph width height) R f})
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
  hRB := by
    have h := (regionBlockedTensorInjective_transport B (translate a b) R).mpr hRB
    rwa [hB a b] at h
  hCB := by
    rw [show Finset.univ \ Region.map (translate a b) R =
        Region.map (translate a b) (Finset.univ \ R) from (Region_map_compl (translate a b) R).symm]
    have h := (regionBlockedTensorInjective_transport B (translate a b) (Finset.univ \ R)).mpr hCB
    rwa [hB a b] at h
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
