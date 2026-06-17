import TNLean.PEPS.TorusEdgeGauge
import TNLean.PEPS.RegionTransferCovariance
import TNLean.PEPS.EdgeGaugeFamily

/-!
# Conjugation covariance of the per-edge gauge on the torus

The per-edge gauges produced by the edge blocking are determined, as conjugation maps, by the
coefficient identities they realize.  This file supplies that algebraic determinacy.

Two invertible matrices `Z` and `Z'` on the same boundary edge `f` of a region `R`, each
realizing the region-insertion coefficient identity of `A` through `B` by conjugation
(`regionInsertedCoeff A R f M = regionInsertedCoeff B R f (conj_Z M)`), induce the *same*
conjugation map (`gaugeConj_eq_of_coeffIdentities`): the region-insertion transfer map is
determined by the coefficient identity (`regionInsertedCoeff_transferMap_unique`), and both
conjugations realize it.  Reindexing across an index-size equality commutes with conjugation
(`reindexAlgEquiv_gaugeConj`), the matrix-algebra fact that turns a transported gauge
`glReindex h Z` into the conjugation by the reindexed matrix.

These two facts turn the geometric translation covariance of the coefficient identity
(`regionInsertedCoeff_translate_coeffIdentity`) into the conjugation form consumed by the
witness transport of the translation-covariant absorbed family; the route is recorded in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines
  1407--1572 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

/-! ### Reindexing commutes with conjugation -/

/-- **Reindexing across an index-size equality commutes with conjugation.**

For an invertible matrix `Z : GL (Fin a) ℂ` and the index-size equality `h : a = b`, the
reindexed conjugation `reindex (Z · N · Z⁻¹)` equals the conjugation by the reindexed matrix
`glReindex h Z` applied to the reindexed `N`: `(glReindex h Z) · (reindex N) · (glReindex h Z)⁻¹`.
Reindexing is an algebra equivalence, hence multiplicative and inverse-preserving, so it
distributes over the triple product.

This is the matrix-algebra fact that identifies the transported reference gauge `glReindex h Xh`
with the conjugation by `Xh` reindexed across the bond-dimension equality. -/
theorem reindexAlgEquiv_gaugeConj {a b : ℕ} (h : a = b) (Z : GL (Fin a) ℂ)
    (N : Matrix (Fin a) (Fin a) ℂ) :
    Matrix.reindexAlgEquiv ℂ ℂ (finCongr h)
        ((Z : Matrix (Fin a) (Fin a) ℂ) * N *
          (↑Z⁻¹ : Matrix (Fin a) (Fin a) ℂ)) =
      (↑(glReindex h Z) : Matrix (Fin b) (Fin b) ℂ) *
          Matrix.reindexAlgEquiv ℂ ℂ (finCongr h) N *
        (↑(glReindex h Z)⁻¹ : Matrix (Fin b) (Fin b) ℂ) := by
  rw [map_mul, map_mul, glReindex_coe,
    show (glReindex h Z)⁻¹ = glReindex h Z⁻¹ from (map_inv (glReindex h) Z).symm, glReindex_coe]

/-! ### Conjugation agreement from the coefficient identity -/

section CoeffBridge

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- **Two conjugating gauges realizing the same coefficient identity induce the same map.**

Two invertible matrices `Z₁` and `Z₂` on the boundary edge `f` of a region `R`, both realizing
the region-insertion coefficient identity of `A` through `B` by conjugation
(`regionInsertedCoeff A R f M = regionInsertedCoeff B R f (conj_{Zᵢ} M)` for all configurations),
induce the same conjugation map across the bond-dimension equality: for every bond matrix `M`,
`Z₁ · (reindex M) · Z₁⁻¹ = Z₂ · (reindex M) · Z₂⁻¹`.  The region-insertion transfer map is
determined by its coefficient identity (`regionInsertedCoeff_transferMap_unique`); both
conjugations realize it, so they coincide.

This is the determinacy step that turns the geometric translation covariance of the coefficient
identity into the conjugation form the witness transport consumes.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 377--457 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem gaugeConj_eq_of_coeffIdentities (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    {hE₁ hE₂ : A.bondDim f.1 = B.bondDim f.1}
    (Z₁ Z₂ : GL (Fin (B.bondDim f.1)) ℂ)
    (h₁ : ∀ (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
      (σ : RegionPhysicalConfig (V := V) (d := d) R)
      (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
      regionInsertedCoeff (G := G) A R f M σ τ =
        regionInsertedCoeff (G := G) B R f
          ((Z₁ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE₁) M *
            (↑Z₁⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)) σ τ)
    (h₂ : ∀ (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
      (σ : RegionPhysicalConfig (V := V) (d := d) R)
      (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
      regionInsertedCoeff (G := G) A R f M σ τ =
        regionInsertedCoeff (G := G) B R f
          ((Z₂ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE₂) M *
            (↑Z₂⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)) σ τ)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) :
    (Z₁ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE₁) M *
      (↑Z₁⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) =
    (Z₂ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE₂) M *
      (↑Z₂⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) :=
  regionInsertedCoeff_transferMap_unique A B R f hRB hCB hposB
    (fun N => (Z₁ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE₁) N *
      (↑Z₁⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ))
    (fun N => (Z₂ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE₂) N *
      (↑Z₂⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ))
    h₁ h₂ M

/-! ### Arbitrary target matrices from coefficient identities -/

/-- **Single-edge conjugation covariance from two coefficient identities.**

On a boundary edge `f` of a region `R`, with `B`'s region and complement blocked-tensor
injective and positive bonds, suppose the per-edge gauge `Z₁` and a second gauge `Z₂` (both
invertible over `B.bondDim f.1`) each realize the region-insertion coefficient identity of `A`
through `B` on `f` by conjugation.  Then they induce the same conjugation map on every bond
matrix `N` over `B.bondDim f.1`.

This is `gaugeConj_eq_of_coeffIdentities` read on an arbitrary target matrix: the bond-dimension
reindexing is surjective, so every `N` is a reindexed `M`, and the determinacy applies.  Reading
it on `N` over `B.bondDim f.1` (rather than `reindex M`) is the conjugation-covariance shape at
the edge `f.1`. -/
theorem gaugeConj_eq_of_coeffIdentities_target
    (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hposB : ∀ g : Edge G, 0 < B.bondDim g)
    {hE₁ hE₂ : A.bondDim f.1 = B.bondDim f.1}
    (Z₁ Z₂ : GL (Fin (B.bondDim f.1)) ℂ)
    (h₁ : ∀ (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
      (σ : RegionPhysicalConfig (V := V) (d := d) R)
      (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
      regionInsertedCoeff (G := G) A R f M σ τ =
        regionInsertedCoeff (G := G) B R f
          ((Z₁ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE₁) M *
            (↑Z₁⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)) σ τ)
    (h₂ : ∀ (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
      (σ : RegionPhysicalConfig (V := V) (d := d) R)
      (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
      regionInsertedCoeff (G := G) A R f M σ τ =
        regionInsertedCoeff (G := G) B R f
          ((Z₂ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE₂) M *
            (↑Z₂⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)) σ τ)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) :
    (Z₁ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) * N *
        (↑Z₁⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) =
      (Z₂ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) * N *
        (↑Z₂⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) := by
  -- Every target matrix `N` is a reindexed `M` (the reindexing is an algebra equivalence).
  obtain ⟨M, rfl⟩ := (Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE₁)).surjective N
  have hmain := gaugeConj_eq_of_coeffIdentities A B R f hRB hCB hposB
    (hE₁ := hE₁) (hE₂ := hE₂) Z₁ Z₂ h₁ h₂ M
  -- The two reindexings along `hE₁` and `hE₂` coincide by proof irrelevance.
  have hcast : (Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE₁) M) =
      (Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE₂) M) := by
    congr 1
  rw [hcast] at hmain
  exact hmain

end CoeffBridge

end PEPS
end TNLean
