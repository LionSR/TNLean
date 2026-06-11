import TNLean.PEPS.RegionTransportInsertion
import TNLean.PEPS.RegionBlock.Algebra
import TNLean.PEPS.TorusBlockingData

/-!
# Covariance of the region-insertion transfer map under translation

The per-edge gauge of the normal PEPS Fundamental Theorem is read off a region-insertion transfer
map `fwd`, the matrix map satisfying the coefficient identity
`regionInsertedCoeff A R f M = regionInsertedCoeff B R f (fwd M)` (the field
`RegionInsertionTransfer.fwd_coeff`).  The gauge interface produces this map non-constructively,
but the identity **determines** it: with the second tensor's region and complement
blocked-tensor injective and positive bond dimensions, two maps satisfying the same coefficient
identity coincide (`regionInsertedCoeff_transferMap_unique`), because the region-inserted
coefficient determines the inserted matrix (`regionInsertedCoeff_injective`).

This determinacy turns the geometric covariance of the region-inserted coefficient
(`regionInsertedCoeff_transport`) into covariance of the transfer map.  On the discrete torus a
translation-invariant tensor satisfies `A.transport (translate a b) = A`, so the coefficient
identity at a reference edge transports to the same identity at every translate of that edge,
with the inserted matrix carried by the bond-dimension reindexing.  The transfer map at the
translated edge therefore agrees with the reference transfer map carried across the translation,
which is the per-edge class agreement the orientation-uniform reduction consumes (obligation 6 of
`docs/paper-gaps/peps_normal_ft_section3_route.tex`).

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines
  1407--1572 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Congruence of the region-inserted coefficient under a tensor equality -/

/-- The region-inserted coefficient is congruent under an equality of tensors: equal tensors have
equal region-inserted coefficients, with the inserted matrix carried across the (definitionally
trivial) bond-dimension equality.  This bridges the literal tensor of a translation-invariant
PEPS with its transported copy `A.transport φ = A`. -/
theorem regionInsertedCoeff_congrTensor {A₁ A₂ : Tensor G d} (h : A₁ = A₂) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A₁.bondDim f.1)) (Fin (A₁.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A₁ R f M σ τ =
      regionInsertedCoeff (G := G) A₂ R f
        (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congrFun (congrArg Tensor.bondDim h) f.1)) M)
        σ τ := by
  subst h
  simp

/-! ### The transfer map is determined by the coefficient identity -/

/-- **Uniqueness of the region-insertion transfer map.**

Two matrix maps `g₁`, `g₂` that both realize the region-inserted coefficient of `A` through `B`
on the boundary edge `f` --- `regionInsertedCoeff A R f M = regionInsertedCoeff B R f (gᵢ M)` for
every region and complement physical configuration --- agree on every inserted matrix, provided
`B`'s region and complement are blocked-tensor injective and every bond dimension of `B` is
positive.  The region-inserted coefficient of `B` determines the inserted matrix
(`regionInsertedCoeff_injective`), so `g₁ M` and `g₂ M` realize the same coefficient and coincide.

This is the determinacy that makes the non-constructive transfer map of the gauge interface
covariant: any two transfer maps satisfying the defining coefficient identity are equal.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 377--457 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_transferMap_unique (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (g₁ g₂ : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ →
      Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (h₁ : ∀ (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
      (σ : RegionPhysicalConfig (V := V) (d := d) R)
      (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
      regionInsertedCoeff (G := G) A R f M σ τ =
        regionInsertedCoeff (G := G) B R f (g₁ M) σ τ)
    (h₂ : ∀ (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
      (σ : RegionPhysicalConfig (V := V) (d := d) R)
      (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
      regionInsertedCoeff (G := G) A R f M σ τ =
        regionInsertedCoeff (G := G) B R f (g₂ M) σ τ)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) :
    g₁ M = g₂ M := by
  refine regionInsertedCoeff_injective (G := G) B R hRB hCB hposB f (g₁ M) (g₂ M)
    (fun σ τ => ?_)
  rw [← h₁ M σ τ, ← h₂ M σ τ]

/-! ### Translation covariance of the coefficient identity on the torus -/

section Torus

variable {width height : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- The bond dimension of a translation-invariant tensor at the translated boundary edge equals
its bond dimension at the reference boundary edge: translation carries the reference edge to its
image, and the tensor is fixed by transport, so the bond dimension is the same. -/
theorem bondDim_boundaryEdgeMap_translate
    {A : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A)
    (a : ZMod width) (b : ZMod height) (R : Finset (TorusVertex width height))
    (f : {f : Edge (torusGraph width height) //
      IsRegionBoundaryEdge (G := torusGraph width height) R f}) :
    A.bondDim (boundaryEdgeMap (translate a b) R f).1 = A.bondDim f.1 := by
  rw [← transport_bondDim_boundaryEdgeMap A (translate a b) R f, hA a b]

/-- **Translation covariance of the coefficient identity on the torus.**

For translation-invariant tensors `A` and `B` on the torus, a coefficient identity at the
reference boundary edge `f` of `R`
(`regionInsertedCoeff A R f M = regionInsertedCoeff B R f (g M)`) transports to the same identity
at the translated boundary edge of the translated region, for the *same* tensors `A` and `B`.
Inserting `M'` on the translated edge and contracting the translated region of `A` gives the same
coefficient as applying `g` to the reference-bond reindex of `M'` and reading it off on `B`.

Translation invariance `A.transport (translate a b) = A` identifies the transported tensor with
the original, so `regionInsertedCoeff_transport` carries the reference coefficient to the
translated edge with no change of tensor.  The inserted matrix is carried between the translated
and reference bonds, which have the same dimension (`bondDim_boundaryEdgeMap_translate`).

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_translate_coeffIdentity
    {A B : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (hB : IsTorusTranslationInvariant B)
    (a : ZMod width) (b : ZMod height) (R : Finset (TorusVertex width height))
    (f : {f : Edge (torusGraph width height) //
      IsRegionBoundaryEdge (G := torusGraph width height) R f})
    (g : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ →
      Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (hg : ∀ (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
      (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) R)
      (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) (Finset.univ \ R)),
      regionInsertedCoeff (G := torusGraph width height) A R f M σ τ =
        regionInsertedCoeff (G := torusGraph width height) B R f (g M) σ τ)
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
        (Matrix.reindexAlgEquiv ℂ ℂ
            (finCongr (bondDim_boundaryEdgeMap_translate hB a b R f).symm)
          (g (Matrix.reindexAlgEquiv ℂ ℂ
            (finCongr (bondDim_boundaryEdgeMap_translate hA a b R f)) M')))
        (regionPhysicalConfigMap (translate a b) R σ)
        (regionPhysicalConfigCongr (d := d) (Region_map_compl (translate a b) R)
          (regionPhysicalConfigMap (translate a b) (Finset.univ \ R) τ)) := by
  -- Step 1: identify the literal-`A` coefficient with the transported-`A` coefficient.
  rw [regionInsertedCoeff_congrTensor (hA a b).symm (Region.map (translate a b) R)
    (boundaryEdgeMap (translate a b) R f) M']
  -- Step 2: geometric transport covariance for `A`.
  rw [regionInsertedCoeff_transport A (translate a b) R f]
  -- Step 3: the reference coefficient identity `hg`.
  rw [hg]
  -- Step 4: geometric transport covariance for `B` (reverse direction).
  rw [show ∀ N, regionInsertedCoeff (G := torusGraph width height) B R f N σ τ =
        regionInsertedCoeff (G := torusGraph width height) (B.transport (translate a b))
          (Region.map (translate a b) R) (boundaryEdgeMap (translate a b) R f)
          (Matrix.reindexAlgEquiv ℂ ℂ
            (finCongr (transport_bondDim_boundaryEdgeMap B (translate a b) R f)).symm N)
          (regionPhysicalConfigMap (translate a b) R σ)
          (regionPhysicalConfigCongr (d := d) (Region_map_compl (translate a b) R)
            (regionPhysicalConfigMap (translate a b) (Finset.univ \ R) τ)) from ?_]
  -- Step 5: identify the transported-`B` coefficient back with the literal-`B` coefficient, and
  -- check the inserted matrices agree.
  rotate_left
  · intro N
    rw [regionInsertedCoeff_transport B (translate a b) R f]
    congr 1
  rw [regionInsertedCoeff_congrTensor (hB a b) (Region.map (translate a b) R)
    (boundaryEdgeMap (translate a b) R f)]
  congr 1

end Torus

end PEPS
end TNLean
