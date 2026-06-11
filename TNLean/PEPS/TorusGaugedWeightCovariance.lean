import TNLean.PEPS.TorusAbsorbedCovariance
import TNLean.PEPS.RegionBlock.GaugeInjectivity2
import TNLean.PEPS.RegionBlock.ProportionalityFromAbsorbed

/-!
# Translation covariance of the gauge-absorbed blocked weights

The final comparison of the normal PEPS Fundamental Theorem on the torus produces, at every
comparison region, a scalar proportionality between the blocked weights of the first tensor and
of the gauge-absorbed second tensor (arXiv:1804.04964, Section 3, proof of Theorem 3, lines
1544--1571 of `Papers/1804.04964/paper_normal.tex`).  The single scalar `λ` of the theorem
requires those proportionality scalars to be the *same at every translate* of the comparison
region.  This file proves the covariance that delivers it: for a translation-invariant second
tensor and a translation-covariant gauge family, the blocked weight of the gauge-absorbed tensor
at a translated region, read at the transported boundary and physical configurations, equals the
blocked weight at the original region (`regionBlockedWeight_applyGauge_translate`).  A scalar
proportionality of the region blocks against the gauge-absorbed tensor therefore transports to
every translate of the comparison region with the *same* scalar
(`twoBlockScalarProportional_translate`).

The per-edge content is the covariance of the surviving boundary gauge
(`regionBoundaryGauge_translate`): on a boundary edge the surviving gauge of the translated
region is the surviving gauge of the original region carried across the bond-dimension equality;
the orientation flips of the translation and of the region membership cancel exactly.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1571
  of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

/-! ### Congruence and reindexing helpers -/

/-- Evaluating a reindexed matrix at the cast indices recovers the original entry. -/
theorem reindexAlgEquiv_apply_cast {m n : ℕ} (h : m = n)
    (M : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) :
    Matrix.reindexAlgEquiv ℂ ℂ (finCongr h) M (Fin.cast h i) (Fin.cast h j) = M i j := by
  rw [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  congr 1

section Generic

variable {V W : Type*} [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
  {G : SimpleGraph V} {G' : SimpleGraph W} {d : ℕ}
variable [DecidableRel G.Adj] [DecidableRel G'.Adj]

omit [Fintype W] [LinearOrder W] [DecidableRel G'.Adj] in
/-- The blocked-region weight is congruent under an equality of tensors, with the boundary
configuration carried across the (propositionally trivial) bond-dimension equality. -/
theorem regionBlockedWeight_congrTensor {T₁ T₂ : Tensor G d} (h : T₁ = T₂) (R : Finset V)
    (bdry : RegionBoundaryConfig (G := G) T₁ R)
    (τ : RegionPhysicalConfig (V := V) (d := d) R) :
    regionBlockedWeight (G := G) T₁ R bdry τ =
      regionBlockedWeight (G := G) T₂ R
        (fun f => Fin.cast (congrFun (congrArg Tensor.bondDim h) f.1) (bdry f)) τ := by
  subst h
  rfl

omit [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
  [DecidableRel G.Adj] [DecidableRel G'.Adj] in
/-- Pushing a region physical configuration through a graph isomorphism is surjective. -/
theorem regionPhysicalConfigMap_surjective (φ : G ≃g G') (R : Finset V) :
    Function.Surjective (regionPhysicalConfigMap (d := d) φ R) := fun τ' =>
  ⟨(regionPhysicalConfigMapEquiv (d := d) φ R).symm τ',
    (regionPhysicalConfigMapEquiv (d := d) φ R).apply_symm_apply τ'⟩

end Generic

/-! ### The transported boundary configuration of a translation-invariant tensor -/

section Torus

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- The boundary configuration of a translation-invariant tensor transported to the translated
region: push through the geometric boundary-edge reindexing and carry each value across the
bond-dimension equality of translation invariance. -/
noncomputable def tiBoundaryConfigMap (T : Tensor (torusGraph width height) d)
    (hT : IsTorusTranslationInvariant T) (a : ZMod width) (b : ZMod height)
    (R : Finset (TorusVertex width height))
    (bdry : RegionBoundaryConfig (G := torusGraph width height) T R) :
    RegionBoundaryConfig (G := torusGraph width height) T (Region.map (translate a b) R) :=
  fun f => Fin.cast (congrFun (congrArg Tensor.bondDim (hT a b)) f.1)
    (regionBoundaryConfigMap T (translate a b) R bdry f)

/-- The transported boundary configuration as a bijection. -/
noncomputable def tiBoundaryConfigEquiv (T : Tensor (torusGraph width height) d)
    (hT : IsTorusTranslationInvariant T) (a : ZMod width) (b : ZMod height)
    (R : Finset (TorusVertex width height)) :
    RegionBoundaryConfig (G := torusGraph width height) T R ≃
      RegionBoundaryConfig (G := torusGraph width height) T (Region.map (translate a b) R) where
  toFun := tiBoundaryConfigMap T hT a b R
  invFun bdry' := (regionBoundaryConfigMapEquiv T (translate a b) R).symm
    (fun f => Fin.cast (congrFun (congrArg Tensor.bondDim (hT a b)) f.1).symm (bdry' f))
  left_inv bdry := by
    beta_reduce
    have hcollapse : (fun f => Fin.cast
        (congrFun (congrArg Tensor.bondDim (hT a b)) f.1).symm
        (tiBoundaryConfigMap T hT a b R bdry f)) =
        regionBoundaryConfigMap T (translate a b) R bdry := by
      funext f
      apply Fin.eq_of_val_eq
      simp [tiBoundaryConfigMap]
    rw [hcollapse, ← regionBoundaryConfigMapEquiv_apply, Equiv.symm_apply_apply]
  right_inv bdry' := by
    beta_reduce
    funext f
    rw [tiBoundaryConfigMap, ← regionBoundaryConfigMapEquiv_apply, Equiv.apply_symm_apply]
    apply Fin.eq_of_val_eq
    simp

@[simp] theorem tiBoundaryConfigEquiv_apply (T : Tensor (torusGraph width height) d)
    (hT : IsTorusTranslationInvariant T) (a : ZMod width) (b : ZMod height)
    (R : Finset (TorusVertex width height))
    (bdry : RegionBoundaryConfig (G := torusGraph width height) T R) :
    tiBoundaryConfigEquiv T hT a b R bdry = tiBoundaryConfigMap T hT a b R bdry := rfl

/-- The transported boundary configuration is surjective onto the boundary configurations of the
translated region. -/
theorem tiBoundaryConfigMap_surjective (T : Tensor (torusGraph width height) d)
    (hT : IsTorusTranslationInvariant T) (a : ZMod width) (b : ZMod height)
    (R : Finset (TorusVertex width height)) :
    Function.Surjective (tiBoundaryConfigMap T hT a b R) := fun bdry' =>
  ⟨(tiBoundaryConfigEquiv T hT a b R).symm bdry',
    (tiBoundaryConfigEquiv T hT a b R).apply_symm_apply bdry'⟩

/-- Reading the transported boundary configuration at the translated distinguished boundary edge
recovers the original value across the bond-dimension equality. -/
theorem tiBoundaryConfigMap_boundaryEdgeMap (T : Tensor (torusGraph width height) d)
    (hT : IsTorusTranslationInvariant T) (a : ZMod width) (b : ZMod height)
    (R : Finset (TorusVertex width height))
    (bdry : RegionBoundaryConfig (G := torusGraph width height) T R)
    (f : {f : Edge (torusGraph width height) //
      IsRegionBoundaryEdge (G := torusGraph width height) R f}) :
    tiBoundaryConfigMap T hT a b R bdry (boundaryEdgeMap (translate a b) R f) =
      Fin.cast (bondDim_boundaryEdgeMap_translate hT a b R f).symm (bdry f) := by
  rw [tiBoundaryConfigMap, regionBoundaryConfigMap_boundaryEdgeMap]
  apply Fin.eq_of_val_eq
  simp

/-- **Translation covariance of the blocked weight of a translation-invariant tensor.**

The blocked weight at the translated region, read at the transported boundary and physical
configurations, is the blocked weight at the original region.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1572 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedWeight_tiBoundaryConfigMap (T : Tensor (torusGraph width height) d)
    (hT : IsTorusTranslationInvariant T) (a : ZMod width) (b : ZMod height)
    (R : Finset (TorusVertex width height))
    (bdry : RegionBoundaryConfig (G := torusGraph width height) T R)
    (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) R) :
    regionBlockedWeight (G := torusGraph width height) T (Region.map (translate a b) R)
        (tiBoundaryConfigMap T hT a b R bdry)
        (regionPhysicalConfigMap (translate a b) R τ) =
      regionBlockedWeight (G := torusGraph width height) T R bdry τ := by
  have h1 := regionBlockedWeight_congrTensor (hT a b) (Region.map (translate a b) R)
    (regionBoundaryConfigMap T (translate a b) R bdry)
    (regionPhysicalConfigMap (translate a b) R τ)
  have h2 := regionBlockedWeight_transport T (translate a b) R bdry τ
  exact h1.symm.trans h2

/-! ### Covariance of the surviving boundary gauge -/

/-- **Translation covariance of the surviving boundary gauge.**

For a translation-covariant gauge family, the surviving boundary gauge of the translated region
at the translated boundary edge is the surviving boundary gauge of the original region carried
across the bond-dimension equality: the endpoint-order flip of the translation and the membership
flip of the translated region cancel.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionBoundaryGauge_translate {B : Tensor (torusGraph width height) d}
    {X : (e : Edge (torusGraph width height)) → GL (Fin (B.bondDim e)) ℂ}
    (hX : IsTranslationCovariantGaugeFamily B X)
    (a : ZMod width) (b : ZMod height) (R : Finset (TorusVertex width height))
    (f : {f : Edge (torusGraph width height) //
      IsRegionBoundaryEdge (G := torusGraph width height) R f})
    (h : B.bondDim f.1 = B.bondDim (boundaryEdgeMap (translate a b) R f).1) :
    regionBoundaryGauge (G := torusGraph width height) B X (Region.map (translate a b) R)
        (boundaryEdgeMap (translate a b) R f) =
      Matrix.reindexAlgEquiv ℂ ℂ (finCongr h)
        (regionBoundaryGauge (G := torusGraph width height) B X R f) := by
  classical
  have hGL : X (boundaryEdgeMap (translate a b) R f).1 =
      if (boundaryEdgeMap (translate a b) R f).1.1.1 = translate a b f.1.1.1 then
        glReindex h (X f.1)
      else glReindex h ((glTranspose (X f.1))⁻¹) := hX a b f.1 h
  have hne : f.1.1.1 ≠ f.1.1.2 := ne_of_lt f.1.2.1
  have hor := boundaryEdgeMap_translate_fst_or R f a b
  rw [regionBoundaryGauge, regionBoundaryGauge]
  rcases hor with hfst | hfst
  · -- The translation preserves the stored endpoint order.
    rw [if_pos hfst] at hGL
    have hmem : (boundaryEdgeMap (translate a b) R f).1.1.1 ∈ Region.map (translate a b) R ↔
        f.1.1.1 ∈ R := by
      rw [hfst]
      exact mem_Region_map_apply (translate a b) R f.1.1.1
    by_cases hPf : f.1.1.1 ∈ R
    · rw [if_pos (hmem.mpr hPf), if_pos hPf, hGL, glReindex_coe]
    · have hX' : (X (boundaryEdgeMap (translate a b) R f).1)⁻¹ =
          glReindex h ((X f.1)⁻¹) := by
        rw [hGL]
        exact (map_inv (glReindex h) (X f.1)).symm
      rw [if_neg (fun hcon => hPf (hmem.mp hcon)), if_neg hPf, hX', glReindex_coe,
        reindexAlgEquiv_transpose]
  · -- The translation swaps the stored endpoint order.
    have hQ : ¬((boundaryEdgeMap (translate a b) R f).1.1.1 = translate a b f.1.1.1) := by
      rw [hfst]
      intro hcon
      exact hne ((translate a b).toEquiv.injective hcon).symm
    rw [if_neg hQ] at hGL
    have hmem : (boundaryEdgeMap (translate a b) R f).1.1.1 ∈ Region.map (translate a b) R ↔
        f.1.1.2 ∈ R := by
      rw [hfst]
      exact mem_Region_map_apply (translate a b) R f.1.1.2
    have hexcl : (f.1.1.1 ∈ R ∧ f.1.1.2 ∉ R) ∨ (f.1.1.1 ∉ R ∧ f.1.1.2 ∈ R) := f.2
    by_cases hPf : f.1.1.1 ∈ R
    · -- First endpoint in: the translated first endpoint is the second, hence outside.
      have hv : f.1.1.2 ∉ R := by
        rcases hexcl with ⟨_, hv⟩ | ⟨hcon, _⟩
        · exact hv
        · exact absurd hPf hcon
      have hX' : (X (boundaryEdgeMap (translate a b) R f).1)⁻¹ =
          glReindex h (glTranspose (X f.1)) := by
        rw [hGL, (map_inv (glReindex h) ((glTranspose (X f.1))⁻¹)).symm]
        exact congrArg (glReindex h) (inv_inv (glTranspose (X f.1)))
      rw [if_neg (fun hcon => hv (hmem.mp hcon)), if_pos hPf, hX',
        glReindex_coe, glTranspose_coe, reindexAlgEquiv_transpose, Matrix.transpose_transpose]
    · have hv : f.1.1.2 ∈ R := by
        rcases hexcl with ⟨hcon, _⟩ | ⟨_, hv⟩
        · exact absurd hcon hPf
        · exact hv
      rw [if_pos (hmem.mpr hv), if_neg hPf, hGL, glReindex_coe, glTranspose_inv_coe]

/-! ### Covariance of the gauge-absorbed blocked weight -/

/-- **Translation covariance of the gauge-absorbed blocked weight.**

For a translation-invariant second tensor and a translation-covariant gauge family, the blocked
weight of the gauge-absorbed tensor at the translated region, read at the transported boundary
and physical configurations, equals the blocked weight at the original region.  The gauge
factorization (`regionBlockedWeight_applyGauge`) reduces both sides to the boundary coupling
against the blocked weights of the bare second tensor; the coupling is covariant edgewise
(`regionBoundaryGauge_translate`) and the bare weights are covariant by translation invariance.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1571 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedWeight_applyGauge_translate {B : Tensor (torusGraph width height) d}
    (hB : IsTorusTranslationInvariant B)
    {X : (e : Edge (torusGraph width height)) → GL (Fin (B.bondDim e)) ℂ}
    (hX : IsTranslationCovariantGaugeFamily B X)
    (a : ZMod width) (b : ZMod height) (R : Finset (TorusVertex width height))
    (bdry : RegionBoundaryConfig (G := torusGraph width height) B R)
    (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) R) :
    regionBlockedWeight (G := torusGraph width height) (applyGauge B X)
        (Region.map (translate a b) R) (tiBoundaryConfigMap B hB a b R bdry)
        (regionPhysicalConfigMap (translate a b) R τ) =
      regionBlockedWeight (G := torusGraph width height) (applyGauge B X) R bdry τ := by
  classical
  rw [regionBlockedWeight_applyGauge (G := torusGraph width height) B X
      (Region.map (translate a b) R) (tiBoundaryConfigMap B hB a b R bdry)
      (regionPhysicalConfigMap (translate a b) R τ),
    regionBlockedWeight_applyGauge (G := torusGraph width height) B X R bdry τ]
  rw [← Equiv.sum_comp (tiBoundaryConfigEquiv B hB a b R)]
  refine Finset.sum_congr rfl (fun bdry' _ => ?_)
  simp only [tiBoundaryConfigEquiv_apply]
  rw [regionBlockedWeight_tiBoundaryConfigMap B hB a b R bdry' τ]
  congr 1
  -- Reindex the boundary-edge product through the geometric boundary-edge bijection.
  rw [← Equiv.prod_comp (regionBoundaryEdgeMapEquiv (translate a b) R).symm]
  refine Finset.prod_congr rfl (fun f _ => ?_)
  -- The per-edge coupling entries match across the bond-dimension casts.
  have hcastB := tiBoundaryConfigMap_boundaryEdgeMap B hB a b R bdry f
  have hcastB' := tiBoundaryConfigMap_boundaryEdgeMap B hB a b R bdry' f
  have hK := regionBoundaryGauge_translate hX a b R f
    (bondDim_boundaryEdgeMap_translate hB a b R f).symm
  rw [show (regionBoundaryEdgeMapEquiv (translate a b) R).symm f =
    boundaryEdgeMap (translate a b) R f from rfl]
  rw [hcastB, hcastB', hK]
  exact reindexAlgEquiv_apply_cast
    (bondDim_boundaryEdgeMap_translate hB a b R f).symm _ (bdry f) (bdry' f)

/-! ### Translation transport of the region-block scalar proportionality -/

/-- **Translation covariance of the reindexed gauge-absorbed blocked weight.**

The blocked weight of the gauge-absorbed second tensor, transported to the first tensor's
bonds, at the translated region and the transported configurations, equals the blocked weight
at the original region.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1571 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedWeight_reindexTensor_translate {A B : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (hB : IsTorusTranslationInvariant B)
    {X : (e : Edge (torusGraph width height)) → GL (Fin (B.bondDim e)) ℂ}
    (hX : IsTranslationCovariantGaugeFamily B X)
    (hbd : A.bondDim = B.bondDim)
    (a : ZMod width) (b : ZMod height) (R : Finset (TorusVertex width height))
    (bdry : RegionBoundaryConfig (G := torusGraph width height) A R)
    (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d) R) :
    regionBlockedWeight (G := torusGraph width height)
        (reindexTensor (G := torusGraph width height) (applyGauge B X) hbd)
        (Region.map (translate a b) R) (tiBoundaryConfigMap A hA a b R bdry)
        (regionPhysicalConfigMap (translate a b) R τ) =
      regionBlockedWeight (G := torusGraph width height)
        (reindexTensor (G := torusGraph width height) (applyGauge B X) hbd) R bdry τ := by
  have hswap : (fun f => (Fin.cast (congr_fun hbd f.1)
      (tiBoundaryConfigMap A hA a b R bdry f) :
        Fin ((applyGauge B X).bondDim f.1))) =
      tiBoundaryConfigMap B hB a b R (fun f => Fin.cast (congr_fun hbd f.1) (bdry f)) := by
    funext f
    apply Fin.eq_of_val_eq
    simp [tiBoundaryConfigMap, regionBoundaryConfigMap]
  have h1 := regionBlockedWeight_reindexTensor (G := torusGraph width height)
    (applyGauge B X) hbd (Region.map (translate a b) R)
    (tiBoundaryConfigMap A hA a b R bdry) (regionPhysicalConfigMap (translate a b) R τ)
  have h3 := regionBlockedWeight_applyGauge_translate hB hX a b R
    (fun f => Fin.cast (congr_fun hbd f.1) (bdry f)) τ
  have h4 := regionBlockedWeight_reindexTensor (G := torusGraph width height)
    (applyGauge B X) hbd R bdry τ
  exact (h1.trans ((congrArg (fun β => regionBlockedWeight (G := torusGraph width height)
    (applyGauge B X) (Region.map (translate a b) R) β
    (regionPhysicalConfigMap (translate a b) R τ)) hswap).trans h3)).trans h4.symm

/-- **The region-block proportionality scalar is translation invariant.**

For translation-invariant `A`, `B` and a translation-covariant gauge family `X`, a scalar
proportionality of the region blocks of `A` against the reindexed gauge-absorbed tensor over `R`
transports to the translated region `Region.map (translate a b) R` with the *same* scalar.

This is the translation step pinning the single `λ` of Theorem 3: the comparison scalar read at
any translate of the comparison region is the scalar at the reference position.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1544--1571 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem twoBlockScalarProportional_translate {A B : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (hB : IsTorusTranslationInvariant B)
    {X : (e : Edge (torusGraph width height)) → GL (Fin (B.bondDim e)) ℂ}
    (hX : IsTranslationCovariantGaugeFamily B X)
    (hbd : A.bondDim = B.bondDim)
    (a : ZMod width) (b : ZMod height) (R : Finset (TorusVertex width height)) {c : ℂ}
    (hprop : TwoBlockScalarProportional.{0, 0, 0, 0}
      (regionTwoBlock (G := torusGraph width height) A R)
      (regionTwoBlock (G := torusGraph width height)
        (reindexTensor (G := torusGraph width height) (applyGauge B X) hbd) R) c) :
    TwoBlockScalarProportional.{0, 0, 0, 0}
      (regionTwoBlock (G := torusGraph width height) A (Region.map (translate a b) R))
      (regionTwoBlock (G := torusGraph width height)
        (reindexTensor (G := torusGraph width height) (applyGauge B X) hbd)
        (Region.map (translate a b) R)) c := by
  intro u bdry' τ'
  obtain ⟨bdry, rfl⟩ := tiBoundaryConfigMap_surjective A hA a b R bdry'
  obtain ⟨τ, rfl⟩ := regionPhysicalConfigMap_surjective (d := d) (translate a b) R τ'
  simp only [regionTwoBlock_apply]
  rw [regionBlockedWeight_tiBoundaryConfigMap A hA a b R bdry τ,
    regionBlockedWeight_reindexTensor_translate hA hB hX hbd a b R bdry τ]
  exact hprop PUnit.unit bdry τ

end Torus

end PEPS
end TNLean
