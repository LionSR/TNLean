/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.AdjacentSupportGeneration

/-!
# Adjacent generation in the canonical finite matrix coordinates

Faithful finite-region embeddings reflect the derived quasi-local
adjacent-generation equalities. The first equality is stated in the
ordered left/right bipartite matrix algebra, and the second in the common
physical pair, after its canonical equality of regions.

Source: GNVW, arXiv:0910.3675v2, equations AARReven and AARRodd,
source lines 1276--1315.

**Scope restriction (homogeneous chain):** The fixed on-site dimension is
positive. The site-dependent GNVW setting is separate; see
`docs/paper-gaps/gnvw12_site_dependent_adjacent_generation_scope.tex`.
-/

namespace SpinChain
namespace PropagatesWithin

variable {d : ℕ} [NeZero d]
  {ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d}

private theorem map_transport_matrixSubalgebra {Λ Γ : Finset ℤ} (h : Λ = Γ)
    (S : StarSubalgebra ℂ (Matrix (Config d Γ) (Config d Γ) ℂ)) :
    (h.symm ▸ S).map (matrixToQuasiLocalObservable d Λ) =
      S.map (matrixToQuasiLocalObservable d Γ) := by
  subst Γ
  rfl

/-- The two actual support algebras fill the common physical-pair matrix
algebra, in the source odd--even order. The equality of regions identifies
the second factor with its canonical copy on that pair; GNVW,
arXiv:0910.3675v2, equation AARRodd, source lines 1306--1315. -/
theorem oddSupportAlgebra_sup_evenSupportAlgebra_eq_top
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    oddSupportAlgebra hω x ⊔
      ((rightPair_eq_leftPair_add_one x).symm ▸ evenSupportAlgebra hω (x + 1)) = ⊤ := by
  let f := matrixToQuasiLocalObservable d (rightPair x)
  have hf : Function.Injective f :=
    (quasiLocalObservable_injective d (rightPair x)).comp
      CStarMatrix.ofMatrixStarAlgEquiv.injective
  apply StarSubalgebra.map_injective hf
  rw [StarSubalgebra.map_sup,
    map_transport_matrixSubalgebra (rightPair_eq_leftPair_add_one x)]
  change embeddedOddSupportAlgebra hω x ⊔ embeddedEvenSupportAlgebra hω (x + 1) =
    (⊤ : StarSubalgebra ℂ (Matrix (Config d (rightPair x)) (Config d (rightPair x)) ℂ)).map f
  rw [adjacentSupportJoin_eq_range_rightPair hω x, ← StarAlgHom.range_eq_map_top]
  ext z
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨CStarMatrix.ofMatrixStarAlgEquiv.symm A, by
      change quasiLocalObservable d (rightPair x)
        (CStarMatrix.ofMatrixStarAlgEquiv (CStarMatrix.ofMatrixStarAlgEquiv.symm A)) = _
      rw [StarAlgEquiv.apply_symm_apply]
      rfl⟩
  · rintro ⟨A, rfl⟩
    exact ⟨CStarMatrix.ofMatrixStarAlgEquiv A, rfl⟩

/-- The finite local image is the join of the ordered left and right
support factors in canonical bipartite coordinates. This is an equality
of bundled star-subalgebras, rather than only their underlying subspaces;
GNVW, arXiv:0910.3675v2, equation AARReven, source lines 1276--1287. -/
theorem evenPairLocalImage_eq_sup_supportAlgebra
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    evenPairLocalImage hω x =
      (evenSupportAlgebra hω x).map
        (Matrix.leftKroneckerEmbed (n := Config d (rightPair x))) ⊔
      (oddSupportAlgebra hω x).map
        (Matrix.rightKroneckerEmbed (m := Config d (leftPair x))) := by
  classical
  let hdisj := disjoint_leftPair_rightPair x
  let htarget := regionSumset_evenPair x
  let e := bipartiteLocalAlgebraEquiv (d := d) hdisj
  let φ := (quasiLocalObservable d (leftPair x ∪ rightPair x)).comp e.symm.toStarAlgHom
  have hφ : Function.Injective φ :=
    (quasiLocalObservable_injective d (leftPair x ∪ rightPair x)).comp e.symm.injective
  have hleft : φ.comp (Matrix.leftKroneckerEmbed (n := Config d (rightPair x))) =
      matrixToQuasiLocalObservable d (leftPair x) := by
    apply StarAlgHom.ext
    intro A
    have hi := bipartiteLocalAlgebraEquiv_localInclusion_left hdisj (CStarMatrix.ofMatrix A)
    change (bipartiteLocalAlgebraEquiv hdisj)
      (localInclusion _ (CStarMatrix.ofMatrix A)) =
        Matrix.leftKroneckerEmbed A at hi
    change quasiLocalObservable d (leftPair x ∪ rightPair x)
      (e.symm (Matrix.leftKroneckerEmbed A)) = _
    rw [← hi, StarAlgEquiv.symm_apply_apply, quasiLocalObservable_localInclusion]
    rfl
  have hright : φ.comp (Matrix.rightKroneckerEmbed (m := Config d (leftPair x))) =
      matrixToQuasiLocalObservable d (rightPair x) := by
    apply StarAlgHom.ext
    intro A
    have hi := bipartiteLocalAlgebraEquiv_localInclusion_right hdisj (CStarMatrix.ofMatrix A)
    change (bipartiteLocalAlgebraEquiv hdisj)
      (localInclusion _ (CStarMatrix.ofMatrix A)) =
        Matrix.rightKroneckerEmbed A at hi
    change quasiLocalObservable d (leftPair x ∪ rightPair x)
      (e.symm (Matrix.rightKroneckerEmbed A)) = _
    rw [← hi, StarAlgEquiv.symm_apply_apply, quasiLocalObservable_localInclusion]
    rfl
  have himage : (evenPairLocalImage hω x).map φ =
      (ω.toStarAlgHom.comp (quasiLocalObservable d (evenPair x))).range := by
    ext z
    constructor
    · rintro ⟨X, hX, rfl⟩
      rw [evenPairLocalImage, bipartiteLocalRestrictionRange,
        StarSubalgebra.bipartiteReindex] at hX
      obtain ⟨b, hb, rfl⟩ := StarSubalgebra.mem_map.mp hX
      obtain ⟨A, hA⟩ := (mem_transport_localRestrictionRange_iff hω htarget b).mp hb
      refine ⟨A, ?_⟩
      change ω (quasiLocalObservable d (evenPair x) A) =
        quasiLocalObservable d (leftPair x ∪ rightPair x)
          (e.symm (bipartiteLocalAlgebraEquiv hdisj b))
      rw [StarAlgEquiv.symm_apply_apply, hA]
      exact (quasiLocalObservable_transport_localRestriction hω htarget A).symm
    · rintro ⟨A, rfl⟩
      let b := htarget ▸ hω.localRestriction (evenPair x) A
      refine ⟨e b, ?_, ?_⟩
      · rw [evenPairLocalImage, bipartiteLocalRestrictionRange,
          StarSubalgebra.bipartiteReindex]
        apply StarSubalgebra.mem_map.mpr
        refine ⟨b, ?_, rfl⟩
        exact (mem_transport_localRestrictionRange_iff hω htarget b).mpr ⟨A, rfl⟩
      · change quasiLocalObservable d (leftPair x ∪ rightPair x) (e.symm (e b)) =
          ω (quasiLocalObservable d (evenPair x) A)
        rw [StarAlgEquiv.symm_apply_apply]
        exact quasiLocalObservable_transport_localRestriction hω htarget A
  apply StarSubalgebra.map_injective hφ
  rw [StarSubalgebra.map_sup, StarSubalgebra.map_map, StarSubalgebra.map_map, hleft, hright,
    himage, range_image_evenPair_eq_adjacentSupportJoin hω x]
  rfl

end PropagatesWithin
end SpinChain
