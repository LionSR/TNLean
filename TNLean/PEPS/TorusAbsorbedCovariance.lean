import TNLean.PEPS.RegionTransferCovariance
import TNLean.PEPS.RegionBlock.AbsorbedEquality

/-!
# Translation covariance of the orientation-adapted absorbing gauge

The bare-edge absorbed equality of the normal PEPS Fundamental Theorem on the torus is realized
by the orientation-adapted absorbing gauge `absorbedBoundaryGauge` of a transported reference
witness (arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1544 of
`Papers/1804.04964/paper_normal.tex`).  This file records how those absorbing gauges at two
translates of one reference witness determine each other: the gauge at the farther translate is
the gauge at the nearer one carried across the bond-dimension equality, *transposed-inverted*
exactly when the connecting translation swaps the ordered endpoints of the edge
(`transportedAbsorbedGauge_translate_pair`).

The orientation flip is forced by the edge convention: an edge stores its endpoints in
increasing order, and a wraparound translation may exchange them.  The absorbing gauge reads its
branch off the membership of the *first* stored endpoint in the witness region, so an endpoint
swap toggles the branch, replacing the absorbing matrix by its transposed inverse --- the matrix
that makes the oriented endpoint gauge action (`edgeGaugeAt`) assign the same two matrices to
the same two geometric endpoints.  A family with this covariance
(`IsTranslationCovariantGaugeFamily`) is the faithful torus form of the source's *"the same
matrix on all horizontal (vertical) edges"*: one reference matrix, transported to every edge of
the class with the orientation of the edge convention accounted for.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1544
  of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-! ### Transport of an invertible matrix across a reflexive index equality -/

/-- Transport of an invertible matrix across a reflexive index-size equality is the identity. -/
theorem glReindex_self {m : ℕ} (h : m = m) (Z : GL (Fin m) ℂ) :
    glReindex h Z = Z := by
  ext : 1
  rw [glReindex_coe]
  simp

/-! ### Composition of torus translations on edges -/

/-- The edge action of two successive torus translations is the edge action of their composite
translation: pushing an edge through `(a, b)` and then `(c, g)` lands on its `(a + c, b + g)`
translate. -/
theorem translateEdge_translateEdge (a c : ZMod width) (b g : ZMod height)
    (e : Edge (torusGraph width height)) :
    Edge.map (translate c g) (Edge.map (translate a b) e) =
      Edge.map (translate (a + c) (b + g)) e := by
  apply Edge.ofAdj_eq_of_endpoints
  rcases Edge.map_endpoints (translate (a + c) (b + g)) e with ⟨o1, o2⟩ | ⟨o1, o2⟩ <;>
    rcases Edge.map_endpoints (translate a b) e with ⟨p1, p2⟩ | ⟨p1, p2⟩
  · exact Or.inl ⟨by rw [p1, o1]; apply Prod.ext <;> simp <;> ring,
      by rw [p2, o2]; apply Prod.ext <;> simp <;> ring⟩
  · exact Or.inr ⟨by rw [p1, o2]; apply Prod.ext <;> simp <;> ring,
      by rw [p2, o1]; apply Prod.ext <;> simp <;> ring⟩
  · exact Or.inr ⟨by rw [p1, o2]; apply Prod.ext <;> simp <;> ring,
      by rw [p2, o1]; apply Prod.ext <;> simp <;> ring⟩
  · exact Or.inl ⟨by rw [p1, o1]; apply Prod.ext <;> simp <;> ring,
      by rw [p2, o2]; apply Prod.ext <;> simp <;> ring⟩

/-! ### Rigidity of the translation parameter on an orientation class

For widths and heights above two, a right (up) edge determines its left (lower) endpoint, so the
translation carrying one fixed reference edge to a given edge of its orientation class is unique.
This is the bookkeeping that identifies the per-edge choice of translation made by the gauge
family with any other translation reaching the same edge. -/

/-- For `2 < width`, distinct left endpoints give distinct right edges. -/
theorem torusRightEdge_injective (hw : 2 < width) {p q : TorusVertex width height}
    (h : torusRightEdge p = torusRightEdge q) : p = q := by
  have h20 : ((2 : ℕ) : ZMod width) ≠ 0 := by
    intro hcon
    rw [ZMod.natCast_eq_zero_iff] at hcon
    have := Nat.le_of_dvd (by norm_num) hcon
    omega
  have hp := Edge.ofAdj_endpoints (torusGraph_adj_right p.1 p.2)
  have hq := Edge.ofAdj_endpoints (torusGraph_adj_right q.1 q.2)
  rw [show Edge.ofAdj (torusGraph_adj_right p.1 p.2) = torusRightEdge q from h] at hp
  rw [show Edge.ofAdj (torusGraph_adj_right q.1 q.2) = torusRightEdge q from rfl] at hq
  simp only [Prod.mk.eta] at hp hq
  rcases hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ <;> rcases hq with ⟨hq1, hq2⟩ | ⟨hq1, hq2⟩
  · exact hp1.symm.trans hq1
  · -- `p = q + (1, 0)` and `p + (1, 0) = q`, so `2 = 0` in `ZMod width`.
    exfalso
    have e1 : p.1 = q.1 + 1 := congrArg Prod.fst (hp1.symm.trans hq1)
    have e2 : p.1 + 1 = q.1 := congrArg Prod.fst (hp2.symm.trans hq2)
    refine h20 (add_left_cancel (a := q.1) (b := ((2 : ℕ) : ZMod width)) (c := 0) ?_)
    push_cast
    linear_combination e2 - e1
  · exfalso
    have e1 : p.1 + 1 = q.1 := congrArg Prod.fst (hp1.symm.trans hq1)
    have e2 : p.1 = q.1 + 1 := congrArg Prod.fst (hp2.symm.trans hq2)
    refine h20 (add_left_cancel (a := q.1) (b := ((2 : ℕ) : ZMod width)) (c := 0) ?_)
    push_cast
    linear_combination e1 - e2
  · exact hp2.symm.trans hq2

/-- For `2 < height`, distinct lower endpoints give distinct up edges. -/
theorem torusUpEdge_injective (hh : 2 < height) {p q : TorusVertex width height}
    (h : torusUpEdge p = torusUpEdge q) : p = q := by
  have h20 : ((2 : ℕ) : ZMod height) ≠ 0 := by
    intro hcon
    rw [ZMod.natCast_eq_zero_iff] at hcon
    have := Nat.le_of_dvd (by norm_num) hcon
    omega
  have hp := Edge.ofAdj_endpoints (torusGraph_adj_up p.1 p.2)
  have hq := Edge.ofAdj_endpoints (torusGraph_adj_up q.1 q.2)
  rw [show Edge.ofAdj (torusGraph_adj_up p.1 p.2) = torusUpEdge q from h] at hp
  rw [show Edge.ofAdj (torusGraph_adj_up q.1 q.2) = torusUpEdge q from rfl] at hq
  simp only [Prod.mk.eta] at hp hq
  rcases hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ <;> rcases hq with ⟨hq1, hq2⟩ | ⟨hq1, hq2⟩
  · exact hp1.symm.trans hq1
  · exfalso
    have e1 : p.2 = q.2 + 1 := congrArg Prod.snd (hp1.symm.trans hq1)
    have e2 : p.2 + 1 = q.2 := congrArg Prod.snd (hp2.symm.trans hq2)
    refine h20 (add_left_cancel (a := q.2) (b := ((2 : ℕ) : ZMod height)) (c := 0) ?_)
    push_cast
    linear_combination e2 - e1
  · exfalso
    have e1 : p.2 + 1 = q.2 := congrArg Prod.snd (hp1.symm.trans hq1)
    have e2 : p.2 = q.2 + 1 := congrArg Prod.snd (hp2.symm.trans hq2)
    refine h20 (add_left_cancel (a := q.2) (b := ((2 : ℕ) : ZMod height)) (c := 0) ?_)
    push_cast
    linear_combination e1 - e2
  · exact hp2.symm.trans hq2

/-- For `2 < width`, the translation carrying a right edge to a given edge is unique. -/
theorem translate_param_unique_right (hw : 2 < width) (p : TorusVertex width height)
    {a a' : ZMod width} {b b' : ZMod height}
    (h : Edge.map (translate a b) (torusRightEdge p) =
      Edge.map (translate a' b') (torusRightEdge p)) :
    a = a' ∧ b = b' := by
  rw [← translateEdge_eq_map, ← translateEdge_eq_map, translateEdge_torusRightEdge,
    translateEdge_torusRightEdge] at h
  have := torusRightEdge_injective hw h
  exact ⟨add_left_cancel (congrArg Prod.fst this), add_left_cancel (congrArg Prod.snd this)⟩

/-- For `2 < height`, the translation carrying an up edge to a given edge is unique. -/
theorem translate_param_unique_up (hh : 2 < height) (p : TorusVertex width height)
    {a a' : ZMod width} {b b' : ZMod height}
    (h : Edge.map (translate a b) (torusUpEdge p) =
      Edge.map (translate a' b') (torusUpEdge p)) :
    a = a' ∧ b = b' := by
  rw [← translateEdge_eq_map, ← translateEdge_eq_map, translateEdge_torusUpEdge,
    translateEdge_torusUpEdge] at h
  have := torusUpEdge_injective hh h
  exact ⟨add_left_cancel (congrArg Prod.fst this), add_left_cancel (congrArg Prod.snd this)⟩

/-! ### The endpoint geometry of a translated boundary edge -/

/-- A boundary edge whose first stored endpoint lies in the region has its second stored
endpoint outside the region. -/
theorem boundary_snd_notMem {R : Finset (TorusVertex width height)}
    {f : Edge (torusGraph width height)}
    (hf : IsRegionBoundaryEdge (G := torusGraph width height) R f) (hmem : f.1.1 ∈ R) :
    f.1.2 ∉ R := by
  rcases hf with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact h2
  · exact absurd hmem h1

/-- The first stored endpoint of a translated boundary edge is the translate of one of the two
stored endpoints of the original edge. -/
theorem boundaryEdgeMap_translate_fst_or
    (R : Finset (TorusVertex width height))
    (f : {f : Edge (torusGraph width height) //
      IsRegionBoundaryEdge (G := torusGraph width height) R f})
    (a : ZMod width) (b : ZMod height) :
    (boundaryEdgeMap (translate a b) R f).1.1.1 = translate a b f.1.1.1 ∨
      (boundaryEdgeMap (translate a b) R f).1.1.1 = translate a b f.1.1.2 := by
  rw [boundaryEdgeMap_coe]
  rcases Edge.map_endpoints (translate a b) f.1 with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact Or.inl h1
  · exact Or.inr h1

/-- **Membership reads orientation.**  For a boundary edge whose first stored endpoint lies in
the region, the first stored endpoint of any translate of the edge lies in the translated region
exactly when the translation preserved the stored endpoint order. -/
theorem boundaryEdgeMap_translate_fst_mem_iff
    (R : Finset (TorusVertex width height))
    (f : {f : Edge (torusGraph width height) //
      IsRegionBoundaryEdge (G := torusGraph width height) R f})
    (hmem : f.1.1.1 ∈ R) (a : ZMod width) (b : ZMod height) :
    (boundaryEdgeMap (translate a b) R f).1.1.1 ∈ Region.map (translate a b) R ↔
      (boundaryEdgeMap (translate a b) R f).1.1.1 = translate a b f.1.1.1 := by
  have hne : f.1.1.1 ≠ f.1.1.2 := ne_of_lt f.1.2.1
  rcases boundaryEdgeMap_translate_fst_or R f a b with h | h
  · rw [h]
    simp only [mem_Region_map_apply, hmem]
  · rw [h]
    constructor
    · intro hmem2
      rw [mem_Region_map_apply] at hmem2
      exact absurd hmem2 (boundary_snd_notMem f.2 hmem)
    · intro heq
      exact absurd ((translate a b).toEquiv.injective heq).symm hne

/-! ### The transported absorbing gauge and its translation covariance -/

/-- The orientation-adapted absorbing gauge of the `(a, b)`-translate of a reference witness:
the absorbing gauge (`absorbedBoundaryGauge`) of the translated region at the translated
boundary edge, applied to the reference gauge `Z` carried across the bond-dimension equality of
the translation-invariant second tensor.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def transportedAbsorbedGauge (B : Tensor (torusGraph width height) d)
    (hB : IsTorusTranslationInvariant B)
    (R : Finset (TorusVertex width height))
    (f : {f : Edge (torusGraph width height) //
      IsRegionBoundaryEdge (G := torusGraph width height) R f})
    (Z : GL (Fin (B.bondDim f.1)) ℂ) (a : ZMod width) (b : ZMod height) :
    GL (Fin (B.bondDim (boundaryEdgeMap (translate a b) R f).1)) ℂ :=
  absorbedBoundaryGauge (G := torusGraph width height) B (Region.map (translate a b) R)
    (boundaryEdgeMap (translate a b) R f)
    (glReindex (bondDim_boundaryEdgeMap_translate hB a b R f).symm Z)

/-- The reference gauge transported to the `(a', b')`-translate is the reference gauge
transported to the `(a, b)`-translate carried across the bond-dimension equality between the two
translated edges. -/
theorem glReindex_glReindex_bondDim
    {B : Tensor (torusGraph width height) d} (hB : IsTorusTranslationInvariant B)
    (R : Finset (TorusVertex width height))
    (f : {f : Edge (torusGraph width height) //
      IsRegionBoundaryEdge (G := torusGraph width height) R f})
    (Z : GL (Fin (B.bondDim f.1)) ℂ) (a a' : ZMod width) (b b' : ZMod height)
    (h : B.bondDim (boundaryEdgeMap (translate a b) R f).1 =
      B.bondDim (boundaryEdgeMap (translate a' b') R f).1) :
    glReindex (bondDim_boundaryEdgeMap_translate hB a' b' R f).symm Z =
      glReindex h (glReindex (bondDim_boundaryEdgeMap_translate hB a b R f).symm Z) := by
  rw [glReindex_glReindex]

/-- **Translation covariance of the transported absorbing gauge.**

The absorbing gauges of two translates of one reference witness determine each other: if the
translation `(c, g)` carries the `(a, b)`-translate of the reference boundary edge onto the
`(a', b')`-translate pointwise on the two stored endpoints, then the absorbing gauge at
`(a', b')` is the absorbing gauge at `(a, b)` carried across the bond-dimension equality when
the stored endpoint order is preserved, and its transposed inverse when the order is swapped.

This is the faithful torus form of the source's single horizontal (vertical) matrix: one
reference gauge, transported to every translate, with the wraparound endpoint swap of the edge
convention accounted for by the transposed inverse.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem transportedAbsorbedGauge_translate_pair
    (B : Tensor (torusGraph width height) d) (hB : IsTorusTranslationInvariant B)
    (R : Finset (TorusVertex width height))
    (f : {f : Edge (torusGraph width height) //
      IsRegionBoundaryEdge (G := torusGraph width height) R f})
    (Z : GL (Fin (B.bondDim f.1)) ℂ) (hmem : f.1.1.1 ∈ R)
    (a a' c : ZMod width) (b b' g : ZMod height)
    (hsu : translate c g (translate a b f.1.1.1) = translate a' b' f.1.1.1)
    (hsv : translate c g (translate a b f.1.1.2) = translate a' b' f.1.1.2)
    (h : B.bondDim (boundaryEdgeMap (translate a b) R f).1 =
      B.bondDim (boundaryEdgeMap (translate a' b') R f).1) :
    (transportedAbsorbedGauge B hB R f Z a' b' :
        Matrix (Fin (B.bondDim (boundaryEdgeMap (translate a' b') R f).1))
          (Fin (B.bondDim (boundaryEdgeMap (translate a' b') R f).1)) ℂ) =
      if (boundaryEdgeMap (translate a' b') R f).1.1.1 =
          translate c g (boundaryEdgeMap (translate a b) R f).1.1.1 then
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr h)
          (transportedAbsorbedGauge B hB R f Z a b :
            Matrix (Fin (B.bondDim (boundaryEdgeMap (translate a b) R f).1))
              (Fin (B.bondDim (boundaryEdgeMap (translate a b) R f).1)) ℂ)
      else
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr h)
          ((↑(transportedAbsorbedGauge B hB R f Z a b)⁻¹ :
            Matrix (Fin (B.bondDim (boundaryEdgeMap (translate a b) R f).1))
              (Fin (B.bondDim (boundaryEdgeMap (translate a b) R f).1)) ℂ)ᵀ) := by
  classical
  have hne : f.1.1.1 ≠ f.1.1.2 := ne_of_lt f.1.2.1
  -- Abbreviate the two transported reference gauges.
  set Zs := glReindex (bondDim_boundaryEdgeMap_translate hB a b R f).symm Z with hZs
  set Zs' := glReindex (bondDim_boundaryEdgeMap_translate hB a' b' R f).symm Z with hZs'
  have hZrel : Zs' = glReindex h Zs := by
    rw [hZs, hZs']
    exact glReindex_glReindex_bondDim hB R f Z a a' b b' h
  -- The two orientation conditions.
  have hPiff := boundaryEdgeMap_translate_fst_mem_iff R f hmem a b
  have hPiff' := boundaryEdgeMap_translate_fst_mem_iff R f hmem a' b'
  rw [transportedAbsorbedGauge, transportedAbsorbedGauge, absorbedBoundaryGauge,
    absorbedBoundaryGauge, ← hZs, ← hZs']
  by_cases hP : (boundaryEdgeMap (translate a b) R f).1.1.1 ∈ Region.map (translate a b) R <;>
    by_cases hP' :
      (boundaryEdgeMap (translate a' b') R f).1.1.1 ∈ Region.map (translate a' b') R
  · -- Both orders preserved: the connecting translation preserves the order.
    have hQ : (boundaryEdgeMap (translate a' b') R f).1.1.1 =
        translate c g (boundaryEdgeMap (translate a b) R f).1.1.1 := by
      rw [hPiff'.mp hP', hPiff.mp hP, hsu]
    rw [if_pos hP, if_pos hP', if_pos hQ, hZrel]
    rw [glTranspose_coe, glTranspose_coe, glReindex_coe, reindexAlgEquiv_transpose]
  · -- Order preserved at `(a, b)`, swapped at `(a', b')`: the connecting translation swaps.
    have hQ : ¬((boundaryEdgeMap (translate a' b') R f).1.1.1 =
        translate c g (boundaryEdgeMap (translate a b) R f).1.1.1) := by
      have hfst' : (boundaryEdgeMap (translate a' b') R f).1.1.1 =
          translate a' b' f.1.1.2 :=
        (boundaryEdgeMap_translate_fst_or R f a' b').resolve_left (fun hcon => hP' (by
          rw [hPiff']; exact hcon))
      rw [hfst', hPiff.mp hP, hsu]
      intro hcon
      exact hne ((translate a' b').toEquiv.injective hcon).symm
    rw [if_pos hP, if_neg hP', if_neg hQ, hZrel]
    rw [glTranspose_inv_coe, Matrix.transpose_transpose, ← map_inv, glReindex_coe,
      Matrix.GeneralLinearGroup.coe_inv]
  · -- Order swapped at `(a, b)`, preserved at `(a', b')`: the connecting translation swaps.
    have hQ : ¬((boundaryEdgeMap (translate a' b') R f).1.1.1 =
        translate c g (boundaryEdgeMap (translate a b) R f).1.1.1) := by
      have hfst : (boundaryEdgeMap (translate a b) R f).1.1.1 = translate a b f.1.1.2 :=
        (boundaryEdgeMap_translate_fst_or R f a b).resolve_left (fun hcon => hP (by
          rw [hPiff]; exact hcon))
      rw [hfst, hPiff'.mp hP', hsv]
      intro hcon
      exact hne ((translate a' b').toEquiv.injective hcon)
    rw [if_neg hP, if_pos hP', if_neg hQ, hZrel]
    rw [glTranspose_coe, Matrix.GeneralLinearGroup.coe_inv, Matrix.GeneralLinearGroup.coe_inv,
      Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp Zs.isUnit),
      glReindex_coe, reindexAlgEquiv_transpose]
  · -- Both orders swapped: the connecting translation preserves the order.
    have hQ : (boundaryEdgeMap (translate a' b') R f).1.1.1 =
        translate c g (boundaryEdgeMap (translate a b) R f).1.1.1 := by
      have hfst : (boundaryEdgeMap (translate a b) R f).1.1.1 = translate a b f.1.1.2 :=
        (boundaryEdgeMap_translate_fst_or R f a b).resolve_left (fun hcon => hP (by
          rw [hPiff]; exact hcon))
      have hfst' : (boundaryEdgeMap (translate a' b') R f).1.1.1 =
          translate a' b' f.1.1.2 :=
        (boundaryEdgeMap_translate_fst_or R f a' b').resolve_left (fun hcon => hP' (by
          rw [hPiff']; exact hcon))
      rw [hfst, hfst', hsv]
    rw [if_neg hP, if_neg hP', if_pos hQ, hZrel]
    rw [← map_inv, glReindex_coe]

/-! ### Translation-covariant gauge families -/

/-- A per-edge gauge family over the bonds of a translation-invariant tensor is **translation
covariant** when the gauge at any translate of an edge is the gauge at the edge carried across
the bond-dimension equality, transposed-inverted exactly when the translation swaps the stored
endpoint order.  This is the faithful torus form of the source's *"the same matrix `X` (`Y`) on
all horizontal (vertical) edges"*, with the wraparound endpoint swap of the ordered edge
convention accounted for.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`. -/
def IsTranslationCovariantGaugeFamily (B : Tensor (torusGraph width height) d)
    (X : (e : Edge (torusGraph width height)) → GL (Fin (B.bondDim e)) ℂ) : Prop :=
  ∀ (a : ZMod width) (b : ZMod height) (e : Edge (torusGraph width height))
    (h : B.bondDim e = B.bondDim (Edge.map (translate a b) e)),
    (X (Edge.map (translate a b) e) :
        Matrix (Fin (B.bondDim (Edge.map (translate a b) e)))
          (Fin (B.bondDim (Edge.map (translate a b) e))) ℂ) =
      if (Edge.map (translate a b) e).1.1 = translate a b e.1.1 then
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr h)
          (X e : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ)
      else
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr h)
          ((↑(X e)⁻¹ : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ)ᵀ)

end PEPS
end TNLean
