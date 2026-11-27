/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Graph.Torus.TorusTranslation
import TNLean.PEPS.Tensor.Network.IsoTransport
import TNLean.PEPS.Tensor.Region.RegionTransport

/-!
# Translation-invariant PEPS tensors on the torus

A PEPS on the discrete torus (`TNLean/PEPS/TorusLatticeGraph.lean`) is
**translation invariant** when it is fixed by transport along every translation
automorphism: `A.transport (translate a b) = A` for all coordinate offsets
`(a, b)`.  This is the faithful formalization of the source's setting, where one
tensor is repeated at every site of a lattice on which translation is a symmetry
(arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1572 of
`Papers/1804.04964/paper_normal.tex`).

Translation invariance has two consequences used by the source's gauge reduction.
First, the state coefficient is invariant under the precomposed translation of the
physical configuration (`stateCoeff_translationInvariant`).  Second, the bond
dimension at any edge equals the bond dimension at every translate of that edge
(`bondDim_translateEdge_of_translationInvariant`); since the translations act
transitively on each orientation class — every horizontal edge is the translate of
every other, and likewise for vertical edges — this is the constant-bond content
that makes the reduction to one horizontal and one vertical matrix well-defined.  The
transitivity is supported by the normal-form characterization
`isHorizontalTorusEdge_eq_rightEdge` of `TNLean/PEPS/Graph/Torus/TorusLatticeGraph.lean`,
writing each horizontal edge as the right edge of its left endpoint; the full
orientation-class constancy is `TorusUniformBondDim` below, recorded in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`, remaining obligation 6.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 1407--1572 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open ManyBody (Edge)

open scoped BigOperators

namespace TNLean
namespace PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- A PEPS tensor on the torus is **translation invariant** when it is fixed by
transport along every translation automorphism.  This is the faithful statement of
the source's setting: one tensor repeated at every site, with translation a
symmetry of the network.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1452 of
`Papers/1804.04964/paper_normal.tex`. -/
def IsTorusTranslationInvariant (A : Tensor (torusGraph width height) d) : Prop :=
  ∀ (a : ZMod width) (b : ZMod height), A.transport (translate a b) = A

/-- Blocked-region injectivity of a translation-invariant tensor transports to every translated
region. -/
theorem regionBlockedTensorInjective_translate {T : Tensor (torusGraph width height) d}
    (hT : IsTorusTranslationInvariant T) (a : ZMod width) (b : ZMod height)
    (R : Finset (TorusVertex width height))
    (h : RegionBlockedTensorInjective (G := torusGraph width height) T R) :
    RegionBlockedTensorInjective (G := torusGraph width height) T
      (Region.map (translate a b) R) := by
  have htr := (regionBlockedTensorInjective_transport T (translate a b) R).mpr h
  rwa [hT a b] at htr

/-- The edge action of the translation `(a, b)` coincides with the edge action of
the translation automorphism `translate a b`: both push the endpoints through the
translation and reorder them into the `Edge` convention. -/
theorem translateEdge_eq_map (a : ZMod width) (b : ZMod height)
    (e : Edge (torusGraph width height)) :
    translateEdge a b e = ManyBody.Edge.map (translate a b) e :=
  rfl

/-- The state coefficient of a translation-invariant tensor is invariant under the
translation of the physical configuration: shifting `σ` by a translation leaves the
coefficient unchanged.  This is the physical-level statement of translation
invariance, obtained from `stateCoeff_transport` and the defining fixed-point
equation.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1572 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem stateCoeff_translationInvariant {A : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (a : ZMod width) (b : ZMod height)
    (σ : TorusVertex width height → Fin d) :
    stateCoeff A (fun v => σ (translate a b v)) = stateCoeff A σ := by
  have h := hA a b
  calc stateCoeff A (fun v => σ (translate a b v))
      = stateCoeff (A.transport (translate a b)) σ := (stateCoeff_transport A _ σ).symm
    _ = stateCoeff A σ := by rw [h]

/-! ### Constant bond dimension on each orientation class

A translation-invariant tensor has the same bond dimension on all horizontal edges
and the same bond dimension on all vertical edges.  The translation moving one
horizontal edge to another carries the bond dimension across, so within each
orientation class the bond dimension is constant.  This is the constant-bond
consequence of translation invariance, recorded below as `TorusUniformBondDim`. -/

/-- The bond dimension of a translation-invariant tensor at the translate of an
edge equals the bond dimension at the original edge.  Transport invariance gives
`A.bondDim (translateEdge a b e) = A.bondDim e` after reindexing through the edge
action.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem bondDim_translateEdge_of_translationInvariant
    {A : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (a : ZMod width) (b : ZMod height)
    (e : Edge (torusGraph width height)) :
    A.bondDim (translateEdge a b e) = A.bondDim e := by
  have h := hA a b
  have hb : (A.transport (translate a b)).bondDim (translateEdge a b e) =
      A.bondDim (translateEdge a b e) := by rw [h]
  rw [Tensor.transport_bondDim] at hb
  rw [← hb]
  congr 1
  -- Edge.map (translate a b).symm (translateEdge a b e) = e
  change ManyBody.Edge.map (translate a b).symm (ManyBody.Edge.map (translate a b) e) = e
  exact ManyBody.Edge.map_symm_map (translate a b) e

/-! ### Transitivity of translations on each orientation class

Translation carries the right edge of `p` to the right edge of the translated
point, and likewise for up edges.  Hence any two horizontal edges (any two
vertical edges) are related by a translation, so a translation-invariant tensor has
the same bond dimension throughout each orientation class. -/

/-- Translation carries the right edge of `p` to the right edge of `p + (a, b)`. -/
theorem translateEdge_torusRightEdge (a : ZMod width) (b : ZMod height)
    (p : TorusVertex width height) :
    translateEdge a b (torusRightEdge p) = torusRightEdge (p.1 + a, p.2 + b) := by
  rw [torusRightEdge, torusRightEdge, translateEdge_eq_map, ManyBody.Edge.map]
  apply ManyBody.Edge.ofAdj_eq_ofAdj
  rcases ManyBody.Edge.ofAdj_endpoints (torusGraph_adj_right p.1 p.2) with ⟨o1, o2⟩ | ⟨o1, o2⟩
  · exact Or.inl ⟨by rw [o1]; apply Prod.ext <;> simp [translate_apply],
      by rw [o2]; apply Prod.ext <;> simp [translate_apply]; ring⟩
  · exact Or.inr ⟨by rw [o1]; apply Prod.ext <;> simp [translate_apply]; ring,
      by rw [o2]; apply Prod.ext <;> simp [translate_apply]⟩

/-- Translation carries the up edge of `p` to the up edge of `p + (a, b)`. -/
theorem translateEdge_torusUpEdge (a : ZMod width) (b : ZMod height)
    (p : TorusVertex width height) :
    translateEdge a b (torusUpEdge p) = torusUpEdge (p.1 + a, p.2 + b) := by
  rw [torusUpEdge, torusUpEdge, translateEdge_eq_map, ManyBody.Edge.map]
  apply ManyBody.Edge.ofAdj_eq_ofAdj
  rcases ManyBody.Edge.ofAdj_endpoints (torusGraph_adj_up p.1 p.2) with ⟨o1, o2⟩ | ⟨o1, o2⟩
  · exact Or.inl ⟨by rw [o1]; apply Prod.ext <;> simp [translate_apply],
      by rw [o2]; apply Prod.ext <;> simp [translate_apply]; ring⟩
  · exact Or.inr ⟨by rw [o1]; apply Prod.ext <;> simp [translate_apply]; ring,
      by rw [o2]; apply Prod.ext <;> simp [translate_apply]⟩

/-- A bond-dimension function invariant under torus translations is constant
on the horizontal edges.

This is the geometric transitivity argument shared by tensor-level and
state-level translation invariance.

Source: arXiv:1804.04964, the horizontal bond-dimension conclusion at lines
1891--1894 of `Papers/1804.04964/paper_normal.tex`. -/
theorem bondDim_torusRightEdge_const_of_translate
    (bondDim : Edge (torusGraph width height) → ℕ)
    (htranslate : ∀ (a : ZMod width) (b : ZMod height) e,
      bondDim (translateEdge a b e) = bondDim e)
    (p p' : TorusVertex width height) :
    bondDim (torusRightEdge p') = bondDim (torusRightEdge p) := by
  have key :
      translateEdge (p'.1 - p.1) (p'.2 - p.2) (torusRightEdge p) =
        torusRightEdge p' := by
    rw [translateEdge_torusRightEdge]
    congr 1
    apply Prod.ext <;> simp
  rw [← key]
  exact htranslate _ _ (torusRightEdge p)

/-- A bond-dimension function invariant under torus translations is constant
on the vertical edges.

This is the geometric transitivity argument shared by tensor-level and
state-level translation invariance.

Source: arXiv:1804.04964, the vertical bond-dimension conclusion at lines
1891--1894 of `Papers/1804.04964/paper_normal.tex`. -/
theorem bondDim_torusUpEdge_const_of_translate
    (bondDim : Edge (torusGraph width height) → ℕ)
    (htranslate : ∀ (a : ZMod width) (b : ZMod height) e,
      bondDim (translateEdge a b e) = bondDim e)
    (p p' : TorusVertex width height) :
    bondDim (torusUpEdge p') = bondDim (torusUpEdge p) := by
  have key :
      translateEdge (p'.1 - p.1) (p'.2 - p.2) (torusUpEdge p) =
        torusUpEdge p' := by
    rw [translateEdge_torusUpEdge]
    congr 1
    apply Prod.ext <;> simp
  rw [← key]
  exact htranslate _ _ (torusUpEdge p)

/-- A translation-invariant tensor has the same bond dimension on every
horizontal edge: the bond dimension of any right edge is independent of its
left endpoint.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem bondDim_torusRightEdge_const {A : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (p p' : TorusVertex width height) :
    A.bondDim (torusRightEdge p') = A.bondDim (torusRightEdge p) :=
  bondDim_torusRightEdge_const_of_translate A.bondDim
    (bondDim_translateEdge_of_translationInvariant hA) p p'

/-- A translation-invariant tensor has the same bond dimension on every vertical
edge: the bond dimension of any up edge is independent of its lower endpoint.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem bondDim_torusUpEdge_const {A : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (p p' : TorusVertex width height) :
    A.bondDim (torusUpEdge p') = A.bondDim (torusUpEdge p) :=
  bondDim_torusUpEdge_const_of_translate A.bondDim
    (bondDim_translateEdge_of_translationInvariant hA) p p'

/-! ### Constant bond dimension on each orientation class

The bond dimension of a translation-invariant tensor is `Dh` on every horizontal
edge and `Dv` on every vertical edge, where `Dh` and `Dv` are read off at a
reference edge of each class.  This is the constant-bond content that makes the
reduction to one horizontal and one vertical matrix well-defined.  The lattice has at
least one edge of each orientation, so the reference dimensions exist. -/

/-- The bond-dimension function of a tensor on the torus is **orientation uniform**
with horizontal dimension `Dh` and vertical dimension `Dv` when every horizontal
edge has bond dimension `Dh` and every vertical edge has bond dimension `Dv`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`. -/
def TorusUniformBondDim (bondDim : Edge (torusGraph width height) → ℕ) (Dh Dv : ℕ) : Prop :=
  (∀ e : Edge (torusGraph width height), IsHorizontalTorusEdge e → bondDim e = Dh) ∧
    (∀ e : Edge (torusGraph width height), IsVerticalTorusEdge e → bondDim e = Dv)

/-- A bond-dimension function invariant under torus translations is uniform
on each orientation class.

Source: arXiv:1804.04964, the orientation-wise bond-dimension conclusion at
lines 1891--1894 of `Papers/1804.04964/paper_normal.tex`. -/
theorem torusUniformBondDim_of_translate
    (bondDim : Edge (torusGraph width height) → ℕ)
    (htranslate : ∀ (a : ZMod width) (b : ZMod height) e,
      bondDim (translateEdge a b e) = bondDim e) :
    TorusUniformBondDim bondDim
      (bondDim (torusRightEdge 0)) (bondDim (torusUpEdge 0)) := by
  refine ⟨fun e he ↦ ?_, fun e he ↦ ?_⟩
  · obtain ⟨p, rfl⟩ := isHorizontalTorusEdge_eq_rightEdge he
    exact bondDim_torusRightEdge_const_of_translate bondDim htranslate 0 p
  · obtain ⟨p, rfl⟩ := isVerticalTorusEdge_eq_upEdge he
    exact bondDim_torusUpEdge_const_of_translate bondDim htranslate 0 p

/-- **A translation-invariant tensor has orientation-uniform bond dimensions.**

Reading off the horizontal dimension `Dh` at the right edge of the origin and the
vertical dimension `Dv` at the up edge of the origin, every horizontal edge has
bond dimension `Dh` and every vertical edge has bond dimension `Dv`.  Each edge is
the right edge (respectively up edge) of its endpoint by the normal form, and the
class constancy carries the reference dimension across.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`, where translation invariance makes the gauge
"the same matrix on all horizontal (vertical) edges". -/
theorem torusUniformBondDim_of_translationInvariant {A : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) :
    TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)) :=
  torusUniformBondDim_of_translate A.bondDim
    (bondDim_translateEdge_of_translationInvariant hA)

end PEPS
end TNLean
