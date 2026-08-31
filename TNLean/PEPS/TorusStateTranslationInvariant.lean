/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.FundamentalTheorem
import TNLean.PEPS.TorusTranslationInvariant

/-!
# Translation-invariant torus states have orientation-uniform bond dimensions

The Applications section of arXiv:1804.04964 considers a possibly site-dependent
injective PEPS whose represented state, rather than its tensor family, is
translation invariant.  Its two-dimensional corollary first concludes that all
horizontal bond dimensions agree and all vertical bond dimensions agree.

This file proves exactly that first conclusion.  Translation invariance of the
state identifies the tensor with each translated transport at the level of state
coefficients.  Vertex injectivity is preserved by transport, so the
virtual-operation algebra isomorphism from the proof of the injective PEPS
Fundamental Theorem forces equality of the corresponding bond dimensions.
Transitivity of torus translations on each orientation class then gives one
horizontal and one vertical dimension.

No site-independent tensor is constructed here.  The source states that second
conclusion without a two-dimensional proof; its unresolved status is recorded
in `docs/paper-gaps/peps_normal_ft_section3_route.tex`.

**Local fix (positive virtual spaces):** The paper's virtual bond spaces have
positive dimension, whereas `Tensor.bondDim` can take the value zero.  The
bond-uniformity theorems below therefore state positivity explicitly.  This
convention and the zero-dimensional obstruction are documented in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`.

## Reference

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Applications section, lines 1801 and 1891--1894 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964).
-/

namespace TNLean
namespace PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- A torus PEPS represents a translation-invariant state when every state
coefficient is unchanged after precomposition of the physical configuration
with a torus translation.

This is weaker than `IsTorusTranslationInvariant A`: the local tensor family
may depend on the site even though its contracted state is translation
invariant.

Source: arXiv:1804.04964, Applications section, lines 1801 and 1891--1894 of
`Papers/1804.04964/paper_normal.tex`. -/
def IsTorusTranslationInvariantState
    (A : Tensor (torusGraph width height) d) : Prop :=
  ∀ (a : ZMod width) (b : ZMod height)
    (σ : TorusVertex width height → Fin d),
    stateCoeff A (fun v ↦ σ (translate a b v)) = stateCoeff A σ

/-- A translation-invariant torus tensor represents a translation-invariant
state.

Source: arXiv:1804.04964, Applications section, lines 1801 and 1891--1894 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem IsTorusTranslationInvariant.isTorusTranslationInvariantState
    {A : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) :
    IsTorusTranslationInvariantState A :=
  fun a b σ ↦ stateCoeff_translationInvariant hA a b σ

/-- State translation invariance identifies a tensor with its transported
translate at the level of all state coefficients.

Source: arXiv:1804.04964, Applications section, lines 1801 and 1891--1894 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem sameState_transport_of_isTorusTranslationInvariantState
    {A : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariantState A)
    (a : ZMod width) (b : ZMod height) :
    SameState A (A.transport (translate a b)) := by
  intro σ
  rw [stateCoeff_transport]
  exact (hA a b σ).symm

/-- For an injective PEPS with positive virtual spaces, translation invariance
of the represented state forces the bond dimension at every translated edge
to equal the original bond dimension.

The proof uses only the virtual-operation algebra isomorphism from the proof of
the injective PEPS Fundamental Theorem.  It does not require a choice of gauge
or a connectivity argument.

Source: arXiv:1804.04964, Applications section, lines 1801 and 1891--1894 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem bondDim_translateEdge_of_isTorusTranslationInvariantState
    {A : Tensor (torusGraph width height) d}
    (hInj : IsVertexInjective A)
    (hTI : IsTorusTranslationInvariantState A)
    (hpos : ∀ e : Edge (torusGraph width height), 0 < A.bondDim e)
    (a : ZMod width) (b : ZMod height)
    (e : Edge (torusGraph width height)) :
    A.bondDim (translateEdge a b e) = A.bondDim e := by
  let φ := translate a b
  have hInjTransport : IsVertexInjective (A.transport φ) :=
    hInj.transport φ
  have hposTransport :
      ∀ f : Edge (torusGraph width height), 0 < (A.transport φ).bondDim f := by
    intro f
    simpa only [Tensor.transport_bondDim] using hpos (Edge.map φ.symm f)
  have hDim : A.bondDim = (A.transport φ).bondDim :=
    bondDim_eq_of_isVertexInjective_sameState A (A.transport φ)
      hInj hInjTransport
      (sameState_transport_of_isTorusTranslationInvariantState hTI a b)
      hpos hposTransport
  rw [translateEdge_eq_map]
  have h := congrFun hDim (Edge.map φ e)
  simpa only [Tensor.transport_bondDim, Edge.map_symm_map] using h

/-- The horizontal bond dimension of an injective translation-invariant state
is independent of the left endpoint of the edge.

Source: arXiv:1804.04964, Applications section, lines 1801 and 1891--1894 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem bondDim_torusRightEdge_const_of_isTorusTranslationInvariantState
    {A : Tensor (torusGraph width height) d}
    (hInj : IsVertexInjective A)
    (hTI : IsTorusTranslationInvariantState A)
    (hpos : ∀ e : Edge (torusGraph width height), 0 < A.bondDim e)
    (p p' : TorusVertex width height) :
    A.bondDim (torusRightEdge p') = A.bondDim (torusRightEdge p) :=
  bondDim_torusRightEdge_const_of_translate A.bondDim
    (bondDim_translateEdge_of_isTorusTranslationInvariantState hInj hTI hpos)
    p p'

/-- The vertical bond dimension of an injective translation-invariant state is
independent of the lower endpoint of the edge.

Source: arXiv:1804.04964, Applications section, lines 1801 and 1891--1894 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem bondDim_torusUpEdge_const_of_isTorusTranslationInvariantState
    {A : Tensor (torusGraph width height) d}
    (hInj : IsVertexInjective A)
    (hTI : IsTorusTranslationInvariantState A)
    (hpos : ∀ e : Edge (torusGraph width height), 0 < A.bondDim e)
    (p p' : TorusVertex width height) :
    A.bondDim (torusUpEdge p') = A.bondDim (torusUpEdge p) :=
  bondDim_torusUpEdge_const_of_translate A.bondDim
    (bondDim_translateEdge_of_isTorusTranslationInvariantState hInj hTI hpos)
    p p'

/-- **An injective PEPS representing a translation-invariant state has
orientation-uniform bond dimensions.**

All horizontal bond dimensions equal the dimension at the reference right
edge, and all vertical bond dimensions equal the dimension at the reference up
edge.  This is the first conclusion of the two-dimensional
Applications-section corollary.

Source: arXiv:1804.04964, Applications section, lines 1801 and 1891--1894 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem torusUniformBondDim_of_isTorusTranslationInvariantState
    {A : Tensor (torusGraph width height) d}
    (hInj : IsVertexInjective A)
    (hTI : IsTorusTranslationInvariantState A)
    (hpos : ∀ e : Edge (torusGraph width height), 0 < A.bondDim e) :
    TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)) :=
  torusUniformBondDim_of_translate A.bondDim
    (bondDim_translateEdge_of_isTorusTranslationInvariantState hInj hTI hpos)

end PEPS
end TNLean
