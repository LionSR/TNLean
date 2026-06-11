import TNLean.PEPS.TorusTranslationInvariant
import TNLean.PEPS.EdgeGaugeFamily

/-!
# Orientation-uniform edge gauges on the torus

The translationally invariant normal PEPS theorem reduces the per-edge gauges produced by the
edge blocking to **one horizontal matrix `X` and one vertical matrix `Y`**
(arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498:
*"these gauges are described by the same matrix `X` (`Y`) on all horizontal (vertical) edges"*).

This file records that reduction on the discrete torus, mirroring the open-lattice carrier
`TNLean/PEPS/NormalSquareTI.lean`.  Given a torus tensor with orientation-uniform bond
dimensions (`TorusUniformBondDim`, available for any translation-invariant tensor), a single
horizontal matrix `Xh` and a single vertical matrix `Xv` determine a per-edge gauge family
`torusOrientationUniformGauge`.  A family of this shape is *orientation uniform*
(`IsTorusOrientationUniformGaugeFamily`); allowing per-edge nonzero scalars gives the
faithful target produced by the source's uniqueness-up-to-scalar step
(`IsTorusOrientationUniformGaugeFamilyModScalar`).

The torus has no boundary, so every edge is interior and the reduction reaches every edge,
unlike the open-lattice carrier whose interior restriction is recorded in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines
  1449--1572 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-! ### The orientation-uniform consequences of `TorusUniformBondDim` -/

/-- The horizontal-edge component of orientation uniformity. -/
theorem TorusUniformBondDim.horizontal
    {bondDim : Edge (torusGraph width height) → ℕ} {Dh Dv : ℕ}
    (h : TorusUniformBondDim bondDim Dh Dv)
    {e : Edge (torusGraph width height)} (he : IsHorizontalTorusEdge e) :
    bondDim e = Dh :=
  h.1 e he

/-- The vertical-edge component of orientation uniformity. -/
theorem TorusUniformBondDim.vertical
    {bondDim : Edge (torusGraph width height) → ℕ} {Dh Dv : ℕ}
    (h : TorusUniformBondDim bondDim Dh Dv)
    {e : Edge (torusGraph width height)} (he : IsVerticalTorusEdge e) :
    bondDim e = Dv :=
  h.2 e he

/-! ### The gauge family built from one horizontal and one vertical matrix -/

/-- The per-edge gauge family on the torus determined by a single horizontal matrix `Xh` and a
single vertical matrix `Xv`, transported to each edge across the uniform bond-dimension
equalities.  Every torus edge is horizontal or vertical
(`torusEdge_horizontal_or_vertical`); the horizontal branch transports `Xh`, the vertical
branch transports `Xv`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def torusOrientationUniformGauge
    {bondDim : Edge (torusGraph width height) → ℕ} {Dh Dv : ℕ}
    (huni : TorusUniformBondDim bondDim Dh Dv)
    (Xh : GL (Fin Dh) ℂ) (Xv : GL (Fin Dv) ℂ) :
    (e : Edge (torusGraph width height)) → GL (Fin (bondDim e)) ℂ :=
  fun e =>
    if he : IsHorizontalTorusEdge e then
      glReindex (huni.horizontal he).symm Xh
    else
      glReindex
        (huni.vertical ((torusEdge_horizontal_or_vertical e).resolve_left he)).symm Xv

/-- On a horizontal edge, the orientation-uniform gauge is `Xh` transported across the
bond-dimension equality. -/
theorem torusOrientationUniformGauge_horizontal
    {bondDim : Edge (torusGraph width height) → ℕ} {Dh Dv : ℕ}
    (huni : TorusUniformBondDim bondDim Dh Dv)
    (Xh : GL (Fin Dh) ℂ) (Xv : GL (Fin Dv) ℂ)
    {e : Edge (torusGraph width height)} (he : IsHorizontalTorusEdge e) :
    torusOrientationUniformGauge huni Xh Xv e = glReindex (huni.horizontal he).symm Xh := by
  rw [torusOrientationUniformGauge, dif_pos he]

/-- On a vertical edge, the orientation-uniform gauge is `Xv` transported across the
bond-dimension equality. -/
theorem torusOrientationUniformGauge_vertical
    {bondDim : Edge (torusGraph width height) → ℕ} {Dh Dv : ℕ}
    (huni : TorusUniformBondDim bondDim Dh Dv)
    (Xh : GL (Fin Dh) ℂ) (Xv : GL (Fin Dv) ℂ)
    {e : Edge (torusGraph width height)} (he : IsVerticalTorusEdge e) :
    torusOrientationUniformGauge huni Xh Xv e = glReindex (huni.vertical he).symm Xv := by
  have hnh : ¬ IsHorizontalTorusEdge e := fun hh =>
    torusEdge_not_horizontal_and_vertical e ⟨hh, he⟩
  rw [torusOrientationUniformGauge, dif_neg hnh]

/-! ### Orientation-uniform gauge families up to per-edge scalars -/

/-- A per-edge gauge family `X` on the torus is **orientation uniform** when there is a single
horizontal matrix and a single vertical matrix whose transported values reproduce `X` on every
edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498. -/
def IsTorusOrientationUniformGaugeFamily
    {bondDim : Edge (torusGraph width height) → ℕ} {Dh Dv : ℕ}
    (huni : TorusUniformBondDim bondDim Dh Dv)
    (X : (e : Edge (torusGraph width height)) → GL (Fin (bondDim e)) ℂ) : Prop :=
  ∃ (Xh : GL (Fin Dh) ℂ) (Xv : GL (Fin Dv) ℂ),
    X = torusOrientationUniformGauge huni Xh Xv

/-- A per-edge gauge family `X` is **orientation uniform up to scalars** when there are a single
horizontal matrix, a single vertical matrix, and a per-edge nonzero scalar `c` such that on
every edge `X e` is the transported orientation matrix rescaled by `c e`.  The per-edge scalars
are the residual multiplicative freedom recorded by Theorem 3's uniqueness up to a multiplicative
constant.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498. -/
def IsTorusOrientationUniformGaugeFamilyModScalar
    {bondDim : Edge (torusGraph width height) → ℕ} {Dh Dv : ℕ}
    (huni : TorusUniformBondDim bondDim Dh Dv)
    (X : (e : Edge (torusGraph width height)) → GL (Fin (bondDim e)) ℂ) : Prop :=
  ∃ (Xh : GL (Fin Dh) ℂ) (Xv : GL (Fin Dv) ℂ)
    (c : Edge (torusGraph width height) → ℂˣ),
    ∀ e : Edge (torusGraph width height),
      (X e : Matrix (Fin (bondDim e)) (Fin (bondDim e)) ℂ) =
        (c e : ℂ) • (torusOrientationUniformGauge huni Xh Xv e :
          Matrix (Fin (bondDim e)) (Fin (bondDim e)) ℂ)

/-- An orientation-uniform gauge family is orientation uniform up to scalars, with all scalars
equal to one. -/
theorem isTorusOrientationUniformGaugeFamilyModScalar_of_isUniform
    {bondDim : Edge (torusGraph width height) → ℕ} {Dh Dv : ℕ}
    {huni : TorusUniformBondDim bondDim Dh Dv}
    {X : (e : Edge (torusGraph width height)) → GL (Fin (bondDim e)) ℂ}
    (hX : IsTorusOrientationUniformGaugeFamily huni X) :
    IsTorusOrientationUniformGaugeFamilyModScalar huni X := by
  obtain ⟨Xh, Xv, rfl⟩ := hX
  exact ⟨Xh, Xv, fun _ => 1, fun e => by simp⟩

/-- **Orientation-uniform selection up to scalars on the torus.**

Suppose every per-edge gauge agrees, up to a nonzero scalar, with one reference horizontal
matrix on horizontal edges and one reference vertical matrix on vertical edges --- the per-edge
content delivered by the per-edge uniqueness across each orientation class under translation
invariance.  Then the whole gauge family is orientation uniform up to scalars.

This is the assembly step of the source's line-1498 reduction on the torus: it gathers the
per-edge "agree up to a constant" facts of the two orientation classes into one
orientation-uniform-up-to-scalar family.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isTorusOrientationUniformGaugeFamilyModScalar_of_classAgreement
    {bondDim : Edge (torusGraph width height) → ℕ} {Dh Dv : ℕ}
    (huni : TorusUniformBondDim bondDim Dh Dv)
    (X : (e : Edge (torusGraph width height)) → GL (Fin (bondDim e)) ℂ)
    (Xh : GL (Fin Dh) ℂ) (Xv : GL (Fin Dv) ℂ)
    (cH cV : Edge (torusGraph width height) → ℂˣ)
    (hH : ∀ (e : Edge (torusGraph width height)) (he : IsHorizontalTorusEdge e),
      (X e : Matrix (Fin (bondDim e)) (Fin (bondDim e)) ℂ) =
        (cH e : ℂ) • (glReindex (huni.horizontal he).symm Xh :
          Matrix (Fin (bondDim e)) (Fin (bondDim e)) ℂ))
    (hV : ∀ (e : Edge (torusGraph width height)) (he : IsVerticalTorusEdge e),
      (X e : Matrix (Fin (bondDim e)) (Fin (bondDim e)) ℂ) =
        (cV e : ℂ) • (glReindex (huni.vertical he).symm Xv :
          Matrix (Fin (bondDim e)) (Fin (bondDim e)) ℂ)) :
    IsTorusOrientationUniformGaugeFamilyModScalar huni X := by
  classical
  refine ⟨Xh, Xv, fun e => if IsHorizontalTorusEdge e then cH e else cV e, ?_⟩
  intro e
  simp only
  by_cases he : IsHorizontalTorusEdge e
  · rw [if_pos he, torusOrientationUniformGauge_horizontal huni Xh Xv he]
    exact hH e he
  · have hv : IsVerticalTorusEdge e :=
      (torusEdge_horizontal_or_vertical e).resolve_left he
    rw [if_neg he, torusOrientationUniformGauge_vertical huni Xh Xv hv]
    exact hV e hv

end PEPS
end TNLean
