import TNLean.PEPS.SquareLatticeGraph
import TNLean.PEPS.EdgeGaugeFamily

/-!
# Translation-invariant edge gauges on the square lattice

The translationally invariant case of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1572 of
`Papers/1804.04964/paper_normal.tex`) reduces the per-edge gauges produced by the
edge blocking to **one horizontal matrix `X` and one vertical matrix `Y`**:

> *"Due to translation invariance, these gauges are described by the same matrix
> `X` (`Y`) on all horizontal (vertical) edges."*  (line 1498)

This file records that reduction at the level of a gauge family on the finite
square-lattice graph. A translationally invariant tensor has, in particular, the
same bond dimension on every horizontal edge and the same bond dimension on every
vertical edge; this constant-bond-dimension content is captured by
`SquareLatticeUniformBondDim`. Given that uniformity, a single horizontal matrix
`Xh` and a single vertical matrix `Xv` determine a gauge family
`orientationUniformGauge` whose value on each edge is the orientation matrix
transported across the bond-dimension equality. A gauge family of this shape is
called *orientation uniform* (`IsOrientationUniformGaugeFamily`); this is the
formal meaning of "described by the same matrix on all horizontal/vertical edges".

The selection of *which* pair `(Xh, Xv)` matches the per-edge gauges supplied by
the edge blocking is the source's uniqueness-up-to-scalar statement
(arXiv:1804.04964, Section 3, Theorem 3: "`X` and `Y` are unique up to a
multiplicative constant"). That uniqueness is the open kernel piece; see the
elimination note in `docs/paper-gaps/peps_normal_ft_section3_route.tex`, remaining
obligation 6. This file provides the carrier construction and its defining
properties, on which the gauge absorption is built.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 1449--1572 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {width height : ℕ}

instance instDecidableIsHorizontalSquareLatticeEdge
    (e : Edge (squareLatticeGraph width height)) :
    Decidable (IsHorizontalSquareLatticeEdge e) := by
  unfold IsHorizontalSquareLatticeEdge squareLatticeHorizontalNeighbor
  infer_instance

instance instDecidableIsVerticalSquareLatticeEdge
    (e : Edge (squareLatticeGraph width height)) :
    Decidable (IsVerticalSquareLatticeEdge e) := by
  unfold IsVerticalSquareLatticeEdge squareLatticeVerticalNeighbor
  infer_instance

/-! ### Uniform horizontal and vertical bond dimensions

A translationally invariant tensor assigns the same bond dimension to every
horizontal edge and the same bond dimension to every vertical edge. The reduction
to a single horizontal matrix and a single vertical matrix is well typed only when
these two dimensions are constant across their orientation classes, so the
constant-bond-dimension content is recorded as a standalone predicate. -/

/-- The bond dimension function of a tensor on the finite square-lattice graph is
**orientation uniform** with horizontal dimension `Dh` and vertical dimension `Dv`
when every horizontal edge has bond dimension `Dh` and every vertical edge has bond
dimension `Dv`. This is the constant-bond-dimension consequence of translation
invariance used to reduce the per-edge gauges to two matrices.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`, where translation invariance makes the gauge
"the same matrix on all horizontal (vertical) edges". -/
def SquareLatticeUniformBondDim (bondDim : Edge (squareLatticeGraph width height) → ℕ)
    (Dh Dv : ℕ) : Prop :=
  (∀ e : Edge (squareLatticeGraph width height),
      IsHorizontalSquareLatticeEdge e → bondDim e = Dh) ∧
    (∀ e : Edge (squareLatticeGraph width height),
      IsVerticalSquareLatticeEdge e → bondDim e = Dv)

/-- The horizontal-edge component of orientation uniformity. -/
theorem SquareLatticeUniformBondDim.horizontal
    {bondDim : Edge (squareLatticeGraph width height) → ℕ} {Dh Dv : ℕ}
    (h : SquareLatticeUniformBondDim bondDim Dh Dv)
    {e : Edge (squareLatticeGraph width height)} (he : IsHorizontalSquareLatticeEdge e) :
    bondDim e = Dh :=
  h.1 e he

/-- The vertical-edge component of orientation uniformity. -/
theorem SquareLatticeUniformBondDim.vertical
    {bondDim : Edge (squareLatticeGraph width height) → ℕ} {Dh Dv : ℕ}
    (h : SquareLatticeUniformBondDim bondDim Dh Dv)
    {e : Edge (squareLatticeGraph width height)} (he : IsVerticalSquareLatticeEdge e) :
    bondDim e = Dv :=
  h.2 e he

/-! ### The gauge family built from a single horizontal and a single vertical
matrix

Given uniform bond dimensions, a single horizontal matrix `Xh : GL (Fin Dh) ℂ` and
a single vertical matrix `Xv : GL (Fin Dv) ℂ` determine a per-edge gauge family:
on each horizontal edge `e` the value is `Xh` transported across `bondDim e = Dh`,
and on each vertical edge it is `Xv` transported across `bondDim e = Dv`. This is
the formal carrier for "the same matrix `X` (`Y`) on all horizontal (vertical)
edges". -/

/-- The per-edge gauge family determined by a single horizontal matrix `Xh` and a
single vertical matrix `Xv`, transported to each edge across the uniform
bond-dimension equalities. Every edge of the square-lattice graph is horizontal or
vertical (`squareLatticeEdge_horizontal_or_vertical`); the horizontal branch
transports `Xh`, the vertical branch transports `Xv`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def orientationUniformGauge
    {bondDim : Edge (squareLatticeGraph width height) → ℕ} {Dh Dv : ℕ}
    (huni : SquareLatticeUniformBondDim bondDim Dh Dv)
    (Xh : GL (Fin Dh) ℂ) (Xv : GL (Fin Dv) ℂ) :
    (e : Edge (squareLatticeGraph width height)) → GL (Fin (bondDim e)) ℂ :=
  fun e =>
    if he : IsHorizontalSquareLatticeEdge e then
      glReindex (huni.horizontal he).symm Xh
    else
      glReindex
        (huni.vertical ((squareLatticeEdge_horizontal_or_vertical e).resolve_left he)).symm Xv

/-- On a horizontal edge, the orientation-uniform gauge is the horizontal matrix
`Xh` transported across the bond-dimension equality.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498. -/
theorem orientationUniformGauge_horizontal
    {bondDim : Edge (squareLatticeGraph width height) → ℕ} {Dh Dv : ℕ}
    (huni : SquareLatticeUniformBondDim bondDim Dh Dv)
    (Xh : GL (Fin Dh) ℂ) (Xv : GL (Fin Dv) ℂ)
    {e : Edge (squareLatticeGraph width height)} (he : IsHorizontalSquareLatticeEdge e) :
    orientationUniformGauge huni Xh Xv e = glReindex (huni.horizontal he).symm Xh := by
  rw [orientationUniformGauge, dif_pos he]

/-- On a vertical edge, the orientation-uniform gauge is the vertical matrix `Xv`
transported across the bond-dimension equality.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498. -/
theorem orientationUniformGauge_vertical
    {bondDim : Edge (squareLatticeGraph width height) → ℕ} {Dh Dv : ℕ}
    (huni : SquareLatticeUniformBondDim bondDim Dh Dv)
    (Xh : GL (Fin Dh) ℂ) (Xv : GL (Fin Dv) ℂ)
    {e : Edge (squareLatticeGraph width height)} (he : IsVerticalSquareLatticeEdge e) :
    orientationUniformGauge huni Xh Xv e = glReindex (huni.vertical he).symm Xv := by
  have hnh : ¬ IsHorizontalSquareLatticeEdge e := by
    intro hh; exact squareLatticeEdge_not_horizontal_and_vertical e ⟨hh, he⟩
  rw [orientationUniformGauge, dif_neg hnh]

/-! ### Orientation-uniform gauge families

A per-edge gauge family is *orientation uniform* when it equals an
`orientationUniformGauge` for some horizontal matrix and some vertical matrix.
This is the precise formal statement that translation invariance reduces the gauge
to one horizontal matrix and one vertical matrix. -/

/-- A per-edge gauge family `X` on the square-lattice graph is **orientation
uniform** when there is a single horizontal matrix and a single vertical matrix
whose transported values reproduce `X` on every edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`: the gauges are "described by the same matrix
`X` (`Y`) on all horizontal (vertical) edges". -/
def IsOrientationUniformGaugeFamily
    {bondDim : Edge (squareLatticeGraph width height) → ℕ} {Dh Dv : ℕ}
    (huni : SquareLatticeUniformBondDim bondDim Dh Dv)
    (X : (e : Edge (squareLatticeGraph width height)) → GL (Fin (bondDim e)) ℂ) : Prop :=
  ∃ (Xh : GL (Fin Dh) ℂ) (Xv : GL (Fin Dv) ℂ),
    X = orientationUniformGauge huni Xh Xv

/-- The gauge family `orientationUniformGauge huni Xh Xv` is orientation uniform,
witnessed by `Xh` and `Xv`. -/
theorem isOrientationUniformGaugeFamily_orientationUniformGauge
    {bondDim : Edge (squareLatticeGraph width height) → ℕ} {Dh Dv : ℕ}
    (huni : SquareLatticeUniformBondDim bondDim Dh Dv)
    (Xh : GL (Fin Dh) ℂ) (Xv : GL (Fin Dv) ℂ) :
    IsOrientationUniformGaugeFamily huni (orientationUniformGauge huni Xh Xv) :=
  ⟨Xh, Xv, rfl⟩

/-- **Translation-invariant reduction of the per-edge gauges (carrier form).**

Given uniform horizontal and vertical bond dimensions, every choice of a single
horizontal matrix `Xh` and a single vertical matrix `Xv` realizes an orientation
uniform gauge family. This is the carrier of the source step at line 1498: the
per-edge gauges are *described by* one horizontal matrix and one vertical matrix.

The complementary statement that the per-edge gauges produced by the edge blocking
are equal to such a family --- i.e. that the same `Xh` and `Xv` work on every edge
--- is the source's uniqueness-up-to-scalar property (Theorem 3: "`X` and `Y` are
unique up to a multiplicative constant"), which is the open kernel piece. See
remaining obligation 6 of
`docs/paper-gaps/peps_normal_ft_section3_route.tex`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_orientationUniformGaugeFamily
    {bondDim : Edge (squareLatticeGraph width height) → ℕ} {Dh Dv : ℕ}
    (huni : SquareLatticeUniformBondDim bondDim Dh Dv)
    (Xh : GL (Fin Dh) ℂ) (Xv : GL (Fin Dv) ℂ) :
    ∃ X : (e : Edge (squareLatticeGraph width height)) → GL (Fin (bondDim e)) ℂ,
      IsOrientationUniformGaugeFamily huni X :=
  ⟨orientationUniformGauge huni Xh Xv,
    isOrientationUniformGaugeFamily_orientationUniformGauge huni Xh Xv⟩

/-! ### Orientation uniformity up to per-edge scalars

The per-edge gauges produced by the edge blocking are determined only up to a
multiplicative constant on each edge (`edgeGauge_unique_scalar`). The reduction
to one horizontal and one vertical matrix therefore holds only *up to per-edge
scalars*: each per-edge gauge equals the transported orientation matrix rescaled
by a nonzero constant. This scalar-carrying form is the faithful target produced
by the uniqueness-up-to-scalar step; the per-edge scalars are the residual
multiplicative freedom the source records as "`X` and `Y` are unique up to a
multiplicative constant". -/

/-- A per-edge gauge family `X` is **orientation uniform up to scalars** when
there are a single horizontal matrix, a single vertical matrix, and a per-edge
nonzero scalar `c` such that on every edge `X e` is the transported orientation
matrix rescaled by `c e`. The per-edge scalars are the residual multiplicative
freedom; without them this is `IsOrientationUniformGaugeFamily`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex` ("the same matrix `X` (`Y`) on all
horizontal (vertical) edges"), together with Theorem 3's uniqueness up to a
multiplicative constant. -/
def IsOrientationUniformGaugeFamilyModScalar
    {bondDim : Edge (squareLatticeGraph width height) → ℕ} {Dh Dv : ℕ}
    (huni : SquareLatticeUniformBondDim bondDim Dh Dv)
    (X : (e : Edge (squareLatticeGraph width height)) → GL (Fin (bondDim e)) ℂ) : Prop :=
  ∃ (Xh : GL (Fin Dh) ℂ) (Xv : GL (Fin Dv) ℂ)
    (c : Edge (squareLatticeGraph width height) → ℂˣ),
    ∀ e : Edge (squareLatticeGraph width height),
      (X e : Matrix (Fin (bondDim e)) (Fin (bondDim e)) ℂ) =
        (c e : ℂ) • (orientationUniformGauge huni Xh Xv e :
          Matrix (Fin (bondDim e)) (Fin (bondDim e)) ℂ)

/-- An orientation-uniform gauge family is orientation uniform up to scalars,
with all scalars equal to one. -/
theorem isOrientationUniformGaugeFamilyModScalar_of_isOrientationUniform
    {bondDim : Edge (squareLatticeGraph width height) → ℕ} {Dh Dv : ℕ}
    {huni : SquareLatticeUniformBondDim bondDim Dh Dv}
    {X : (e : Edge (squareLatticeGraph width height)) → GL (Fin (bondDim e)) ℂ}
    (hX : IsOrientationUniformGaugeFamily huni X) :
    IsOrientationUniformGaugeFamilyModScalar huni X := by
  obtain ⟨Xh, Xv, rfl⟩ := hX
  exact ⟨Xh, Xv, fun _ => 1, fun e => by simp⟩

/-- **Orientation-uniform selection up to scalars.**

Suppose every per-edge gauge agrees, up to a nonzero scalar, with one reference
horizontal matrix on horizontal edges and one reference vertical matrix on
vertical edges --- the per-edge content delivered by `edgeGauge_unique_scalar`
across each orientation class under translation invariance. Then the whole gauge
family is orientation uniform up to scalars.

This is the assembly step of the source's line-1498 reduction: it gathers the
per-edge "agree up to a constant" facts of the two orientation classes into one
orientation-uniform-up-to-scalar family. The hypotheses `hH` and `hV` are exactly
the per-edge conclusions of `edgeGauge_unique_scalar` applied at every edge of
each class against the transported reference, with the scalars `cH e`, `cV e`
collected into a single per-edge scalar.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isOrientationUniformGaugeFamilyModScalar_of_classAgreement
    {bondDim : Edge (squareLatticeGraph width height) → ℕ} {Dh Dv : ℕ}
    (huni : SquareLatticeUniformBondDim bondDim Dh Dv)
    (X : (e : Edge (squareLatticeGraph width height)) → GL (Fin (bondDim e)) ℂ)
    (Xh : GL (Fin Dh) ℂ) (Xv : GL (Fin Dv) ℂ)
    (cH cV : Edge (squareLatticeGraph width height) → ℂˣ)
    (hH : ∀ (e : Edge (squareLatticeGraph width height))
        (he : IsHorizontalSquareLatticeEdge e),
      (X e : Matrix (Fin (bondDim e)) (Fin (bondDim e)) ℂ) =
        (cH e : ℂ) • (glReindex (huni.horizontal he).symm Xh :
          Matrix (Fin (bondDim e)) (Fin (bondDim e)) ℂ))
    (hV : ∀ (e : Edge (squareLatticeGraph width height))
        (he : IsVerticalSquareLatticeEdge e),
      (X e : Matrix (Fin (bondDim e)) (Fin (bondDim e)) ℂ) =
        (cV e : ℂ) • (glReindex (huni.vertical he).symm Xv :
          Matrix (Fin (bondDim e)) (Fin (bondDim e)) ℂ)) :
    IsOrientationUniformGaugeFamilyModScalar huni X := by
  classical
  refine ⟨Xh, Xv, fun e => if IsHorizontalSquareLatticeEdge e then cH e else cV e, ?_⟩
  intro e
  simp only
  by_cases he : IsHorizontalSquareLatticeEdge e
  · rw [if_pos he, orientationUniformGauge_horizontal huni Xh Xv he]
    exact hH e he
  · have hv : IsVerticalSquareLatticeEdge e :=
      (squareLatticeEdge_horizontal_or_vertical e).resolve_left he
    rw [if_neg he, orientationUniformGauge_vertical huni Xh Xv hv]
    exact hV e hv

end PEPS
end TNLean
