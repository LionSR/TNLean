/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.FiniteDomain
import Mathlib.Analysis.Convex.Hull
import Mathlib.Basic.Real.Basic

/-!
# Polygonal lattice templates and ordered two-family partitions

Templates are finite ambient lattice sets covered by sampled closed convex
rectangles and triangles with the four prescribed side slopes. Their union
may be disconnected. The template size and clearance conditions are kept
separate from induced-graph distance.

The finite two-family partition contains only disjoint sets, their family
labels, and an order. It contains no spectral or information estimate.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Definition 9.3 (`scanner:template`) and
  Lemma 11.1 (`geometry:cancellation`).
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- A side direction of slope `0`, `∞`, `1`, or `-1`.
Source: area-law Definition 9.3. -/
def IsAllowedSlope (u : ℝ × ℝ) : Prop :=
  u.1 = 0 ∨ u.2 = 0 ∨ u.1 = u.2 ∨ u.1 = -u.2

/-- The rectangles and triangles permitted in a template. The vertices of a
triangle are noncollinear; the adjacent sides of a rectangle are nonzero and
orthogonal. Source: area-law Definition 9.3, closed convex rectangles and triangles. -/
inductive TemplatePolygon where
  /-- A triangle whose three sides have allowed slopes. -/
  | triangle (a b c : ℝ × ℝ)
      (noncollinear : (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) ≠ 0)
      (ab : IsAllowedSlope (b - a)) (bc : IsAllowedSlope (c - b))
      (ca : IsAllowedSlope (a - c))
  /-- A rectangle with orthogonal adjacent sides of allowed slopes. -/
  | rectangle (a u v : ℝ × ℝ) (u_ne_zero : u ≠ 0) (v_ne_zero : v ≠ 0)
      (orthogonal : u.1 * v.1 + u.2 * v.2 = 0)
      (u_slope : IsAllowedSlope u) (v_slope : IsAllowedSlope v)

/-- The closed convex polygon specified by its vertices.
Source: area-law Definition 9.3. -/
noncomputable def TemplatePolygon.region : TemplatePolygon → Set (ℝ × ℝ)
  | .triangle a b c _ _ _ _ => convexHull ℝ {a, b, c}
  | .rectangle a u v _ _ _ _ _ => convexHull ℝ {a, a + u, a + u + v, a + v}

/-- Integer points regarded as ambient real-plane points.
Source: area-law Definition 9.3, the sampling `P_a ∩ ℤ²`. -/
def integerPoint (x : ℤ × ℤ) : ℝ × ℝ := ((x.1 : ℝ), (x.2 : ℝ))

/-- A template, with its scale parameters and complete polygonal sampling data.
`Ctpl` represents the fixed, sufficiently large positive numerical constant of
Definition 9.3; it is chosen before the templates. The structure is defined for
every real parameter. Geometric estimates must therefore state the required
uniform lower bound on `Ctpl` explicitly, rather than infer it from the scale
field. Source: area-law Definition 9.3 and Lemma 9.4 (`scanner:templates`). -/
structure Template (Ctpl : ℝ) (n s₀ : ℕ) where
  /-- The global size parameter is positive. -/
  n_pos : 0 < n
  /-- The piece-size parameter is positive. -/
  s₀_pos : 0 < s₀
  /-- The number of sampled polygonal pieces. -/
  pieceCount : ℕ
  /-- At least one polygon is present. -/
  pieceCount_pos : 0 < pieceCount
  /-- The closed convex rectangles or triangles of the cover. -/
  polygon : Fin pieceCount → TemplatePolygon
  /-- The lattice points sampled from each polygon. -/
  sample : Fin pieceCount → Finset (ℤ × ℤ)
  /-- Sampling includes exactly the integer points of the closed polygon. -/
  mem_sample : ∀ i x, x ∈ sample i ↔ integerPoint x ∈ (polygon i).region
  /-- Every polygon has sup-norm diameter at most `s₀`. -/
  piece_diameter : ∀ i, ∀ x ∈ (polygon i).region, ∀ y ∈ (polygon i).region,
    max |x.1 - y.1| |x.2 - y.2| ≤ (s₀ : ℝ)
  /-- The ambient lattice set covered by the sampled pieces. -/
  points : Finset (ℤ × ℤ)
  /-- The template has at least one lattice point. -/
  nonempty : points.Nonempty
  /-- The template is exactly the union of its sampled pieces. -/
  cover : points = Finset.univ.biUnion sample
  /-- The template scale bounds the number and sizes of its pieces. -/
  scale : Ctpl * pieceCount * (s₀ + 1 : ℝ) ≤ (n : ℝ)
  /-- The whole template has ambient sup-norm diameter at most `n`. -/
  diameter : ∀ x ∈ points, ∀ y ∈ points,
    max |(x.1 : ℝ) - y.1| |(x.2 : ℝ) - y.2| ≤ (n : ℝ)

/-- Clearance from the fixed cut set in ambient sup-norm distance.
Source: area-law Definition 9.3, `dist∞(T,Z) > 4 D₀ s₀`.
The empty cut set gives no clearance obstruction. -/
def Template.IsSeparated {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (D₀ : ℝ) (Z : Finset (ℤ × ℤ)) : Prop :=
  ∀ x ∈ T.points, ∀ z ∈ Z,
    4 * D₀ * s₀ < max |(x.1 : ℝ) - z.1| |(x.2 : ℝ) - z.2|

/-- The template core inside a fixed cut. Source: Definition 9.3, `X = A ∩ T`. -/
def Template.core {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (A : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  A ∩ T.points

/-- The ambient dilated collar inside a fixed cut.
Source: Definition 9.3, `Q_j = A ∩ (T_j ∖ T)`. -/
def Template.collar {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (A : Finset (ℤ × ℤ)) (j : ℕ) : Finset (ℤ × ℤ) :=
  A ∩ (ambientDilation T.points j \ T.points)

/-- A finite ordered partition into a residual set and two families.
Source: area-law Lemma 11.1 (`geometry:cancellation`). A single order on all
labels induces the required order on each family. No geometric estimate is assumed. -/
structure OrderedTwoFamilyPartition {ι : Type*} [DecidableEq ι] (A : Finset ι) where
  /-- The number of pieces; zero pieces are permitted. -/
  pieceCount : ℕ
  /-- One of the two family labels for each piece. -/
  family : Fin pieceCount → Fin 2
  /-- The regional pieces in the common order. -/
  piece : Fin pieceCount → Finset ι
  /-- Sites not retained in either family. -/
  residual : Finset ι
  /-- Distinct pieces are disjoint, including pieces from different families. -/
  disjoint : ∀ i j, i ≠ j → Disjoint (piece i) (piece j)
  /-- Every piece is disjoint from the residual set. -/
  residual_disjoint : ∀ i, Disjoint residual (piece i)
  /-- The residual and the pieces partition the fixed region. -/
  cover : A = residual ∪ Finset.univ.biUnion piece

/-- The union of earlier pieces in the same family, using the common label order.
Source: area-law Lemma 11.1, the union over `j < i` in `𝓘_f`. -/
def OrderedTwoFamilyPartition.earlierSameFamily {ι : Type*} [DecidableEq ι]
    {A : Finset ι} (P : OrderedTwoFamilyPartition A) (i : Fin P.pieceCount) : Finset ι :=
  (Finset.univ.filter fun j ↦ j < i ∧ P.family j = P.family i).biUnion P.piece

end TNLean.PEPS.AreaLaw.Geometry
