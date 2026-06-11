import TNLean.PEPS.NormalSquareTI
import TNLean.PEPS.FundamentalTheorem
import TNLean.PEPS.FundamentalTheorem.Uniqueness

/-!
# Absorbing the translation-invariant edge gauges on the square lattice

This file performs the absorption step of the translationally invariant normal
PEPS Fundamental Theorem (arXiv:1804.04964, Section 3, proof of Theorem 3, lines
1500--1519 of `Papers/1804.04964/paper_normal.tex`):

> *"Define now `B̃` by incorporating the local gauges into the tensors `B`, such
> as in the injective case."* (line 1500)

The absorption is the same construction `absorbEdgeGauges` used in the injective
case (`TNLean.PEPS.FundamentalTheorem`). The translationally invariant input is an
**orientation-uniform** gauge family (`IsOrientationUniformGaugeFamily`): one
horizontal matrix on every horizontal edge and one vertical matrix on every
vertical edge. After absorption, the modified tensor `B̃` has the same bond
dimensions as `B` (still orientation uniform), is vertex injective whenever `B`
is, and --- given the post-absorption edge-insertion equality supplied by the edge
blocking --- agrees with `A` on every inserted-edge coefficient. This is the
content needed for the final `R`/`S` comparison.

## The conditional structure

The per-edge gauge family produced by the edge blocking
(`lem:inj_isomorph`/`lem:injective_union`) is the open kernel piece of the normal
route (remaining obligation 5 of
`docs/paper-gaps/peps_normal_ft_section3_route.tex`). This file is therefore
**conditional** on that gauge family: the post-absorption edge-insertion equality
`PostAbsorptionEdgeInsertionEquality A (absorbEdgeGauges B Z)` is taken as a
hypothesis with the shape the kernel will deliver --- exactly the output of
`post_absorption_edge_insertion_equality` in the vertex-injective case. The source
proof's Theorem 3 likewise consumes the output of `lem:inj_isomorph`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 1500--1519 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {width height : ℕ} {d : ℕ}

/-! ### The absorbed tensor on the square lattice

The translationally invariant `B̃` is `absorbEdgeGauges B Z` with `Z` orientation
uniform. The two facts the comparison step needs are: `B̃` is vertex injective
(when `B` is), and `B̃` has the same orientation-uniform bond dimensions as `B`. -/

/-- The translationally invariant modified tensor `B̃`: the second PEPS tensor with
an orientation-uniform edge-gauge family absorbed into it.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1500--1519 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def tiAbsorb (B : Tensor (squareLatticeGraph width height) d)
    (Z : (e : Edge (squareLatticeGraph width height)) → GL (Fin (B.bondDim e)) ℂ) :
    Tensor (squareLatticeGraph width height) d :=
  absorbEdgeGauges B Z

/-- The absorbed tensor has the same bond dimensions as `B`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1500--1519. -/
@[simp] theorem tiAbsorb_bondDim (B : Tensor (squareLatticeGraph width height) d)
    (Z : (e : Edge (squareLatticeGraph width height)) → GL (Fin (B.bondDim e)) ℂ) :
    (tiAbsorb B Z).bondDim = B.bondDim := rfl

/-- The absorbed tensor inherits the orientation-uniform bond dimensions of `B`:
absorption changes only the component data, not the bond spaces.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1500--1519. -/
theorem squareLatticeUniformBondDim_tiAbsorb
    (B : Tensor (squareLatticeGraph width height) d)
    (Z : (e : Edge (squareLatticeGraph width height)) → GL (Fin (B.bondDim e)) ℂ)
    {Dh Dv : ℕ} (huni : SquareLatticeUniformBondDim B.bondDim Dh Dv) :
    SquareLatticeUniformBondDim (tiAbsorb B Z).bondDim Dh Dv := by
  rw [tiAbsorb_bondDim]; exact huni

/-- The absorbed tensor is vertex injective whenever `B` is.

This is the square-lattice instance of `isVertexInjective_absorbEdgeGauges`: the
oriented endpoint gauges recombine the linearly independent local family of `B` by
an invertible product kernel, preserving linear independence.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1500: the absorbed
family `B̃` is again injective. -/
theorem isVertexInjective_tiAbsorb (B : Tensor (squareLatticeGraph width height) d)
    (Z : (e : Edge (squareLatticeGraph width height)) → GL (Fin (B.bondDim e)) ℂ)
    (hB : IsVertexInjective B) :
    IsVertexInjective (tiAbsorb B Z) :=
  isVertexInjective_absorbEdgeGauges B Z hB

/-! ### The translation-invariant gauge absorption datum

Bundling the absorbed tensor together with the post-absorption edge-insertion
equality records the output of the absorption step: a second tensor `B̃`,
orientation uniform and vertex injective, on whose inserted-edge coefficients `A`
agrees. The post-absorption edge-insertion equality is the conditional kernel
input (`PostAbsorptionEdgeInsertionEquality`), the analogue of
`eq:inj_equal_edge`. -/

/-- The translationally invariant gauge-absorption datum at the square lattice.

This records the result of incorporating the orientation-uniform edge gauges into
the second tensor: the absorbed tensor `Btilde`, the witness that its gauge family
is orientation uniform (`gauge_uniform`), and the post-absorption edge-insertion
equality with `A` (`post_absorption`). The post-absorption equality is the
conditional kernel input; see the module docstring.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1500--1519 of
`Papers/1804.04964/paper_normal.tex` and `eq:inj_equal_edge` at lines 1037--1065. -/
structure TINormalGaugeAbsorptionData
    (A B : Tensor (squareLatticeGraph width height) d) {Dh Dv : ℕ}
    (huni : SquareLatticeUniformBondDim B.bondDim Dh Dv) where
  /-- The orientation-uniform edge-gauge family absorbed into `B`. -/
  gauge : (e : Edge (squareLatticeGraph width height)) → GL (Fin (B.bondDim e)) ℂ
  /-- The absorbed gauge family is orientation uniform. -/
  gauge_uniform : IsOrientationUniformGaugeFamily huni gauge
  /-- After absorption, `A` and `B̃` agree on every inserted-edge coefficient. -/
  post_absorption : PostAbsorptionEdgeInsertionEquality A (absorbEdgeGauges B gauge)

/-- **Translation-invariant gauge absorption.**

Given an orientation-uniform edge-gauge family `Z` on the square lattice and the
post-absorption edge-insertion equality between `A` and the absorbed tensor (the
conditional kernel input), the absorption datum is assembled: the absorbed tensor
is orientation uniform and `A` agrees with it on every inserted-edge coefficient.

The orientation-uniform gauge family is the translation-invariant reduction of the
per-edge gauges to one horizontal and one vertical matrix
(`NormalSquareTI.IsOrientationUniformGaugeFamily`). The post-absorption equality is
the kernel input matching the shape produced by
`post_absorption_edge_insertion_equality` in the vertex-injective case.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1500--1519 of
`Papers/1804.04964/paper_normal.tex`. -/
def tiNormalGaugeAbsorption
    (A B : Tensor (squareLatticeGraph width height) d) {Dh Dv : ℕ}
    (huni : SquareLatticeUniformBondDim B.bondDim Dh Dv)
    (Z : (e : Edge (squareLatticeGraph width height)) → GL (Fin (B.bondDim e)) ℂ)
    (hZuni : IsOrientationUniformGaugeFamily huni Z)
    (hPA : PostAbsorptionEdgeInsertionEquality A (absorbEdgeGauges B Z)) :
    TINormalGaugeAbsorptionData A B huni :=
  ⟨Z, hZuni, hPA⟩

/-! ### Existence of the post-absorption equality in the vertex-injective case

For vertex-injective tensors with positive bond dimensions, the post-absorption
edge-insertion equality holds for *some* per-edge gauge family `Z`. This is the
square-lattice instance of `post_absorption_edge_insertion_equality`. It supplies
the post-absorption equality unconditionally; the orientation uniformity of `Z`
(the reduction to one horizontal and one vertical matrix) is the conditional
kernel piece and is not asserted here. -/

/-- For vertex-injective square-lattice tensors with matching positive bond
dimensions and the same state, there is a per-edge gauge family `Z` whose
absorption yields the post-absorption edge-insertion equality.

This is the square-lattice instance of `post_absorption_edge_insertion_equality`.
The orientation uniformity of `Z` --- the translationally invariant reduction to
one horizontal and one vertical matrix --- is the open kernel piece and is *not*
part of this statement; see remaining obligation 6 of
`docs/paper-gaps/peps_normal_ft_section3_route.tex`.

Source: arXiv:1804.04964, Section 3, `eq:inj_equal_edge` (lines 1037--1065 of
`Papers/1804.04964/paper_normal.tex`), reused in the translationally invariant
proof of Theorem 3 at lines 1500--1519. -/
theorem exists_postAbsorption_of_vertexInjective
    (A B : Tensor (squareLatticeGraph width height) d)
    (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (hpos : ∀ e : Edge (squareLatticeGraph width height), 0 < A.bondDim e) :
    ∃ Z : (e : Edge (squareLatticeGraph width height)) → GL (Fin (B.bondDim e)) ℂ,
      PostAbsorptionEdgeInsertionEquality A (absorbEdgeGauges B Z) :=
  post_absorption_edge_insertion_equality A B hA hB hAB hDim hpos

/-! ### Absorbing the per-edge scalars

The per-edge gauges are determined only up to a multiplicative constant on each
edge (`edgeGauge_unique_scalar`), so the orientation-uniform reduction produces an
orientation-uniform family only *up to per-edge scalars*. When those scalars are
vertex-balanced --- their oriented product around every vertex is one --- the
scalar-rescaled gauge family and the underlying exact orientation-uniform family
absorb into the *same* tensor.  This is the absorption-side reflection of the fact
that a balanced edge-scalar reweighting leaves every local gauged tensor
unchanged (`GaugeEquivModEdgeScalars.applyGauge_eq`); it lets the conditional
square-lattice theorem consume an exact orientation-uniform gauge even though the
edge blocking delivers one only up to balanced scalars.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 and lines
1500--1519 of `Papers/1804.04964/paper_normal.tex`; the per-edge multiplicative
freedom is the source's "`X` and `Y` are unique up to a multiplicative constant". -/

section ScalarAbsorption

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A per-edge scalar rescaling of a gauge family is a balanced-edge-scalar
reweighting of it.  If `Z e` has matrix `c e • (Y e)` on every edge, with `c`
vertex-balanced, then `Z` and `Y` are equivalent modulo balanced edge scalars.

The proof is the matrix-level reading used in `gauge_unique_mod_edge_scalars`: the
lower endpoint carries `c e`, the upper endpoint carries `(c e)⁻¹` through the
transposed inverse, which is exactly `edgeScalarAt c`.

Source: `docs/paper-gaps/peps_gauge_edge_scalars.tex`; the balanced edge-scalar
quotient of the per-edge gauges. -/
theorem gaugeEquivModEdgeScalars_of_matrixScalar (B : Tensor G d)
    (Z Y : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ)
    (c : (e : Edge G) → ℂˣ) (hc : IsVertexBalanced (G := G) c)
    (hZY : ∀ e : Edge G,
      (Z e : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) =
        (c e : ℂ) • (Y e : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ)) :
    GaugeEquivModEdgeScalars (G := G) B Z Y := by
  -- Inverse gauges carry the inverse scalar, exactly as in the uniqueness proof.
  have hZYinv : ∀ e : Edge G,
      ((Z e)⁻¹).val = ((c e)⁻¹ : ℂ) • ((Y e)⁻¹).val := by
    intro e
    have hcne : (c e : ℂ) ≠ 0 := (c e).ne_zero
    have hYdet : IsUnit (Y e).val.det := (Matrix.isUnit_iff_isUnit_det _).mp (Y e).isUnit
    rw [Matrix.coe_units_inv, Matrix.coe_units_inv]
    refine Matrix.inv_eq_right_inv ?_
    rw [hZY e, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_inv_cancel₀ hcne, one_smul, Matrix.mul_nonsing_inv _ hYdet]
  refine ⟨c, hc, ?_⟩
  intro v ie
  unfold edgeScalarAt edgeGaugeAt
  by_cases h : ie.1.1.1 = v
  · simp only [if_pos h]; rw [hZY ie.1]
  · simp only [if_neg h]
    rw [hZYinv ie.1, Matrix.transpose_smul, Units.val_inv_eq_inv_val]

/-- A balanced per-edge scalar rescaling absorbs identically: if `Z e` has matrix
`c e • (Y e)` with `c` vertex-balanced, then `absorbEdgeGauges B Z =
absorbEdgeGauges B Y`.

This discharges the per-edge multiplicative freedom of the orientation-uniform
reduction at the absorption step: the scalar-carrying gauge and the exact
orientation-uniform gauge produce the same modified tensor.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1500--1519 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem absorbEdgeGauges_eq_of_matrixScalar (B : Tensor G d)
    (Z Y : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ)
    (c : (e : Edge G) → ℂˣ) (hc : IsVertexBalanced (G := G) c)
    (hZY : ∀ e : Edge G,
      (Z e : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) =
        (c e : ℂ) • (Y e : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ)) :
    absorbEdgeGauges B Z = absorbEdgeGauges B Y :=
  GaugeEquivModEdgeScalars.applyGauge_eq (G := G)
    (gaugeEquivModEdgeScalars_of_matrixScalar B Z Y c hc hZY)

end ScalarAbsorption

/-! ### Feeding the conditional square-lattice theorem from a scalar-carrying gauge

The conditional theorem `fundamentalTheorem_normalSquarePEPS` consumes a gauge
absorption datum built on an *exact* orientation-uniform gauge.  The edge blocking
delivers only an orientation-uniform-up-to-scalar gauge.  When the per-edge scalars
are vertex balanced, the two absorb into the same tensor, so the exact
orientation-uniform reference inherits the scalar-carrying gauge's post-absorption
equality and assembles the datum the theorem expects. -/

/-- **Gauge-absorption datum from a balanced scalar-carrying orientation-uniform
gauge.**

Given a gauge family `Z` that is orientation uniform up to vertex-balanced per-edge
scalars and whose absorption satisfies the post-absorption edge-insertion equality,
the exact orientation-uniform reference `Y = orientationUniformGauge Xh Xv`
extracted from `Z` carries the same absorbed tensor (the balanced scalars absorb
identically), hence the same post-absorption equality, and so assembles a
`TINormalGaugeAbsorptionData A B huni` --- the input of
`fundamentalTheorem_normalSquarePEPS`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1500--1519 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def tiNormalGaugeAbsorptionData_of_modScalar
    (A B : Tensor (squareLatticeGraph width height) d) {Dh Dv : ℕ}
    (huni : SquareLatticeUniformBondDim B.bondDim Dh Dv)
    (Z : (e : Edge (squareLatticeGraph width height)) → GL (Fin (B.bondDim e)) ℂ)
    (Xh : GL (Fin Dh) ℂ) (Xv : GL (Fin Dv) ℂ)
    (c : Edge (squareLatticeGraph width height) → ℂˣ)
    (hc : IsVertexBalanced (G := squareLatticeGraph width height) c)
    (hZ : ∀ e : Edge (squareLatticeGraph width height),
      (Z e : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) =
        (c e : ℂ) • (orientationUniformGauge huni Xh Xv e :
          Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ))
    (hPA : PostAbsorptionEdgeInsertionEquality A (absorbEdgeGauges B Z)) :
    TINormalGaugeAbsorptionData A B huni where
  gauge := orientationUniformGauge huni Xh Xv
  gauge_uniform := isOrientationUniformGaugeFamily_orientationUniformGauge huni Xh Xv
  post_absorption := by
    have heq : absorbEdgeGauges B Z =
        absorbEdgeGauges B (orientationUniformGauge huni Xh Xv) :=
      absorbEdgeGauges_eq_of_matrixScalar B Z (orientationUniformGauge huni Xh Xv) c hc hZ
    rwa [heq] at hPA

end PEPS
end TNLean
