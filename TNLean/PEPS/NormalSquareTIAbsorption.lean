import TNLean.PEPS.NormalSquareTI
import TNLean.PEPS.FundamentalTheorem

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

end PEPS
end TNLean
