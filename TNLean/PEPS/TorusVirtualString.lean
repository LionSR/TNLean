/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusSiteTensor

/-!
# Virtual strings on a torus PEPS and pulling them through a rectangle

A virtual string operator on a PEPS acts on the bonds it crosses, diagonally in the bond
basis: a bond carrying the index `α` contributes the element `X α` of a monoid `M`, and the
contributions are multiplied in the order in which the string crosses the bonds. For a matrix
algebra `M` this is a matrix product operator on the virtual level whose own bond is the
matrix index of `M`. For the torus PEPS of a four-leg tensor `a`
(`TNLean.PEPS.torusSiteTensor`), this file considers the two strings across a rectangle of
`m` columns and `n` rows with upper left site `v₀` that run from its upper left to its lower
right corner: one crosses the left legs of the leftmost column, from top to bottom, and then
the down legs of the bottom row, from left to right; the other crosses the top legs of the top
row and then the right legs of the rightmost column.

If on the support of `a` the string can be moved across one site,
`X t * X r = X l * X b` whenever `a t r b l s ≠ 0`, then on every nonvanishing term of the
contraction the two strings agree for every rectangle, and so the contracted network with the
string inserted does not depend on which of the two paths the string takes. This is the
pulling-through property of a matrix product operator symmetry of a PEPS, arXiv:2011.12127,
Section "MPO and PEPO", `Papers/2011.12127/TN-Review-main.tex` lines 405–408, used for the
primal quantum-double tensor in Appendix A, "The Toric Code and quantum double models",
line 2465.

The strings here are diagonal in the bond basis. The deformation of strings of `U_g` across a
`G`-injective PEPS, arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex` lines 1624–1648
(equation `eq:2d:move-strings`) and lines 2199–2211, acts on the bonds by the regular
representation and is a different statement, not formalized here.

The combinatorial core is a statement about a grid of monoid elements: if every elementary
square commutes, then the two boundary paths of a rectangle have the same product
(`TNLean.PEPS.gridPath_prod_eq`).

## Main definitions

* `TNLean.PEPS.torusWestSouthString`, `TNLean.PEPS.torusNorthEastString`: the two strings
  across a rectangle.

## Main results

* `TNLean.PEPS.gridPath_column_prod_eq`, `TNLean.PEPS.gridPath_prod_eq`: path independence on
  a grid of commuting squares.
* `TNLean.PEPS.torusWestSouthString_eq_torusNorthEastString`: the two strings agree on every
  nonvanishing term of the contraction.
* `TNLean.PEPS.sum_smul_torusWestSouthString_eq`: the contracted network with the string
  inserted is the same for both paths.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped BigOperators

namespace TNLean
namespace PEPS

/-! ### Path independence on a grid -/

section Grid

variable {M : Type*} [Monoid M]

/-- One column of a grid of commuting squares. The element `P i j` sits on the vertical
segment of column `i` in row `j` and `Q i j` on the horizontal segment of column `i` above
row `j`; if each square `Q i j * P (i + 1) j = P i j * Q i (j + 1)` of column `i` commutes,
then going down the left side and across the bottom equals going across the top and down the
right side. -/
theorem gridPath_column_prod_eq (P Q : ℕ → ℕ → M) (i n : ℕ)
    (h : ∀ j < n, Q i j * P (i + 1) j = P i j * Q i (j + 1)) :
    ((List.range n).map (P i)).prod * Q i n =
      Q i 0 * ((List.range n).map (P (i + 1))).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    rw [mul_assoc, ← h n (Nat.lt_succ_self n), ← mul_assoc,
      ih fun j hj => h j (Nat.lt_succ_of_lt hj), mul_assoc]

/-- Path independence on a grid of commuting squares: if every square
`Q i j * P (i + 1) j = P i j * Q i (j + 1)` with `i < m`, `j < n` commutes, then the product
down the left side and across the bottom of the `m × n` rectangle equals the product across
the top and down the right side. -/
theorem gridPath_prod_eq (P Q : ℕ → ℕ → M) (m n : ℕ)
    (h : ∀ i < m, ∀ j < n, Q i j * P (i + 1) j = P i j * Q i (j + 1)) :
    ((List.range n).map (P 0)).prod * ((List.range m).map fun i => Q i n).prod =
      ((List.range m).map fun i => Q i 0).prod * ((List.range n).map (P m)).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    rw [← mul_assoc, ih fun i hi => h i (Nat.lt_succ_of_lt hi), mul_assoc,
      gridPath_column_prod_eq P Q m n (h m (Nat.lt_succ_self m)), ← mul_assoc]

end Grid

/-! ### Strings on the torus -/

variable {width height : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]
variable {D : ℕ} {M : Type*}

section Monoid

variable [Monoid M]

/-- The virtual string across the rectangle of `m` columns and `n` rows with upper left site
`v₀` that crosses the left legs of the sites `(x₀, y₀ - j)`, `j = 0, …, n - 1`, and then the
down legs of the sites `(x₀ + i, y₀ - n + 1)`, `i = 0, …, m - 1`. A bond with index `α`
contributes `X α`. -/
def torusWestSouthString (X : Fin D → M) (η : Edge (torusGraph width height) → Fin D)
    (v₀ : TorusVertex width height) (m n : ℕ) : M :=
  ((List.range n).map fun j : ℕ => X (η (torusLeftEdge (v₀.1, v₀.2 - j)))).prod *
    ((List.range m).map fun i : ℕ => X (η (torusUpEdge (v₀.1 + i, v₀.2 - n)))).prod

/-- The virtual string across the rectangle of `m` columns and `n` rows with upper left site
`v₀` that crosses the top legs of the sites `(x₀ + i, y₀)`, `i = 0, …, m - 1`, and then the
right legs of the sites `(x₀ + m - 1, y₀ - j)`, `j = 0, …, n - 1`. A bond with index `α`
contributes `X α`. -/
def torusNorthEastString (X : Fin D → M) (η : Edge (torusGraph width height) → Fin D)
    (v₀ : TorusVertex width height) (m n : ℕ) : M :=
  ((List.range m).map fun i : ℕ => X (η (torusUpEdge (v₀.1 + i, v₀.2)))).prod *
    ((List.range n).map fun j : ℕ => X (η (torusLeftEdge (v₀.1 + m, v₀.2 - j)))).prod

/-- Pulling a virtual string through a rectangle of a torus PEPS. If the string can be moved
across one site on the support of `a`, `X t * X r = X l * X b` whenever `a t r b l s ≠ 0`,
then on every nonvanishing term `η` of the contraction the two strings across any rectangle
agree.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2465, the virtual
symmetry of a PEPS whose virtual labels fuse to the identity. -/
theorem torusWestSouthString_eq_torusNorthEastString {d : ℕ}
    (a : Fin D → Fin D → Fin D → Fin D → Fin d → ℂ) (X : Fin D → M)
    (hX : ∀ t r b l s, a t r b l s ≠ 0 → X t * X r = X l * X b)
    (σ : TorusVertex width height → Fin d) (η : Edge (torusGraph width height) → Fin D)
    (hη : ∏ v, a (η (torusUpEdge v)) (η (torusRightEdge v)) (η (torusDownEdge v))
      (η (torusLeftEdge v)) (σ v) ≠ 0)
    (v₀ : TorusVertex width height) (m n : ℕ) :
    torusWestSouthString X η v₀ m n = torusNorthEastString X η v₀ m n := by
  have key := gridPath_prod_eq (fun i j => X (η (torusLeftEdge (v₀.1 + i, v₀.2 - j))))
    (fun i j => X (η (torusUpEdge (v₀.1 + i, v₀.2 - j)))) m n fun i _ j _ => ?_
  · simpa [torusWestSouthString, torusNorthEastString] using key
  have hv := hX _ _ _ _ _ (Finset.prod_ne_zero_iff.mp hη (v₀.1 + i, v₀.2 - j)
    (Finset.mem_univ _))
  have hr : torusLeftEdge (v₀.1 + ((i + 1 : ℕ) : ZMod width), v₀.2 - (j : ZMod height)) =
      torusRightEdge (v₀.1 + (i : ZMod width), v₀.2 - (j : ZMod height)) := by
    rw [← torusLeftEdge_add_one]
    push_cast
    rw [add_assoc]
  have hb : torusUpEdge (v₀.1 + (i : ZMod width), v₀.2 - ((j + 1 : ℕ) : ZMod height)) =
      torusDownEdge (v₀.1 + (i : ZMod width), v₀.2 - (j : ZMod height)) := by
    rw [torusDownEdge]
    push_cast
    rw [sub_sub]
  simp only [hr, hb]
  exact hv

end Monoid

/-- Pulling a virtual string through a rectangle of a torus PEPS, for the contracted network.
Under the one-site hypothesis of `torusWestSouthString_eq_torusNorthEastString`, the
contraction of the torus PEPS of `a` with the string inserted along the left and bottom sides
of a rectangle equals the contraction with the string inserted along its top and right
sides.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2465, the virtual
symmetry of a PEPS whose virtual labels fuse to the identity. -/
theorem sum_smul_torusWestSouthString_eq [Semiring M] [Module ℂ M] {d : ℕ}
    (a : Fin D → Fin D → Fin D → Fin D → Fin d → ℂ) (X : Fin D → M)
    (hX : ∀ t r b l s, a t r b l s ≠ 0 → X t * X r = X l * X b)
    (σ : TorusVertex width height → Fin d) (v₀ : TorusVertex width height) (m n : ℕ) :
    ∑ η : Edge (torusGraph width height) → Fin D,
        (∏ v, a (η (torusUpEdge v)) (η (torusRightEdge v)) (η (torusDownEdge v))
          (η (torusLeftEdge v)) (σ v)) • torusWestSouthString X η v₀ m n =
      ∑ η : Edge (torusGraph width height) → Fin D,
        (∏ v, a (η (torusUpEdge v)) (η (torusRightEdge v)) (η (torusDownEdge v))
          (η (torusLeftEdge v)) (σ v)) • torusNorthEastString X η v₀ m n := by
  refine Finset.sum_congr rfl fun η _ => ?_
  by_cases hη : ∏ v, a (η (torusUpEdge v)) (η (torusRightEdge v)) (η (torusDownEdge v))
      (η (torusLeftEdge v)) (σ v) = 0
  · rw [hη, zero_smul, zero_smul]
  · rw [torusWestSouthString_eq_torusNorthEastString a X hX σ η hη]

end PEPS
end TNLean
