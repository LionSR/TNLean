/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import TNLean.PEPS.GInjective
import TNLean.PEPS.TorusSiteTensor

/-!
# Operator strings on a torus PEPS and their deformation

**Source.** Schuch, Cirac, Pérez-García 2010 (arXiv:1001.3807),
`Papers/1001.3807/paper_v3.tex`:
* Definition `def:2d-Ug-inj`, lines 1278–1295, clause i), equation `eq:2d-ug-sym`: a
  `G`-injective PEPS tensor is invariant under `U_g` on its virtual level; the figure places
  `U_g` on the two incoming legs (left and top) and `U_g⁻¹` on the two outgoing legs (right and
  down), the horizontal edges pointing right and the vertical edges pointing down.
* Lines 1622–1647, equation `eq:2d:move-strings`: by this invariance a string of `U_g`'s on
  the virtual bonds of the contracted network can be deformed continuously across a site;
  whether `U_g` or `U_g⁻¹` sits on a bond depends on the side from which the oriented string
  crosses the oriented edge (lines 1645–1647).
* Lemma "Deformations of the string", lines 2199–2204, with proof lines 2205–2214: away from
  its endpoint plaquettes a string can be deformed at will without acting on the system; the
  proof uses only `eq:2d:move-strings`.

**Formalized here.** A PEPS on the `width × height` torus whose bonds carry operators: each
bond, oriented as in the source, carries a matrix, and the network contracts the site tensors
through these matrices (`TNLean.PEPS.torusBondNetwork`). With identity matrices this is the
contracted PEPS (`torusBondNetwork_one`, `stateCoeff_torusSiteTensor_eq_torusBondNetwork`);
with diagonal matrices it is the contraction with a diagonal virtual string inserted
(`torusBondNetwork_diagonal`). A local change of basis on the legs of every site can be moved
from the bonds into the site tensors (`torusBondNetwork_gauge`). For a site tensor invariant
under `U_g` on its four legs, clause i) of Definition `def:2d-Ug-inj`
(`TNLean.PEPS.IsGInjective.invariant`), the string of `U_g`'s along the left and bottom sides
of a rectangle of sites and the string along its top and right sides give the same network
(`torusBondNetwork_westSouthOperatorString_eq`). This is the deformation of the string across
the sites of the rectangle, `eq:2d:move-strings` iterated over the rectangle.

The argument uses only the invariance clause i). The source assumes in Definition
`def:2d-Ug-inj` that `U_g` is semi-regular; the deformation holds for every representation, and
the Lean statement assumes only the invariance, as does the source's proof (lines 2205–2214).
The endpoint clause of the Lemma (the parity of `g`'s around a plaquette cannot change) is not
formalized here.

The rectangle has fewer columns than the torus width and fewer rows than its height, so that
it does not wrap around the torus; the source deforms strings locally.

## Relation to the diagonal strings

The strings of `TNLean.PEPS.torusWestSouthString` act on each bond diagonally, by an element
`X α` of a monoid, possibly noncommutative, multiplied in the order of the crossings: a matrix
product operator on the virtual level. The operator strings here act on each crossed bond by a
matrix. For scalar values `X α` both are the network with diagonal matrices on the crossed
bonds, `torusBondNetwork_diagonal`.

## Main definitions

* `TNLean.PEPS.torusLegKernel`, `TNLean.PEPS.torusLegMatrix`, `TNLean.PEPS.torusLegRep`: the
  action of `U_g` on the four virtual legs of a site, as in `eq:2d-ug-sym`.
* `TNLean.PEPS.torusBondNetwork`: the torus network with an operator on every bond.
* `TNLean.PEPS.torusDress`: a site tensor with matrices absorbed into its legs.
* `TNLean.PEPS.torusWestSouthOperatorString`, `TNLean.PEPS.torusNorthEastOperatorString`: the
  two strings of `U_g`'s along the sides of a rectangle.

## Main results

* `TNLean.PEPS.torusBondNetwork_diagonal`, `TNLean.PEPS.torusBondNetwork_one`.
* `TNLean.PEPS.torusBondNetwork_gauge`: moving bond matrices into the site tensors.
* `TNLean.PEPS.torusBondNetwork_westSouthOperatorString_eq`: deformation of a string of
  `U_g`'s across a rectangle of `G`-invariant tensors.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Kronecker

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The action of `U_g` on the four legs of a site -/

section Legs

/-- The matrix on the four virtual legs, ordered top, right, down, left, that places `P` on the
incoming legs (top and left) and `Q` on the outgoing legs (right and down), each acting along
the orientation of its edge. A site tensor `A` absorbs it as the row vector `A ᵥ* K`. -/
def torusLegKernel (P Q : Matrix V V ℂ) : Matrix (V × V × V × V) (V × V × V × V) ℂ :=
  P ⊗ₖ (Q.transpose ⊗ₖ (Q.transpose ⊗ₖ P))

omit [Fintype V] [DecidableEq V] in
theorem torusLegKernel_apply (P Q : Matrix V V ℂ) (c c' : V × V × V × V) :
    torusLegKernel P Q c c' =
      P c.1 c'.1 * Q c'.2.1 c.2.1 * Q c'.2.2.1 c.2.2.1 * P c.2.2.2 c'.2.2.2 := by
  obtain ⟨t, r, b, l⟩ := c
  obtain ⟨t', r', b', l'⟩ := c'
  simp [torusLegKernel, mul_assoc]

omit [DecidableEq V] in
theorem torusLegKernel_mul (P Q P' Q' : Matrix V V ℂ) :
    torusLegKernel P Q * torusLegKernel P' Q' = torusLegKernel (P * P') (Q' * Q) := by
  simp only [torusLegKernel, ← Matrix.mul_kronecker_mul, Matrix.transpose_mul]

variable {G : Type*} [Group G]

/-- Source: arXiv:1001.3807, Definition `def:2d-Ug-inj`, `Papers/1001.3807/paper_v3.tex`
lines 1278–1295, equation `eq:2d-ug-sym`. For a representation `U` of `G` by matrices on one
bond, the matrix of `U_g` on the incoming legs (top and left) and `U_g⁻¹` on the outgoing legs
(right and down) of a site. -/
def torusLegMatrix (U : G →* Matrix V V ℂ) : G →* Matrix (V × V × V × V) (V × V × V × V) ℂ where
  toFun g := torusLegKernel (U g) (U g⁻¹)
  map_one' := by simp [torusLegKernel]
  map_mul' g h := by rw [torusLegKernel_mul, mul_inv_rev, map_mul, map_mul]

/-- Source: arXiv:1001.3807, Definition `def:2d-Ug-inj`, `Papers/1001.3807/paper_v3.tex`
lines 1278–1295, equation `eq:2d-ug-sym`. The representation of `G` on the virtual level of a
site with four legs, `U_g` on the incoming legs and `U_g⁻¹` on the outgoing legs. -/
noncomputable def torusLegRep (U : G →* Matrix V V ℂ) :
    Representation ℂ G ((V × V × V × V) → ℂ) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp (torusLegMatrix U)

theorem torusLegRep_apply (U : G →* Matrix V V ℂ) (g : G) (x : (V × V × V × V) → ℂ) :
    torusLegRep U g x = Matrix.mulVec (torusLegMatrix U g) x :=
  Matrix.toLinAlgEquiv'_apply _ _

/-- Clause i) of Definition `def:2d-Ug-inj` for a site tensor, in coordinates: for every
physical index `s`, the virtual tensor `c ↦ a c s` absorbs the matrix of `U_g` on its legs. -/
theorem vecMul_torusLegMatrix_of_comp_eq {Phys : Type*} (U : G →* Matrix V V ℂ)
    (a : V → V → V → V → Phys → ℂ) (ha : ∀ g, siteMap a ∘ₗ torusLegRep U g = siteMap a)
    (g : G) (s : Phys) :
    Matrix.vecMul (fun c => a c.1 c.2.1 c.2.2.1 c.2.2.2 s) (torusLegMatrix U g) =
      fun c => a c.1 c.2.1 c.2.2.1 c.2.2.2 s := by
  funext c₀
  have h := congrFun (LinearMap.congr_fun (ha g) (Pi.single c₀ 1)) s
  simpa [siteMap_apply, torusLegRep_apply, Matrix.mulVec, dotProduct, Pi.single_apply,
    Matrix.vecMul, Finset.mul_sum] using h

end Legs

/-! ### The torus network with an operator on every bond -/

variable {width height : ℕ} [NeZero width] [NeZero height]

/-- The torus network of the site tensors `A v`, functions of the four virtual indices ordered
top, right, down, left, with the matrix `Oh v` on the horizontal bond from `v` to its right
neighbour and `Ov v` on the vertical bond between `v` and its upper neighbour. As in
arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex` lines 1278–1295 and 1622–1647, horizontal
edges point right and vertical edges point down, and a bond carrying the matrix `O` has weight
`O i j` when its head reads `i` and its tail reads `j`.

The sum runs over the bond ends `β v = (hT, hH, vT, vH)`: the indices read by the tail `v` and
the head `(x + 1, y)` of the horizontal bond of `v = (x, y)`, and by the tail `(x, y + 1)` and
the head `v` of its vertical bond. The site `v` reads `vH v` on top, `hT v` on the right,
`vT (x, y - 1)` below and `hH (x - 1, y)` on the left. -/
def torusBondNetwork (A : TorusVertex width height → (V × V × V × V) → ℂ)
    (Oh Ov : TorusVertex width height → Matrix V V ℂ) : ℂ :=
  ∑ β : TorusVertex width height → V × V × V × V,
    (∏ v, Oh v (β v).2.1 (β v).1 * Ov v (β v).2.2.2 (β v).2.2.1) *
      ∏ v, A v ((β v).2.2.2, (β v).1, (β (v.1, v.2 - 1)).2.2.1, (β (v.1 - 1, v.2)).2.1)

/-- With diagonal matrices on every bond, the network is the contraction over one index per
bond, weighted by the diagonal entries: the contraction of the PEPS with a diagonal virtual
string inserted. -/
theorem torusBondNetwork_diagonal (A : TorusVertex width height → (V × V × V × V) → ℂ)
    (xh xv : TorusVertex width height → V → ℂ) :
    torusBondNetwork A (fun v => Matrix.diagonal (xh v)) (fun v => Matrix.diagonal (xv v)) =
      ∑ hb : TorusVertex width height → V, ∑ vb : TorusVertex width height → V,
        (∏ v, xh v (hb v) * xv v (vb v)) *
          ∏ v, A v (vb v, hb v, vb (v.1, v.2 - 1), hb (v.1 - 1, v.2)) := by
  rw [← Fintype.sum_prod_type']
  unfold torusBondNetwork
  refine (Fintype.sum_of_injective (fun p v => (p.1 v, p.1 v, p.2 v, p.2 v)) ?_ _ _ ?_ ?_).symm
  · intro p q h
    have h' := fun v => congrFun h v
    simp only [Prod.mk.injEq] at h'
    exact Prod.ext (funext fun v => (h' v).1) (funext fun v => (h' v).2.2.1)
  · intro β hβ
    have : ∃ v, (β v).2.1 ≠ (β v).1 ∨ (β v).2.2.2 ≠ (β v).2.2.1 := by
      by_contra hne
      push Not at hne
      exact hβ ⟨(fun v => (β v).1, fun v => (β v).2.2.1), funext fun v =>
        Prod.ext rfl (Prod.ext (hne v).1.symm (Prod.ext rfl (hne v).2.symm))⟩
    obtain ⟨v, hv⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ v), zero_mul]
    rcases hv with hv | hv <;> simp [Matrix.diagonal_apply_ne _ hv]
  · intro p
    simp [Matrix.diagonal_apply_eq]

/-- With the identity on every bond, the network is the contraction over one index per bond,
the contracted PEPS. -/
theorem torusBondNetwork_one (A : TorusVertex width height → (V × V × V × V) → ℂ) :
    torusBondNetwork A 1 1 =
      ∑ hb : TorusVertex width height → V, ∑ vb : TorusVertex width height → V,
        ∏ v, A v (vb v, hb v, vb (v.1, v.2 - 1), hb (v.1 - 1, v.2)) := by
  have h := torusBondNetwork_diagonal A (fun _ _ => 1) (fun _ _ => 1)
  simp only [Matrix.diagonal_one, mul_one, Finset.prod_const_one, one_mul] at h
  exact h

/-- Bridge: on a torus of width and height at least three, the coefficient of the torus PEPS
of a four-leg tensor `a` is the network of `a` with the identity on every bond. -/
theorem stateCoeff_torusSiteTensor_eq_torusBondNetwork [Fact (1 < width)] [Fact (1 < height)]
    [Fact (2 < width)] [Fact (2 < height)] {D d : ℕ}
    (a : Fin D → Fin D → Fin D → Fin D → Fin d → ℂ) (σ : TorusVertex width height → Fin d) :
    stateCoeff (torusSiteTensor a) σ =
      torusBondNetwork (fun v c => a c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v)) 1 1 := by
  rw [torusBondNetwork_one, stateCoeff_torusSiteTensor]

/-! ### Moving bond matrices into the site tensors -/

/-- The site tensor `A` with the matrix `P` absorbed into its incoming legs (top and left) and
`Q` into its outgoing legs (right and down). -/
def torusDress (P Q : Matrix V V ℂ) (A : (V × V × V × V) → ℂ) : (V × V × V × V) → ℂ :=
  Matrix.vecMul A (torusLegKernel P Q)

omit [DecidableEq V] in
/-- A change of basis on the bonds of the torus network can be moved into the site tensors:
multiplying the matrix of every bond by `P` at its head and by `Q` at its tail gives the
network in which every site tensor has absorbed `P v` into its incoming legs and `Q v` into its
outgoing legs. This is the move of `eq:2d:move-strings`, arXiv:1001.3807,
`Papers/1001.3807/paper_v3.tex` lines 1622–1647, at every site at once. -/
theorem torusBondNetwork_gauge (A : TorusVertex width height → (V × V × V × V) → ℂ)
    (Oh Ov P Q : TorusVertex width height → Matrix V V ℂ) :
    torusBondNetwork A (fun v => P (v.1 + 1, v.2) * Oh v * Q v)
        (fun v => P v * Ov v * Q (v.1, v.2 + 1)) =
      torusBondNetwork (fun v => torusDress (P v) (Q v) (A v)) Oh Ov := by
  -- The site arguments read from the bond ends.
  set args : (TorusVertex width height → V × V × V × V) →
      TorusVertex width height → V × V × V × V :=
    fun β v => ((β v).2.2.2, (β v).1, (β (v.1, v.2 - 1)).2.2.1, (β (v.1 - 1, v.2)).2.1)
    with hargs
  let φ : (TorusVertex width height → V × V × V × V) ≃
      (TorusVertex width height → V × V × V × V) :=
    { toFun := args
      invFun := fun C v => ((C v).2.1, (C (v.1 + 1, v.2)).2.2.2, (C (v.1, v.2 + 1)).2.2.1,
        (C v).1)
      left_inv := fun β => funext fun v => by simp [hargs]
      right_inv := fun C => funext fun v => by simp [hargs] }
  -- Expanding the products of matrices on the bonds.
  have hL : ∀ β : TorusVertex width height → V × V × V × V,
      (∏ v, (P (v.1 + 1, v.2) * Oh v * Q v) (β v).2.1 (β v).1 *
          (P v * Ov v * Q (v.1, v.2 + 1)) (β v).2.2.2 (β v).2.2.1) =
        ∑ γ : TorusVertex width height → V × V × V × V, ∏ v,
          (P (v.1 + 1, v.2) (β v).2.1 (γ v).2.1 * Oh v (γ v).2.1 (γ v).1 * Q v (γ v).1 (β v).1 *
            (P v (β v).2.2.2 (γ v).2.2.2 * Ov v (γ v).2.2.2 (γ v).2.2.1 *
              Q (v.1, v.2 + 1) (γ v).2.2.1 (β v).2.2.1)) := by
    intro β
    refine (Finset.prod_congr rfl fun v _ => mul_comm _ _).trans ?_
    refine (Finset.prod_congr rfl fun v _ => ?_).trans
      (Fintype.prod_sum fun v (γ : V × V × V × V) =>
      P (v.1 + 1, v.2) (β v).2.1 γ.2.1 * Oh v γ.2.1 γ.1 * Q v γ.1 (β v).1 *
        (P v (β v).2.2.2 γ.2.2.2 * Ov v γ.2.2.2 γ.2.2.1 * Q (v.1, v.2 + 1) γ.2.2.1 (β v).2.2.1))
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  -- Expanding the dressed site tensors.
  have hR : ∀ β : TorusVertex width height → V × V × V × V,
      (∏ v, torusDress (P v) (Q v) (A v) (args β v)) =
        ∑ C : TorusVertex width height → V × V × V × V,
          ∏ v, A v (C v) * torusLegKernel (P v) (Q v) (C v) (args β v) := by
    intro β
    exact Fintype.prod_sum fun v (c : V × V × V × V) =>
      A v c * torusLegKernel (P v) (Q v) c (args β v)
  -- Matching the terms.
  have key : ∀ β γ : TorusVertex width height → V × V × V × V,
      (∏ v, (P (v.1 + 1, v.2) (β v).2.1 (γ v).2.1 * Oh v (γ v).2.1 (γ v).1 *
          Q v (γ v).1 (β v).1 * (P v (β v).2.2.2 (γ v).2.2.2 * Ov v (γ v).2.2.2 (γ v).2.2.1 *
            Q (v.1, v.2 + 1) (γ v).2.2.1 (β v).2.2.1))) * ∏ v, A v (args β v) =
        (∏ v, Oh v (γ v).2.1 (γ v).1 * Ov v (γ v).2.2.2 (γ v).2.2.1) *
          ∏ v, A v (args β v) * torusLegKernel (P v) (Q v) (args β v) (args γ v) := by
    intro β γ
    have hP := prod_torus_sub_fst (width := width) (height := height)
      fun u u' => P u (β u').2.1 (γ u').2.1
    have hQ := prod_torus_sub_snd (width := width) (height := height)
      fun u u' => Q u (γ u').2.2.1 (β u').2.2.1
    simp only [hargs, torusLegKernel_apply, Finset.prod_mul_distrib, hP, hQ]
    ring
  unfold torusBondNetwork
  simp only [hL, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun γ _ => ?_
  change _ = _ * ∏ v, torusDress (P v) (Q v) (A v) (args γ v)
  rw [hR, Finset.mul_sum]
  exact Fintype.sum_equiv φ _ _ fun β => key β γ

/-! ### Strings of `U_g` along the sides of a rectangle -/

section Strings

variable {G : Type*} [Group G]

/-- A comparison of the column (or row) offsets of the two ends of a bond, when the bond does
not cross either side of the interval `[0, m)`. -/
private theorem zmod_val_add_one_lt_iff {w : ℕ} [NeZero w] {c : ZMod w} {m : ℕ}
    (h0 : c + 1 ≠ 0) (h1 : c + 1 ≠ m) : (c + 1).val < m ↔ c.val < m := by
  have hlt := ZMod.val_lt c
  have hc : c + 1 = ((c.val + 1 : ℕ) : ZMod w) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  have hne : c.val + 1 ≠ w := fun h => h0 (by rw [hc, h, ZMod.natCast_self])
  have hv : (c + 1).val = c.val + 1 := by
    rw [hc, ZMod.val_natCast_of_lt (by omega)]
  have hm' : c.val + 1 ≠ m := fun h => h1 (by rw [hc, h])
  rw [hv]
  omega

private theorem zmod_not_val_lt_of_add_one_eq_zero {w : ℕ} [NeZero w] {c : ZMod w} {m : ℕ}
    (hm : m < w) (h0 : c + 1 = 0) : ¬c.val < m := by
  have hc : c + 1 = ((c.val + 1 : ℕ) : ZMod w) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [hc, ZMod.natCast_eq_zero_iff] at h0
  have := Nat.le_of_dvd (Nat.succ_pos _) h0
  omega

private theorem zmod_val_lt_of_add_one_eq {w : ℕ} [NeZero w] {c : ZMod w} {m : ℕ}
    (hm : m < w) (h0 : c + 1 ≠ 0) (h1 : c + 1 = m) : ¬(c + 1).val < m ∧ c.val < m := by
  have hlt := ZMod.val_lt c
  have hc : c + 1 = ((c.val + 1 : ℕ) : ZMod w) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  have hne : c.val + 1 ≠ w := fun h => h0 (by rw [hc, h, ZMod.natCast_self])
  rw [h1, ZMod.val_natCast_of_lt hm]
  rw [hc, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hm] at h1
  omega

/-- Source: arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex` lines 1622–1647, equation
`eq:2d:move-strings`. The string of `U_g`'s across the rectangle of `m` columns and `n` rows
with upper left site `v₀ = (x₀, y₀)` that runs down across the left legs of the sites
`(x₀, y₀ - j)`, `j < n`, and then right across the down legs of the sites
`(x₀ + i, y₀ - n + 1)`, `i < m`. By the orientation rule of lines 1645–1647, the string carries
`U_g⁻¹` on the horizontal bonds, which it crosses going down, and `U_g` on the vertical bonds,
which it crosses going right. The pair lists the matrices on the horizontal and on the vertical
bonds. -/
def torusWestSouthOperatorString (U : G →* Matrix V V ℂ) (g : G)
    (v₀ : TorusVertex width height) (m n : ℕ) :
    (TorusVertex width height → Matrix V V ℂ) × (TorusVertex width height → Matrix V V ℂ) :=
  (fun v => if v.1 + 1 = v₀.1 ∧ (v₀.2 - v.2).val < n then U g⁻¹ else 1,
    fun v => if v.2 = v₀.2 - n ∧ (v.1 - v₀.1).val < m then U g else 1)

/-- Source: arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex` lines 1622–1647, equation
`eq:2d:move-strings`. The string of `U_g`'s across the rectangle of `m` columns and `n` rows
with upper left site `v₀ = (x₀, y₀)` that runs right across the top legs of the sites
`(x₀ + i, y₀)`, `i < m`, and then down across the right legs of the sites
`(x₀ + m - 1, y₀ - j)`, `j < n`, with `U_g` on the vertical and `U_g⁻¹` on the horizontal
bonds. -/
def torusNorthEastOperatorString (U : G →* Matrix V V ℂ) (g : G)
    (v₀ : TorusVertex width height) (m n : ℕ) :
    (TorusVertex width height → Matrix V V ℂ) × (TorusVertex width height → Matrix V V ℂ) :=
  (fun v => if v.1 + 1 = v₀.1 + m ∧ (v₀.2 - v.2).val < n then U g⁻¹ else 1,
    fun v => if v.2 = v₀.2 ∧ (v.1 - v₀.1).val < m then U g else 1)

/-- Source: arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex` lines 1622–1647 (equation
`eq:2d:move-strings`) and the Lemma "Deformations of the string", lines 2199–2214. Let `a` be a
four-leg PEPS tensor that satisfies clause i) of Definition `def:2d-Ug-inj`, lines 1278–1295:
it is invariant under `U_g` on its incoming and `U_g⁻¹` on its outgoing legs. Then in the torus
network of `a` the string of `U_g`'s along the left and bottom sides of a rectangle of sites
can be deformed into the string along its top and right sides: both give the same network.

Only the invariance clause i) is used. The source assumes that `U` is semi-regular; the
deformation holds for every representation, and its proof in the source (lines 2205–2214) uses
only the invariance, so no hypothesis is added. The rectangle does not wrap around the torus,
`m < width` and `n < height`. -/
theorem torusBondNetwork_westSouthOperatorString_eq {Phys : Type*} (U : G →* Matrix V V ℂ)
    (a : V → V → V → V → Phys → ℂ) (ha : ∀ g, siteMap a ∘ₗ torusLegRep U g = siteMap a)
    (σ : TorusVertex width height → Phys) (g : G) (v₀ : TorusVertex width height) {m n : ℕ}
    (hm : m < width) (hn : n < height) :
    torusBondNetwork (fun v c => a c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
        (torusWestSouthOperatorString U g v₀ m n).1
        (torusWestSouthOperatorString U g v₀ m n).2 =
      torusBondNetwork (fun v c => a c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
        (torusNorthEastOperatorString U g v₀ m n).1
        (torusNorthEastOperatorString U g v₀ m n).2 := by
  -- The gauge transformation by `g⁻¹` on the sites of the rectangle.
  set Φ : TorusVertex width height → G :=
    fun v => if (v.1 - v₀.1).val < m ∧ (v₀.2 - v.2).val < n then g⁻¹ else 1 with hΦ
  have hU : U g⁻¹ * U g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have h1 : (torusWestSouthOperatorString U g v₀ m n).1 =
      fun v => U (Φ (v.1 + 1, v.2)) * (torusNorthEastOperatorString U g v₀ m n).1 v *
        U (Φ v)⁻¹ := by
    funext v
    simp only [torusWestSouthOperatorString, torusNorthEastOperatorString, hΦ]
    by_cases hr : (v₀.2 - v.2).val < n
    · set c := v.1 - v₀.1 with hc
      have e : v.1 + 1 - v₀.1 = c + 1 := by rw [hc]; ring
      have e0 : v.1 + 1 = v₀.1 ↔ c + 1 = 0 := by
        rw [hc]; constructor <;> intro h <;> linear_combination h
      have e1 : v.1 + 1 = v₀.1 + m ↔ c + 1 = m := by
        rw [hc]; constructor <;> intro h <;> linear_combination h
      simp only [e, e0, e1, hr, and_true]
      by_cases h0 : c + 1 = 0
      · have ht := zmod_not_val_lt_of_add_one_eq_zero hm h0
        rcases Nat.eq_zero_or_pos m with rfl | hm0
        · simp [h0]
        · have hne : ¬c + 1 = (m : ZMod width) := by
            rw [h0]; intro h
            have := Nat.le_of_dvd hm0 ((ZMod.natCast_eq_zero_iff _ _).1 h.symm)
            omega
          simp only [eq_true h0, eq_false hne, eq_false ht, ite_true, ite_false]
          simp [h0, hm0]
      · by_cases h1 : c + 1 = m
        · obtain ⟨hs, ht⟩ := zmod_val_lt_of_add_one_eq hm h0 h1
          simp only [eq_false h0, eq_false hs, eq_true h1, eq_true ht, ite_true, ite_false]
          simp [hU]
        · simp only [zmod_val_add_one_lt_iff h0 h1, eq_false h0, eq_false h1, ite_false, mul_one]
          split_ifs <;> simp [hU]
    · simp [hr]
  have h2 : (torusWestSouthOperatorString U g v₀ m n).2 =
      fun v => U (Φ v) * (torusNorthEastOperatorString U g v₀ m n).2 v *
        U (Φ (v.1, v.2 + 1))⁻¹ := by
    funext v
    simp only [torusWestSouthOperatorString, torusNorthEastOperatorString, hΦ]
    by_cases hr : (v.1 - v₀.1).val < m
    · set c := v₀.2 - (v.2 + 1) with hc
      have e : v₀.2 - v.2 = c + 1 := by rw [hc]; ring
      have e0 : v.2 = v₀.2 ↔ c + 1 = 0 := by
        rw [hc]; constructor <;> intro h <;> linear_combination -h
      have e1 : v.2 = v₀.2 - n ↔ c + 1 = n := by
        rw [hc]; constructor <;> intro h <;> linear_combination -h
      simp only [e, e0, e1, hr, true_and]
      by_cases h0 : c + 1 = 0
      · have ht := zmod_not_val_lt_of_add_one_eq_zero hn h0
        rcases Nat.eq_zero_or_pos n with rfl | hn0
        · simp [h0]
        · have hne : ¬c + 1 = (n : ZMod height) := by
            rw [h0]; intro h
            have := Nat.le_of_dvd hn0 ((ZMod.natCast_eq_zero_iff _ _).1 h.symm)
            omega
          simp only [eq_false hne, eq_true h0, eq_false ht, ite_false]
          simp [h0, hn0, hU]
      · by_cases h1 : c + 1 = n
        · obtain ⟨hs, ht⟩ := zmod_val_lt_of_add_one_eq hn h0 h1
          simp only [eq_true h1, eq_false hs, eq_false h0, eq_true ht, ite_true, ite_false]
          simp
        · simp only [zmod_val_add_one_lt_iff h0 h1, eq_false h0, eq_false h1]
          split_ifs <;> simp [hU]
    · simp [hr]
  rw [h1, h2]
  refine (torusBondNetwork_gauge _ _ _ (fun v => U (Φ v)) (fun v => U (Φ v)⁻¹)).trans ?_
  congr 1
  funext v
  exact vecMul_torusLegMatrix_of_comp_eq U a ha (Φ v) (σ v)

/-- Source: arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex` lines 1622–1647 and 2199–2214,
for a `G`-injective tensor: the string deformation of
`torusBondNetwork_westSouthOperatorString_eq` holds for every tensor that is `G`-injective for
the representation `torusLegRep U`, since it uses only the invariance clause. -/
theorem IsGInjective.torusBondNetwork_westSouthOperatorString_eq {Phys : Type*}
    {U : G →* Matrix V V ℂ} {a : V → V → V → V → Phys → ℂ}
    (ha : IsGInjective (torusLegRep U) (siteMap a))
    (σ : TorusVertex width height → Phys) (g : G) (v₀ : TorusVertex width height) {m n : ℕ}
    (hm : m < width) (hn : n < height) :
    torusBondNetwork (fun v c => a c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
        (torusWestSouthOperatorString U g v₀ m n).1
        (torusWestSouthOperatorString U g v₀ m n).2 =
      torusBondNetwork (fun v c => a c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
        (torusNorthEastOperatorString U g v₀ m n).1
        (torusNorthEastOperatorString U g v₀ m n).2 :=
  PEPS.torusBondNetwork_westSouthOperatorString_eq U a ha.invariant σ g v₀ hm hn

end Strings

end PEPS
end TNLean
