/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import TNLean.PEPS.TorusSiteTensor

/-!
# RVB: the nearest-neighbour resonating valence bond state as a PEPS

**Source.** Cirac, Pérez-García, Schuch, Verstraete 2021 (arXiv:2011.12127), Appendix A,
"Two dimensions: PEPS", "The RVB state", `Papers/2011.12127/TN-Review-main.tex`
lines 2440–2448: the nearest-neighbour RVB state is the superposition of all coverings of
the lattice by nearest-neighbour singlets; its `D = 3` PEPS tensor combines the projector
$P=\lvert0\rangle[(0222\rvert+(2022\rvert+\dots]+\lvert1\rangle[(1222\rvert+(2122\rvert+\dots]$
with `±Y` on the links, and for the square lattice with a translation-invariant orientation
of the singlets it is $A=P(\mathbb 1\otimes\mathbb 1\otimes Y\otimes Y)$.
Review: arXiv:2011.12127, Appendix A, "The RVB state".

**Formalized here.** With the virtual legs ordered top, right, down, left:

* the local dimer constraint: $A^s_{urdl}\neq0$ exactly when one leg carries a spin and the
  other three carry the vacuum `2`, the spin on an unmodified leg being `s` and on a
  singlet leg `1 - s`; the nonzero entries are `±1`;
* on a torus of width and height at least three, the PEPS is the sum over all
  nearest-neighbour dimer coverings of the torus of the product of singlets
  $Y_{\sigma_{v+e},\sigma_v}$ on the covered edges, each oriented from `v` to its right or
  upper neighbour `v + e`: the superposition of nearest-neighbour singlet coverings with the
  translation-invariant orientation.

The entries are integers; the tensors are defined over `ℤ` and cast to `ℂ`.

The bond matrix of the `D = 3` bond is `Y ⊕ 1`, the singlet `Y` on the spin states `0, 1`
and `1` on the vacuum `2`, so that the bond state is $\lvert01)-\lvert10)+\lvert22)$.
The review prints only the `2 × 2` matrix `Y` (line 2446); its extension by `0` on the
vacuum would make every tensor entry vanish, since a singlet leg could then never carry
the vacuum and no configuration would have three vacuum legs. The general `±Y` orientation
choices on other lattices and the spin-liquid properties of the state are not formalized.

**Scope restriction (torus size):** the covering formula is stated for a torus of width and
height at least three sites. Documented in
`docs/paper-gaps/rmp_peps_examples_small_torus.tex`.

## Main definitions

* `TNLean.PEPS.rvbSingletY`: the bond matrix `Y ⊕ 1`.
* `TNLean.PEPS.rvbProjector`: the projector `P`.
* `TNLean.PEPS.rvbSiteTensorInt`, `TNLean.PEPS.rvbSiteTensor`, `TNLean.PEPS.rvbPEPS`: the
  tensor $P(\mathbb 1\otimes\mathbb 1\otimes Y\otimes Y)$ and its torus PEPS.
* `TNLean.PEPS.IsTorusDimerCovering`: nearest-neighbour dimer coverings of the torus.

## Main results

* `TNLean.PEPS.rvbSiteTensor_ne_zero_iff`, `TNLean.PEPS.rvbSiteTensor_apply`: the local
  dimer constraint and the explicit entries.
* `TNLean.PEPS.stateCoeff_rvbPEPS`: the RVB PEPS is the superposition of singlet coverings.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped BigOperators

namespace TNLean
namespace PEPS

/-! ### The local tensor -/

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2440–2448.
The bond matrix `Y ⊕ 1` of the `D = 3` bond: the singlet
$Y=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$ on the spin states `0, 1`
(line 2434) and `1` on the vacuum `2`. -/
def rvbSingletY : Matrix (Fin 3) (Fin 3) ℤ := !![0, -1, 0; 1, 0, 0; 0, 0, 1]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2440–2443.
The projector
$P=\lvert0\rangle[(0222\rvert+(2022\rvert+\dots]+\lvert1\rangle[(1222\rvert+(2122\rvert+\dots]$:
the entry at physical index `s` and virtual labels `u, r, d, l` is `1` when exactly one
label differs from the vacuum `2` and that label equals `s`, and `0` otherwise. -/
def rvbProjector (s : Fin 2) (u r d l : Fin 3) : ℤ :=
  if [u, r, d, l].filter (· ≠ 2) = [s.castSucc] then 1 else 0

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2444–2448.
The RVB tensor $A=P(\mathbb 1\otimes\mathbb 1\otimes Y\otimes Y)$ over `ℤ`, with the bond
matrix `rvbSingletY` on the down and left legs. -/
def rvbSiteTensorInt (s : Fin 2) (u r d l : Fin 3) : ℤ :=
  ∑ d' : Fin 3, ∑ l' : Fin 3, rvbProjector s u r d' l' * rvbSingletY d' d * rvbSingletY l' l

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2444–2448.
The RVB tensor with virtual arguments ordered top, right, down, left. -/
def rvbSiteTensor (u r d l : Fin 3) (s : Fin 2) : ℂ :=
  (rvbSiteTensorInt s u r d l : ℂ)

variable (width height : ℕ) [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2440–2448.
The RVB tensor at every site of the `width × height` torus. -/
def rvbPEPS : Tensor (torusGraph width height) 2 :=
  torusSiteTensor rvbSiteTensor

/-- The spin label read through a singlet leg: `0 ↔ 1`, and the vacuum `2` is fixed. -/
def rvbFlip : Fin 3 → Fin 3 := ![1, 0, 2]

theorem rvbSiteTensorInt_eq (s : Fin 2) (u r d l : Fin 3) :
    rvbSiteTensorInt s u r d l =
      if [u, r, rvbFlip d, rvbFlip l].filter (· ≠ 2) = [s.castSucc] then
        (if d = 1 ∨ l = 1 then -1 else 1) else 0 := by
  revert s u r d l
  decide

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2440–2448.
The explicit entries of the RVB tensor: `±1` when exactly one leg carries a spin, equal to
`s` on the top and right legs and to `1 - s` on the singlet legs (down and left), with sign
`-1` exactly when a singlet leg carries `1`; `0` otherwise. -/
theorem rvbSiteTensor_apply (u r d l : Fin 3) (s : Fin 2) :
    rvbSiteTensor u r d l s =
      if [u, r, rvbFlip d, rvbFlip l].filter (· ≠ 2) = [s.castSucc] then
        (if d = 1 ∨ l = 1 then -1 else 1) else 0 := by
  rw [rvbSiteTensor, rvbSiteTensorInt_eq]
  split_ifs <;> simp

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2440–2448.
The local dimer constraint: $A^s_{urdl}\neq0$ exactly when one of the four legs carries a
spin and the other three the vacuum `2`, the spin being `s` on the top and right legs and
`1 - s` on the down and left legs. -/
theorem rvbSiteTensor_ne_zero_iff (u r d l : Fin 3) (s : Fin 2) :
    rvbSiteTensor u r d l s ≠ 0 ↔
      [u, r, rvbFlip d, rvbFlip l].filter (· ≠ 2) = [s.castSucc] := by
  rw [rvbSiteTensor_apply]
  split_ifs <;> simp_all

/-- A bond label that is a spin `a` on an occupied edge and the vacuum otherwise. -/
def rvbBondLabel (b : Bool) (a : Fin 2) : Fin 3 :=
  if b then a.castSucc else 2

theorem rvbBondLabel_ne_two_iff (b : Bool) (a : Fin 2) : rvbBondLabel b a ≠ 2 ↔ b = true := by
  revert b a
  decide

/-- The nonzero entries force one occupied leg, and the spin `s` on the top and right
legs. -/
theorem rvbSiteTensorInt_ne_zero (s : Fin 2) (u r d l : Fin 3)
    (h : rvbSiteTensorInt s u r d l ≠ 0) :
    [decide (u ≠ 2), decide (r ≠ 2), decide (d ≠ 2), decide (l ≠ 2)].count true = 1 ∧
      rvbBondLabel (decide (u ≠ 2)) s = u ∧ rvbBondLabel (decide (r ≠ 2)) s = r := by
  revert h
  revert s u r d l
  decide

/-- The entry of the RVB tensor on the bond labels of a dimer pattern with one occupied
leg: the singlet matrix on an occupied down or left leg. -/
theorem rvbSiteTensorInt_bondLabel (s a b : Fin 2) (pu pr pd pl : Bool)
    (h : [pu, pr, pd, pl].count true = 1) :
    rvbSiteTensorInt s (rvbBondLabel pu s) (rvbBondLabel pr s) (rvbBondLabel pd b)
        (rvbBondLabel pl a) =
      (if pd then rvbSingletY s.castSucc b.castSucc else 1) *
        (if pl then rvbSingletY s.castSucc a.castSucc else 1) := by
  revert h
  revert s a b pu pr pd pl
  decide

/-! ### Dimer coverings of the torus -/

variable {width height}

/-- A nearest-neighbour dimer covering of the torus, recorded by the occupied right edge
`right v` and the occupied up edge `up v` of each site `v`: every site is covered by exactly
one of its top, right, down and left edges. -/
def IsTorusDimerCovering (right up : TorusVertex width height → Bool) : Prop :=
  ∀ v : TorusVertex width height,
    [up v, right v, up (v.1, v.2 - 1), right (v.1 - 1, v.2)].count true = 1

instance (right up : TorusVertex width height → Bool) :
    Decidable (IsTorusDimerCovering right up) := by
  unfold IsTorusDimerCovering
  infer_instance

/-- The bond configuration of a dimer covering: the spin of `v` on its occupied right and up
edges, and the vacuum on unoccupied edges. -/
def rvbCoveringBonds (σ : TorusVertex width height → Fin 2)
    (c : (TorusVertex width height → Bool) × (TorusVertex width height → Bool)) :
    (TorusVertex width height → Fin 3) × (TorusVertex width height → Fin 3) :=
  (fun v => rvbBondLabel (c.1 v) (σ v), fun v => rvbBondLabel (c.2 v) (σ v))

variable [Fact (2 < width)] [Fact (2 < height)]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2440–2448.
On a torus of width and height at least three the RVB PEPS is the superposition of all
nearest-neighbour dimer coverings, each weighted by the product of the singlets
$Y_{\sigma_{v+e},\sigma_v}$ on its occupied edges from `v` to `v + e`, `e` the unit step to
the right or up (the translation-invariant orientation of the singlets). -/
theorem stateCoeff_rvbPEPS (σ : TorusVertex width height → Fin 2) :
    stateCoeff (rvbPEPS width height) σ =
      ∑ c : {c : (TorusVertex width height → Bool) × (TorusVertex width height → Bool) //
          IsTorusDimerCovering c.1 c.2},
        ∏ v, ((if c.1.1 v then (rvbSingletY (σ (v.1 + 1, v.2)).castSucc (σ v).castSucc : ℂ)
            else 1) *
          (if c.1.2 v then (rvbSingletY (σ (v.1, v.2 + 1)).castSucc (σ v).castSucc : ℂ)
            else 1)) := by
  rw [rvbPEPS, stateCoeff_torusSiteTensor, ← Fintype.sum_prod_type']
  -- the product at the bonds of a covering
  have hval : ∀ c : {c : (TorusVertex width height → Bool) ×
      (TorusVertex width height → Bool) // IsTorusDimerCovering c.1 c.2},
      (∏ v, rvbSiteTensor ((rvbCoveringBonds σ c.1).2 v) ((rvbCoveringBonds σ c.1).1 v)
        ((rvbCoveringBonds σ c.1).2 (v.1, v.2 - 1))
        ((rvbCoveringBonds σ c.1).1 (v.1 - 1, v.2)) (σ v)) =
      ∏ v, ((if c.1.1 v then (rvbSingletY (σ (v.1 + 1, v.2)).castSucc (σ v).castSucc : ℂ)
            else 1) *
          (if c.1.2 v then (rvbSingletY (σ (v.1, v.2 + 1)).castSucc (σ v).castSucc : ℂ)
            else 1)) := by
    intro c
    have hsite : ∀ v : TorusVertex width height,
        rvbSiteTensor ((rvbCoveringBonds σ c.1).2 v) ((rvbCoveringBonds σ c.1).1 v)
          ((rvbCoveringBonds σ c.1).2 (v.1, v.2 - 1))
          ((rvbCoveringBonds σ c.1).1 (v.1 - 1, v.2)) (σ v) =
        (if c.1.2 (v.1, v.2 - 1) then
            (rvbSingletY (σ v).castSucc (σ (v.1, v.2 - 1)).castSucc : ℂ) else 1) *
          (if c.1.1 (v.1 - 1, v.2) then
            (rvbSingletY (σ v).castSucc (σ (v.1 - 1, v.2)).castSucc : ℂ) else 1) := by
      intro v
      rw [rvbSiteTensor, rvbCoveringBonds, rvbSiteTensorInt_bondLabel _ _ _ _ _ _ _ (c.2 v)]
      split_ifs <;> simp
    simp only [hsite, Finset.prod_mul_distrib]
    rw [mul_comm]
    congr 1
    · exact (Fintype.prod_equiv (Equiv.addRight ((1, 0) : TorusVertex width height)) _ _
        fun u => by
          simp only [Equiv.coe_addRight,
            show u + (1, 0) = (u.1 + 1, u.2) from Prod.ext rfl (add_zero _),
            add_sub_cancel_right]).symm
    · exact (Fintype.prod_equiv (Equiv.addRight ((0, 1) : TorusVertex width height)) _ _
        fun u => by
          simp only [Equiv.coe_addRight,
            show u + (0, 1) = (u.1, u.2 + 1) from Prod.ext (add_zero _) rfl,
            add_sub_cancel_right]).symm
  symm
  refine Finset.sum_bij_ne_zero (fun c _ _ => rvbCoveringBonds σ c.1) (fun _ _ _ =>
    Finset.mem_univ _) ?_ ?_ ?_
  · intro c₁ _ _ c₂ _ _ h
    apply Subtype.ext
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
    · have := congrFun h1 v
      simp only [rvbCoveringBonds] at this
      have e1 := rvbBondLabel_ne_two_iff (c₁.1.1 v) (σ v)
      have e2 := rvbBondLabel_ne_two_iff (c₂.1.1 v) (σ v)
      rw [this] at e1
      exact Bool.eq_iff_iff.mpr (e1.symm.trans e2)
    · have := congrFun h2 v
      simp only [rvbCoveringBonds] at this
      have e1 := rvbBondLabel_ne_two_iff (c₁.1.2 v) (σ v)
      have e2 := rvbBondLabel_ne_two_iff (c₂.1.2 v) (σ v)
      rw [this] at e1
      exact Bool.eq_iff_iff.mpr (e1.symm.trans e2)
  · intro x _ hx
    have hsite : ∀ v, rvbSiteTensorInt (σ v) (x.2 v) (x.1 v) (x.2 (v.1, v.2 - 1))
        (x.1 (v.1 - 1, v.2)) ≠ 0 := by
      intro v hv
      apply hx
      exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [rvbSiteTensor, hv])
    let c : {c : (TorusVertex width height → Bool) × (TorusVertex width height → Bool) //
        IsTorusDimerCovering c.1 c.2} :=
      ⟨(fun v => decide (x.1 v ≠ 2), fun v => decide (x.2 v ≠ 2)), fun v =>
        (rvbSiteTensorInt_ne_zero _ _ _ _ _ (hsite v)).1⟩
    have hbond : rvbCoveringBonds σ c.1 = x :=
      Prod.ext (funext fun v => (rvbSiteTensorInt_ne_zero _ _ _ _ _ (hsite v)).2.2)
        (funext fun v => (rvbSiteTensorInt_ne_zero _ _ _ _ _ (hsite v)).2.1)
    refine ⟨c, Finset.mem_univ _, ?_, hbond⟩
    rw [← hval, hbond]
    exact hx
  · intro c _ _
    exact (hval c).symm

end PEPS
end TNLean
