/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusOperatorString
import TNLean.Algebra.FinSumPermutation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Local Gram expansion of a torus PEPS with bond operators

The overlap of two actual torus bond networks is a double sum over their bond-end
labels. The sum over physical configurations factors into one local site pairing
per vertex. The horizontal and vertical matrices remain in their original bond
weights, with no assumption on the Gram operator of the contracted network.

For permutation matrices, each head label is determined by its tail label. Thus
one label remains per bond. In the left regular representation the head is the
group element of the operator multiplied by the tail.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807,
`Papers/1001.3807/paper_v3.tex`, equation `eq:2d:peps-with-ug-uh`, lines 1515–1525,
and Definition 6.1 (`def:iso:isopeps`), lines 1692–1702. The orientation is that of
`torusBondNetwork`: horizontal bonds point right and vertical bonds point down.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

/-- Expanding a pairing of weighted products and summing the independent physical
labels gives a product of local pairings. This finite-sum identity applies to any
finite site set and two independently indexed families of virtual assignments. -/
theorem sum_star_weightedSiteProduct_mul
    {Site Phys I J : Type*} [Fintype Site] [DecidableEq Site]
    [Fintype Phys] [Fintype I] [Fintype J]
    (a : I → Site → Phys → ℂ) (b : J → Site → Phys → ℂ) (u : I → ℂ) (w : J → ℂ) :
    (∑ σ : Site → Phys, star (∑ i : I, u i * ∏ v, a i v (σ v)) *
      ∑ j : J, w j * ∏ v, b j v (σ v)) =
      ∑ i : I, ∑ j : J, (star (u i) * w j) *
        ∏ v, ∑ s : Phys, star (a i v s) * b j v s := by
  classical
  simp only [star_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Fintype.sum_reverse_three]
  apply Finset.sum_congr₂
  intro i _ j _
  calc
    _ = (star (u i) * w j) * ∑ σ : Site → Phys,
        star (∏ v, a i v (σ v)) * ∏ v, b j v (σ v) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      rw [star_mul]
      ring
    _ = _ := by
      congr 1
      simp only [star_prod, ← Finset.prod_mul_distrib]
      exact (Fintype.prod_sum (fun (v : Site) (s : Phys) =>
        star (a i v s) * b j v s)).symm

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {width height : ℕ} [NeZero width] [NeZero height]

/-- The four labels read by a torus vertex from the bond-end assignment,
ordered top, right, bottom, left, exactly as in the actual bond network. -/
def torusBondSiteLabels (β : TorusVertex width height → V × V × V × V)
    (v : TorusVertex width height) : V × V × V × V :=
  ((β v).2.2.2, (β v).1, (β (v.1, v.2 - 1)).2.2.1, (β (v.1 - 1, v.2)).2.1)

/-- The product of all operator entries on the oriented torus bonds.
Rows are head labels and columns are tail labels. -/
def torusBondWeight (Oh Ov : TorusVertex width height → Matrix V V ℂ)
    (β : TorusVertex width height → V × V × V × V) : ℂ :=
  ∏ v, Oh v (β v).2.1 (β v).1 * Ov v (β v).2.2.2 (β v).2.2.1

omit [Fintype V] [DecidableEq V] in
/-- Summing physical configurations factors the pairing of the vertex products
into the literal pairings of the site tensors. -/
theorem sum_star_torusSiteProduct_mul {Phys : Type*} [Fintype Phys]
    (a b : TorusVertex width height → (V × V × V × V) → Phys → ℂ)
    (β γ : TorusVertex width height → V × V × V × V) :
    (∑ σ : TorusVertex width height → Phys,
      star (∏ v, a v (torusBondSiteLabels β v) (σ v)) *
        ∏ v, b v (torusBondSiteLabels γ v) (σ v)) =
      ∏ v, ∑ s : Phys,
        star (a v (torusBondSiteLabels β v) s) * b v (torusBondSiteLabels γ v) s := by
  classical
  simp only [star_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (v : TorusVertex width height) (s : Phys) =>
    star (a v (torusBondSiteLabels β v) s) * b v (torusBondSiteLabels γ v) s)).symm

omit [DecidableEq V] in
/-- Source: SCP10, equation `eq:2d:peps-with-ug-uh`, lines 1515–1525, and
Definition 6.1, lines 1692–1702. The overlap of two actual torus networks is the
double contraction of their bond weights and literal site Gram pairings. -/
theorem sum_star_torusBondNetwork_mul {Phys : Type*} [Fintype Phys]
    (a b : TorusVertex width height → (V × V × V × V) → Phys → ℂ)
    (OhA OvA OhB OvB : TorusVertex width height → Matrix V V ℂ) :
    (∑ σ : TorusVertex width height → Phys,
      star (torusBondNetwork (fun v c => a v c (σ v)) OhA OvA) *
        torusBondNetwork (fun v c => b v c (σ v)) OhB OvB) =
      ∑ β : TorusVertex width height → V × V × V × V,
        ∑ γ : TorusVertex width height → V × V × V × V,
          (star (torusBondWeight OhA OvA β) * torusBondWeight OhB OvB γ) *
            ∏ v, ∑ s : Phys,
              star (a v (torusBondSiteLabels β v) s) * b v (torusBondSiteLabels γ v) s := by
  simpa only [torusBondNetwork, torusBondWeight, torusBondSiteLabels] using
    sum_star_weightedSiteProduct_mul
      (fun β v s => a v (torusBondSiteLabels β v) s)
      (fun γ v s => b v (torusBondSiteLabels γ v) s)
      (torusBondWeight OhA OvA) (torusBondWeight OhB OvB)

/-- The permutation-matrix homomorphism places the image of the tail label
at the head of the oriented bond. -/
theorem permMatrixHom_apply_eq_ite (σ : Equiv.Perm V) (i j : V) :
    Matrix.permMatrixHom (R := ℂ) σ i j = if i = σ j then (1 : ℂ) else 0 := by
  simp only [Matrix.permMatrixHom_apply, Equiv.Perm.permMatrix, Equiv.Perm.inv_def,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
    Equiv.symm_apply_eq]

/-- The four virtual labels read from one label per oriented permutation bond. -/
def torusPermutationSiteLabels
    (σh σv : TorusVertex width height → Equiv.Perm V)
    (hb vb : TorusVertex width height → V) (v : TorusVertex width height) :
    V × V × V × V :=
  (σv v (vb v), hb v, vb (v.1, v.2 - 1), σh (v.1 - 1, v.2) (hb (v.1 - 1, v.2)))

/-- Source: SCP10, equation `eq:2d:peps-with-ug-uh`, lines 1515–1525.
With permutation matrices on the oriented bonds, the head label is the image
of its tail label, leaving exactly one independent index per bond. -/
theorem torusBondNetwork_perm
    (A : TorusVertex width height → (V × V × V × V) → ℂ)
    (σh σv : TorusVertex width height → Equiv.Perm V) :
    torusBondNetwork A (fun v => Matrix.permMatrixHom (R := ℂ) (σh v))
        (fun v => Matrix.permMatrixHom (R := ℂ) (σv v)) =
      ∑ hb : TorusVertex width height → V, ∑ vb : TorusVertex width height → V,
        ∏ v, A v (torusPermutationSiteLabels σh σv hb vb v) := by
  simp only [torusPermutationSiteLabels]
  rw [← Fintype.sum_prod_type']
  unfold torusBondNetwork
  refine (Fintype.sum_of_injective
    (fun p v => (p.1 v, σh v (p.1 v), p.2 v, σv v (p.2 v))) ?_ _ _ ?_ ?_).symm
  · intro p q h
    have h' := fun v => congrFun h v
    simp only [Prod.mk.injEq] at h'
    exact Prod.ext (funext fun v => (h' v).1) (funext fun v => (h' v).2.2.1)
  · intro β hβ
    have : ∃ v, (β v).2.1 ≠ σh v ((β v).1) ∨
        (β v).2.2.2 ≠ σv v ((β v).2.2.1) := by
      by_contra hne
      push Not at hne
      exact hβ ⟨(fun v => (β v).1, fun v => (β v).2.2.1), funext fun v =>
        Prod.ext rfl (Prod.ext (hne v).1.symm (Prod.ext rfl (hne v).2.symm))⟩
    obtain ⟨v, hv⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ v), zero_mul]
    rcases hv with h | h <;> simp [permMatrixHom_apply_eq_ite, h]
  · intro p
    simp only [permMatrixHom_apply_eq_ite, ite_true, mul_one, Finset.prod_const_one, one_mul]

/-- Source: SCP10, equation `eq:2d:peps-with-ug-uh`, lines 1515–1525, and
Definition 6.1, lines 1692–1702. The overlap of actual torus networks with
permutation bonds has one virtual index per bond on each side of the pairing.
The physical sum is the product of the literal local site Gram kernels. -/
theorem sum_star_torusBondNetwork_perm_mul {Phys : Type*} [Fintype Phys]
    (a b : TorusVertex width height → (V × V × V × V) → Phys → ℂ)
    (σhA σvA σhB σvB : TorusVertex width height → Equiv.Perm V) :
    (∑ σ : TorusVertex width height → Phys,
      star (torusBondNetwork (fun v c => a v c (σ v))
        (fun v => Matrix.permMatrixHom (R := ℂ) (σhA v))
        (fun v => Matrix.permMatrixHom (R := ℂ) (σvA v))) *
      torusBondNetwork (fun v c => b v c (σ v))
        (fun v => Matrix.permMatrixHom (R := ℂ) (σhB v))
        (fun v => Matrix.permMatrixHom (R := ℂ) (σvB v))) =
      ∑ hb : TorusVertex width height → V, ∑ vb : TorusVertex width height → V,
        ∑ hb' : TorusVertex width height → V, ∑ vb' : TorusVertex width height → V,
          ∏ v, ∑ s : Phys,
            star (a v (torusPermutationSiteLabels σhA σvA hb vb v) s) *
              b v (torusPermutationSiteLabels σhB σvB hb' vb' v) s := by
  classical
  simp only [torusBondNetwork_perm]
  have h := sum_star_weightedSiteProduct_mul
    (fun (p : (TorusVertex width height → V) × (TorusVertex width height → V)) v s =>
      a v (torusPermutationSiteLabels σhA σvA p.1 p.2 v) s)
    (fun (p : (TorusVertex width height → V) × (TorusVertex width height → V)) v s =>
      b v (torusPermutationSiteLabels σhB σvB p.1 p.2 v) s)
    (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ))
  simpa only [Fintype.sum_prod_type, one_mul, star_one, mul_one] using h

end TNLean.PEPS




