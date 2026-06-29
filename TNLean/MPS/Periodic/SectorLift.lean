/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.CornerTransition
import TNLean.MPS.Core.Blocking

/-!
# Telescoping the one-site corner products into a blocked diagonal corner

This file isolates the purely algebraic backbone of the `m`-factor cyclic
contraction of arXiv:1708.00029, Appendix A (lines 1012--1046): the one-site
corner-transition product `A_u^{i_1} A_{u+1}^{i_2} \cdots` (eq:Auprop, eq:Fu)
telescopes into a single diagonal corner `P_u (A^{[m]})^{\mathbf i} P_u` of the
blocked tensor (eq:Cu / Lemma bdcf).

## The two projector conventions

arXiv:1708.00029 grades the one-site tensors *off-diagonally* with
$A^i = \sum_u P_u A^i P_{u+1}$, so that the sector letter
$A_u^i = P_u A^i P_{u+1}$ (eq:Auprop) is the nonzero corner and a product of
such letters telescopes through the intermediate projectors.  This is the
convention under which `MPSTensor.cornerProd` is nonzero.

The cyclic sector data (`IsCyclicSectorDecompWith`) instead satisfies the
*adjoint* shift $\mathcal E^*(P_{k+1}) = P_k$, which gives the inverse-indexed
grading $A^i = \sum_u P_{u+1} A^i P_u$ — equivalently
$P_{k+1} A^i = A^i P_k$ (`offDiag_shift_of_adjoint_cyclic_shift`).  Under this
convention $P_u A^i P_{u+1} = 0$ for $m \ge 3$, so `cornerProd` is identically
zero on these projectors directly.  The two conventions agree after the inverse
cyclic reindexing $P_k \mapsto P_{-k}$ (documented at `IsCyclicSectorDecompWith`):
`negReindex_paper_shift` derives the paper-convention shift for `fun k => P (-k)`
from the adjoint shift, repairing the index mismatch so the telescoping applies.

## Main declarations

* `MPSTensor.cornerProd_eq_conj_evalWord` — the telescoping identity
  `cornerProd P A u w = P u * evalWord A w * P (u + w.length • 1)` under the
  paper-convention shift `P k * A i = A i * P (k + 1)`.
* `MPSTensor.cornerProd_eq_diagCorner_of_length_smul_eq_zero` — for a word whose
  length is a multiple of the period (`w.length • 1 = 0`), the product is the
  diagonal corner `P u * evalWord A w * P u`.
* `MPSTensor.cornerProd_eq_blockDiagCorner` — for a single blocked letter
  `wordOfBlock d m I`, the product is `P u * (blockTensor A m) I * P u`
  (eq:Cu).
* `MPSTensor.negReindex_paper_shift` — converts the adjoint cyclic shift
  into the paper-convention shift for the inverse-reindexed projectors.

## References

* De las Cuevas, Cirac, Schuch, Pérez-García,
  *Irreducible forms of Matrix Product States: Theory and Applications*,
  arXiv:1708.00029, Appendix A (eq:Auprop, eq:Cvprop, eq:BCmprop, eq:Fu).
-/

open scoped Matrix BigOperators
open Matrix

namespace MPSTensor

variable {d D : ℕ}

section Telescope

variable {m : ℕ} [NeZero m]

/-- **Telescoping of a one-site corner-transition product into a conjugated word.**

Under the *paper* off-diagonal convention `P k * A i = A i * P (k + 1)`
(arXiv:1708.00029, the grading $A^i = \sum_u P_u A^i P_{u+1}$ underlying
eq:Auprop), the repeated corner-transition product `cornerProd P A u w`
collapses through its intermediate projectors:
`cornerProd P A u w = P u * evalWord A w * P (u + w.length • 1)`.

The starting projector `P u` is kept on the left, every intermediate junction
projector is absorbed by the shift and projector idempotency, and a single
projector `P (u + w.length • 1)` records the accumulated sector offset on the
right.  This is the algebraic mechanism by which Appendix A repeats a single
sector block around the cycle (eq:Fu). -/
theorem cornerProd_eq_conj_evalWord
    (P : Fin m → MatrixAlg D) (A : MPSTensor d D)
    (hproj : ∀ k, IsOrthogonalProjection (P k))
    (hshift : ∀ k (i : Fin d), P k * A i = A i * P (k + 1))
    (u : Fin m) (w : List (Fin d)) :
    cornerProd P A u w = P u * evalWord A w * P (u + w.length • (1 : Fin m)) := by
  induction w generalizing u with
  | nil =>
    simp only [cornerProd_nil, evalWord_nil, List.length_nil, zero_smul, add_zero,
      Matrix.mul_one]
    exact ((hproj u).2).symm
  | cons i w ih =>
    -- The head junction `P u * A i * P (u + 1)` collapses to `P u * A i`.
    have key : P u * A i * P (u + 1) = P u * A i := by
      rw [Matrix.mul_assoc, ← hshift u i, ← Matrix.mul_assoc, (hproj u).2]
    -- Realign the accumulated sector offset.
    have hlen : (u + 1) + w.length • (1 : Fin m) = u + (i :: w).length • (1 : Fin m) := by
      simp only [List.length_cons, add_smul, one_smul]; abel
    rw [cornerProd_cons, ih (u + 1), evalWord_cons]
    calc
      P u * A i * (P (u + 1) * evalWord A w * P ((u + 1) + w.length • (1 : Fin m)))
          = (P u * A i * P (u + 1)) * evalWord A w *
              P ((u + 1) + w.length • (1 : Fin m)) := by
            simp only [Matrix.mul_assoc]
      _ = (P u * A i) * evalWord A w * P ((u + 1) + w.length • (1 : Fin m)) := by rw [key]
      _ = P u * (A i * evalWord A w) * P (u + (i :: w).length • (1 : Fin m)) := by
            rw [hlen, Matrix.mul_assoc (P u) (A i) (evalWord A w)]

/-- **Diagonal-corner collapse for a period-aligned word.**

If the word length is a multiple of the period (`w.length • 1 = 0` in `Fin m`),
then the accumulated sector offset vanishes and the corner-transition product is
the diagonal corner `P u * evalWord A w * P u`. -/
theorem cornerProd_eq_diagCorner_of_length_smul_eq_zero
    (P : Fin m → MatrixAlg D) (A : MPSTensor d D)
    (hproj : ∀ k, IsOrthogonalProjection (P k))
    (hshift : ∀ k (i : Fin d), P k * A i = A i * P (k + 1))
    (u : Fin m) (w : List (Fin d)) (hlen : w.length • (1 : Fin m) = 0) :
    cornerProd P A u w = P u * evalWord A w * P u := by
  rw [cornerProd_eq_conj_evalWord P A hproj hshift u w, hlen, add_zero]

/-- **Single blocked letter as a diagonal corner** (arXiv:1708.00029, eq:Cu).

For one blocked letter `wordOfBlock d m I` (a word of length exactly the period
`m`), the corner-transition product is the diagonal blocked corner
`P u * (blockTensor A m) I * P u = C_u^{I}` of Lemma bdcf.  Combined with the
corner-isomorphism letter identity of `IsCyclicSectorDecompWith`
(`(φ k (blocks k I)).1 = P k * blockTensor A m I * P k`), this exhibits the
compressed sector letter as the corner-transition product. -/
theorem cornerProd_eq_blockDiagCorner
    (P : Fin m → MatrixAlg D) (A : MPSTensor d D)
    (hproj : ∀ k, IsOrthogonalProjection (P k))
    (hshift : ∀ k (i : Fin d), P k * A i = A i * P (k + 1))
    (u : Fin m) (I : Fin (blockPhysDim d m)) :
    cornerProd P A u (wordOfBlock d m I) = P u * (blockTensor A m) I * P u := by
  have hlen : (wordOfBlock d m I).length • (1 : Fin m) = 0 := by
    rw [length_wordOfBlock]
    have h := card_nsmul_eq_zero (x := (1 : Fin m))
    rwa [Fintype.card_fin] at h
  rw [cornerProd_eq_diagCorner_of_length_smul_eq_zero P A hproj hshift u _ hlen]
  rfl

end Telescope

section NegReindex

variable {m : ℕ} [NeZero m]

/-- **Inverse cyclic reindexing of the adjoint shift into the paper
convention.**

The cyclic sector decomposition satisfies the adjoint cyclic shift
`𝓔^*(P_{k+1}) = P_k`, which yields the inverse-indexed grading
`P_{k+1} A^i = A^i P_k` (`offDiag_shift_of_adjoint_cyclic_shift`).  After the
inverse cyclic reindexing `P_k ↦ P_{-k}` documented at
`IsCyclicSectorDecompWith`, the projectors satisfy the *paper* off-diagonal
convention `P_{-k} A^i = A^i P_{-(k+1)}` (arXiv:1708.00029, eq:Auprop grading),
which is the shift hypothesis of `cornerProd_eq_conj_evalWord`. -/
theorem negReindex_paper_shift
    (A : MPSTensor d D)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    {P : Fin m → MatrixAlg D}
    (hproj : ∀ k, IsOrthogonalProjection (P k))
    (hShift : ∀ k, transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (k : Fin m) (i : Fin d) :
    P (-k) * A i = A i * P (-(k + 1)) := by
  have h := offDiag_shift_of_adjoint_cyclic_shift A hLeft hproj hShift (-(k + 1)) i
  have he : (-(k + 1) + 1 : Fin m) = -k := by abel
  rwa [he] at h

end NegReindex

end MPSTensor
