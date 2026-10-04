/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.SwapKronecker
import TNLean.MPS.MPU.StaircaseGates

/-!
# Gauge invariance of the time-reversal trace

The four-site expression `tr[S₁₂,₃₄ v₂₃ (u₁₂ ⊗ u₃₄) v₂₃]` is unchanged by
`u' = (x ⊗ y) u` and `v' = v (y† ⊗ x†)` for unitary `x` and `y`.
The middle placement is the existing `staircaseMiddle`, with the four legs in
spatial order. The pair exchange is the existing swap matrix transported to
the two-site product coordinates.

## Main results

* `Matrix.trace_mul_mul_eq_of_intertwine`: cyclicity of the trace for an
  intertwining pair of changes of basis.
* `MPOTensor.timeReversalTrace`: the four-site trace in the source formula.
* `MPOTensor.timeReversalTrace_gauge`: invariance under the standard-form gauge.

## References

* [J. I. Cirac, D. Pérez-García, N. Schuch, F. Verstraete, *Matrix product
  unitaries: structure, symmetries, and topological invariants*,
  arXiv:1703.09188, equation `eq:sigma-from-trace` and Proposition
  `prop:sigma-well-defined`, lines 1595--1630][Cirac2017MPU]
-/

open scoped Matrix Kronecker

namespace Matrix

/-- A trace pairing is unchanged by an intertwining pair of changes of basis.
The identities `S L = R S` and `K R = I` give
`tr(S L M K) = tr(S M)` by cyclicity.

This is the final trace step in arXiv:1703.09188, Proposition
`prop:sigma-well-defined`, lines 1624--1630. -/
lemma trace_mul_mul_eq_of_intertwine {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S L R K M : Matrix ι ι ℂ) (hSL : S * L = R * S) (hKR : K * R = 1) :
    Matrix.trace (S * (L * M * K)) = Matrix.trace (S * M) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hSL, Matrix.trace_mul_cycle]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc K R, hKR, Matrix.one_mul]

end Matrix

namespace MPOTensor

variable {d : ℕ}

private lemma staircaseMiddle_kronecker
    (a b : Matrix (Fin d) (Fin d) ℂ) :
    staircaseMiddle (A := Fin d) (E := Fin d) (a ⊗ₖ b) =
      ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ a) ⊗ₖ
        (b ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) := by
  ext ⟨⟨i, j⟩, k, l⟩ ⟨⟨i', j'⟩, k', l'⟩
  simp only [staircaseMiddle, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    mul_assoc]

private lemma staircaseMiddle_commute_outer
    (v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (x y : Matrix (Fin d) (Fin d) ℂ) :
    staircaseMiddle (A := Fin d) (E := Fin d) v *
        ((x ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) ⊗ₖ
          ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ y)) =
      ((x ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) ⊗ₖ
        ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ y)) * staircaseMiddle v := by
  ext ⟨⟨i, j⟩, k, l⟩ ⟨⟨i', j'⟩, k', l'⟩
  simp [staircaseMiddle, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, ite_mul,
    Finset.sum_ite_irrel, mul_comm, mul_assoc]

private lemma pairSwap_mul_kronecker
    (a b : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix.reindex (finProdFinEquiv.prodCongr finProdFinEquiv).symm
        (finProdFinEquiv.prodCongr finProdFinEquiv).symm
        (Matrix.swapMatrix (d * d)) * (a ⊗ₖ b) =
      (b ⊗ₖ a) * Matrix.reindex (finProdFinEquiv.prodCongr finProdFinEquiv).symm
        (finProdFinEquiv.prodCongr finProdFinEquiv).symm
        (Matrix.swapMatrix (d * d)) := by
  have h := Matrix.swapMatrix_mul_kronecker
    (Matrix.reindex finProdFinEquiv finProdFinEquiv a)
    (Matrix.reindex finProdFinEquiv finProdFinEquiv b)
  have h' := congrArg (Matrix.reindexRingEquiv ℂ
    (finProdFinEquiv.prodCongr finProdFinEquiv).symm) h
  simp only [map_mul, Matrix.coe_reindexRingEquiv] at h'
  simp only [Matrix.kroneckerMap_reindex] at h'
  simpa only [← Matrix.reindex_symm, Equiv.symm_apply_apply] using h'

private lemma staircaseMiddle_gauge_product
    (u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (x y : Matrix (Fin d) (Fin d) ℂ)
    (hx : x ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hy : y ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    staircaseMiddle (A := Fin d) (E := Fin d) (v * (yᴴ ⊗ₖ xᴴ)) *
        (((x ⊗ₖ y) * u) ⊗ₖ ((x ⊗ₖ y) * u)) *
        staircaseMiddle (v * (yᴴ ⊗ₖ xᴴ)) =
      ((x ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) ⊗ₖ
        ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ y)) *
        (staircaseMiddle v * (u ⊗ₖ u) * staircaseMiddle v) *
        staircaseMiddle (yᴴ ⊗ₖ xᴴ) := by
  have hxx : xᴴ * x = 1 := hx.1
  have hyy : yᴴ * y = 1 := hy.1
  have hcancel : staircaseMiddle (A := Fin d) (E := Fin d) (yᴴ ⊗ₖ xᴴ) *
      ((x ⊗ₖ y) ⊗ₖ (x ⊗ₖ y)) =
      ((x ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) ⊗ₖ
        ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ y)) := by
    simp only [staircaseMiddle_kronecker, ← Matrix.mul_kronecker_mul,
      hxx, hyy, Matrix.one_mul]
  simp only [← staircaseMiddle_mul (A := Fin d) (E := Fin d) v (yᴴ ⊗ₖ xᴴ),
    Matrix.mul_kronecker_mul]
  calc
    _ = staircaseMiddle v *
        (staircaseMiddle (yᴴ ⊗ₖ xᴴ) * ((x ⊗ₖ y) ⊗ₖ (x ⊗ₖ y))) *
        (u ⊗ₖ u) * staircaseMiddle v * staircaseMiddle (yᴴ ⊗ₖ xᴴ) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hcancel, staircaseMiddle_commute_outer]
      simp only [Matrix.mul_assoc]

/-- The four-site trace used to extract the time-reversal sign of a standard
form, with middle gates on sites `23` and exchange of the pairs `12` and `34`.
The exchange is transported from the standard swap matrix on two spaces of
dimension `d²`.

Source: arXiv:1703.09188, equation `eq:sigma-from-trace`, lines 1595--1603. -/
noncomputable def timeReversalTrace
    (u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℂ :=
  Matrix.trace
    (Matrix.reindex (finProdFinEquiv.prodCongr finProdFinEquiv).symm
      (finProdFinEquiv.prodCongr finProdFinEquiv).symm (Matrix.swapMatrix (d * d)) *
      (staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u) * staircaseMiddle v))

/-- The time-reversal trace is invariant under the standard-form gauge
`u' = (x ⊗ y) u`, `v' = v (y† ⊗ x†)`. The four-site order is `12,23,34`.
Only gauge unitarity is used; the identity therefore applies to all standard
form gates without an additional time-reversal hypothesis.

Source: arXiv:1703.09188, Proposition `prop:sigma-well-defined`, lines
1624--1630. -/
lemma timeReversalTrace_gauge
    (u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (x y : Matrix (Fin d) (Fin d) ℂ)
    (hx : x ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hy : y ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    timeReversalTrace ((x ⊗ₖ y) * u) (v * (yᴴ ⊗ₖ xᴴ)) = timeReversalTrace u v := by
  unfold timeReversalTrace
  rw [staircaseMiddle_gauge_product u v x y hx hy]
  refine Matrix.trace_mul_mul_eq_of_intertwine _ _
    (staircaseMiddle (A := Fin d) (E := Fin d) (y ⊗ₖ x)) _ _ ?_ ?_
  · rw [staircaseMiddle_kronecker, pairSwap_mul_kronecker]
  · have hxx : xᴴ * x = 1 := hx.1
    have hyy : yᴴ * y = 1 := hy.1
    rw [staircaseMiddle_mul, ← Matrix.mul_kronecker_mul, hxx, hyy,
      Matrix.one_kronecker_one, staircaseMiddle_one]

end MPOTensor
