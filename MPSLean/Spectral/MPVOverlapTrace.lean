/-
Copyright (c) 2025 MPSLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MPSLean.MPS.MPVOverlap
import MPSLean.Spectral.MixedTransfer

import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Matrix.Trace

namespace MPSTensor

open scoped Matrix BigOperators

/-!
# MPV overlaps as traces of mixed transfer operators

This module proves the key identity (standard in the MPS literature) expressing the overlap
\[
  \sum_{\sigma : \mathrm{Fin}\,N \to \mathrm{Fin}\,d}
    \mathrm{mpv}(A,\sigma)\,\overline{\mathrm{mpv}(B,\sigma)}
\]
as the trace of the $N$-th power of the mixed transfer operator.

The main technical step is an explicit expansion of `LinearMap.trace` on endomorphisms of the
matrix algebra using the matrix-unit basis `Matrix.single p q 1`.
-/

section TraceExpansion

lemma linearMap_trace_eq_sum_apply_single
    {D : ℕ} [NeZero D]
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    (LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ)) T
      = ∑ p : Fin D, ∑ q : Fin D, (T (Matrix.single p q (1 : ℂ))) p q := by
  classical
  -- Use the standard `Pi` basis on `Fin D → Fin D → ℂ` (definitionally `Matrix (Fin D) (Fin D) ℂ`).
  -- Use the standard matrix-unit basis, indexed by pairs `(p,q)`.
  let b : Module.Basis (Fin D × Fin D) ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.stdBasis ℂ (Fin D) (Fin D)
  -- A key computation: coordinates of the standard basis are just matrix entries.
  have hrepr (X : Matrix (Fin D) (Fin D) ℂ) (p q : Fin D) :
      (b.repr X) (p, q) = X p q := by
    classical
    -- Unfold `Matrix.stdBasis` into a reindexed `Pi` basis and compute the coordinate.
    simp [b, Matrix.stdBasis, Module.Basis.map_repr, Pi.basis_repr, Pi.basisFun_repr]
  -- Expand the trace using the matrix-unit basis.
  calc
    (LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ)) T
        = Matrix.trace (LinearMap.toMatrix b b T) := by
            simpa using (LinearMap.trace_eq_matrix_trace (R := ℂ)
              (M := Matrix (Fin D) (Fin D) ℂ) (b := b) (f := T))
    _ = ∑ x : Fin D × Fin D, (b.repr (T (b x))) x := by
            simp [Matrix.trace, LinearMap.toMatrix_apply]
    _ = ∑ p : Fin D, ∑ q : Fin D, (b.repr (T (b (p, q)))) (p, q) := by
            simpa using
              (Fintype.sum_prod_type (f := fun x : Fin D × Fin D => (b.repr (T (b x))) x))
    _ = ∑ p : Fin D, ∑ q : Fin D, (T (Matrix.single p q (1 : ℂ))) p q := by
            refine Fintype.sum_congr
              (f := fun p : Fin D => ∑ q : Fin D, (b.repr (T (b (p, q)))) (p, q))
              (g := fun p : Fin D => ∑ q : Fin D, (T (Matrix.single p q (1 : ℂ))) p q)
              (fun p => ?_)
            refine Fintype.sum_congr
              (f := fun q : Fin D => (b.repr (T (b (p, q)))) (p, q))
              (g := fun q : Fin D => (T (Matrix.single p q (1 : ℂ))) p q)
              (fun q => ?_)
            have hb : b (p, q) = Matrix.single p q (1 : ℂ) := by
              simpa [b] using
                (Matrix.stdBasis_eq_single (R := ℂ) (m := Fin D) (n := Fin D) p q)
            -- Use the `repr` coordinate computation and rewrite the basis vector.
            calc
              (b.repr (T (b (p, q)))) (p, q)
                  = (T (b (p, q))) p q := by
                      simpa using (hrepr (X := T (b (p, q))) p q)
              _ = (T (Matrix.single p q (1 : ℂ))) p q := by
                      simp [hb]

end TraceExpansion

section SingleEntry

lemma entry_mul_single_mul
    {D : ℕ} [NeZero D]
    (M N : Matrix (Fin D) (Fin D) ℂ) (p q : Fin D) :
    (M * Matrix.single p q (1 : ℂ) * N) p q = M p p * N q q := by
  classical
  -- Reassociate and expand the last multiplication.
  -- The factor `M * single p q 1` has only column `q` possibly nonzero.
  simp [Matrix.mul_apply]
  -- Collapse the outer `Fintype` sum to the single contributing term `x = q`.
  refine (Fintype.sum_eq_single q ?_).trans ?_
  · intro x hx
    have : (∑ j : Fin D, M p j * Matrix.single p q (1 : ℂ) j x) = 0 := by
      -- This is exactly the `(p,x)` entry of `M * single p q 1` for `x ≠ q`.
      simpa [Matrix.mul_apply] using
        (Matrix.mul_single_apply_of_ne (i := p) (j := q) (a := p) (b := x)
          (hbj := hx) (M := M) (c := (1 : ℂ)))
    simp [this]
  · have : (∑ j : Fin D, M p j * Matrix.single p q (1 : ℂ) j q) = M p p := by
      -- This is the `(p,q)` entry of `M * single p q 1`.
      simpa [Matrix.mul_apply] using
        (Matrix.mul_single_apply_same (i := p) (j := q) (a := p) (M := M) (c := (1 : ℂ)))
    simp [this]

end SingleEntry

section Main

/-- The operator trace of the mixed transfer operator power encodes the MPV overlap.

This is the identity
$$\mathrm{Tr}(F_{AB}^N) = \sum_{\sigma} \mathrm{mpv}(A,\sigma)\,\overline{\mathrm{mpv}(B,\sigma)}.$$
-/
theorem trace_mixedTransferMap_pow_eq_mpvOverlap {d D : ℕ} [NeZero D]
    (A B : MPSTensor d D) (N : ℕ) :
    (LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ)) ((mixedTransferMap A B) ^ N)
      = mpvOverlap (d := d) A B N := by
  classical
  -- Expand the operator trace as a sum over matrix units.
  rw [linearMap_trace_eq_sum_apply_single (T := ((mixedTransferMap A B) ^ N))]
  -- Expand the iterated mixed transfer map on each matrix unit.
  simp only [mixedTransferMap_pow_apply (A := A) (B := B) (N := N)]
  -- Push the `(p,q)` entry inside the σ-sum and use `entry_mul_single_mul`.
  have h1 :
      (∑ p : Fin D, ∑ q : Fin D,
          (∑ σ : Fin N → Fin d,
              evalWord A (List.ofFn σ) * Matrix.single p q (1 : ℂ) *
                (evalWord B (List.ofFn σ))ᴴ) p q)
        = ∑ p : Fin D, ∑ q : Fin D, ∑ σ : Fin N → Fin d,
            evalWord A (List.ofFn σ) p p * (evalWord B (List.ofFn σ))ᴴ q q := by
    classical
    refine Fintype.sum_congr _ _ (fun p => ?_)
    refine Fintype.sum_congr _ _ (fun q => ?_)
    let g : (Fin N → Fin d) → Matrix (Fin D) (Fin D) ℂ := fun σ =>
      evalWord A (List.ofFn σ) * Matrix.single p q (1 : ℂ) *
        (evalWord B (List.ofFn σ))ᴴ
    have hentry : (∑ σ : Fin N → Fin d, g σ) p q = ∑ σ : Fin N → Fin d, g σ p q := by
      -- NOTE: use `exact`, not `simpa`, because `simp` will simplify `Fintype.sum_apply` to `True`.
      have hp : (∑ σ : Fin N → Fin d, g σ) p = ∑ σ : Fin N → Fin d, g σ p := by
        exact Fintype.sum_apply (a := p) (g := g)
      have hq : ((∑ σ : Fin N → Fin d, g σ) p) q = (∑ σ : Fin N → Fin d, g σ p) q := by
        exact congrArg (fun v : Fin D → ℂ => v q) hp
      have hq' : (∑ σ : Fin N → Fin d, g σ p) q = ∑ σ : Fin N → Fin d, g σ p q := by
        exact Fintype.sum_apply (a := q) (g := fun σ => g σ p)
      exact hq.trans hq'
    calc
      (∑ σ : Fin N → Fin d,
            evalWord A (List.ofFn σ) * Matrix.single p q (1 : ℂ) *
              (evalWord B (List.ofFn σ))ᴴ) p q
          = ∑ σ : Fin N → Fin d, g σ p q := hentry
      _ = ∑ σ : Fin N → Fin d,
          evalWord A (List.ofFn σ) p p * (evalWord B (List.ofFn σ))ᴴ q q := by
          refine Fintype.sum_congr _ _ (fun σ => ?_)
          simp [g, entry_mul_single_mul]
  -- Reorder the triple sum so that σ is outermost.
  have hswap :
      (∑ p : Fin D, ∑ q : Fin D, ∑ σ : Fin N → Fin d,
          evalWord A (List.ofFn σ) p p * (evalWord B (List.ofFn σ))ᴴ q q)
        = ∑ σ : Fin N → Fin d, ∑ p : Fin D, ∑ q : Fin D,
            evalWord A (List.ofFn σ) p p * (evalWord B (List.ofFn σ))ᴴ q q := by
    classical
    -- `Finset.sum_comm_cycle` is the workhorse for swapping three finite sums.
    simpa using
      (Finset.sum_comm_cycle
        (s := (Finset.univ : Finset (Fin D)))
        (t := (Finset.univ : Finset (Fin D)))
        (u := (Finset.univ : Finset (Fin N → Fin d)))
        (f := fun p q σ =>
          evalWord A (List.ofFn σ) p p * (evalWord B (List.ofFn σ))ᴴ q q))
  -- Apply the helper equalities.
  rw [h1, hswap]
  -- Unfold `mpvOverlap`/`mpv`/`coeff` so both sides are sums over σ.
  simp [mpvOverlap, MPSTensor.mpv, MPSTensor.coeff]
  -- Now compute the inner double sum termwise in σ.
  refine Fintype.sum_congr _ _ (fun σ => ?_)
  calc
    (∑ p : Fin D, ∑ q : Fin D,
        evalWord A (List.ofFn σ) p p * (evalWord B (List.ofFn σ))ᴴ q q)
        = (∑ p : Fin D, evalWord A (List.ofFn σ) p p) *
            (∑ q : Fin D, (evalWord B (List.ofFn σ))ᴴ q q) := by
            simpa using
              (Fintype.sum_mul_sum
                (f := fun p : Fin D => evalWord A (List.ofFn σ) p p)
                (g := fun q : Fin D => (evalWord B (List.ofFn σ))ᴴ q q)).symm
    _ = Matrix.trace (evalWord A (List.ofFn σ)) *
          star (Matrix.trace (evalWord B (List.ofFn σ))) := by
            simp [Matrix.trace]

end Main

end MPSTensor
