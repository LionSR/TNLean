/-
Copyright (c) 2025 MPSLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MPSLean.MPS.MPVOverlap
import MPSLean.Spectral.MixedTransferRect

import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Matrix.Trace

namespace MPSTensor

open scoped Matrix BigOperators

/-!
# MPV overlaps as traces of **rectangular** mixed transfer operators

This module is the rectangular analogue of `MPSLean.Spectral.MPVOverlapTrace`.

The key identity is

$$\mathrm{Tr}(F_{AB}^N) = \sum_{\sigma} \mathrm{mpv}(A,\sigma)\,\overline{\mathrm{mpv}(B,\sigma)},$$

where now `A : MPSTensor d D₁` and `B : MPSTensor d D₂` may have different bond dimensions, and the
mixed transfer map acts on `Matrix (Fin D₁) (Fin D₂) ℂ`.
-/

section TraceExpansion

lemma linearMap_trace_eq_sum_apply_single₂
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (T : Matrix (Fin D₁) (Fin D₂) ℂ →ₗ[ℂ] Matrix (Fin D₁) (Fin D₂) ℂ) :
    (LinearMap.trace ℂ (Matrix (Fin D₁) (Fin D₂) ℂ)) T
      = ∑ p : Fin D₁, ∑ q : Fin D₂, (T (Matrix.single p q (1 : ℂ))) p q := by
  classical
  -- Use the matrix-unit basis, indexed by pairs `(p,q)`.
  let b : Module.Basis (Fin D₁ × Fin D₂) ℂ (Matrix (Fin D₁) (Fin D₂) ℂ) :=
    Matrix.stdBasis ℂ (Fin D₁) (Fin D₂)
  -- Coordinates of the standard basis are just matrix entries.
  have hrepr (X : Matrix (Fin D₁) (Fin D₂) ℂ) (p : Fin D₁) (q : Fin D₂) :
      (b.repr X) (p, q) = X p q := by
    classical
    simp [b, Matrix.stdBasis, Module.Basis.map_repr, Pi.basis_repr, Pi.basisFun_repr]
  -- Expand the trace using the matrix-unit basis.
  calc
    (LinearMap.trace ℂ (Matrix (Fin D₁) (Fin D₂) ℂ)) T
        = Matrix.trace (LinearMap.toMatrix b b T) := by
            simpa using (LinearMap.trace_eq_matrix_trace (R := ℂ)
              (M := Matrix (Fin D₁) (Fin D₂) ℂ) (b := b) (f := T))
    _ = ∑ x : Fin D₁ × Fin D₂, (b.repr (T (b x))) x := by
            simp [Matrix.trace, LinearMap.toMatrix_apply]
    _ = ∑ p : Fin D₁, ∑ q : Fin D₂, (b.repr (T (b (p, q)))) (p, q) := by
            simpa using
              (Fintype.sum_prod_type (f := fun x : Fin D₁ × Fin D₂ => (b.repr (T (b x))) x))
    _ = ∑ p : Fin D₁, ∑ q : Fin D₂, (T (Matrix.single p q (1 : ℂ))) p q := by
            refine Fintype.sum_congr
              (f := fun p : Fin D₁ => ∑ q : Fin D₂, (b.repr (T (b (p, q)))) (p, q))
              (g := fun p : Fin D₁ => ∑ q : Fin D₂, (T (Matrix.single p q (1 : ℂ))) p q)
              (fun p => ?_)
            refine Fintype.sum_congr
              (f := fun q : Fin D₂ => (b.repr (T (b (p, q)))) (p, q))
              (g := fun q : Fin D₂ => (T (Matrix.single p q (1 : ℂ))) p q)
              (fun q => ?_)
            have hb : b (p, q) = Matrix.single p q (1 : ℂ) := by
              simpa [b] using
                (Matrix.stdBasis_eq_single (R := ℂ) (m := Fin D₁) (n := Fin D₂) p q)
            calc
              (b.repr (T (b (p, q)))) (p, q)
                  = (T (b (p, q))) p q := by
                      simpa using (hrepr (X := T (b (p, q))) p q)
              _ = (T (Matrix.single p q (1 : ℂ))) p q := by
                      simp [hb]

end TraceExpansion

section SingleEntry

lemma entry_mul_single_mul₂
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (M : Matrix (Fin D₁) (Fin D₁) ℂ) (N : Matrix (Fin D₂) (Fin D₂) ℂ)
    (p : Fin D₁) (q : Fin D₂) :
    (M * Matrix.single p q (1 : ℂ) * N) p q = M p p * N q q := by
  classical
  -- Expand the final multiplication. We will show that only the `q`-th term contributes.
  rw [Matrix.mul_apply]
  refine (Fintype.sum_eq_single q ?_).trans ?_
  · intro x hx
    have hMx : (M * Matrix.single p q (1 : ℂ)) p x = 0 := by
      simpa using
        (Matrix.mul_single_apply_of_ne (M := M) (c := (1 : ℂ)) (i := p) (j := q) (a := p)
          (b := x) (hbj := hx))
    simp [hMx]
  · have hMq : (M * Matrix.single p q (1 : ℂ)) p q = M p p := by
      simp [Matrix.mul_single_apply_same (M := M) (c := (1 : ℂ)) (i := p) (j := q) (a := p)]
    simp [hMq]

end SingleEntry

section Main

/-- The operator trace of the rectangular mixed transfer operator power encodes the MPV overlap. -/
theorem trace_mixedTransferMap₂_pow_eq_mpvOverlap
    {d D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) (N : ℕ) :
    (LinearMap.trace ℂ (Matrix (Fin D₁) (Fin D₂) ℂ)) ((mixedTransferMap₂ A B) ^ N)
      = mpvOverlap (d := d) A B N := by
  classical
  -- Expand the operator trace as a sum over matrix units.
  rw [linearMap_trace_eq_sum_apply_single₂ (T := ((mixedTransferMap₂ A B) ^ N))]
  -- Expand the iterated mixed transfer map on each matrix unit.
  simp only [mixedTransferMap₂_pow_apply (A := A) (B := B) (N := N)]
  -- Push the `(p,q)` entry inside the σ-sum and use `entry_mul_single_mul₂`.
  have h1 :
      (∑ p : Fin D₁, ∑ q : Fin D₂,
          (∑ σ : Fin N → Fin d,
              evalWord A (List.ofFn σ) * Matrix.single p q (1 : ℂ) *
                (evalWord B (List.ofFn σ))ᴴ) p q)
        = ∑ p : Fin D₁, ∑ q : Fin D₂, ∑ σ : Fin N → Fin d,
            evalWord A (List.ofFn σ) p p * (evalWord B (List.ofFn σ))ᴴ q q := by
    classical
    refine Fintype.sum_congr _ _ (fun p => ?_)
    refine Fintype.sum_congr _ _ (fun q => ?_)
    let g : (Fin N → Fin d) → Matrix (Fin D₁) (Fin D₂) ℂ := fun σ =>
      evalWord A (List.ofFn σ) * Matrix.single p q (1 : ℂ) *
        (evalWord B (List.ofFn σ))ᴴ
    have hentry : (∑ σ : Fin N → Fin d, g σ) p q = ∑ σ : Fin N → Fin d, g σ p q := by
      -- NOTE: use `exact`, not `simpa`, because `simp` will simplify `Fintype.sum_apply` to `True`.
      have hp : (∑ σ : Fin N → Fin d, g σ) p = ∑ σ : Fin N → Fin d, g σ p := by
        exact Fintype.sum_apply (a := p) (g := g)
      have hq : ((∑ σ : Fin N → Fin d, g σ) p) q = (∑ σ : Fin N → Fin d, g σ p) q := by
        exact congrArg (fun v : Fin D₂ → ℂ => v q) hp
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
          simp [g, entry_mul_single_mul₂]
  -- Reorder the triple sum so that σ is outermost.
  have hswap :
      (∑ p : Fin D₁, ∑ q : Fin D₂, ∑ σ : Fin N → Fin d,
          evalWord A (List.ofFn σ) p p * (evalWord B (List.ofFn σ))ᴴ q q)
        = ∑ σ : Fin N → Fin d, ∑ p : Fin D₁, ∑ q : Fin D₂,
            evalWord A (List.ofFn σ) p p * (evalWord B (List.ofFn σ))ᴴ q q := by
    classical
    simpa using
      (Finset.sum_comm_cycle
        (s := (Finset.univ : Finset (Fin D₁)))
        (t := (Finset.univ : Finset (Fin D₂)))
        (u := (Finset.univ : Finset (Fin N → Fin d)))
        (f := fun p q σ =>
          evalWord A (List.ofFn σ) p p * (evalWord B (List.ofFn σ))ᴴ q q))
  -- Apply the helper equalities.
  rw [h1, hswap]
  -- Unfold `mpvOverlap`/`mpv`/`coeff` so both sides are sums over σ.
  simp only [mpvOverlap, MPSTensor.mpv, MPSTensor.coeff]
  -- Now compute the inner double sum termwise in σ.
  refine Fintype.sum_congr _ _ (fun σ => ?_)
  calc
    (∑ p : Fin D₁, ∑ q : Fin D₂,
        evalWord A (List.ofFn σ) p p * (evalWord B (List.ofFn σ))ᴴ q q)
        = (∑ p : Fin D₁, evalWord A (List.ofFn σ) p p) *
            (∑ q : Fin D₂, (evalWord B (List.ofFn σ))ᴴ q q) := by
            simpa using
              (Fintype.sum_mul_sum
                (f := fun p : Fin D₁ => evalWord A (List.ofFn σ) p p)
                (g := fun q : Fin D₂ => (evalWord B (List.ofFn σ))ᴴ q q)).symm
    _ = Matrix.trace (evalWord A (List.ofFn σ)) *
          star (Matrix.trace (evalWord B (List.ofFn σ))) := by
            simp [Matrix.trace]

end Main

end MPSTensor
