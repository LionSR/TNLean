/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Defs
import TNLean.MPS.Overlap.Basic

import Mathlib.Data.Matrix.Mul

/-!
# Open-boundary matrix product states

The translation-invariant tensors of `TNLean.MPS.Defs` close a chain into a ring
by tracing the ordered matrix product.  Some states only admit a non-periodic
representation: the matrix product is closed not by a trace but by a left and a
right boundary vector.

This file adds the minimal infrastructure for that contraction.  For a tensor
`A : MPSTensor d D`, a left boundary `vL : Fin D → ℂ`, a right boundary
`vR : Fin D → ℂ`, and a configuration `σ : Cfg d N`, the open-boundary amplitude
is
\[
    \langle v_L \mid A^{\sigma_1} A^{\sigma_2} \cdots A^{\sigma_N} \mid v_R\rangle
    = v_L^{\mathsf T}\,
      \bigl(A^{\sigma_1} \cdots A^{\sigma_N}\bigr)\,
      v_R,
\]
and the open-boundary state assembles these amplitudes into a vector indexed by
configurations.

The boundary is written with `vecMul`/`mulVec` rather than a conjugate transpose:
the source uses the bilinear pairing `(l| M |r)` and the W-state example below has
real boundary vectors, so the bilinear and sesquilinear pairings agree there.

## Main definitions

* `openCoeff vL vR A w` — the boundary contraction `vL ⬝ (evalWord A w) ⬝ vR` of a
  word `w`.
* `openState vL vR A N` — the open-boundary state on `N` sites as a function on
  configurations, sending `σ` to `openCoeff vL vR A (List.ofFn σ)`.

## References

* Cirac--Pérez-García--Schuch--Verstraete 2021, arXiv:2011.12127, lines
  2348--2362 (the open-boundary contraction `(l| A^{i_1} … A^{i_N} |r)`).
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- The open-boundary contraction of a word `w` against a left boundary covector
`vL` and a right boundary vector `vR`:
\(v_L^{\mathsf T}\,(\mathrm{evalWord}\,A\,w)\,v_R\).

This is the bilinear pairing `(l| A^{w} |r)` of arXiv:2011.12127, lines
2358--2362. -/
noncomputable def openCoeff (vL vR : Fin D → ℂ) (A : MPSTensor d D)
    (w : List (Fin d)) : ℂ :=
  vL ⬝ᵥ (evalWord A w).mulVec vR

@[simp] lemma openCoeff_def (vL vR : Fin D → ℂ) (A : MPSTensor d D) (w : List (Fin d)) :
    openCoeff vL vR A w = vL ⬝ᵥ (evalWord A w).mulVec vR := rfl

/-- The empty-word contraction is the boundary overlap `vL ⬝ vR`. -/
@[simp] lemma openCoeff_nil (vL vR : Fin D → ℂ) (A : MPSTensor d D) :
    openCoeff vL vR A [] = vL ⬝ᵥ vR := by
  simp [openCoeff]

/-- Peeling the first letter: the contraction of `i :: w` pushes `A i` into the
left boundary covector. -/
lemma openCoeff_cons (vL vR : Fin D → ℂ) (A : MPSTensor d D)
    (i : Fin d) (w : List (Fin d)) :
    openCoeff vL vR A (i :: w) =
      openCoeff (Matrix.vecMul vL (A i)) vR A w := by
  simp only [openCoeff, evalWord_cons]
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]

/-- The open-boundary state on `N` sites: the configuration amplitudes
`σ ↦ (l| A^{σ_1} ⋯ A^{σ_N} |r)`, assembled as a function on configurations.

This is the W-state-style state vector of arXiv:2011.12127, line 2361. -/
noncomputable def openState (vL vR : Fin D → ℂ) (A : MPSTensor d D) (N : ℕ) :
    Cfg d N → ℂ :=
  fun σ : Cfg d N => openCoeff vL vR A (List.ofFn σ)

@[simp] lemma openState_apply (vL vR : Fin D → ℂ) (A : MPSTensor d D)
    (N : ℕ) (σ : Cfg d N) :
    openState vL vR A N σ = openCoeff vL vR A (List.ofFn σ) := rfl

end MPSTensor
