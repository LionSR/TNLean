/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.OpenBoundary

/-!
# The W state as an open-boundary Matrix Product State

The W state on `N` sites is the single-excitation symmetric state
\[
    \ket{W_N}
    = \ket{10\cdots0} + \ket{010\cdots0} + \cdots + \ket{0\cdots01},
\]
the (unnormalized) equal-weight superposition of all configurations with exactly
one excitation.

Following arXiv:2011.12127 (lines 2348--2362), the W state is an open-boundary
MPS with bond dimension `D = 2` and physical dimension `d = 2`, with the
site-independent tensor
\[
    A^0 = \begin{pmatrix}1&0\\0&1\end{pmatrix},
    \qquad
    A^1 = \begin{pmatrix}0&1\\0&0\end{pmatrix},
\]
and boundary covectors `(l| = (0|` and `|r) = |1)`.  The open-boundary
contraction `(l| A^{σ_1} ⋯ A^{σ_N} |r)` is `1` exactly when `σ` has a single
excitation, reproducing `\ket{W_N}`.

This is not a translation-invariant representation: the boundary is not closed by
a trace.  Closing it periodically would give `tr(A^{σ_1} ⋯ A^{σ_N})`, a different
(and, for the W state, unattainable at fixed bond dimension) object; see the
discussion in arXiv:2011.12127, line 2362, and the bond-dimension lower bound
recorded in `docs/paper-gaps/rmp_w_state_ti_bound.tex`.

## Main definitions

* `wTensor` — the open-boundary W tensor `A^0 = I`, `A^1 = raising`.
* `wLeftBoundary`, `wRightBoundary` — the covectors `(0|` and `|1)`.
* `wIndicator` — the configuration amplitude of `\ket{W_N}`: `1` on
  single-excitation configurations, `0` elsewhere.

## Main results

* `wTensor_openState_eq_wIndicator` — the open-boundary contraction of `wTensor`
  reproduces the W state: `openState wLeftBoundary wRightBoundary wTensor N`
  equals `wIndicator N`, for every `N`.

## References

* Cirac--Pérez-García--Schuch--Verstraete 2021, arXiv:2011.12127, lines
  2348--2362.
-/

open scoped Matrix

namespace MPSTensor

/-! ### The W tensor and its boundary vectors -/

/-- The W MPS tensor with `d = D = 2`:
`A^0 = I` and `A^1 = !![0,1;0,0]` (the single raising operator).
Source: arXiv:2011.12127, line 2358. -/
def wTensor : MPSTensor 2 2 :=
  fun i => if i = 0 then 1 else !![(0 : ℂ), 1; 0, 0]

@[simp] lemma wTensor_zero : wTensor 0 = 1 := rfl

@[simp] lemma wTensor_one : wTensor 1 = !![(0 : ℂ), 1; 0, 0] := rfl

/-- The left boundary covector `(l| = (0|`. Source: arXiv:2011.12127, line 2360. -/
def wLeftBoundary : Fin 2 → ℂ := Pi.single 0 1

/-- The right boundary vector `|r) = |1)`. Source: arXiv:2011.12127, line 2360. -/
def wRightBoundary : Fin 2 → ℂ := Pi.single 1 1

/-- The single raising matrix `A^1 = !![0,1;0,0]`. -/
private def raising : Matrix (Fin 2) (Fin 2) ℂ := !![(0 : ℂ), 1; 0, 0]

/-- `A^1` squares to zero: two excitations annihilate the chain. -/
lemma raising_mul_raising : raising * raising = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [raising, Matrix.mul_apply, Fin.sum_univ_two]

/-! ### The W-state amplitude

We classify the ordered product `evalWord wTensor w` by the number of excitations
(`1` letters) in the word `w`: it is the identity with no excitations, the raising
matrix with one excitation, and zero with two or more.  Reading off the `(0,1)`
entry against the boundary covectors gives the W-state amplitude. -/

/-- The word product of `wTensor` is governed by the excitation count:
* no excitations give the identity;
* exactly one excitation gives the raising matrix `A^1`;
* two or more excitations annihilate, giving the zero matrix. -/
lemma evalWord_wTensor (w : List (Fin 2)) :
    evalWord wTensor w =
      match w.count 1 with
      | 0 => 1
      | 1 => raising
      | _ => 0 := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [evalWord_cons, ih, List.count_cons]
    match i with
    | 0 =>
      -- head is `0`: `A^0 = I`, the count is unchanged.
      simp
    | 1 =>
      -- head is `1`: `A^1 = raising`, the count increases by one.
      rw [show wTensor 1 = raising from rfl]
      simp only [Fin.isValue, beq_self_eq_true, if_true]
      rcases hc : w.count 1 with _ | _ | k
      · exact mul_one raising
      · exact raising_mul_raising
      · exact mul_zero raising

/-- The boundary contraction reads off the `(0,1)` entry: identity gives `0`,
the raising matrix gives `1`, and the zero matrix gives `0`. -/
private lemma openCoeff_wTensor_entry (w : List (Fin 2)) :
    openCoeff wLeftBoundary wRightBoundary wTensor w = (evalWord wTensor w) 0 1 := by
  simp only [openCoeff, wLeftBoundary, wRightBoundary]
  rw [single_dotProduct]
  simp [Matrix.mulVec]

/-- The open-boundary contraction of `wTensor` against `(0|·|1)` is `1` exactly
when the word has a single excitation, and `0` otherwise. -/
lemma openCoeff_wTensor (w : List (Fin 2)) :
    openCoeff wLeftBoundary wRightBoundary wTensor w =
      if w.count 1 = 1 then 1 else 0 := by
  rw [openCoeff_wTensor_entry, evalWord_wTensor]
  rcases hc : w.count 1 with _ | _ | k
  · simp
  · simp [raising]
  · simp

/-! ### The W-state identification -/

/-- The amplitude of the (unnormalized) W state `\ket{W_N}` in the computational
basis: `1` on configurations with exactly one excitation, `0` otherwise.
Source: arXiv:2011.12127, line 2350. -/
def wIndicator (N : ℕ) : Cfg 2 N → ℂ :=
  fun σ => if (List.ofFn σ).count 1 = 1 then 1 else 0

@[simp] lemma wIndicator_apply (N : ℕ) (σ : Cfg 2 N) :
    wIndicator N σ = if (List.ofFn σ).count 1 = 1 then 1 else 0 := rfl

/-- **Central identification.** The open-boundary contraction of the W tensor with
boundary covectors `(0|` and `|1)` reproduces the W state on every number of
sites `N`:
\[
    \ket{W_N}
    = \sum_{\sigma} (0|\, A^{\sigma_1} \cdots A^{\sigma_N}\, |1)\, \ket{\sigma}.
\]
Source: arXiv:2011.12127, lines 2350--2361. -/
theorem wTensor_openState_eq_wIndicator (N : ℕ) :
    openState wLeftBoundary wRightBoundary wTensor N = wIndicator N := by
  funext σ
  rw [openState_apply, openCoeff_wTensor, wIndicator_apply]

/-! ### A concrete three-site witness

The three single-excitation configurations of `\ket{W_3}` each receive amplitude
`1`, and any configuration with a different number of excitations receives
amplitude `0`.  These are direct instances of the identification above. -/

/-- The configuration with the single excitation at site `k`, among `N` sites. -/
def excitedAt (N : ℕ) (k : Fin N) : Cfg 2 N := fun j => if j = k then 1 else 0

/-- A single-excitation configuration has exactly one `1`, so its W-state
amplitude is `1`. -/
theorem wState_three_excitedAt (k : Fin 3) :
    openState wLeftBoundary wRightBoundary wTensor 3 (excitedAt 3 k) = 1 := by
  rw [wTensor_openState_eq_wIndicator, wIndicator_apply, if_pos]
  fin_cases k <;> decide

/-- The all-zero configuration has no excitation, so its W-state amplitude is
`0`: the W state has no vacuum component. -/
theorem wState_three_vacuum :
    openState wLeftBoundary wRightBoundary wTensor 3 (fun _ => 0) = 0 := by
  rw [wTensor_openState_eq_wIndicator, wIndicator_apply, if_neg]
  decide

/-- A two-excitation configuration receives amplitude `0`: the W state has no
multiply-excited component. -/
theorem wState_three_double :
    openState wLeftBoundary wRightBoundary wTensor 3
        (fun j => if j = 0 then 1 else if j = 1 then 1 else 0) = 0 := by
  rw [wTensor_openState_eq_wIndicator, wIndicator_apply, if_neg]
  decide

end MPSTensor
