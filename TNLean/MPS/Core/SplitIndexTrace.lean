/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.CyclicTrace

/-!
# Split-index presentation of periodic amplitudes

Suppose every letter of a tensor factors through an intermediate bond of dimension `m`,
`A^i = R^i L^i`, with `R^i` a `D × m` and `L^i` an `m × D` matrix. Regrouping the ring
`A^{σ_0} ⋯ A^{σ_{N-1}}` around the intermediate bonds gives the split-index tensor
`S^{ab} = L^a R^b`, which carries the physical labels of two neighbouring sites:

`tr (A^{σ_0} ⋯ A^{σ_{N-1}}) = tr (S^{σ_0 σ_1} S^{σ_1 σ_2} ⋯ S^{σ_{N-1} σ_0})`.

This is the split-index presentation of arXiv:2502.20257, `Papers/2502.20257/main.tex`
lines 3970–4001, which cites arXiv:2404.15883 for split-index matrix product states.

If an invertible matrix `X` rescales every factor of a ring, `X S_k X⁻¹ = c_k S_k`, then the
product of the scalars `c_k` fixes the trace of the ring. This is how a symmetry that acts on
the two legs of each split-index tensor by a phase is implemented on the intermediate bond.

## Main results

* `MPSTensor.prod_ofFn_mul_eq_mul_prod_mul`: `∏_k r_k l_k = r_0 (∏_{k<n} l_k r_{k+1}) l_n`.
* `MPSTensor.mpv_eq_trace_prod_ofFn_of_eq_mul`: the periodic amplitude of a tensor with
  factored letters is the trace of the ring of split-index tensors.
* `MPSTensor.mul_prod_ofFn_mul_eq_smul`, `MPSTensor.prod_mul_trace_prod_ofFn_eq`: a bond matrix
  rescaling every factor of a ring rescales the product by the product of the scalars, which
  then fixes the trace.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D m : ℕ}

/-- **Regrouping a product of factored letters** around the intermediate bonds:
`∏_k r_k l_k = r_0 (∏_{k<n} l_k r_{k+1}) l_n` for `n + 1` factors. -/
theorem prod_ofFn_mul_eq_mul_prod_mul :
    ∀ (n : ℕ) (r : Fin (n + 1) → Matrix (Fin D) (Fin m) ℂ)
      (l : Fin (n + 1) → Matrix (Fin m) (Fin D) ℂ),
      (List.ofFn fun k ↦ r k * l k).prod =
        r 0 * (List.ofFn fun k : Fin n ↦ l k.castSucc * r k.succ).prod * l (Fin.last n)
  | 0, r, l => by simp
  | n + 1, r, l => by
    rw [List.ofFn_succ (f := fun k : Fin (n + 1 + 1) ↦ r k * l k), List.prod_cons,
      prod_ofFn_mul_eq_mul_prod_mul n (fun k ↦ r k.succ) (fun k ↦ l k.succ),
      List.ofFn_succ (f := fun k : Fin (n + 1) ↦ l k.castSucc * r k.succ), List.prod_cons]
    -- The two sides now differ only by `castSucc 0 = 0`, `(last n).succ = last (n + 1)` and
    -- `k.castSucc.succ = k.succ.castSucc`, which hold by definition.
    simp only [Matrix.mul_assoc] <;> rfl

/-- **The split-index presentation of a periodic amplitude** (arXiv:2502.20257, lines
3970–4001). If every letter factors as `A^i = R^i L^i` through an intermediate bond, the
periodic amplitude on a ring of `n + 1` sites is the trace of the ring of split-index tensors
`S^{ab} = L^a R^b`, each carrying the labels of two neighbouring sites:
`tr (A^{σ_0} ⋯ A^{σ_n}) = tr (S^{σ_0 σ_1} ⋯ S^{σ_n σ_0})`. -/
theorem mpv_eq_trace_prod_ofFn_of_eq_mul (A : MPSTensor d D)
    (R : Fin d → Matrix (Fin D) (Fin m) ℂ) (L : Fin d → Matrix (Fin m) (Fin D) ℂ)
    (hA : ∀ i, A i = R i * L i) {n : ℕ} (σ : Fin (n + 1) → Fin d) :
    mpv A σ = (List.ofFn fun k ↦ L (σ k) * R (σ (k + 1))).prod.trace := by
  rw [mpv_eq, coeff_eq, evalWord_ofFn_eq_prod]
  simp only [hA]
  rw [prod_ofFn_mul_eq_mul_prod_mul n (fun k ↦ R (σ k)) (fun k ↦ L (σ k)), Matrix.mul_assoc,
    Matrix.trace_mul_comm (R (σ 0)), Matrix.mul_assoc,
    List.ofFn_succ' (fun k ↦ L (σ k) * R (σ (k + 1))), List.prod_concat]
  simp only [Fin.coeSucc_eq_succ, Fin.last_add_one]

/-- **A bond matrix rescaling every factor rescales the product**: if `X Y = Y X = 1` and
`X S_k Y = c_k S_k` for every factor, then `X (∏_k S_k) Y = (∏_k c_k) ∏_k S_k`. -/
theorem mul_prod_ofFn_mul_eq_smul {X Y : Matrix (Fin D) (Fin D) ℂ} (hXY : X * Y = 1)
    (hYX : Y * X = 1) {N : ℕ} (S : Fin N → Matrix (Fin D) (Fin D) ℂ) (c : Fin N → ℂ)
    (hS : ∀ k, X * S k * Y = c k • S k) :
    X * (List.ofFn S).prod * Y = (∏ k, c k) • (List.ofFn S).prod := by
  have hsplit (P Q : Matrix (Fin D) (Fin D) ℂ) : X * (P * Q) * Y = X * P * Y * (X * Q * Y) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Y X, hYX, Matrix.one_mul]
  induction N with
  | zero => simp [hXY]
  | succ N ih =>
    rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ, hsplit, hS 0,
      ih (fun k ↦ S k.succ) (fun k ↦ c k.succ) (fun k ↦ hS k.succ), Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]

/-- **The scalars of a rescaled ring fix its trace**: if `X Y = Y X = 1` and
`X S_k Y = c_k S_k` for every factor, then `(∏_k c_k) tr (∏_k S_k) = tr (∏_k S_k)`. -/
theorem prod_mul_trace_prod_ofFn_eq {X Y : Matrix (Fin D) (Fin D) ℂ} (hXY : X * Y = 1)
    (hYX : Y * X = 1) {N : ℕ} (S : Fin N → Matrix (Fin D) (Fin D) ℂ) (c : Fin N → ℂ)
    (hS : ∀ k, X * S k * Y = c k • S k) :
    (∏ k, c k) * (List.ofFn S).prod.trace = (List.ofFn S).prod.trace := by
  calc (∏ k, c k) * (List.ofFn S).prod.trace
      = ((∏ k, c k) • (List.ofFn S).prod).trace := by
        simp only [Matrix.trace_smul, smul_eq_mul]
    _ = (X * (List.ofFn S).prod * Y).trace := by rw [mul_prod_ofFn_mul_eq_smul hXY hYX S c hS]
    _ = (List.ofFn S).prod.trace := by
        rw [Matrix.mul_assoc, Matrix.trace_mul_comm X, Matrix.mul_assoc, hYX, Matrix.mul_one]

end MPSTensor
