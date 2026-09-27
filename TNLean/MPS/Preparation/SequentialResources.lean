/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.IsometricChain
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Bond dimensions of the successive-decomposition representation

After the successive-decomposition recipe of Schön, Solano, Verstraete, Cirac,
and Wolf (arXiv:quant-ph/0501096, eq. `induction`), the source bounds the size of
the isometries it produces: "Simple rank considerations show that
`V'_{[n-k]}` has dimension `2min[D,2^k] × min[D,2^{k+1}]`" (lines 200--202 of
`References/quant-ph_0501096/PhotoMPS.tex`, for qubits). This file proves the
statement for local dimension `d`, together with the mirror bound obtained by
running the recipe once from each end.

## Site order

The source writes the state as `⟨φ_F| Ṽ_{[n]} ⋯ Ṽ_{[1]} |φ_I⟩` and starts the
decompositions at the `φ_F` end, with the `2 × 2` matrix `V'_{[n]}`. An
`OBCChainTensor` is read from site `0` to site `N - 1`, and
`OBCChainTensor.exists_isometric_coeff_eq` starts its sweep at site `0`, so site
`k` here is the source's `V'_{[n-k]}`, and the bond `k` of the chain (between
sites `k - 1` and `k`) is the bond of `V'_{[n-k]}` on the `φ_F` side. The source's
bound `min[D, 2^k]` therefore counts the `k` sites between that bond and the end
where the sweep starts: in the chain, bond `k` has dimension at most
`min(D, d^k)`.

## Main results

* `OBCChainTensor.bondDim_succ_le_mul` — a site with `∑_i A_i^† A_i = 1` has
  right bond at most `d` times its left bond; this is the rank consideration.
* `OBCChainTensor.bondDim_le_pow` — in an open chain whose sites except the last
  satisfy `∑_i A_i^† A_i = 1`, bond `k` has dimension at most `d^k`.
* `OBCChainTensor.exists_isometric_coeff_eq_le_pow` — the representation of
  `exists_isometric_coeff_eq` obeys the source's bound `min(D, d^k)`.
* `OBCChainTensor.reverse`, `OBCChainTensor.coeff_reverse` — reading an open
  chain from the other end.
* `OBCChainTensor.exists_isometric_coeff_eq_le_min` — running the recipe first
  from the right end and then from the left end gives a representation with the
  same isometric sites whose bond `k` is at most
  `min(D_k, d^k, d^{N-k})`, where `D_k ≤ D` is the bond of the given chain.

## References

* Schön, Solano, Verstraete, Cirac, Wolf, *Sequential generation of entangled
  multiqubit states*, Phys. Rev. Lett. 95, 110503 (2005), arXiv:quant-ph/0501096,
  eq. `induction` and lines 200--203 of
  `References/quant-ph_0501096/PhotoMPS.tex`.
* Pérez-García, Verstraete, Wolf, Cirac, *Matrix product state representations*,
  arXiv:quant-ph/0608197, lines 1574--1578 of
  `Papers/quant-ph_0608197/MPSarchive.tex`: the proof of Theorem `Thm:seqwith`
  "also provides a \emph{recipe} for the generation of any given state (with
  minimal resources)".
-/

open scoped BigOperators Matrix ComplexOrder

namespace OBCChainTensor

variable {d D N : ℕ}

/-- **The rank consideration.** If `A_0, …, A_{d-1}` are `a × b` matrices with
`∑_i A_i^† A_i = 1`, then `b ≤ a d`: the stacked `(a d) × b` matrix has
orthonormal columns.

This is the step behind "Simple rank considerations show that `V'_{[n-k]}` has
dimension `2min[D,2^k] × min[D,2^{k+1}]`", arXiv:quant-ph/0501096, lines
200--202 of `References/quant-ph_0501096/PhotoMPS.tex`, for local dimension
`d`. -/
theorem le_mul_of_sum_conjTranspose_mul_eq_one {a b : ℕ}
    (A : Fin d → Matrix (Fin a) (Fin b) ℂ) (hA : ∑ i, (A i)ᴴ * A i = 1) : b ≤ a * d := by
  let S : Matrix (Fin a × Fin d) (Fin b) ℂ := Matrix.of fun x β => A x.2 x.1 β
  have hS : Sᴴ * S = 1 := by
    rw [← hA]
    ext β β'
    simp only [S, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.of_apply]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc b = (1 : Matrix (Fin b) (Fin b) ℂ).rank := by rw [Matrix.rank_one, Fintype.card_fin]
    _ = S.rank := by rw [← hS, Matrix.rank_conjTranspose_mul_self]
    _ ≤ Fintype.card (Fin a × Fin d) := Matrix.rank_le_card_height S
    _ = a * d := by simp

/-- A site of an open chain with `∑_i A_i^† A_i = 1` has right bond at most `d`
times its left bond. See `le_mul_of_sum_conjTranspose_mul_eq_one`. -/
theorem bondDim_succ_le_mul (B : OBCChainTensor d D N) (p : Fin N)
    (hp : ∑ i, (B.tensor p i)ᴴ * B.tensor p i = 1) :
    B.bondDim p.succ ≤ B.bondDim p.castSucc * d :=
  le_mul_of_sum_conjTranspose_mul_eq_one (B.tensor p) hp

/-- **Bond growth from the start of the sweep.** In an open chain of positive
local dimension whose sites, except possibly the last, satisfy
`∑_i A_i^† A_i = 1`, bond `k` has dimension at most `d^k`.

This is the bound `min[D, 2^k]` of arXiv:quant-ph/0501096, lines 200--202 of
`References/quant-ph_0501096/PhotoMPS.tex`, for local dimension `d`, in the site
order of `OBCChainTensor` (see the module docstring). -/
theorem bondDim_le_pow [NeZero d] {n : ℕ} (B : OBCChainTensor d D (n + 1))
    (hiso : ∀ p : Fin (n + 1), p ≠ Fin.last n → ∑ i, (B.tensor p i)ᴴ * B.tensor p i = 1)
    (k : Fin (n + 2)) : B.bondDim k ≤ d ^ (k : ℕ) := by
  induction k using Fin.induction with
  | zero => simp [B.left_dim]
  | succ p ih =>
    by_cases hp : p = Fin.last n
    · subst hp
      rw [Fin.succ_last, B.right_dim]
      exact Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne d))
    · calc B.bondDim p.succ ≤ B.bondDim p.castSucc * d := B.bondDim_succ_le_mul p (hiso p hp)
        _ ≤ d ^ (p : ℕ) * d := Nat.mul_le_mul_right _ (by simpa using ih)
        _ = d ^ ((p.succ : Fin (n + 2)) : ℕ) := by simp [pow_succ]

/-- **Resources of the successive-decomposition recipe.** Every open-boundary
chain state of positive local dimension has an open-boundary representation in
which every site except the last satisfies `∑_i A_i^† A_i = 1` and bond `k` has
dimension at most `min(D_k, d^k)`, where `D_k ≤ D` is the bond of the given
chain.

This is the recipe of arXiv:quant-ph/0501096, eq. `induction`, with the bound
"`V'_{[n-k]}` has dimension `2min[D,2^k] × min[D,2^{k+1}]`" (lines 200--202 of
`References/quant-ph_0501096/PhotoMPS.tex`) for local dimension `d`; bond `k` of
the chain is the `φ_F`-side bond of the source's `V'_{[n-k]}`. -/
theorem exists_isometric_coeff_eq_le_pow [NeZero d] {n : ℕ} (B : OBCChainTensor d D (n + 1)) :
    ∃ B' : OBCChainTensor d D (n + 1), B'.coeff = B.coeff ∧
      (∀ k, B'.bondDim k ≤ B.bondDim k) ∧ (∀ k, B'.bondDim k ≤ d ^ (k : ℕ)) ∧
      ∀ p : Fin (n + 1), p ≠ Fin.last n → ∑ i, (B'.tensor p i)ᴴ * B'.tensor p i = 1 := by
  obtain ⟨B', hB', hbond, hiso⟩ := B.exists_isometric_coeff_eq
  exact ⟨B', hB', hbond, B'.bondDim_le_pow hiso, hiso⟩

/-- The open chain read from the other end: bond `k` is the bond `N - k` of the
given chain, and the site matrices are transposed. This auxiliary operation is
not in the sources; it is used to run the recipe of arXiv:quant-ph/0501096,
eq. `induction`, starting from the other end of the chain. -/
def reverse (B : OBCChainTensor d D N) : OBCChainTensor d D N where
  bondDim k := B.bondDim k.rev
  bondDim_le k := B.bondDim_le _
  left_dim := by simpa using B.right_dim
  right_dim := by simpa using B.left_dim
  tensor p i α β :=
    B.tensor p.rev i (Fin.cast (by rw [Fin.rev_succ]) β) (Fin.cast (by rw [Fin.rev_castSucc]) α)

/-- Bond `k` of the reversed chain is bond `N - k` of the given chain. -/
@[simp] theorem bondDim_reverse (B : OBCChainTensor d D N) (k : Fin (N + 1)) :
    B.reverse.bondDim k = B.bondDim k.rev := rfl

/-- The coefficients of the reversed chain are those of the given chain at the
reversed configuration. -/
theorem coeff_reverse (B : OBCChainTensor d D N) (σ : Fin N → Fin d) :
    B.reverse.coeff σ = B.coeff fun p => σ p.rev := by
  let e : ((k : Fin (N + 1)) → Fin (B.bondDim k)) ≃
      ((k : Fin (N + 1)) → Fin (B.bondDim k.rev)) :=
    { toFun := fun β k => β k.rev
      invFun := fun α k => Fin.cast (by rw [Fin.rev_rev]) (α k.rev)
      left_inv := fun β => by
        funext k
        have key : ∀ {q q' : Fin (N + 1)} (h : q = q') (hc : B.bondDim q = B.bondDim q'),
            Fin.cast hc (β q) = β q' := by
          rintro _ _ rfl _; rfl
        exact key (Fin.rev_rev k) _
      right_inv := fun α => by
        funext k
        have key : ∀ q, q = k → ∀ (hc : B.bondDim q.rev = B.bondDim k.rev),
            Fin.cast hc (α q) = α k := by
          rintro q rfl hc; rfl
        exact key k.rev.rev (Fin.rev_rev k) _ }
  refine (Fintype.sum_equiv e _ _ fun β => ?_).symm
  rw [← Equiv.prod_comp (Fin.revPerm : Equiv.Perm (Fin N))]
  refine Finset.prod_congr rfl fun p _ => ?_
  have key : ∀ {q q' : Fin (N + 1)} (h : q = q') (hc : B.bondDim q = B.bondDim q'),
      Fin.cast hc (β q) = β q' := by
    rintro _ _ rfl _; rfl
  simp only [Fin.revPerm_apply, Fin.rev_rev, reverse, e, Equiv.coe_fn_mk]
  rw [key (Fin.rev_succ p) _, key (Fin.rev_castSucc p) _]
  rfl

/-- **Resources of the recipe run from both ends.** Every open-boundary chain
state of positive local dimension has an open-boundary representation in which
every site except the last satisfies `∑_i A_i^† A_i = 1` and bond `k` has
dimension at most `min(D_k, d^k, d^{N-k})`, where `D_k ≤ D` is the bond of the
given chain and `N = n + 1` is the length.

The bound `d^k` is the one of arXiv:quant-ph/0501096, lines 200--202 of
`References/quant-ph_0501096/PhotoMPS.tex`, counted from the end where the
sweep starts. The bound `d^{N-k}` comes from first running the same recipe from
the other end; the source states only the one-sided bound. -/
theorem exists_isometric_coeff_eq_le_min [NeZero d] {n : ℕ} (B : OBCChainTensor d D (n + 1)) :
    ∃ B' : OBCChainTensor d D (n + 1), B'.coeff = B.coeff ∧
      (∀ k, B'.bondDim k ≤ B.bondDim k) ∧ (∀ k, B'.bondDim k ≤ d ^ (k : ℕ)) ∧
      (∀ k : Fin (n + 2), B'.bondDim k ≤ d ^ (n + 1 - k)) ∧
      ∀ p : Fin (n + 1), p ≠ Fin.last n → ∑ i, (B'.tensor p i)ᴴ * B'.tensor p i = 1 := by
  obtain ⟨C, hC, hCbond, hCpow, -⟩ := B.reverse.exists_isometric_coeff_eq_le_pow
  obtain ⟨B', hB', hbond, hpow, hiso⟩ := C.reverse.exists_isometric_coeff_eq_le_pow
  refine ⟨B', ?_, fun k => ?_, hpow, fun k => ?_, hiso⟩
  · funext σ
    rw [hB', coeff_reverse, hC, coeff_reverse]
    simp
  · refine (hbond k).trans ?_
    simpa using hCbond k.rev
  · refine (hbond k).trans ?_
    simpa [Fin.val_rev] using hCpow k.rev

end OBCChainTensor
