/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.CornerTransition

/-!
# The `m`-factor `Ω`-contraction for the periodic-overlap Case 3

This file formalizes the two algebraic mechanisms of the contraction step of
arXiv:1708.00029, Appendix A (lines 1041--1068):

* the **repeated-block matrix identity** (the `(m·N₀+1)`-fold repetition of
  `eq:BCmprop`), obtained from the cyclic concatenation law
  `cornerProd_append`; and
* the **`Ω`-contraction** that applies the tensor of right inverses
  `Ω_{u+1} ⊗ ⋯ ⊗ Ω_u` to the concatenated product
  `A_u^{i_1} F_{u+1} A_{u+1}^{i_2} F_{u+2} ⋯ A_{u+m-1}^{i_m} F_u`, using the
  finite-sum recovery identity `eq:Omegauprop` to replace each repeated product
  `F` by an inserted matrix.

The setting is the one-site corner letters `A_u^i` (`cornerLetter`) and their
repeated products `F_u` (`cornerProd` over a word whose length is a positive
multiple of `m`).

## Main results

* `cornerProd_blockMatch_pow` — the **repeated-block matrix identity** (step (a),
  lines 1041--1056).  Assuming the `m`-block product identity `eq:BCmprop`
  `A_u^{i_1}\cdots A_{u+m-1}^{i_m} = c_u · B_v^{i_1}\cdots B_{v+m-1}^{i_m}`
  holds for every length-`m` word, it propagates to every word `W` of length
  `k·m` (`k ≥ 1`): `cornerProd P A u W = (c u) ^ k • cornerProd Q B (u + q) W`.
  The full-cycle shift `m • 1 = 0` anchors every block at the base sector, so
  each contributes the same factor `c u`.

* `ofFn_contraction` — the **`Ω`-contraction mechanism** (step (b), lines
  1057--1062), as an abstract finite-product identity over any complex algebra:
  summing the ordered chain `∏_k (A_k · G_k^{ρ_k})` weighted by the inverse
  coefficients `∏_k (c_k X_k)_{ρ_k}` collapses each repeated product `G_k` to the
  inserted matrix `X_k`, yielding `∏_k (A_k · X_k)`.  This is the algebraic
  content of "apply `Ω_{u+1} ⊗ ⋯ ⊗ Ω_u` and use `eq:Omegauprop`".

* `cornerProd_contraction` — `ofFn_contraction` specialized to the periodic
  corner data, contracting the concatenation
  `∏_k (A_k^{σ_k} · F_{k+1}^{ρ_k})` to the chain `∏_k (A_k^{σ_k} · X_k)`.

The remaining steps of Appendix A (lines 1063--1080) — recombining the two
mechanisms with the per-sector scalar bookkeeping into the uniform
product-tensor identity `eq:resultprop`, and feeding it to
`PiTensorProductPhase.exists_kappa_product_one_of_piTensorProduct_eq_root_smul`
— are not addressed here; see
`docs/paper-gaps/1708_periodic_overlap_route_alignment.tex`.

## References

* De las Cuevas, Cirac, Schuch, Pérez-García,
  *Irreducible forms of Matrix Product States: Theory and Applications*,
  arXiv:1708.00029, Appendix A (eq:BCmprop, eq:Fu, eq:Omegauprop, eq:resultprop).
-/

open scoped Matrix BigOperators
open Matrix

namespace MPSTensor

variable {d D : ℕ}

/-! ## Step (a): the repeated-block matrix identity -/

section RepeatedBlock

variable {m : ℕ} [NeZero m]

/-- A full cycle of unit shifts is trivial in `Fin m`: `m • (1 : Fin m) = 0`.
This is the algebraic reason the appendix can repeat a single length-`m` block
around the cycle without moving the base sector. -/
lemma nsmul_card_one_fin : (m • (1 : Fin m)) = 0 := by
  have h : (Fintype.card (Fin m)) • (1 : Fin m) = 0 := card_nsmul_eq_zero
  simpa using h

/-- **Repeated-block matrix identity** (arXiv:1708.00029, Appendix A,
step toward eq:resultprop, lines 1041--1056).

If the `m`-block product identity `eq:BCmprop` holds for every length-`m` word,
then it propagates to every word `W` whose length is a positive multiple of `m`:
`cornerProd P A u W = (c u) ^ k • cornerProd Q B (u + q) W` when `|W| = k·m` with
`k ≥ 1`.  The scalar is `(c u) ^ k` because the full-cycle shift `m • 1 = 0`
anchors every length-`m` block at the same base sector `u`, so each block
contributes the same factor `c u`. -/
lemma cornerProd_blockMatch_pow
    (P : Fin m → MatrixAlg D) (Q : Fin m → MatrixAlg D)
    (A B : MPSTensor d D) (q : Fin m) (c : Fin m → ℂ)
    (hP : ∀ k, IsOrthogonalProjection (P k))
    (hQ : ∀ k, IsOrthogonalProjection (Q k))
    (hBC : ∀ (u : Fin m) (w : List (Fin d)), w.length = m →
      cornerProd P A u w = c u • cornerProd Q B (u + q) w)
    (u : Fin m) (k : ℕ) :
    ∀ W : List (Fin d), W.length = (k + 1) * m →
      cornerProd P A u W = (c u) ^ (k + 1) • cornerProd Q B (u + q) W := by
  induction k with
  | zero =>
    intro W hW
    rw [zero_add, one_mul] at hW
    simpa using hBC u W hW
  | succ k ih =>
    intro W hW
    set block := W.take m with hblock_def
    set rest := W.drop m with hrest_def
    have hWlen : m ≤ W.length := by rw [hW]; nlinarith [Nat.zero_le k]
    have hblock_len : block.length = m := by
      rw [hblock_def, List.length_take, Nat.min_eq_left hWlen]
    have hrest_len : rest.length = (k + 1) * m := by
      rw [hrest_def, List.length_drop, hW]; ring_nf; omega
    have hWeq : W = block ++ rest := (List.take_append_drop m W).symm
    -- The junction shift for a length-`m` block is trivial.
    have hshift : (block.length • (1 : Fin m)) = 0 := by
      rw [hblock_len]; exact nsmul_card_one_fin
    rw [hWeq, cornerProd_append P A hP u block rest, hshift, add_zero,
      hBC u block hblock_len, ih rest hrest_len]
    rw [cornerProd_append Q B hQ (u + q) block rest, hshift, add_zero]
    rw [smul_mul_smul_comm, ← pow_succ']

end RepeatedBlock

/-! ## Step (b): the `Ω`-contraction mechanism

The contraction is an algebraic identity over any complex algebra: it does not
use the matrix structure, only the bilinearity of the product and the finite-sum
recovery identity `eq:Omegauprop`.  We therefore state it for a general
`ℂ`-algebra `R`; the periodic instance is `R = M_D(ℂ)`. -/

section AbstractContraction

variable {R : Type*} [Ring R] {J : Type*} [Fintype J]

/-- Ordered noncommutative distributivity: the ordered product of finite sums is
the sum, over all choices, of the ordered products of the chosen summands.  This
is the combinatorial core of applying the tensor of inverses
`Ω_{u+1} ⊗ ⋯ ⊗ Ω_u` to a concatenated matrix product. -/
theorem ofFn_prod_sum {m : ℕ} (f : Fin m → J → R) :
    (List.ofFn (fun k : Fin m => ∑ j : J, f k j)).prod
      = ∑ ρ : Fin m → J, (List.ofFn (fun k => f k (ρ k))).prod := by
  classical
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.prod_cons, ih (fun k => f k.succ), Finset.sum_mul_sum]
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (m + 1) => J)), Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun ρ' _ => ?_))
    rw [List.ofFn_succ, List.prod_cons]
    simp [Fin.consEquiv]

variable [Algebra ℂ R]

/-- The scalars pull out of an ordered product: `∏_k (s_k • M_k) = (∏_k s_k) •
∏_k M_k`.  This collects the inverse coefficients of the contraction into a
single scalar in front of each chosen ordered product. -/
theorem ofFn_prod_smul {m : ℕ} (s : Fin m → ℂ) (M : Fin m → R) :
    (List.ofFn (fun k : Fin m => s k • M k)).prod = (∏ k, s k) • (List.ofFn M).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.prod_cons, ih (fun k => s k.succ) (fun k => M k.succ),
      smul_mul_smul_comm, Fin.prod_univ_succ, List.ofFn_succ, List.prod_cons]

/-- **The `Ω`-contraction** (arXiv:1708.00029, Appendix A, lines 1057--1062).

Each gap of the concatenation carries a repeated product `G_k`, recovered at the
inserted matrix `X_k` by the finite-sum coefficients `∑_j (c_k X_k)_j • G_k^j =
X_k` (`eq:Omegauprop` evaluated at `X_k`).  Summing the concatenated chain
`∏_k (A_k · G_k^{ρ_k})` against the coefficients `∏_k (c_k X_k)_{ρ_k}` collapses
each `G_k` to the inserted matrix `X_k`, leaving the chain `∏_k (A_k · X_k)`.
This is the algebraic content of applying `Ω_{u+1} ⊗ ⋯ ⊗ Ω_u` and invoking
`eq:Omegauprop`.

The recovery is required only at each inserted matrix `X_k`, not for every `Y`.
This matters for the cyclic-sector instance, where the right inverse `Ω_u`
recovers only the corner-supported matrices `P_u Y P_{u + L • 1}`, so a recovery
identity for every `Y` would force `P_u = 1`. -/
theorem ofFn_contraction {m : ℕ} (A X : Fin m → R) (G : Fin m → J → R)
    (c : Fin m → R → J → ℂ)
    (hinv : ∀ k : Fin m, ∑ j, c k (X k) j • G k j = X k) :
    ∑ ρ : Fin m → J, (∏ k, c k (X k) (ρ k)) • (List.ofFn (fun k => A k * G k (ρ k))).prod
      = (List.ofFn (fun k => A k * X k)).prod := by
  have hf : ∀ k, A k * X k = ∑ j, c k (X k) j • (A k * G k j) := by
    intro k
    conv_lhs => rw [← hinv k]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => mul_smul_comm _ _ _)
  symm
  calc (List.ofFn (fun k => A k * X k)).prod
      = (List.ofFn (fun k => ∑ j, c k (X k) j • (A k * G k j))).prod := by simp_rw [hf]
    _ = ∑ ρ : Fin m → J, (List.ofFn (fun k => c k (X k) (ρ k) • (A k * G k (ρ k)))).prod :=
        ofFn_prod_sum (fun k j => c k (X k) j • (A k * G k j))
    _ = ∑ ρ : Fin m → J,
          (∏ k, c k (X k) (ρ k)) • (List.ofFn (fun k => A k * G k (ρ k))).prod :=
        Finset.sum_congr rfl (fun ρ _ =>
          ofFn_prod_smul (fun k => c k (X k) (ρ k)) (fun k => A k * G k (ρ k)))

end AbstractContraction

/-! ## Step (b), periodic instance -/

section PeriodicContraction

variable {m : ℕ} [NeZero m]

/-- The `Ω`-contraction specialized to the periodic corner data
(arXiv:1708.00029, Appendix A, lines 1057--1062).

Here `A_k^i = cornerLetter P A k i`, the gap repeated products are
`F_{k+1}^{𝐣} = cornerProd P A (k+1) 𝐣` over length-`L` words, and `Ω_{k+1}`
recovers each inserted matrix `X_k`: `∑_{𝐣} (Ω_{k+1} X_k)_{𝐣} F_{k+1}^{𝐣} = X_k`
(`eq:Omegauprop` evaluated at `X_k`).  Contracting the concatenation
`∏_k (A_k^{σ_k} · F_{k+1}^{ρ_k})` with these coefficients replaces each `F_{k+1}`
by `X_k`, giving the chain `∏_k (A_k^{σ_k} · X_k)`.

The recovery is required only at the inserted matrices `X_k`, which in the
Case-3 contraction are the corner-supported tensors `P_{k+1} X_k P_{k+1+L•1}`
that `Ω_{k+1}` actually inverts. -/
theorem cornerProd_contraction
    (P : Fin m → MatrixAlg D) (A : MPSTensor d D) (L : ℕ)
    (Ω : Fin m → MatrixAlg D → (Fin L → Fin d) → ℂ)
    (σ : Fin m → Fin d) (X : Fin m → MatrixAlg D)
    (hΩ : ∀ k : Fin m,
      ∑ j : Fin L → Fin d, Ω (k + 1) (X k) j •
        cornerProd P A (k + 1) (List.ofFn j) = X k) :
    ∑ ρ : Fin m → (Fin L → Fin d),
        (∏ k, Ω (k + 1) (X k) (ρ k)) •
          (List.ofFn (fun k => cornerLetter P A k (σ k) *
            cornerProd P A (k + 1) (List.ofFn (ρ k)))).prod
      = (List.ofFn (fun k => cornerLetter P A k (σ k) * X k)).prod :=
  ofFn_contraction
    (fun k => cornerLetter P A k (σ k)) X
    (fun k j => cornerProd P A (k + 1) (List.ofFn j))
    (fun k => Ω (k + 1))
    hΩ

end PeriodicContraction

end MPSTensor
