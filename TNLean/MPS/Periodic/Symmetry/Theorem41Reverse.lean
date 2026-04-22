/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Symmetry.Theorem41Forward

/-!
# Theorem 4.1, reverse direction

This module contains the reverse half of Theorem 4.1 in its current conditional
formalization.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-! ## Theorem 4.1 — reverse direction (`p`-divisibility ⇒ `p`-refinability) -/

section Theorem41Reverse

variable {d D : ℕ}


/-- **Inverse canonicalization hypothesis for the reverse direction of Theorem 4.1.**

This Prop records the analytic content that connects `IsPDivisibleChannel (transferMap B) p`
(a channel-level `p`-th-root statement) to the existence of a witness tensor
`A : MPSTensor d D` whose `p`-blocked transfer map matches that of `B`.

Morally, if `transferMap B = (E')^p` for a CPTP map `E'`, one would like to choose a Kraus
representation `A` of `E'` with exactly `d` Kraus operators. In general the minimum Kraus
rank of `E'` may exceed `d`, so formalising this step requires a Kraus-rank reduction /
canonical-form argument (the analogue of left-canonical reduction used for the forward
direction). We expose the end-result as a hypothesis in the same style as
`PRefinementCanonicalization`. -/
def PRefinementInverseCanonicalization (d D p : ℕ) : Prop :=
  ∀ {B : MPSTensor d D}, IsIrreducibleForm B →
    IsPDivisibleChannel (transferMap B) p →
    ∃ A : MPSTensor d D, transferMap B = transferMap (blockTensor A p)

/-- **Reverse direction of Theorem 4.1 (conditional form).**

Let `B` be an MPS tensor in irreducible form II and let `p ≥ 1`. Assume the inverse
canonicalization hypothesis `PRefinementInverseCanonicalization` (which records the
remaining analytic bridge from `p`-divisibility of `transferMap B` to a compatible
Kraus-reducible witness). Then `IsPDivisibleChannel (transferMap B) p` implies
`IsPRefinable B p`.

The proof follows the paper (arXiv:1708.00029 §4.1, converse paragraph): from the inverse
canonicalization we obtain `A : MPSTensor d D` with
`transferMap B = transferMap (blockTensor A p)`; this matches two Kraus representations of
the same CP map (`blockTensor A p` with `d^p` operators and `B` with `d` operators), so
Wolf Theorem 2.18 (`kraus_isometry_freedom_iff`) supplies an isometry
`V : Matrix (Fin (d^p)) (Fin d) ℂ` with `Vᴴ V = 1` and
`blockTensor A p α = ∑_j V α j • B j`. Expanding `coeff (blockTensor A p) (ofFn τ)` with
the helper `evalWord_sum_smul_ofFn` and linearity of `trace` produces exactly the
`W`-weighted coefficient identity defining `IsPRefinable B p`. -/
theorem thm_4_1_p_refinement_reverse
    (B : MPSTensor d D) (hB : IsIrreducibleForm B)
    (p : ℕ) (hp : 0 < p)
    (hInverse : PRefinementInverseCanonicalization d D p)
    (hDivisible : IsPDivisibleChannel (transferMap B) p) :
    IsPRefinable B p := by
  obtain ⟨A, hTransferEq⟩ := hInverse hB hDivisible
  classical
  -- `d ≤ d^p = blockPhysDim d p` whenever `p ≥ 1`: the Kraus-rank comparison needed by
  -- Wolf Theorem 2.18.
  have hCard : Fintype.card (Fin d) ≤ Fintype.card (Fin (blockPhysDim d p)) := by
    simp only [Fintype.card_fin, blockPhysDim_eq_pow]
    exact Nat.le_self_pow hp.ne' d
  -- Translate the linear-map equality into the Kraus-family equality needed by the freedom
  -- lemma.
  have hKraus :
      ∀ X : Matrix (Fin D) (Fin D) ℂ,
        ∑ α : Fin (blockPhysDim d p), blockTensor A p α * X * (blockTensor A p α)ᴴ =
          ∑ j : Fin d, B j * X * (B j)ᴴ := by
    intro X
    have hEq : transferMap (blockTensor A p) X = transferMap B X := by
      rw [← hTransferEq]
    simpa [transferMap_apply] using hEq
  -- Extract the isometric mixing matrix `V` from Wolf Thm 2.18.
  obtain ⟨V, hV, hBA⟩ :=
    (kraus_isometry_freedom_iff (blockTensor A p) B hCard).mp hKraus
  refine ⟨A, V, hV, ?_⟩
  intro N τ
  simp only [coeff_eq]
  -- Pointwise rewrite `blockTensor A p` as the `V`-mixing of `B`.
  have hAeq : (blockTensor A p : MPSTensor (blockPhysDim d p) D) =
      fun α => ∑ j : Fin d, V α j • B j := funext hBA
  rw [hAeq, evalWord_sum_smul_ofFn B V N τ, Matrix.trace_sum]
  refine Finset.sum_congr rfl ?_
  intro σ _
  rw [Matrix.trace_smul]
  rfl

end Theorem41Reverse

end MPSTensor
