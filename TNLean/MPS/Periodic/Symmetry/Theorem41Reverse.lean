/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.KrausRank
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

This proposition states the analytic content that connects `IsPDivisibleChannel (transferMap B) p`
(a channel-level `p`-th-root statement) to the existence of a witness tensor
`A : MPSTensor d D` whose `p`-blocked transfer map matches that of `B`.

Morally, if `transferMap B = (E')^p` for a CPTP map `E'`, one would like to choose a Kraus
representation `A` of `E'` with exactly `d` Kraus operators. In general the minimum Kraus
rank of `E'` may exceed `d`, so formalising this step requires a Kraus-rank reduction /
canonical-form argument (the analogue of left-canonical reduction used for the forward
direction). The theorem `pRefinementInverseCanonicalization_of_rootKrausRankBound` below
shows that it is enough to prove a bounded-Kraus-rank statement for the root channel. -/
def PRefinementInverseCanonicalization (d D p : ℕ) : Prop :=
  ∀ {B : MPSTensor d D}, IsIrreducibleForm B →
    IsPDivisibleChannel (transferMap B) p →
    ∃ A : MPSTensor d D, transferMap B = transferMap (blockTensor A p)

/-- A bounded Kraus-rank witness for a channel root can be expressed as an
`MPSTensor` with the ambient physical dimension by zero-padding the Kraus family. -/
theorem exists_tensor_of_hasKrausRankLE
    {E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hE : Channel.HasKrausRankLE (D := D) E d) :
    ∃ A : MPSTensor d D, transferMap A = E := by
  rcases hE with ⟨s, hs, hE⟩
  obtain ⟨K, hK⟩ := Channel.hasKrausCard_mono (D := D) hE hs
  refine ⟨K, ?_⟩
  ext X i j
  simpa [transferMap_apply] using congrArg (fun M => M i j) (hK X).symm

/-- **Channel-root formulation of blocked-to-root reconstruction.**

This Prop isolates the channel-theoretic core of
`PeripheralEqualCaseRootFromZGauge`: from a blocked `Z`-gauge witness between
`C` and `blockTensor A p`, extract a CPTP root `E'` of `transferMap C` whose
Kraus rank is at most the ambient physical dimension `d`. Once such a root is
available, the tensor-level reconstruction follows by choosing a Kraus family
with `d` operators. -/
def PeripheralEqualCaseRootChannelOfZGauge (d D p : ℕ) : Prop :=
  ∀ {A : MPSTensor d D} {C : MPSTensor (blockPhysDim d p) D} {m : ℕ},
    IsIrreducibleForm C →
    0 < m →
    ZGaugeEquiv m C (blockTensor A p) →
      ∃ E' : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ,
        IsChannel E' ∧
        transferMap C = E' ^ p ∧
        Channel.HasKrausRankLE (D := D) E' d

/-- **Tensor-level blocked-to-root reconstruction from a bounded channel root.**

If a blocked `Z`-gauge witness yields a CPTP root channel of `transferMap C`
with Kraus rank at most `d`, then one can choose a tensor `A' : MPSTensor d D`
realizing that root. The channel property forces `A'` to be left-canonical,
and blocking recovers the transfer map of `C`. -/
theorem peripheralEqualCaseRootFromZGauge_of_rootChannel
    (hRoot : PeripheralEqualCaseRootChannelOfZGauge d D p) :
    PeripheralEqualCaseRootFromZGauge d D p := by
  intro A C m hC hm hZ
  obtain ⟨E', hE'chan, hpow, hRank⟩ :=
    hRoot (A := A) (C := C) (m := m) hC hm hZ
  obtain ⟨A', hA'⟩ := exists_tensor_of_hasKrausRankLE (d := d) (D := D) hRank
  refine ⟨A', ?_, ?_⟩
  · have hK :
        ∀ X : Matrix (Fin D) (Fin D) ℂ,
          E' X = ∑ i : Fin d, A' i * X * (A' i)ᴴ := by
        intro X
        simpa [transferMap_apply] using (congrArg (fun T => T X) hA').symm
    simpa using kraus_sum_conjTranspose_mul_of_tp A' E' hK hE'chan.tp
  · calc
      transferMap C = E' ^ p := hpow
      _ = (transferMap A') ^ p := by rw [← hA']
      _ = transferMap (blockTensor A' p) := by rw [transferMap_blockTensor]

/-- A clean root-cardinality hypothesis that isolates the remaining Kraus-rank
step in the reverse direction of Theorem 4.1. -/
def PRefinementInverseRootKrausRankBound (d D p : ℕ) : Prop :=
  ∀ {B : MPSTensor d D}, IsIrreducibleForm B →
    ∀ {E' : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ},
      IsChannel E' → transferMap B = E' ^ p → Channel.HasKrausRankLE (D := D) E' d

/-- A bounded-Kraus-rank root hypothesis is enough to recover the existing
inverse canonicalization hypothesis. -/
theorem pRefinementInverseCanonicalization_of_rootKrausRankBound
    (hRoot : PRefinementInverseRootKrausRankBound d D p) :
    PRefinementInverseCanonicalization d D p := by
  intro B hB hDivisible
  rcases hDivisible with ⟨E', hE'chan, hpow⟩
  have hRank : Channel.HasKrausRankLE (D := D) E' d := hRoot hB hE'chan hpow
  obtain ⟨A, hA⟩ := exists_tensor_of_hasKrausRankLE (d := d) (D := D) hRank
  refine ⟨A, ?_⟩
  calc
    transferMap B = E' ^ p := hpow
    _ = (transferMap A) ^ p := by rw [← hA]
    _ = transferMap (blockTensor A p) := by rw [transferMap_blockTensor]

/-- **Reverse direction of Theorem 4.1 (conditional form).**

Let `B` be an MPS tensor in irreducible form II and let `p ≥ 1`. Assume the inverse
canonicalization hypothesis `PRefinementInverseCanonicalization` (which states the
remaining analytic passage from `p`-divisibility of `transferMap B` to a compatible
Kraus-reducible witness). Then `IsPDivisibleChannel (transferMap B) p` implies
`IsPRefinable B p`.

The proof follows the paper (arXiv:1708.00029 §4.1, converse paragraph): from the inverse
canonicalization we obtain `A : MPSTensor d D` with
`transferMap B = transferMap (blockTensor A p)`; this matches two Kraus representations of
the same CP map (`blockTensor A p` with `d^p` operators and `B` with `d` operators), so
Wolf Theorem 2.18 (`kraus_isometry_freedom_iff`) supplies an isometry
`V : Matrix (Fin (d^p)) (Fin d) ℂ` with `Vᴴ V = 1` and
`blockTensor A p α = ∑_j V α j • B j`. Expanding `coeff (blockTensor A p) (ofFn τ)` with
the auxiliary `evalWord_sum_smul_ofFn` and linearity of `trace` produces exactly the
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
