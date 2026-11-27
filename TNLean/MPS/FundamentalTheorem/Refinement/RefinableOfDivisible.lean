/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.KrausMap.KrausRank
import TNLean.MPS.FundamentalTheorem.Refinement.IsometryTensor
import QICLean.Channel.PSDConeAutomorphism.InjectivePositiveMapRank
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import QICLean.Channel.KrausMap.KrausMap
import QICLean.Channel.Schwarz.Closure
import QICLean.Kraus.ChoiRankSpan
import QICLean.Kraus.Wielandt.SpanGrowth.InvertibleWordSpan
import QICLean.Kraus.WordSpan
import QICLean.Algebra.Matrix.MatrixRankBaseChange

/-!
# Theorem 4.1, reverse direction

This module contains the reverse half of Theorem 4.1. Equality of the transfer
map with a blocked transfer map gives a refinement tensor, and so does a channel
root represented by at most the physical dimension's number of Kraus operators.
The remaining root-selection problem is recorded in
`docs/paper-gaps/dccsp17_root_kraus_rank_thm41.tex`.

## Refinement of tensors with invertible transfer maps

Every completely positive root of an invertible transfer map has Choi rank
at most that of the transfer map. Thus channel divisibility gives tensor
refinement without a separate choice of a bounded-rank root.

**Scope restriction (invertible transfer map):** This proves the converse
of arXiv:1708.00029, Theorem 4.1, lines 812--818, for transfer maps that are
invertible as linear maps. The singular case remains the selection problem
recorded in `docs/paper-gaps/dccsp17_root_kraus_rank_thm41.tex`.
-/

open MPTensor

section

open scoped Matrix BigOperators
open Kraus (blockPhysDim blockPhysDim_eq_pow blockTensor)

namespace MPSTensor

/-! ## Theorem 4.1 — reverse direction (`p`-divisibility ⇒ `p`-refinability) -/

section Theorem41Reverse

variable {d D : ℕ}


/-- **Inverse canonicalization hypothesis for the reverse direction of Theorem 4.1.**

This proposition states the analytic content that connects
`IsPDivisibleChannel (Kraus.transferMap B) p`
(a channel-level `p`-th-root statement) to the existence of a witness tensor
`A : MPSTensor d D` whose `p`-blocked transfer map matches that of `B`.

Morally, if `Kraus.transferMap B = (E')^p` for a CPTP map `E'`, one would like to choose a Kraus
representation `A` of `E'` with exactly `d` Kraus operators. In general the minimum Kraus
rank of `E'` may exceed `d`, so formalising this step requires a Kraus-rank reduction /
canonical-form argument (the analogue of left-canonical reduction used for the forward
direction). The theorem `pRefinementInverseCanonicalization_of_rootKrausRankBound` below
shows that it is enough to prove a bounded-Kraus-rank statement for the root channel. -/
def PRefinementInverseCanonicalization (d D p : ℕ) : Prop :=
  ∀ {B : MPSTensor d D}, IsIrreducibleForm B →
    IsPDivisibleChannel (Kraus.transferMap B) p →
    ∃ A : MPSTensor d D, Kraus.transferMap B = Kraus.transferMap (blockTensor A p)

/-- A bounded Kraus-rank witness for a channel root can be expressed as an
`MPSTensor` with the ambient physical dimension by zero-padding the Kraus family. -/
theorem exists_tensor_of_hasKrausRankLE
    {E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hE : Channel.HasKrausRankLE E d) :
    ∃ A : MPSTensor d D, Kraus.transferMap A = E := by
  rcases hE with ⟨s, hs, hE⟩
  obtain ⟨K, hK⟩ := Channel.hasKrausCard_mono hE hs
  refine ⟨K, ?_⟩
  ext X i j
  simpa [Kraus.transferMap_apply] using congrArg (fun M => M i j) (hK X).symm

/-- A clean root-cardinality hypothesis that isolates the remaining Kraus-rank
step in the reverse direction of Theorem 4.1. -/
def PRefinementInverseRootKrausRankBound (d D p : ℕ) : Prop :=
  ∀ {B : MPSTensor d D}, IsIrreducibleForm B →
    ∀ {E' : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ},
      IsChannel E' → Kraus.transferMap B = E' ^ p → Channel.HasKrausRankLE E' d

/-- A bounded-Kraus-rank root hypothesis is enough to recover the existing
inverse canonicalization hypothesis. -/
theorem pRefinementInverseCanonicalization_of_rootKrausRankBound
    {p : ℕ}
    (hRoot : PRefinementInverseRootKrausRankBound d D p) :
    PRefinementInverseCanonicalization d D p := by
  intro B hB hDivisible
  rcases hDivisible with ⟨E', hE'chan, hpow⟩
  have hRank : Channel.HasKrausRankLE E' d := hRoot hB hE'chan hpow
  obtain ⟨A, hA⟩ := exists_tensor_of_hasKrausRankLE (d := d) (D := D) hRank
  refine ⟨A, ?_⟩
  calc
    Kraus.transferMap B = E' ^ p := hpow
    _ = (Kraus.transferMap A) ^ p := by rw [← hA]
    _ = Kraus.transferMap (blockTensor A p) := by rw [Kraus.transferMap_blockTensor]

/-- Equality with a blocked transfer map gives a refinement isometry.
No irreducible-form assumption is needed for this Kraus representation step:
the two Kraus representations of the same map are related by an isometry
(Wolf Theorem 2.1(4), `kraus_isometry_freedom_iff`), and expanding the blocked
coefficients with `evalWord_sum_smul_ofFn` gives the weighted coefficient
identity defining `IsPRefinable B p`.
Source: arXiv:1708.00029, Theorem 4.1, converse paragraph, lines 812--818. -/
theorem isPRefinable_of_transferMap_eq_blockTensor
    (B A : MPSTensor d D) {p : ℕ} (hp : 0 < p)
    (hTransferEq : Kraus.transferMap B = Kraus.transferMap (blockTensor A p)) :
    IsPRefinable B p := by
  classical
  -- `d ≤ d^p = blockPhysDim d p` whenever `p ≥ 1`: the Kraus-rank comparison needed by
  -- Wolf Theorem 2.1(4).
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
    have hEq : Kraus.transferMap (blockTensor A p) X = Kraus.transferMap B X := by
      rw [← hTransferEq]
    simpa [Kraus.transferMap_apply] using hEq
  -- Extract the isometric mixing matrix `V` from Wolf Theorem 2.1(4).
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


/-- A selected channel root with at most the physical dimension's number
of Kraus operators gives a refinement tensor.

**Scope restriction (bounded root):** This proves the converse step of
arXiv:1708.00029, Theorem 4.1, lines 812--818, when the selected root has
Kraus rank at most `d`. Existence of such a root from divisibility alone is
not proved; see `docs/paper-gaps/dccsp17_root_kraus_rank_thm41.tex`. -/
theorem isPRefinable_of_channel_root_hasKrausRankLE
    (B : MPSTensor d D) {p : ℕ} (hp : 0 < p)
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hpow : Kraus.transferMap B = E ^ p)
    (hRank : Channel.HasKrausRankLE E d) :
    IsPRefinable B p := by
  obtain ⟨A, hA⟩ := exists_tensor_of_hasKrausRankLE hRank
  apply isPRefinable_of_transferMap_eq_blockTensor B A hp
  rw [Kraus.transferMap_blockTensor, hA]
  exact hpow

/-- **Reverse direction of Theorem 4.1 (conditional form).**

Let `B` be an MPS tensor in irreducible form II and let `p ≥ 1`. Assume the inverse
canonicalization hypothesis `PRefinementInverseCanonicalization` (which states the
remaining analytic passage from `p`-divisibility of `Kraus.transferMap B` to a compatible
Kraus-reducible witness). Then `IsPDivisibleChannel (Kraus.transferMap B) p` implies
`IsPRefinable B p`, by `isPRefinable_of_transferMap_eq_blockTensor`.
Source: arXiv:1708.00029, Section 4.1, converse paragraph. -/
theorem thm_4_1_p_refinement_reverse
    (B : MPSTensor d D) (hB : IsIrreducibleForm B)
    (p : ℕ) (hp : 0 < p)
    (hInverse : PRefinementInverseCanonicalization d D p)
    (hDivisible : IsPDivisibleChannel (Kraus.transferMap B) p) :
    IsPRefinable B p := by
  obtain ⟨A, hTransferEq⟩ := hInverse hB hDivisible
  exact isPRefinable_of_transferMap_eq_blockTensor B A hp hTransferEq

end Theorem41Reverse

end MPSTensor

end

section

open scoped Matrix

namespace MPSTensor

/-- Channel divisibility implies refinement when the target transfer map is
injective, hence invertible in finite dimension. No canonical-form assumption
is required. Source context: arXiv:1708.00029, Theorem 4.1, converse,
lines 812--818. -/
theorem isPRefinable_of_isPDivisibleChannel_of_injective
    {d D p : ℕ} (B : MPSTensor d D) (hp : 0 < p)
    (hB : Function.Injective (Kraus.transferMap B))
    (hDiv : IsPDivisibleChannel (Kraus.transferMap B) p) :
    IsPRefinable B p := by
  obtain ⟨F, hF, hpow⟩ := hDiv
  have hPowInjective : Function.Injective (F ^ p) := hpow ▸ hB
  have hFInjective : Function.Injective F := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
    intro X Y hXY
    apply hPowInjective
    simp only [pow_succ, Module.End.mul_apply, hXY]
  have hRank : Channel.choiRank F ≤ d := by
    calc
      Channel.choiRank F ≤ Channel.choiRank (F ^ p) :=
        Channel.choiRank_le_pow_of_injective hF.cp hFInjective hp
      _ = Channel.choiRank (Kraus.transferMap B) := congrArg Channel.choiRank hpow.symm
      _ ≤ d := Channel.choiRank_le_of_hasKrausCard ⟨B, by intro X; simp⟩
  exact isPRefinable_of_channel_root_hasKrausRankLE B hp F hpow
    ⟨Channel.choiRank F, hRank, Channel.hasKrausCard_choiRank_of_cp hF.cp⟩

end MPSTensor

end

section

/-!
## Bounded roots for qubit channels

Every qubit channel has Choi rank at most that of each positive power.
Consequently channel divisibility gives refinement for every tensor of bond
dimension two, including singular and reducible transfer maps. This proves
the bond-dimension-two case of arXiv:1708.00029, Theorem 4.1, converse.
The general higher-dimensional singular selection problem remains open;
see `docs/paper-gaps/dccsp17_root_kraus_rank_thm41.tex`.
-/

open scoped Matrix BigOperators

private theorem channel_injective_of_choiRank_le_one {D : ℕ}
    {F : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)} (hF : IsChannel F)
    (hRank : Channel.choiRank F ≤ 1) : Function.Injective F := by
  obtain ⟨K, hK⟩ := Channel.hasKrausCard_mono
    (Channel.hasKrausCard_choiRank_of_cp hF.cp) hRank
  have hNorm : (K 0)ᴴ * K 0 = 1 := by
    simpa using kraus_sum_conjTranspose_mul_of_tp K F hK hF.tp
  have hMap (X : Matrix (Fin D) (Fin D) ℂ) : F X = K 0 * X * (K 0)ᴴ := by
    simpa using hK X
  have hInv (X : Matrix (Fin D) (Fin D) ℂ) :
      (K 0)ᴴ * (K 0 * X * (K 0)ᴴ) * K 0 = X := by
    calc
      _ = ((K 0)ᴴ * K 0) * X * ((K 0)ᴴ * K 0) := by noncomm_ring
      _ = X := by simp only [hNorm, Matrix.one_mul, Matrix.mul_one]
  intro X Y hXY
  have h := congrArg (fun Z => (K 0)ᴴ * Z * K 0) hXY
  simpa only [hMap, hInv] using h

namespace Channel

/-- Every qubit channel has Choi rank at most that of every positive
power. No irreducibility or invertibility assumption is needed. This
proves the full bond-dimension-two root-rank step in arXiv:1708.00029,
Theorem 4.1, converse, lines 812--818. -/
theorem _root_.TNLean.MPS.FundamentalTheorem.choiRank_le_pow_fin_two
    {F : Module.End ℂ (Matrix (Fin 2) (Fin 2) ℂ)} (hF : IsChannel F)
    {p : ℕ} (hp : 0 < p) : choiRank F ≤ choiRank (F ^ p) := by
  by_cases hSmall : choiRank (F ^ p) ≤ 1
  · have hPowInj : Function.Injective (F ^ p) :=
      channel_injective_of_choiRank_le_one ⟨hF.cp.pow p, hF.tp.pow p⟩ hSmall
    have hInj : Function.Injective F := by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
      intro X Y hXY
      apply hPowInj
      simp only [pow_succ, Module.End.mul_apply, hXY]
    exact choiRank_le_pow_of_injective hF.cp hInj hp
  by_cases hRank : choiRank F ≤ 2
  · omega
  obtain ⟨r, A, hA, _⟩ := hF.exists_kraus_map_eq_and_normalized
  have hDim : 2 < Module.finrank ℂ (Kraus.wordSpan A 1) := by
    have h := choiRank_mapLM_eq_finrank_wordSpan_one A
    rw [← hA] at h
    omega
  obtain ⟨X, hX, hUnit⟩ : ∃ X ∈ Kraus.wordSpan A 1, IsUnit X := by
    by_contra! hNoUnit
    have hDet (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : X ∈ Kraus.wordSpan A 1) : X.det = 0 := by
      have h := hNoUnit X hX
      rwa [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at h
    have hLe := Matrix.finrank_le_two_of_forall_det_eq_zero_fin_two
      (Kraus.wordSpan A 1) hDet
    omega
  calc
    choiRank F = Module.finrank ℂ (Kraus.wordSpan A 1) := by
      rw [hA, choiRank_mapLM_eq_finrank_wordSpan_one]
    _ ≤ Module.finrank ℂ (Kraus.wordSpan A p) :=
      Kraus.wordSpan_one_finrank_le_of_isUnit_mem_wordSpan_one A hp hX hUnit
    _ = choiRank (Kraus.transferMap (Kraus.blockTensor A p)) := by
      rw [choiRank_mapLM_eq_finrank_wordSpan_one, Kraus.wordSpan_blockTensor_one]
    _ = choiRank (F ^ p) := by rw [Kraus.transferMap_blockTensor, hA]

end Channel

namespace MPSTensor

/-- Every tensor of bond dimension two is refinable whenever its transfer
map is channel-divisible. The target may be singular or reducible; no
bounded-root hypothesis is assumed. This proves the bond-dimension-two
case of arXiv:1708.00029, Theorem 4.1, converse. -/
theorem isPRefinable_of_isPDivisibleChannel_fin_two
    {d p : ℕ} (B : MPSTensor d 2) (hp : 0 < p)
    (hDiv : IsPDivisibleChannel (Kraus.transferMap B) p) : IsPRefinable B p := by
  obtain ⟨F, hF, hpow⟩ := hDiv
  have hRank : Channel.choiRank F ≤ d := by
    calc
      Channel.choiRank F ≤ Channel.choiRank (F ^ p) :=
          TNLean.MPS.FundamentalTheorem.choiRank_le_pow_fin_two hF hp
      _ = Channel.choiRank (Kraus.transferMap B) := congrArg Channel.choiRank hpow.symm
      _ ≤ d := Channel.choiRank_le_of_hasKrausCard ⟨B, by intro X; simp⟩
  exact isPRefinable_of_channel_root_hasKrausRankLE B hp F hpow
    ⟨Channel.choiRank F, hRank, Channel.hasKrausCard_choiRank_of_cp hF.cp⟩

end MPSTensor

end
