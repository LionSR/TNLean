/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Reduction.LongWords
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessDifferentFlags

/-!
# Long words and the one-block theorem

Let `P` and `Q` be two multi-block compressions of the same tensor `B` onto the same family of
normal blocks `C s`, `s ∈ S`, of positive bond dimension, with flags `M_k` and `M'_{k'}`,
reading maps `W_s`, `W'_s` and injections `V_s`, `V'_s`. Suppose the block `C_s` occurs once in
the family up to gauge. Then the matching of the two flags pairs the position `k` of `s` in `P`
with the position `k'` of `s` in `Q`, and Theorem C gives a nonzero scalar `λ` with
`W'_s = λ W_s` on `U = M_k ∩ M'_{k'}` and `V'_s ≡ λ⁻¹ V_s` modulo `N = M_{k-1} + M'_{k'-1}`.

A word of length `|w| ≥ z` maps the bond space into the step of the last block slot and kills
the step below the first block slot (lecture note MultiBlockUniqueness, Lemma 5.6 (Long words in a
triangular form)). So when `s`
is the last block slot in both compressions, `B^w` maps everything into `U`, and
`W'_s B^w = λ W_s B^w`; when `s` is the first block slot in both, `B^w` kills `N`, and
`B^w V'_s = λ⁻¹ B^w V_s` (Corollary 5.10 (C3: extremal slots)). With one block every other slot is a
zero slot,
and both identities hold for `|w| ≥ z = D_B - D_s` (Corollary 5.8 (C2: the one-block theorem)).
When `s` is the last slot outright `U` is the whole bond space, and when it is the first slot
outright `N = 0`; then the bare maps agree up to the scalar (Corollary 5.7 (C1: bare uniqueness at
the ends of the flag)).

## Main results

* `MPSTensor.MultiBlockCompression.matching_ord_inl_of_unique`: a block occurring once up to
  gauge is matched with itself.
* `MPSTensor.MultiBlockCompression.evalWord_mulVec_mem_flag_of_forall_le`,
  `MPSTensor.MultiBlockCompression.evalWord_mulVec_eq_zero_of_mem_flag_of_forall_ge`:
  Lemma 5.6 (Long words in a triangular form) read in the flag, `B^w ℂ^{D_B} ⊆ M_{k_max}` and
  `B^w M_{k_min - 1} = 0`.
* `MPSTensor.MultiBlockCompression.exists_left_eq_smul_of_last`,
  `MPSTensor.MultiBlockCompression.exists_right_eq_inv_smul_of_first`: Corollary 5.7 (C1: bare
  uniqueness at the ends of the flag).
* `MPSTensor.MultiBlockCompression.exists_smul_single_block`: Corollary 5.8 (C2: the one-block
  theorem).
* `MPSTensor.MultiBlockCompression.exists_left_mul_evalWord_eq_smul_of_last`,
  `MPSTensor.MultiBlockCompression.exists_evalWord_mul_right_eq_inv_smul_of_first`:
  Corollary 5.10 (C3: extremal slots).

## References

Lecture note MultiBlockUniqueness, Section 5.1: Lemma 5.6 (Long words in a triangular form),
Corollary 5.7 (C1: bare uniqueness at the ends of the flag), Corollary 5.8 (C2: the one-block
theorem) and
Corollary 5.10 (C3: extremal slots).
-/

open scoped Matrix

namespace MPSTensor

namespace MultiBlockCompression

variable {d DB : ℕ} {ι : Type*} [DecidableEq ι] {D : ι → ℕ} {B : MPSTensor d DB}
  {S : Finset ι} {C : ∀ s, MPSTensor d (D s)}

section OneCompression

variable (P : MultiBlockCompression B S C)

/-- The block coordinates of `A v` are the matrix of `A` in the block coordinates applied to the
block coordinates of `v`. -/
theorem gauge_mulVec (A : Matrix (Fin DB) (Fin DB) ℂ) (v : Fin DB → ℂ) :
    P.gauge (A *ᵥ v) = conjMatrix P.gauge A *ᵥ P.gauge v := by
  rw [conjMatrix_apply, LinearMap.toMatrix'_mulVec, LinearEquiv.conj_apply_apply,
    Matrix.toLin'_apply, LinearEquiv.symm_apply_apply]

/-- **Long words land in the step of the last block slot** (lecture note MultiBlockUniqueness,
Lemma 5.6 (Long words in a triangular form),
`B^w ℂ^{D_B} ⊆ M_{k_max}`). If every block slot sits at a position `≤ k` and
`|w| ≥ z`, then `B^w v ∈ M_k` for every vector `v` of the bond space. -/
theorem evalWord_mulVec_mem_flag_of_forall_le {k : Fin (S.card + P.z)}
    (hk : ∀ s : {s // s ∈ S}, P.ord (Sum.inl s) ≤ k) (w : List (Fin d)) (hw : P.z ≤ w.length)
    (v : Fin DB → ℂ) :
    (WordModule.toVec B).symm (Kraus.evalWord B w *ᵥ v) ∈ P.flag k.succ := by
  refine P.mem_flag_iff.2 fun y hy => ?_
  rw [coord_apply, LinearEquiv.apply_symm_apply, gauge_mulVec]
  have hky : k < P.ord y.1 := Fin.succ_le_castSucc_iff.1 hy
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun y' _ => ?_
  rw [P.conjMatrix_evalWord_eq_zero_of_forall_lt_row w hw (fun s => (hk s).trans_lt hky) y',
    zero_mul]

/-- **Long words kill the step below the first block slot** (lecture note
MultiBlockUniqueness, Lemma 5.6 (Long words in a triangular form),
`B^w M_{k_min - 1} = 0`). If every block slot sits at a
position `≥ k` and `|w| ≥ z`, then `B^w x = 0` for every `x ∈ M_{k-1}`, the span of the slots
at positions `< k`. -/
theorem evalWord_mulVec_eq_zero_of_mem_flag_of_forall_ge {k : Fin (S.card + P.z)}
    (hk : ∀ s : {s // s ∈ S}, k ≤ P.ord (Sum.inl s)) (w : List (Fin d)) (hw : P.z ≤ w.length)
    {x : B.WordModule} (hx : x ∈ P.flag k.castSucc) :
    Kraus.evalWord B w *ᵥ WordModule.toVec B x = 0 := by
  apply P.gauge.injective
  rw [gauge_mulVec, map_zero]
  funext y
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  refine Finset.sum_eq_zero fun y' _ => ?_
  by_cases hy' : k ≤ P.ord y'.1
  · rw [← coord_apply, P.mem_flag_iff.1 hx y' (Fin.castSucc_le_castSucc_iff.2 hy'), mul_zero]
  · rw [P.conjMatrix_evalWord_eq_zero_of_forall_lt_col w hw
      (fun s => (not_le.1 hy').trans_le (hk s)) y, zero_mul]

/-- If the slot at position `k` is the last slot, the step `M_k` is the whole bond space. -/
theorem flag_succ_eq_top_of_forall_le {k : Fin (S.card + P.z)} (hk : ∀ b, P.ord b ≤ k) :
    P.flag k.succ = ⊤ :=
  eq_top_iff.2 fun _ _ => P.mem_flag_iff.2 fun y hy =>
    absurd hy (not_le.2 (Fin.castSucc_lt_succ_iff.2 (hk y.1)))

/-- If the slot at position `k` is the first slot, the step `M_{k-1}` below it is zero. -/
theorem flag_castSucc_eq_bot_of_forall_ge {k : Fin (S.card + P.z)} (hk : ∀ b, k ≤ P.ord b) :
    P.flag k.castSucc = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
  have h : P.coord x = 0 :=
    funext fun y => P.mem_flag_iff.1 hx y (Fin.castSucc_le_castSucc_iff.2 (hk y.1))
  exact P.coord.map_eq_zero_iff.1 h

/-- With a single block `C_s` the number of zero slots is `z = D_B - D_s` (lecture note
MultiBlockUniqueness, Corollary 5.8 (C2: the one-block theorem)). -/
theorem z_eq_of_single_block {s : {s // s ∈ S}} (hS : ∀ t ∈ S, t = s.1) :
    P.z = DB - D s.1 := by
  have hsum : ∑ t ∈ S, D t = D s.1 :=
    Finset.sum_eq_single_of_mem s.1 s.2 fun t ht hne => absurd (hS t ht) hne
  have h := P.dim_eq
  omega

end OneCompression

section SameFamily

variable (P Q : MultiBlockCompression B S C) (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
  (hD : ∀ s ∈ S, 0 < D s)

/-- **A block occurring once up to gauge is matched with itself** (lecture note
MultiBlockUniqueness, proofs of Corollary 5.7 (C1: bare uniqueness at the ends of the flag) and
Corollary 5.8 (C2: the one-block theorem)): the matched label of `s` carries a
block gauge related to `C_s` (Theorem 4.3 (A: the blocks are unique)), so it is `s`. -/
theorem labelMatching_eq_of_unique {s : {s // s ∈ S}}
    (hs : ∀ t ∈ S, IsGaugeRelated (C s.1) (C t) → t = s.1) :
    P.labelMatching Q hC hD hC hD s = s := by
  have h := P.isGaugeRelated_slotMatching Q hC hD hC hD (Sum.inl s)
  rw [slotMatching_inl] at h
  exact Subtype.ext (hs _ (P.labelMatching Q hC hD hC hD s).2 h)

/-- **The two `s`-steps are matched** (lecture note MultiBlockUniqueness, proofs of
Corollary 5.7 (C1: bare uniqueness at the ends of the flag) and Corollary 5.8 (C2: the one-block
theorem)): if `C_s` occurs once up to gauge, the matching sends the position of
`s` in `P` to the position of `s` in `Q`. -/
theorem matching_ord_inl_of_unique {s : {s // s ∈ S}}
    (hs : ∀ t ∈ S, IsGaugeRelated (C s.1) (C t) → t = s.1) :
    P.matching Q hC hD hC hD (P.ord (Sum.inl s)) = Q.ord (Sum.inl s) := by
  have h := P.slotMatching_inl Q hC hD hC hD s
  rw [slotMatching_apply, P.labelMatching_eq_of_unique Q hC hD hs] at h
  exact Q.ord.symm_apply_eq.1 h

include hC hD

/-- **Long words and an unrepeated block** (lecture note MultiBlockUniqueness, proofs of
Corollary 5.8 (C2: the one-block theorem) and Corollary 5.10 (C3: extremal
slots)). Let `C_s` occur once in the family up to gauge. There is one nonzero
scalar `λ` such that, for every word with `|w| ≥ z`, `W'_s B^w = λ W_s B^w` when `s` is the last
block slot in both compressions, and `B^w V'_s = λ⁻¹ B^w V_s` when it is the first block slot in
both. -/
theorem exists_smul_evalWord_of_unique {s : {s // s ∈ S}}
    (hs : ∀ t ∈ S, IsGaugeRelated (C s.1) (C t) → t = s.1) :
    ∃ c : ℂ, c ≠ 0 ∧
      ((∀ t : {t // t ∈ S}, P.ord (Sum.inl t) ≤ P.ord (Sum.inl s)) →
        (∀ t : {t // t ∈ S}, Q.ord (Sum.inl t) ≤ Q.ord (Sum.inl s)) →
        ∀ w : List (Fin d), P.z ≤ w.length →
          Q.left s * Kraus.evalWord B w = c • (P.left s * Kraus.evalWord B w)) ∧
      ((∀ t : {t // t ∈ S}, P.ord (Sum.inl s) ≤ P.ord (Sum.inl t)) →
        (∀ t : {t // t ∈ S}, Q.ord (Sum.inl s) ≤ Q.ord (Sum.inl t)) →
        ∀ w : List (Fin d), P.z ≤ w.length →
          Kraus.evalWord B w * Q.right s = c⁻¹ • (Kraus.evalWord B w * P.right s)) := by
  have hk' := (P.matching_ord_inl_of_unique Q hC hD hs).symm
  obtain ⟨c, hc, hW, hV⟩ := P.exists_smul_of_matching_inl Q hC hD _ s rfl hk'
  rw [← hk'] at hW hV
  have hz := P.z_eq Q hC hD hC hD
  refine ⟨c, hc, fun hP hQ w hw => ?_, fun hP hQ w hw => ?_⟩
  · -- `B^w` maps the bond space into `U = M_k ∩ M'_{k'}`.
    refine Matrix.ext_iff_mulVec.2 fun v => ?_
    have hx := hW _ ⟨P.evalWord_mulVec_mem_flag_of_forall_le hP w hw v,
      Q.evalWord_mulVec_mem_flag_of_forall_le hQ w (hz ▸ hw) v⟩
    rw [LinearEquiv.apply_symm_apply] at hx
    rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
    exact hx
  · -- `B^w` kills `N = M_{k-1} + M'_{k'-1}`.
    refine Matrix.ext_iff_mulVec.2 fun v => ?_
    obtain ⟨y, hy, y', hy', hyy⟩ := Submodule.mem_sup.1 (hV v)
    have h0 := congrArg (fun x => Kraus.evalWord B w *ᵥ WordModule.toVec B x) hyy
    simp only [map_add, Matrix.mulVec_add,
      P.evalWord_mulVec_eq_zero_of_mem_flag_of_forall_ge hP w hw hy,
      Q.evalWord_mulVec_eq_zero_of_mem_flag_of_forall_ge hQ w (hz ▸ hw) hy', add_zero,
      LinearEquiv.apply_symm_apply, Matrix.mulVec_sub] at h0
    rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul]
    exact sub_eq_zero.1 h0.symm

/-- **C3: an unrepeated last block slot** (lecture note MultiBlockUniqueness, Corollary 5.10 (C3:
extremal slots)).
If `C_s` occurs once up to gauge and `s` is the last block slot in both compressions, only zero
slots coming after it, then there is a nonzero scalar `λ` with `W'_s B^w = λ W_s B^w` for every
word with `|w| ≥ z`. -/
theorem exists_left_mul_evalWord_eq_smul_of_last {s : {s // s ∈ S}}
    (hs : ∀ t ∈ S, IsGaugeRelated (C s.1) (C t) → t = s.1)
    (hP : ∀ t : {t // t ∈ S}, P.ord (Sum.inl t) ≤ P.ord (Sum.inl s))
    (hQ : ∀ t : {t // t ∈ S}, Q.ord (Sum.inl t) ≤ Q.ord (Sum.inl s)) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ w : List (Fin d), P.z ≤ w.length →
      Q.left s * Kraus.evalWord B w = c • (P.left s * Kraus.evalWord B w) := by
  obtain ⟨c, hc, h, -⟩ := P.exists_smul_evalWord_of_unique Q hC hD hs
  exact ⟨c, hc, h hP hQ⟩

/-- **C3: an unrepeated first block slot** (lecture note MultiBlockUniqueness, Corollary 5.10 (C3:
extremal slots)).
If `C_s` occurs once up to gauge and `s` is the first block slot in both compressions, only zero
slots coming before it, then there is a nonzero scalar `λ` with `B^w V'_s = λ⁻¹ B^w V_s` for
every word with `|w| ≥ z`. -/
theorem exists_evalWord_mul_right_eq_inv_smul_of_first {s : {s // s ∈ S}}
    (hs : ∀ t ∈ S, IsGaugeRelated (C s.1) (C t) → t = s.1)
    (hP : ∀ t : {t // t ∈ S}, P.ord (Sum.inl s) ≤ P.ord (Sum.inl t))
    (hQ : ∀ t : {t // t ∈ S}, Q.ord (Sum.inl s) ≤ Q.ord (Sum.inl t)) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ w : List (Fin d), P.z ≤ w.length →
      Kraus.evalWord B w * Q.right s = c⁻¹ • (Kraus.evalWord B w * P.right s) := by
  obtain ⟨c, hc, -, h⟩ := P.exists_smul_evalWord_of_unique Q hC hD hs
  exact ⟨c, hc, h hP hQ⟩

/-- **C2: the one-block theorem** (lecture note MultiBlockUniqueness, Corollary 5.8 (C2: the
one-block theorem)). For two
compressions of `B` onto a single block `C_s`, with maps `(W, V)` and `(W', V')`, there is a
nonzero scalar `λ` with `W' B^w = λ W B^w` and `B^w V' = λ⁻¹ B^w V` for every word with
`|w| ≥ D_B - D_s`. -/
theorem exists_smul_single_block {s : {s // s ∈ S}} (hS : ∀ t ∈ S, t = s.1) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ w : List (Fin d), DB - D s.1 ≤ w.length →
      Q.left s * Kraus.evalWord B w = c • (P.left s * Kraus.evalWord B w) ∧
        Kraus.evalWord B w * Q.right s = c⁻¹ • (Kraus.evalWord B w * P.right s) := by
  have heq : ∀ t : {t // t ∈ S}, t = s := fun t => Subtype.ext (hS t.1 t.2)
  obtain ⟨c, hc, hl, hr⟩ := P.exists_smul_evalWord_of_unique Q hC hD fun t ht _ => hS t ht
  refine ⟨c, hc, fun w hw => ?_⟩
  rw [← P.z_eq_of_single_block hS] at hw
  exact ⟨hl (fun t => by rw [heq t]) (fun t => by rw [heq t]) w hw,
    hr (fun t => by rw [heq t]) (fun t => by rw [heq t]) w hw⟩

/-- **C1: bare uniqueness at the end of the flag** (lecture note MultiBlockUniqueness,
Corollary 5.7 (C1: bare uniqueness at the ends of the
flag)). If `C_s` occurs once up to gauge and `s` is the last slot in both compressions,
then `W'_s = λ W_s` as matrices for a nonzero scalar `λ`: here `U` is the whole bond space. -/
theorem exists_left_eq_smul_of_last {s : {s // s ∈ S}}
    (hs : ∀ t ∈ S, IsGaugeRelated (C s.1) (C t) → t = s.1)
    (hP : ∀ b, P.ord b ≤ P.ord (Sum.inl s)) (hQ : ∀ b, Q.ord b ≤ Q.ord (Sum.inl s)) :
    ∃ c : ℂ, c ≠ 0 ∧ Q.left s = c • P.left s := by
  have hk' := (P.matching_ord_inl_of_unique Q hC hD hs).symm
  obtain ⟨c, hc, hW, -⟩ := P.exists_smul_of_matching_inl Q hC hD _ s rfl hk'
  rw [← hk', P.flag_succ_eq_top_of_forall_le hP, Q.flag_succ_eq_top_of_forall_le hQ,
    top_inf_eq] at hW
  refine ⟨c, hc, Matrix.ext_iff_mulVec.2 fun v => ?_⟩
  have h := hW ((WordModule.toVec B).symm v) Submodule.mem_top
  rw [LinearEquiv.apply_symm_apply] at h
  rw [Matrix.smul_mulVec]
  exact h

/-- **C1: bare uniqueness at the start of the flag** (lecture note MultiBlockUniqueness,
Corollary 5.7 (C1: bare uniqueness at the ends of the
flag)). If `C_s` occurs once up to gauge and `s` is the first slot in both compressions,
then `V'_s = λ⁻¹ V_s` as matrices for a nonzero scalar `λ`: here `N = 0`. -/
theorem exists_right_eq_inv_smul_of_first {s : {s // s ∈ S}}
    (hs : ∀ t ∈ S, IsGaugeRelated (C s.1) (C t) → t = s.1)
    (hP : ∀ b, P.ord (Sum.inl s) ≤ P.ord b) (hQ : ∀ b, Q.ord (Sum.inl s) ≤ Q.ord b) :
    ∃ c : ℂ, c ≠ 0 ∧ Q.right s = c⁻¹ • P.right s := by
  have hk' := (P.matching_ord_inl_of_unique Q hC hD hs).symm
  obtain ⟨c, hc, -, hV⟩ := P.exists_smul_of_matching_inl Q hC hD _ s rfl hk'
  rw [← hk', P.flag_castSucc_eq_bot_of_forall_ge hP, Q.flag_castSucc_eq_bot_of_forall_ge hQ,
    bot_sup_eq] at hV
  refine ⟨c, hc, Matrix.ext_iff_mulVec.2 fun v => ?_⟩
  have h := (Submodule.mem_bot _).1 (hV v)
  rw [LinearEquiv.map_eq_zero_iff, sub_eq_zero] at h
  rw [Matrix.smul_mulVec]
  exact h

end SameFamily

end MultiBlockCompression

end MPSTensor
