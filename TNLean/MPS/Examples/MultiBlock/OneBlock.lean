/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.MultiBlock.Running
import TNLean.MPS.Examples.MultiBlock.SharpnessOneBlock

/-!
# Two flags with one block

The tensor `B = [[1, 1], [0, 0]]` with one letter and the block `C = (1)` (*The asymmetric
fundamental theorem of matrix product states*, Example 6.15) has the two invariant lines `ℂ e₁` (on
which `B` acts by `1`) and `ℂ (e₁ - e₂)` (on which `B` acts by `0`). The reduction `g = 1` puts the
block first, with the flag `0 ⊂ ℂ e₁ ⊂ ℂ²`; the reduction `g̃ = [[0, -1], [1, 1]]` puts the zero
block first, with the flag `0 ⊂ ℂ (e₁ - e₂) ⊂ ℂ²` and `g̃ B g̃⁻¹ = diag(0, 1)`. The two reductions
are the objects `MultiBlockExamples.SharpnessOneBlock.firstCompression`,
`MultiBlockExamples.SharpnessOneBlock.lastCompression` of the case `z = 1` of the sharpness example.
The matching sends the block at position `1` to position `2`, `U = ℂ e₁`, `N = ℂ (e₁ - e₂)`; the
reading maps agree on `U` and after one letter, but not on `e₂`; the second reduction is split and
the first is not.

## Main results

* `MultiBlockExamples.OneBlock.isInvariantSubmodule_span_tensorB_iff`, `z_eq_one_and_gInt_conj`,
  `flagVec_one_firstCompression_and_lastCompression`,
  `eq_toFlagData_firstCompression_or_lastCompression`: the invariant lines, the two reductions and
  their flags.
* `MultiBlockExamples.OneBlock.left_right_matching_firstCompression_lastCompression`,
  `left_mulVec_e_one_and_left_mul_tensorB`,
  `remainder_lastCompression_eq_zero_and_firstCompression_ne_zero`: the matching, the reading maps
  and splitness.

## References

*The asymmetric fundamental theorem of matrix product states*, Example 6.15.
-/

open scoped Matrix

namespace MultiBlockExamples

namespace OneBlock

open MPSTensor MultiBlockExamples.SharpnessOneBlock

/-- The block `C = (1)` is normal (*The asymmetric fundamental theorem of matrix product states*,
Example 6.15): its letter spans `M₁(ℂ)`. -/
theorem isNormal_blockC : ∀ s ∈ oneSlot, Kraus.IsNormal (blockC s) := by
  intro s _
  refine Kraus.IsInjective.isNormal (Submodule.eq_top_of_forall_single_mem _ fun x y => ?_)
  obtain rfl : x = 0 := Subsingleton.elim x 0
  obtain rfl : y = 0 := Subsingleton.elim y 0
  have h1 : Matrix.single (0 : Fin 1) (0 : Fin 1) (1 : ℂ) = blockC s 0 := by
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim i 0
    obtain rfl : j = 0 := Subsingleton.elim j 0
    simp [blockC]
  rw [h1]
  exact Submodule.subset_span ⟨0, rfl⟩

theorem blockC_pos : ∀ s ∈ oneSlot, 0 < (fun _ : Unit => 1) s := fun _ _ => Nat.one_pos

theorem tensorB_apply (i : Fin 1) : tensorB i = !![1, 1; 0, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [tensorB, bInt, complexOfRing_apply]

/-- **The invariant lines** (*The asymmetric fundamental theorem of matrix product states*, Example
6.15): the lines invariant under `B = [[1, 1], [0, 0]]` are `ℂ e₁` and `ℂ (e₁ - e₂)`. -/
theorem isInvariantSubmodule_span_tensorB_iff (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    Matrix.IsInvariantSubmodule tensorB (Submodule.span ℂ {v}) ↔
      Submodule.span ℂ {v} = Submodule.span ℂ {e 0} ∨
        Submodule.span ℂ {v} = Submodule.span ℂ {e 0 - e 1} := by
  rw [isInvariantSubmodule_span_singleton_iff]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := h 0
    have a0 : v 0 + v 1 = c * v 0 := by
      simpa [tensorB_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hc 0
    have a1 : 0 = c * v 1 := by
      simpa [tensorB_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hc 1
    by_cases hv1 : v 1 = 0
    · have hv0 : v 0 ≠ 0 := fun h0 => hv (by ext i; fin_cases i <;> simp [h0, hv1])
      refine Or.inl (span_singleton_eq_of_eq_smul hv0 ?_)
      ext i; fin_cases i <;> simp [hv1]
    · have hc : c = 0 := (mul_eq_zero.1 a1.symm).resolve_right hv1
      rw [hc, zero_mul] at a0
      have hv0 : v 0 ≠ 0 := fun h0 => hv1 (by rw [h0, zero_add] at a0; exact a0)
      refine Or.inr (span_singleton_eq_of_eq_smul hv0 ?_)
      ext i; fin_cases i <;> simp
      linear_combination a0
  · rintro (h | h) i
    · obtain ⟨c, hc⟩ := exists_eq_smul_of_span_singleton_eq h
      have hv1 : v 1 = 0 := by simpa using congrFun hc 1
      refine ⟨1, ?_⟩
      ext j; fin_cases j <;> simp [tensorB_apply, Matrix.mulVec, dotProduct, hv1]
    · obtain ⟨c, hc⟩ := exists_eq_smul_of_span_singleton_eq h
      have hv0 : v 0 = c := by simpa using congrFun hc 0
      have hv1 : v 1 = -c := by simpa using congrFun hc 1
      refine ⟨0, ?_⟩
      ext j; fin_cases j <;> simp [tensorB_apply, Matrix.mulVec, dotProduct, hv0, hv1]

/-- **The two reductions** (*The asymmetric fundamental theorem of matrix product states*, Example
6.15): both reductions have `z = 1`, and `g̃ B g̃⁻¹ = diag(0, 1)`. -/
theorem z_eq_one_and_gInt_conj : firstCompression.z = 1 ∧ lastCompression.z = 1 ∧
    gInt * bInt * gInvInt = !![0, 0; 0, 1] :=
  ⟨rfl, rfl, by decide⟩

theorem mem_flagVec_first_one (k : Fin (oneSlot.card + firstCompression.z + 1)) (hk : k.val = 1)
    (v : Fin 2 → ℂ) : v ∈ flagVec firstCompression k ↔ v 1 = 0 := by
  rw [mem_flagVec_gaugeOfMatrix firstCompression (τ := firstTau)
    (hG := complexOfRing_mul_eq_one _ (by decide : (1 : Matrix (Fin 2) (Fin 2) ℤ) * 1 = 1))
    (hG' := complexOfRing_mul_eq_one _ (by decide : (1 : Matrix (Fin 2) (Fin 2) ℤ) * 1 = 1)) rfl]
  constructor
  · intro h
    have h1 := h (firstTau.symm 1) (by rw [Fin.le_def, hk]; decide)
    erw [Equiv.apply_symm_apply] at h1
    simpa [complexOfRing_one] using h1
  · intro h y hy
    obtain ⟨n, rfl⟩ := firstTau.symm.surjective y
    fin_cases n
    · exact absurd hy (by rw [Fin.le_def, hk]; decide)
    · erw [Equiv.apply_symm_apply]
      simpa [complexOfRing_one] using h

theorem mem_flagVec_last_one (k : Fin (oneSlot.card + lastCompression.z + 1)) (hk : k.val = 1)
    (v : Fin 2 → ℂ) : v ∈ flagVec lastCompression k ↔ v 0 + v 1 = 0 := by
  rw [mem_flagVec_gaugeOfMatrix lastCompression (τ := lastTau)
    (hG := complexOfRing_mul_eq_one _ (by decide : gInt * gInvInt = 1))
    (hG' := complexOfRing_mul_eq_one _ (by decide : gInvInt * gInt = 1)) rfl]
  constructor
  · intro h
    have h1 := h (lastTau.symm 1) (by rw [Fin.le_def, hk]; decide)
    erw [Equiv.apply_symm_apply] at h1
    simpa [gInt, complexOfRing_apply, Matrix.mulVec, dotProduct] using h1
  · intro h y hy
    obtain ⟨n, rfl⟩ := lastTau.symm.surjective y
    fin_cases n
    · exact absurd hy (by rw [Fin.le_def, hk]; decide)
    · erw [Equiv.apply_symm_apply]
      simpa [gInt, complexOfRing_apply, Matrix.mulVec, dotProduct] using h

theorem mem_span_e0 (v : Fin 2 → ℂ) : v ∈ Submodule.span ℂ {e 0} ↔ v 1 = 0 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩; simp
  · intro h
    exact ⟨v 0, by ext i; fin_cases i <;> simp [h]⟩

theorem mem_span_e0_sub_e1 (v : Fin 2 → ℂ) :
    v ∈ Submodule.span ℂ {e 0 - e 1} ↔ v 0 + v 1 = 0 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩; simp
  · intro h
    refine ⟨v 0, ?_⟩
    ext i; fin_cases i <;> simp
    linear_combination -h

theorem flagVec_first_one (k : Fin (oneSlot.card + firstCompression.z + 1)) (hk : k.val = 1) :
    flagVec firstCompression k = Submodule.span ℂ {e 0} := by
  ext v; rw [mem_flagVec_first_one k hk, mem_span_e0]

theorem flagVec_last_one (k : Fin (oneSlot.card + lastCompression.z + 1)) (hk : k.val = 1) :
    flagVec lastCompression k = Submodule.span ℂ {e 0 - e 1} := by
  ext v; rw [mem_flagVec_last_one k hk, mem_span_e0_sub_e1]

/-- **The two flags** (*The asymmetric fundamental theorem of matrix product states*, Example 6.15):
the flags are `0 ⊂ ℂ e₁ ⊂ ℂ²` and `0 ⊂ ℂ (e₁ - e₂) ⊂ ℂ²`. -/
theorem flagVec_one_firstCompression_and_lastCompression :
    (∀ k : Fin (oneSlot.card + firstCompression.z + 1), k.val = 1 →
      flagVec firstCompression k = Submodule.span ℂ {e 0}) ∧
    ∀ k : Fin (oneSlot.card + lastCompression.z + 1), k.val = 1 →
      flagVec lastCompression k = Submodule.span ℂ {e 0 - e 1} :=
  ⟨flagVec_first_one, flagVec_last_one⟩

theorem matching_first_last :
    firstCompression.matching lastCompression isNormal_blockC blockC_pos isNormal_blockC
        blockC_pos (firstCompression.ord (Sum.inl oneSlotMem)) =
      lastCompression.ord (Sum.inl oneSlotMem) := by
  refine matching_eq_of_flagVec_inf _ _ _ _ _ _ _ _ ⟨e 0, ?_, ?_, ?_⟩ ?_
  · rw [flagVec_first_one _ rfl]; exact Submodule.mem_span_singleton_self _
  · rw [flagVec_eq_top _ _ rfl]; exact Submodule.mem_top
  · rw [flagVec_eq_bot _ _ rfl]; simp
  · intro j hj v hv1 hv2
    have hj0 : j.val = 0 := by
      have := Fin.lt_def.1 hj
      change j.val < 1 at this
      omega
    rw [flagVec_first_one _ rfl] at hv1
    rw [mem_flagVec_last_one _ (by simp [hj0])] at hv2
    rw [mem_span_e0] at hv1
    have hv : v = 0 := by
      ext i; fin_cases i
      · simpa [hv1] using hv2
      · exact hv1
    rw [hv]
    exact Submodule.zero_mem _

/-- In a reduction of `B` onto `C = (1)` with the slot `b₀` at position `0`, the member `M₁` is
`ℂ e₁` when `b₀` is the block, and `ℂ (e₁ - e₂)` when `b₀` is a zero slot: `M₁` is an invariant
line containing `V_{b₀}`, on which `B` acts by the diagonal block of `b₀`. -/
theorem flagVec_one_cases (P : MultiBlockCompression tensorB oneSlot blockC)
    (b₀ b₁ : BlockIndex oneSlot P.z) (h₀ : (P.ord b₀).val = 0) (h₁ : (P.ord b₁).val = 1)
    (k : Fin (oneSlot.card + P.z + 1)) (hk : k.val = 1) :
    (b₀ = Sum.inl oneSlotMem ∧ flagVec P k = Submodule.span ℂ {e 0}) ∨
      ((∃ t, b₀ = Sum.inr t) ∧ flagVec P k = Submodule.span ℂ {e 0 - e 1}) := by
  have hks : (P.ord b₀).succ = k := Fin.ext (by rw [Fin.val_succ, h₀, hk])
  have hks' : (P.ord b₁).castSucc = k := Fin.ext (by rw [Fin.val_castSucc, h₁, hk])
  set u := P.rightCol b₀ *ᵥ (fun _ => (1 : ℂ)) with hu_def
  have hu : u ∈ flagVec P k := hks ▸ rightCol_mulVec_mem_flagVec P b₀ _
  have hWu : P.leftRow b₀ *ᵥ u = fun _ => 1 := by
    rw [hu_def, Matrix.mulVec_mulVec, P.leftRow_mul_rightCol_self, Matrix.one_mulVec]
  have hu0 : u ≠ 0 := fun h0 => by
    have := congrFun hWu ⟨0, by rw [slotSize_unit]; exact Nat.one_pos⟩
    rw [h0, Matrix.mulVec_zero] at this
    simp at this
  have hu' : P.rightCol b₁ *ᵥ (fun _ => (1 : ℂ)) ∉ flagVec P k := fun hin => by
    have h0 := leftRow_mulVec_eq_zero_of_mem_flagVec P (b := b₁) (hks'.symm ▸ hin)
    rw [Matrix.mulVec_mulVec, P.leftRow_mul_rightCol_self, Matrix.one_mulVec] at h0
    have := congrFun h0 ⟨0, by rw [slotSize_unit]; exact Nat.one_pos⟩
    simp at this
  have hinv : Matrix.IsInvariantSubmodule tensorB (flagVec P k) :=
    fun i v hv => mulVec_mem_flagVec P k i hv
  have hrank : Module.finrank ℂ (flagVec P k) = 1 := by
    have hle : Module.finrank ℂ (flagVec P k) ≤ 2 := by
      simpa using Submodule.finrank_le (flagVec P k)
    have h0 : Module.finrank ℂ (flagVec P k) ≠ 0 := fun h =>
      hu0 ((Submodule.mem_bot ℂ).1 (Submodule.finrank_eq_zero.1 h ▸ hu))
    have h2 : Module.finrank ℂ (flagVec P k) ≠ 2 := fun h =>
      hu' ((Submodule.eq_top_of_finrank_eq (S := flagVec P k) (by rw [h]; simp)) ▸
        Submodule.mem_top)
    omega
  obtain ⟨v, hv, hspan⟩ := exists_eq_span_singleton_of_finrank_eq_one _ hrank
  have hW := leftRow_mulVec_mulVec_of_mem_flagVec P (b := b₀) 0 (hks.symm ▸ hu)
  rcases (isInvariantSubmodule_span_tensorB_iff v hv).1 (hspan ▸ hinv) with h | h
  · have hfk := hspan.trans h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hfk ▸ hu)
    have hBu : tensorB 0 *ᵥ u = u := by
      rw [← ha]
      ext i; fin_cases i <;> simp [tensorB_apply, Matrix.mulVec, dotProduct]
    rw [hBu, hWu] at hW
    refine Or.inl ⟨?_, hfk⟩
    rcases b₀ with s | t
    · rw [eq_oneSlotMem s]
    · exfalso
      have := congrFun hW 0
      simp [blockOf, Matrix.mulVec, dotProduct] at this
  · have hfk := hspan.trans h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hfk ▸ hu)
    have hBu : tensorB 0 *ᵥ u = 0 := by
      rw [← ha]
      ext i; fin_cases i <;> simp [tensorB_apply, Matrix.mulVec, dotProduct]
    rw [hBu, Matrix.mulVec_zero, hWu] at hW
    refine Or.inr ⟨?_, hfk⟩
    rcases b₀ with s | t
    · exfalso
      obtain rfl : s = oneSlotMem := eq_oneSlotMem s
      have := congrFun hW 0
      simp [blockOf, blockC, Matrix.mulVec, dotProduct] at this
    · exact ⟨t, rfl⟩

theorem flag_eq_of_flagVec_eq {d DB : ℕ} {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {D : ι → ℕ} {D' : κ → ℕ} {S : Finset ι} {S' : Finset κ} {C : ∀ s, MPSTensor d (D s)}
    {C' : ∀ s, MPSTensor d (D' s)} {B : MPSTensor d DB} (P : MultiBlockCompression B S C)
    (Q : MultiBlockCompression B S' C') (k : Fin (S.card + P.z + 1))
    (k' : Fin (S'.card + Q.z + 1)) (h : flagVec P k = flagVec Q k') : P.flag k = Q.flag k' :=
  Submodule.restrictScalars_injective ℂ _ _
    (Submodule.map_injective_of_injective (WordModule.toVec B).injective h)

/-- **The labelled flags** (*The asymmetric fundamental theorem of matrix product states*, Example
6.15): the labelled invariant flags of `B` for `C = (1)` are exactly the flags of the two reductions
`g = 1` and `g̃`. -/
theorem eq_toFlagData_firstCompression_or_lastCompression
    (F : FlagData tensorB.WordModule oneSlot blockC) :
    F = firstCompression.toFlagData ∨ F = lastCompression.toFlagData := by
  have hz : F.z = 1 := by
    have := F.toMultiBlockCompression.dim_eq
    simp only [Finset.sum_const, Finset.card_singleton, smul_eq_mul, mul_one] at this
    change 2 = 1 + F.z at this
    omega
  have hr : F.r = 2 := by rw [F.r_eq, hz]; rfl
  obtain ⟨r, z, H, H0, Hl, Hm, label, hlb, hmat, hunf, hus⟩ := F
  dsimp only at hz hr
  subst hz hr
  set F : FlagData tensorB.WordModule oneSlot blockC :=
    ⟨2, 1, H, H0, Hl, Hm, label, hlb, hmat, hunf, hus⟩ with hF
  set P := F.toMultiBlockCompression with hP
  have hH : ∀ k, H k = P.flag (Fin.cast (congrArg (· + 1) F.r_eq) k) :=
    fun k => (F.toMultiBlockCompression_flag k).symm
  have hlab : ∀ k, label k = P.ord.symm (Fin.cast F.r_eq k) :=
    fun k => (F.toMultiBlockCompression_ord_symm k).symm
  have hb₀ : (P.ord (P.ord.symm (Fin.cast F.r_eq 0))).val = 0 := by
    rw [Equiv.apply_symm_apply]; rfl
  have hb₁ : (P.ord (P.ord.symm (Fin.cast F.r_eq 1))).val = 1 := by
    rw [Equiv.apply_symm_apply]; rfl
  have hne : label 0 ≠ label 1 := fun h => absurd (hlb.1 h) (by decide)
  have hH0 : H 0 = ⊥ := H0
  have hH2 : H 2 = ⊤ := Hl
  rcases flagVec_one_cases P _ _ hb₀ hb₁ (Fin.cast (congrArg (· + 1) F.r_eq) 1) rfl with
    ⟨hl0, hflag⟩ | ⟨⟨t, hl0⟩, hflag⟩
  · left
    have hl0' : label 0 = Sum.inl oneSlotMem := (hlab 0).trans hl0
    have hl1 : label 1 = Sum.inr 0 := by
      rcases h1 : label 1 with s | t
      · exact absurd (hl0'.trans ((eq_oneSlotMem s) ▸ h1).symm) hne
      · rw [Subsingleton.elim t 0]
    have hH1 : H 1 = firstCompression.flag 1 := by
      rw [hH 1]
      exact flag_eq_of_flagVec_eq _ _ _ _ (hflag.trans (flagVec_first_one _ rfl).symm)
    have hHeq : H = firstCompression.flag := by
      funext k
      fin_cases k
      · exact hH0.trans firstCompression.flag_zero.symm
      · exact hH1
      · exact hH2.trans firstCompression.flag_last.symm
    have hleq : label = firstOrd.symm := by
      funext k
      fin_cases k
      · exact hl0'
      · exact hl1
    subst hHeq hleq
    rfl
  · right
    have hl0' : label 0 = Sum.inr 0 := (hlab 0).trans (hl0.trans (congrArg Sum.inr
      (Fin.ext (by have := t.isLt; change t.val < 1 at this; change t.val = 0; omega))))
    have hl1 : label 1 = Sum.inl oneSlotMem := by
      rcases h1 : label 1 with s | t
      · rw [eq_oneSlotMem s]
      · exact absurd (hl0'.trans ((Subsingleton.elim t 0) ▸ h1).symm) hne
    have hH1 : H 1 = lastCompression.flag 1 := by
      rw [hH 1]
      exact flag_eq_of_flagVec_eq _ _ _ _ (hflag.trans (flagVec_last_one _ rfl).symm)
    have hHeq : H = lastCompression.flag := by
      funext k
      fin_cases k
      · exact hH0.trans lastCompression.flag_zero.symm
      · exact hH1
      · exact hH2.trans lastCompression.flag_last.symm
    have hleq : label = lastOrd.symm := by
      funext k
      fin_cases k
      · exact hl0'
      · exact hl1
    subst hHeq hleq
    rfl

/-- **The matching and the maps** (*The asymmetric fundamental theorem of matrix product states*,
Example 6.15): `W = (1, 0)`, `V = e₁`, `W̃ = (1, 1)`, `Ṽ = e₁`; the matching sends the block at
position `1` to position `2`; `U = ℂ e₁`, `N = ℂ (e₁ - e₂)`, `W̃ e₁ = W e₁ = 1`, `Ṽ - V = 0`. -/
theorem left_right_matching_firstCompression_lastCompression :
    firstCompression.left oneSlotMem = !![1, 0] ∧ firstCompression.right oneSlotMem = !![1; 0] ∧
    lastCompression.left oneSlotMem = !![1, 1] ∧ lastCompression.right oneSlotMem = !![1; 0] ∧
    (firstCompression.ord (Sum.inl oneSlotMem)).val = 0 ∧
    (lastCompression.ord (Sum.inl oneSlotMem)).val = 1 ∧
    firstCompression.matching lastCompression isNormal_blockC blockC_pos isNormal_blockC blockC_pos
        (firstCompression.ord (Sum.inl oneSlotMem)) = lastCompression.ord (Sum.inl oneSlotMem) ∧
    (let k := firstCompression.ord (Sum.inl oneSlotMem)
     let m := firstCompression.matching lastCompression isNormal_blockC blockC_pos
       isNormal_blockC blockC_pos k
     ((firstCompression.flag k.succ ⊓ lastCompression.flag m.succ).restrictScalars ℂ).map
         (WordModule.toVec tensorB).toLinearMap = Submodule.span ℂ {e 0} ∧
     ((firstCompression.flag k.castSucc ⊔ lastCompression.flag m.castSucc).restrictScalars ℂ).map
         (WordModule.toVec tensorB).toLinearMap = Submodule.span ℂ {e 0 - e 1}) ∧
    lastCompression.left oneSlotMem *ᵥ e 0 = ![1] ∧ firstCompression.left oneSlotMem *ᵥ e 0 = ![1] ∧
    lastCompression.right oneSlotMem - firstCompression.right oneSlotMem = 0 := by
  have hfirstV : firstCompression.right oneSlotMem = !![1; 0] := by
    rw [firstCompression, right_compressionOf]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_eq_one,
        Int.cast_eq_zero] <;> decide
  have hlastV : lastCompression.right oneSlotMem = !![1; 0] := by
    rw [right_eq, hfirstV]
  refine ⟨left_firstCompression, hfirstV, left_lastCompression, hlastV, rfl, rfl,
    matching_first_last, ?_, ?_, ?_, by rw [right_eq, sub_self]⟩
  · simp only
    rw [matching_first_last, map_toVec_inf, map_toVec_sup]
    refine ⟨?_, ?_⟩
    · change flagVec firstCompression _ ⊓ flagVec lastCompression _ = _
      rw [flagVec_first_one _ rfl, flagVec_eq_top _ _ rfl, inf_top_eq]
    · change flagVec firstCompression _ ⊔ flagVec lastCompression _ = _
      rw [flagVec_eq_bot _ _ rfl, flagVec_last_one _ rfl, bot_sup_eq]
  · rw [left_lastCompression]
    ext i; fin_cases i; simp [Matrix.mulVec, dotProduct]
  · rw [left_firstCompression]
    ext i; fin_cases i; simp [Matrix.mulVec, dotProduct]

/-- **The reading maps differ, but not after one letter** (*The asymmetric fundamental theorem of
matrix product states*, Example 6.15): `W̃ e₂ = 1 ≠ 0 = W e₂`, and `W̃ B = W B`. -/
theorem left_mulVec_e_one_and_left_mul_tensorB :
    lastCompression.left oneSlotMem *ᵥ e 1 = ![1] ∧ firstCompression.left oneSlotMem *ᵥ e 1 = ![0] ∧
    lastCompression.left oneSlotMem * tensorB 0 = firstCompression.left oneSlotMem * tensorB 0 := by
  refine ⟨?_, ?_, left_mul_eq 0⟩
  · rw [left_lastCompression]
    ext i; fin_cases i; simp [Matrix.mulVec, dotProduct]
  · rw [left_firstCompression]
    ext i; fin_cases i; simp [Matrix.mulVec, dotProduct]

/-- **Only the second reduction is split** (*The asymmetric fundamental theorem of matrix product
states*, Example 6.15): the second reduction is split and the first is not. -/
theorem remainder_lastCompression_eq_zero_and_firstCompression_ne_zero :
    lastCompression.remainder = 0 ∧ firstCompression.remainder ≠ 0 := by
  have hfirstV : firstCompression.right oneSlotMem = !![1; 0] := by
    rw [firstCompression, right_compressionOf]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_eq_one,
        Int.cast_eq_zero] <;> decide
  have hlastV : lastCompression.right oneSlotMem = !![1; 0] := by
    rw [right_eq, hfirstV]
  constructor
  · funext i
    rw [MultiBlockCompression.remainder_oneSlot _ oneSlotMem, hlastV, left_lastCompression,
      tensorB_apply]
    ext a b; fin_cases a <;> fin_cases b <;> simp [blockC]
  · intro h
    have h0 := congrFun h 0
    rw [MultiBlockCompression.remainder_oneSlot _ oneSlotMem, hfirstV, left_firstCompression,
      tensorB_apply] at h0
    have := congrFun (congrFun h0 0) 1
    simp [blockC] at this

end OneBlock

end MultiBlockExamples
