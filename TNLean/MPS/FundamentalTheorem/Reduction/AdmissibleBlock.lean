/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Reduction.IrreducibleTensor

/-!
# Admissible blocks

A tensor `C` of bond dimension `c` is *admissible* when it is irreducible
(`Matrix.IsIrreducibleAction C`: no subspace other than `0` and `ℂ^c` is invariant under every
letter) and some letter is nonzero (`∃ i, C i ≠ 0`). Throughout the library the two conditions are
written as two separate hypotheses, `hirr` and `hlet`, as in the density theorem and the
independence of traces on which these statements rest.

This file collects the facts about admissible blocks used by the fundamental theorem for arbitrary
tensors. That a matrix commuting with every letter is a
scalar is Schur's lemma `exists_eq_smul_one_of_intertwines`; the normal case of the
irreducibility and nonzero-letter facts is `isIrreducibleAction_of_isNormal` together with
`exists_ne_zero_of_isNormal`.

## Main results

* `MPSTensor.eq_empty_of_isIrreducibleAction_of_forall_sum_trace_evalWord_eq_zero`.
* `MPSTensor.eq_zero_of_forall_apply_mul_eq_zero`,
  `MPSTensor.eq_zero_of_forall_mul_apply_eq_zero`.
* `MPSTensor.exists_ne_nil_and_trace_evalWord_ne_zero`,
  `MPSTensor.exists_length_eq_and_evalWord_ne_zero`.
* `MPSTensor.isIrreducibleAction_smul`, `MPSTensor.exists_smul_apply_ne_zero`.
* `MPSTensor.isIrreducibleAction_transpose`, `MPSTensor.exists_transpose_ne_zero`.
-/

open scoped Matrix

namespace MPSTensor

open WordAlgebra

variable {d : ℕ}

/-- A tensor with a nonzero letter has a letter acting as a nonzero map on its word module. -/
private lemma exists_ofWord_smul_ne_zero_of_exists_ne_zero {D : ℕ} {C : MPSTensor d D}
    (h : ∃ i, C i ≠ 0) :
    ∃ (i : Fin d) (q : C.WordModule), (ofWord [i] : WordAlgebra d) • q ≠ 0 := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨u, hu⟩ : ∃ u, C i *ᵥ u ≠ 0 := by
    by_contra h
    push Not at h
    exact hi (Matrix.toLin'.map_eq_zero_iff.1 (LinearMap.ext fun u => by
      rw [Matrix.toLin'_apply, h u, LinearMap.zero_apply]))
  refine ⟨i, C.wordRep.asModuleEquiv.symm u, fun h => hu ?_⟩
  have := congrArg C.wordRep.asModuleEquiv h
  rwa [asModuleEquiv_letter_smul, LinearEquiv.apply_symm_apply, map_zero] at this

/-- **Vanishing sums of characters**. If the word traces of a finite family
of admissible tensors sum to zero on every nonempty word, the family is empty. -/
theorem eq_empty_of_isIrreducibleAction_of_forall_sum_trace_evalWord_eq_zero {ι : Type*}
    {D : ι → ℕ} {S : Finset ι} {C : ∀ s, MPSTensor d (D s)}
    (hirr : ∀ s ∈ S, Matrix.IsIrreducibleAction (C s)) (hlet : ∀ s ∈ S, ∃ i, C s i ≠ 0)
    (h : ∀ w : List (Fin d), w ≠ [] → ∑ s ∈ S, Matrix.trace (Kraus.evalWord (C s) w) = 0) :
    S = ∅ := by
  by_contra hS
  obtain ⟨s₀, hs₀⟩ := Finset.nonempty_iff_ne_empty.2 hS
  obtain ⟨N, _, _, _, _, _, hN, hN0⟩ := exists_module_traceWord_eq_sum S C
  have hpos : 0 < D s₀ := dim_pos_of_exists_ne_zero (hlet s₀ hs₀)
  have : IsSimpleModule (WordAlgebra d) (C s₀).WordModule :=
    (isIrreducibleAction_and_pos_iff_isSimpleModule (C s₀)).1 ⟨hirr s₀ hs₀, hpos⟩
  obtain ⟨u, hu, hu'⟩ := exists_aug_eq_zero_smul_eq_self (C s₀).WordModule
    (exists_ofWord_smul_ne_zero_of_exists_ne_zero (hlet s₀ hs₀))
  have hzero : ∀ k : ℕ, 0 < k → LinearMap.trace ℂ N ((Algebra.lsmul ℂ ℂ N u) ^ k) = 0 := by
    intro k hk
    have hχ : ∀ w : List (Fin d), w ≠ [] → traceWord N w = (0 : WordAlgebra d →ₗ[ℂ] ℂ) (ofWord w) :=
      fun w hw => by rw [hN, h w hw, LinearMap.zero_apply]
    rw [← map_pow, ← traceChar_apply, traceChar_eq_of_traceWord_eq hχ (aug_pow hu hk),
      LinearMap.zero_apply]
  obtain ⟨n, hn⟩ := LinearMap.isNilpotent_of_forall_trace_pow_eq_zero (Algebra.lsmul ℂ ℂ N u) hzero
  have hpow : ∀ x : N, (u ^ n) • x = 0 := by
    intro x
    have := LinearMap.congr_fun hn x
    simpa [← map_pow] using this
  have hpowQ : ∀ (k : ℕ) (v : (C s₀).WordModule), (u ^ k) • v = v := by
    intro k v
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_smul, hu', ih]
  have : Nonempty (Fin (D s₀)) := ⟨⟨0, hpos⟩⟩
  have : Nontrivial (C s₀).WordModule := (C s₀).wordRep.asModuleEquiv.toEquiv.nontrivial
  obtain ⟨v, hv⟩ := exists_ne (0 : (C s₀).WordModule)
  exact hv ((hpowQ n v).symm.trans (hN0 (u ^ n) hpow s₀ hs₀ v))

variable {c : ℕ} {C : MPSTensor d c}

/-- **Facts about admissible blocks**. For an admissible tensor `C`, a
`c × m` matrix `E` with `C^i E = 0` for every letter is zero. -/
theorem eq_zero_of_forall_apply_mul_eq_zero (hirr : Matrix.IsIrreducibleAction C)
    (hlet : ∃ i, C i ≠ 0) {m : ℕ} {E : Matrix (Fin c) (Fin m) ℂ} (h : ∀ i, C i * E = 0) :
    E = 0 := by
  let N : Submodule ℂ (Fin c → ℂ) := ⨅ i, LinearMap.ker (Matrix.toLin' (C i))
  have hmem : ∀ v, v ∈ N ↔ ∀ i, C i *ᵥ v = 0 := fun v => by
    simp [N, Submodule.mem_iInf, Matrix.toLin'_apply]
  have hinv : Matrix.IsInvariantSubmodule C N := fun i v hv => by
    rw [(hmem v).1 hv i]
    exact N.zero_mem
  have hN : N = ⊥ := (hirr N hinv).resolve_right fun htop => by
    obtain ⟨i, hi⟩ := hlet
    refine hi (Matrix.toLin'.map_eq_zero_iff.1 (LinearMap.ext fun v => ?_))
    rw [Matrix.toLin'_apply, LinearMap.zero_apply]
    exact (hmem v).1 (htop ▸ Submodule.mem_top) i
  ext r k
  have hcol : (fun x => E x k) ∈ N := (hmem _).2 fun i => by
    funext x
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun (congrFun (h i) x) k
  rw [hN, Submodule.mem_bot] at hcol
  simpa using congrFun hcol r

/-- The transpose of an irreducible tensor is irreducible: the vectors orthogonal, for the bilinear
pairing `u ⬝ᵥ v`, to a subspace invariant under the transposed letters form a subspace invariant
under the letters, and a proper subspace has a nonzero orthogonal vector. -/
private lemma isIrreducibleAction_transpose_of_isIrreducibleAction
    (hirr : Matrix.IsIrreducibleAction C) : Matrix.IsIrreducibleAction (fun i => (C i)ᵀ) := by
  classical
  intro W hW
  let W' : Submodule ℂ (Fin c → ℂ) :=
    { carrier := {v | ∀ u ∈ W, u ⬝ᵥ v = 0}
      add_mem' := fun ha hb u hu => by rw [dotProduct_add, ha u hu, hb u hu, add_zero]
      zero_mem' := fun u _ => dotProduct_zero u
      smul_mem' := fun a v hv u hu => by rw [dotProduct_smul, hv u hu, smul_zero] }
  have hmem : ∀ v, v ∈ W' ↔ ∀ u ∈ W, u ⬝ᵥ v = 0 := fun v => Iff.rfl
  have hinv : Matrix.IsInvariantSubmodule C W' := fun i v hv => (hmem _).2 fun u hu => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    exact (hmem v).1 hv _ (hW i u hu)
  rcases hirr W' hinv with h | h
  · refine Or.inr (eq_top_iff.2 fun x _ => ?_)
    by_contra hx
    obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (p := W)
      (lt_top_iff_ne_top.2 fun hW' => hx (by rw [hW']; exact Submodule.mem_top)) inferInstance
    let a : Fin c → ℂ := fun j => f (Pi.single j 1)
    have hf' : ∀ y, f y = y ⬝ᵥ a := fun y => by
      conv_lhs => rw [pi_eq_sum_univ' y]
      simp [map_sum, dotProduct, a]
    have ha : a ∈ W' := (hmem a).2 fun u hu => by
      rw [← hf']
      exact (Submodule.mem_bot ℂ).1 (hmap ▸ Submodule.mem_map_of_mem hu)
    rw [h, Submodule.mem_bot] at ha
    exact hf (LinearMap.ext fun y => by rw [hf' y, ha, dotProduct_zero, LinearMap.zero_apply])
  · refine Or.inl ((Submodule.eq_bot_iff W).2 fun u hu => funext fun j => ?_)
    have := (hmem (Pi.single j 1)).1 (h ▸ Submodule.mem_top) u hu
    simpa using this

/-- **Facts about admissible blocks**. For an admissible tensor `C`, an
`m × c` matrix `E` with `E C^i = 0` for every letter is zero. -/
theorem eq_zero_of_forall_mul_apply_eq_zero (hirr : Matrix.IsIrreducibleAction C)
    (hlet : ∃ i, C i ≠ 0) {m : ℕ} {E : Matrix (Fin m) (Fin c) ℂ} (h : ∀ i, E * C i = 0) :
    E = 0 := by
  obtain ⟨i₀, hi₀⟩ := hlet
  have hT := eq_zero_of_forall_apply_mul_eq_zero (C := fun i => (C i)ᵀ)
    (isIrreducibleAction_transpose_of_isIrreducibleAction hirr)
    ⟨i₀, fun h0 => hi₀ (Matrix.transpose_eq_zero.1 h0)⟩ (E := Eᵀ) fun i => by
      rw [← Matrix.transpose_mul, h i, Matrix.transpose_zero]
  exact Matrix.transpose_eq_zero.1 hT

/-- **Admissible blocks, the character**. The character of
an admissible tensor does not vanish: some nonempty word has nonzero trace. -/
theorem exists_ne_nil_and_trace_evalWord_ne_zero (hirr : Matrix.IsIrreducibleAction C)
    (hlet : ∃ i, C i ≠ 0) :
    ∃ w : List (Fin d), w ≠ [] ∧ Matrix.trace (Kraus.evalWord C w) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h1 := eq_zero_of_forall_sum_mul_trace_evalWord_eq_zero (J := Unit) (D := fun _ => c)
    (fun _ => C) (fun _ => hirr) (fun j k hjk => absurd (Subsingleton.elim j k) hjk)
    (fun _ => hlet) (fun _ => 1) fun w hw => by simp [hcon w hw]
  exact one_ne_zero (congrFun h1 ())

/-- **Admissible blocks, the words**. No length kills every
word of an admissible tensor: for every `n` some word of length `n` is nonzero. -/
theorem exists_length_eq_and_evalWord_ne_zero (hirr : Matrix.IsIrreducibleAction C)
    (hlet : ∃ i, C i ≠ 0) (n : ℕ) :
    ∃ w : List (Fin d), w.length = n ∧ Kraus.evalWord C w ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hge : ∀ v : List (Fin d), n ≤ v.length → Kraus.evalWord C v = 0 := by
    intro v hv
    rw [← List.take_append_drop n v, Kraus.evalWord_append, hcon _ (List.length_take_of_le hv),
      Matrix.zero_mul]
  have hpow : ∀ (w : List (Fin d)) (k : ℕ), ∃ v : List (Fin d),
      v.length = k * w.length ∧ Kraus.evalWord C v = Kraus.evalWord C w ^ k := by
    intro w k
    induction k with
    | zero => exact ⟨[], by simp, by simp⟩
    | succ k ih =>
      obtain ⟨v, hv, hv'⟩ := ih
      exact ⟨w ++ v, by rw [List.length_append, hv]; ring,
        by rw [Kraus.evalWord_append, hv', pow_succ']⟩
  obtain ⟨w, hw, htr⟩ := exists_ne_nil_and_trace_evalWord_ne_zero hirr hlet
  obtain ⟨v, hv, hv'⟩ := hpow w n
  have hlen : n ≤ v.length := by
    rw [hv]
    exact Nat.le_mul_of_pos_right n (List.length_pos_iff.2 hw)
  have hnil : IsNilpotent (Kraus.evalWord C w) := ⟨n, by rw [← hv']; exact hge v hlen⟩
  exact htr (Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero

/-- **Admissible blocks, irreducibility**. A nonzero
multiple `μ C` of an irreducible tensor is irreducible. -/
theorem isIrreducibleAction_smul (hirr : Matrix.IsIrreducibleAction C) {μ : ℂ} (hμ : μ ≠ 0) :
    Matrix.IsIrreducibleAction (μ • C) := by
  intro W hW
  refine hirr W fun i v hv => ?_
  have := W.smul_mem μ⁻¹ (hW i v hv)
  rwa [Pi.smul_apply, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ hμ, one_smul] at this

/-- **Admissible blocks, the nonzero letter**. A nonzero
multiple `μ C` of a tensor with a nonzero letter has a nonzero letter. -/
theorem exists_smul_apply_ne_zero (hlet : ∃ i, C i ≠ 0) {μ : ℂ} (hμ : μ ≠ 0) :
    ∃ i, (μ • C) i ≠ 0 := by
  obtain ⟨i, hi⟩ := hlet
  exact ⟨i, by rw [Pi.smul_apply]; exact smul_ne_zero hμ hi⟩

/-- **Admissible blocks, irreducibility**. The transpose
`Cᵀ`, with letters `(C^i)ᵀ`, of an irreducible tensor is irreducible. -/
theorem isIrreducibleAction_transpose (hirr : Matrix.IsIrreducibleAction C) :
    Matrix.IsIrreducibleAction (fun i => (C i)ᵀ) :=
  isIrreducibleAction_transpose_of_isIrreducibleAction hirr

/-- **Admissible blocks, the nonzero letter**. The
transpose of a tensor with a nonzero letter has a nonzero letter. -/
theorem exists_transpose_ne_zero (hlet : ∃ i, C i ≠ 0) : ∃ i, (C i)ᵀ ≠ 0 := by
  obtain ⟨i, hi⟩ := hlet
  exact ⟨i, fun h => hi (Matrix.transpose_eq_zero.1 h)⟩

end MPSTensor
