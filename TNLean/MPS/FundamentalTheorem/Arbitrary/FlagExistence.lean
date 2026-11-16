/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixFamilyAction
import TNLean.MPS.FundamentalTheorem.Reduction.AdmissibleBlock
import TNLean.MPS.FundamentalTheorem.Arbitrary.Basic
import TNLean.MPS.FundamentalTheorem.Reduction.Flag
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlock

/-!
# Flags and reductions for admissible families

Let `(C_s)_{s ∈ S}` be a finite family of admissible tensors (irreducible, with a nonzero
letter). A finite-dimensional module over the free algebra on the letters whose word traces are
`∑_s tr C_s^w` on every nonempty word carries a labelled invariant flag for the family; in
particular a tensor `B` with these word traces has a multi-block reduction onto the family, with
`D_B - ∑_s D_s` zero blocks. The statement for normal blocks of positive bond
dimension is `exists_flagData` and `exists_multiBlockCompression_of_isNormal`; the reduction is
obtained from the flag by `FlagData.toMultiBlockCompression`.

## Main results

* `MPSTensor.exists_flagData_of_isIrreducibleAction`: the labelled invariant flag.
* `MPSTensor.exists_multiBlockCompression_z_eq_of_isIrreducibleAction`: the reduction.
-/

universe u

namespace MPSTensor

open WordAlgebra

variable {d : ℕ} {ι : Type*}

/-- **Existence of a flag for admissible blocks**. A
finite-dimensional module whose word traces are the sums of the word traces of a finite family of
admissible tensors on every nonempty word has a labelled invariant flag for that family. -/
theorem exists_flagData_of_isIrreducibleAction {S : Finset ι} {D : ι → ℕ}
    (C : ∀ s, MPSTensor d (D s)) (hirr : ∀ s ∈ S, Matrix.IsIrreducibleAction (C s))
    (hlet : ∀ s ∈ S, ∃ i, C s i ≠ 0)
    (M : Type u) [AddCommGroup M] [Module ℂ M] [Module (WordAlgebra d) M]
    [IsScalarTower ℂ (WordAlgebra d) M] [FiniteDimensional ℂ M]
    (htr : ∀ w : List (Fin d), w ≠ [] →
      traceWord M w = ∑ s ∈ S, Matrix.trace (Kraus.evalWord (C s) w)) :
    Nonempty (FlagData M S C) := by
  suffices key : ∀ n : ℕ, ∀ (M : Type u) [AddCommGroup M] [Module ℂ M] [Module (WordAlgebra d) M]
      [IsScalarTower ℂ (WordAlgebra d) M] [FiniteDimensional ℂ M] (S : Finset ι),
      Module.finrank ℂ M = n → (∀ s ∈ S, Matrix.IsIrreducibleAction (C s)) →
      (∀ s ∈ S, ∃ i, C s i ≠ 0) →
      (∀ w : List (Fin d), w ≠ [] →
        traceWord M w = ∑ s ∈ S, Matrix.trace (Kraus.evalWord (C s) w)) →
      Nonempty (FlagData M S C) from key _ M S rfl hirr hlet htr
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ _ _ _ _ S hn hirr hlet htr
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · -- trivial module: no slots, since the sum of the characters vanishes
    have : Subsingleton M := Module.finrank_zero_iff.1 hn
    have hS : S = ∅ := by
      refine eq_empty_of_isIrreducibleAction_of_forall_sum_trace_evalWord_eq_zero hirr hlet
        fun w hw => ?_
      rw [← htr w hw, traceWord_def, Subsingleton.elim (Algebra.lsmul ℂ ℂ M (ofWord w)) 0, map_zero]
    subst hS
    exact ⟨FlagData.ofSubsingleton⟩
  -- nontrivial module: choose a maximal invariant subspace
  have : Nontrivial M := Module.nontrivial_of_finrank_pos (hn ▸ hpos)
  have : IsNoetherian (WordAlgebra d) M := isNoetherian_of_tower ℂ inferInstance
  obtain ⟨K, hK, -⟩ :=
    (eq_top_or_exists_le_coatom (⊥ : Submodule (WordAlgebra d) M)).resolve_left bot_ne_top
  have : IsSimpleModule (WordAlgebra d) (M ⧸ K) := (isSimpleModule_iff_isCoatom).2 hK
  have : FiniteDimensional ℂ K :=
    Module.Finite.of_injective (K.subtype.restrictScalars ℂ) K.subtype_injective
  have hlt : Module.finrank ℂ K < n := by
    rw [← hn,
      ← ((Submodule.restrictScalarsEquiv ℂ (WordAlgebra d) M K).restrictScalars ℂ).finrank_eq]
    exact Submodule.finrank_lt fun h => hK.1 ((Submodule.restrictScalars_eq_top_iff ℂ _ _).1 h)
  have hadd := traceWord_eq_add_quotient K
  by_cases hQ : ∃ (i : Fin d) (q : M ⧸ K), (ofWord [i] : WordAlgebra d) • q ≠ 0
  · -- the quotient is one of the blocks, which are simple modules by admissibility
    obtain ⟨s₀, hs₀, ⟨e⟩⟩ := exists_linearEquiv_wordModule_of_isSimpleModule_quotient M K hQ S C
      (fun s hs => (isIrreducibleAction_and_pos_iff_isSimpleModule (C s)).1
        ⟨hirr s hs, dim_pos_of_exists_ne_zero (hlet s hs)⟩) htr
    have htrK : ∀ w : List (Fin d), w ≠ [] →
        traceWord K w = ∑ s ∈ S.erase s₀, Matrix.trace (Kraus.evalWord (C s) w) := by
      intro w hw
      rw [Finset.sum_erase_eq_sub hs₀, ← htr w hw, hadd w, traceWord_congr e,
        traceWord_wordModule, add_sub_cancel_right]
    obtain ⟨F⟩ := ih _ hlt K (S.erase s₀) rfl (fun s hs => hirr s (Finset.mem_of_mem_erase hs))
      (fun s hs => hlet s (Finset.mem_of_mem_erase hs)) htrK
    rw [← Finset.insert_erase hs₀]
    exact ⟨F.extendMatched K s₀ (Finset.notMem_erase s₀ S) e⟩
  · -- the quotient is a zero module
    simp only [not_exists, not_not] at hQ
    have hfin : Module.finrank ℂ (M ⧸ K) = 1 :=
      finrank_eq_one_of_isSimpleModule_of_forall_smul_eq_zero hQ
    have hQw : ∀ w : List (Fin d), w ≠ [] → traceWord (M ⧸ K) w = 0 := fun _ hw =>
      traceWord_eq_zero_of_forall_smul_eq_zero hQ hw
    have htrK : ∀ w : List (Fin d), w ≠ [] →
        traceWord K w = ∑ s ∈ S, Matrix.trace (Kraus.evalWord (C s) w) := by
      intro w hw
      rw [← htr w hw, hadd w, hQw w hw, add_zero]
    obtain ⟨F⟩ := ih _ hlt K S rfl hirr hlet htrK
    exact ⟨F.extendZero K hfin hQ⟩

/-- **Existence of a reduction for admissible blocks**. A
tensor `B` whose word traces are the sums of the word traces of a finite family of admissible
tensors on every nonempty word has a multi-block reduction onto that family, with
`D_B - ∑_s D_s` zero blocks. -/
theorem exists_multiBlockCompression_z_eq_of_isIrreducibleAction [DecidableEq ι] {DB : ℕ}
    (S : Finset ι) {D : ι → ℕ} (C : ∀ s, MPSTensor d (D s))
    (hirr : ∀ s ∈ S, Matrix.IsIrreducibleAction (C s)) (hlet : ∀ s ∈ S, ∃ i, C s i ≠ 0)
    (B : MPSTensor d DB)
    (htr : ∀ w : List (Fin d), w ≠ [] →
      Matrix.trace (Kraus.evalWord B w) = ∑ s ∈ S, Matrix.trace (Kraus.evalWord (C s) w)) :
    ∃ P : MultiBlockCompression B S C, P.z = DB - ∑ s ∈ S, D s := by
  obtain ⟨F⟩ := exists_flagData_of_isIrreducibleAction C hirr hlet B.WordModule
    fun w hw => by rw [traceWord_wordModule]; exact htr w hw
  refine ⟨F.toMultiBlockCompression, ?_⟩
  have := F.toMultiBlockCompression.dim_eq
  omega

end MPSTensor
