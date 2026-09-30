/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Data.Fin.Tuple.Basic
import TNLean.Algebra.Subquotient
import TNLean.MPS.FundamentalTheorem.Reduction.WordModule

/-!
# Labelled invariant flags

The conclusion of the composition-series step of the multi-block asymmetric compression theorem
(`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, §7.5, clauses (i)–(iii)
and (vii)): a chain of invariant subspaces of the word-algebra module whose steps are labelled
bijectively by the target slots `S` together with `z` further one-dimensional zero steps. Matched
steps have subquotients isomorphic to the corresponding blocks; unmatched steps are
one-dimensional with every generator acting as zero.

## Main definitions

* `MPSTensor.FlagData M S C`: the labelled flag.
* `MPSTensor.FlagData.extendZero`, `MPSTensor.FlagData.extendMatched`: append a final step
  `K ⊂ M` to a flag of a submodule `K`, labelled by a new zero index or by a new slot.
* `MPSTensor.FlagData.ofSubsingleton`: the empty flag of a trivial module with no slots.
-/

namespace MPSTensor

open WordAlgebra

variable {d : ℕ} {ι : Type*}

/-- The labelled invariant flag data of Theorem 7.7(i)–(iii). Steps `k : Fin r` of the chain
`H 0 ≤ ⋯ ≤ H r` are labelled bijectively by slots `s ∈ S` or by zero indices `t : Fin z`. -/
structure FlagData (M : Type*) [AddCommGroup M] [Module ℂ M] [Module (WordAlgebra d) M]
    [IsScalarTower ℂ (WordAlgebra d) M] (S : Finset ι) {D : ι → ℕ}
    (C : ∀ s, MPSTensor d (D s)) where
  /-- number of steps -/
  r : ℕ
  /-- number of unmatched (zero) steps -/
  z : ℕ
  /-- the chain of invariant subspaces -/
  H : Fin (r + 1) → Submodule (WordAlgebra d) M
  H_zero : H 0 = ⊥
  H_last : H (Fin.last r) = ⊤
  H_mono : Monotone H
  /-- the step labels -/
  label : Fin r → ({s // s ∈ S} ⊕ Fin z)
  label_bijective : Function.Bijective label
  /-- matched steps carry the blocks -/
  matched : ∀ (k : Fin r) (s : {s // s ∈ S}), label k = Sum.inl s →
    Nonempty (Submodule.subquot (H k.castSucc) (H k.succ) ≃ₗ[WordAlgebra d] (C s).WordModule)
  /-- unmatched steps are one-dimensional -/
  unmatched_finrank : ∀ (k : Fin r) (t : Fin z), label k = Sum.inr t →
    Module.finrank ℂ (Submodule.subquot (H k.castSucc) (H k.succ)) = 1
  /-- every generator acts as zero on an unmatched step -/
  unmatched_smul : ∀ (k : Fin r) (t : Fin z), label k = Sum.inr t → ∀ (i : Fin d)
    (x : Submodule.subquot (H k.castSucc) (H k.succ)), (ofWord [i] : WordAlgebra d) • x = 0

namespace FlagData

variable {M : Type*} [AddCommGroup M] [Module ℂ M] [Module (WordAlgebra d) M]
  [IsScalarTower ℂ (WordAlgebra d) M] {S : Finset ι} {D : ι → ℕ} {C : ∀ s, MPSTensor d (D s)}

/-- The subquotient at step `k`. -/
abbrev step (F : FlagData M S C) (k : Fin F.r) : Type _ :=
  Submodule.subquot (F.H k.castSucc) (F.H k.succ)

/-- The empty flag of a trivial module with no slots. -/
noncomputable def ofSubsingleton [Subsingleton M] : FlagData M (∅ : Finset ι) C where
  r := 0
  z := 0
  H := fun _ => ⊥
  H_zero := rfl
  H_last := Subsingleton.elim _ _
  H_mono := monotone_const
  label := Fin.elim0
  label_bijective := ⟨fun k => k.elim0, fun x => x.elim (fun s => (Finset.notMem_empty _ s.2).elim)
    Fin.elim0⟩
  matched := fun k => k.elim0
  unmatched_finrank := fun k => k.elim0
  unmatched_smul := fun k => k.elim0

section Extend

variable (K : Submodule (WordAlgebra d) M)

/-- The chain obtained by pushing a flag of `K` into `M` and appending `M` itself. -/
noncomputable def extendChain {S' : Finset ι} (F : FlagData K S' C) :
    Fin (F.r + 1 + 1) → Submodule (WordAlgebra d) M :=
  Fin.snoc (fun k => (F.H k).map K.subtype) ⊤

lemma extendChain_castSucc {S' : Finset ι} (F : FlagData K S' C) (k : Fin (F.r + 1)) :
    extendChain K F k.castSucc = (F.H k).map K.subtype := by
  simp [extendChain, Fin.snoc_castSucc]

lemma extendChain_last {S' : Finset ι} (F : FlagData K S' C) :
    extendChain K F (Fin.last _) = ⊤ := by
  simp [extendChain, Fin.snoc_last]

lemma extendChain_zero {S' : Finset ι} (F : FlagData K S' C) : extendChain K F 0 = ⊥ := by
  rw [show (0 : Fin (F.r + 1 + 1)) = (0 : Fin (F.r + 1)).castSucc from rfl, extendChain_castSucc,
    F.H_zero, Submodule.map_bot]

lemma extendChain_mono {S' : Finset ι} (F : FlagData K S' C) : Monotone (extendChain K F) := by
  intro i j hij
  rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rw [extendChain_castSucc, extendChain_castSucc]
      exact Submodule.map_mono (F.H_mono (Fin.castSucc_le_castSucc_iff.1 hij))
    · exact absurd hij (not_le.2 (Fin.castSucc_lt_last j'))
  · rw [extendChain_last]
    exact le_top

/-- The subquotient of the extended chain at an old step is the old subquotient. -/
noncomputable def extendStepEquiv {S' : Finset ι} (F : FlagData K S' C) (k : Fin F.r) :
    Submodule.subquot (extendChain K F k.castSucc.castSucc) (extendChain K F k.castSucc.succ)
      ≃ₗ[WordAlgebra d] F.step k :=
  (Submodule.subquotCongr (extendChain_castSucc K F k.castSucc)
    (by rw [Fin.succ_castSucc, extendChain_castSucc])).trans (Submodule.subquotMapEquiv K _ _).symm

/-- The subquotient of the extended chain at the new last step is `M ⧸ K`. -/
noncomputable def extendLastEquiv {S' : Finset ι} (F : FlagData K S' C) :
    Submodule.subquot (extendChain K F (Fin.last F.r).castSucc)
      (extendChain K F (Fin.last F.r).succ) ≃ₗ[WordAlgebra d] (M ⧸ K) :=
  (Submodule.subquotCongr
    (by rw [extendChain_castSucc, F.H_last, Submodule.map_subtype_top])
    (by rw [Fin.succ_last, extendChain_last])).trans (Submodule.subquotTopEquiv K)

/-- Append a one-dimensional zero step `K ⊂ M` to a flag of `K`. -/
noncomputable def extendZero (F : FlagData K S C)
    (hfin : Module.finrank ℂ (M ⧸ K) = 1)
    (hsmul : ∀ (i : Fin d) (x : M ⧸ K), (ofWord [i] : WordAlgebra d) • x = 0) :
    FlagData M S C where
  r := F.r + 1
  z := F.z + 1
  H := extendChain K F
  H_zero := extendChain_zero K F
  H_last := extendChain_last K F
  H_mono := extendChain_mono K F
  label := Fin.snoc (fun k => Sum.map id Fin.castSucc (F.label k)) (Sum.inr (Fin.last F.z))
  label_bijective := by
    constructor
    · intro k k' h
      rcases Fin.eq_castSucc_or_eq_last k with ⟨k, rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last k' with ⟨k', rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc] at h
        rw [F.label_bijective.1
          (Sum.map_injective.2 ⟨fun _ _ h => h, Fin.castSucc_injective _⟩ h)]
      · simp only [Fin.snoc_castSucc, Fin.snoc_last] at h
        rcases hk : F.label k with s | t <;> rw [hk] at h <;> simp at h
      · simp only [Fin.snoc_castSucc, Fin.snoc_last] at h
        rcases hk : F.label k' with s | t <;> rw [hk] at h <;> simp at h
        exact absurd h.symm (Fin.castSucc_lt_last t).ne
      · rfl
    · rintro (s | t)
      · obtain ⟨k, hk⟩ := F.label_bijective.2 (Sum.inl s)
        exact ⟨k.castSucc, by simp [Fin.snoc_castSucc, hk]⟩
      · rcases Fin.eq_castSucc_or_eq_last t with ⟨t, rfl⟩ | rfl
        · obtain ⟨k, hk⟩ := F.label_bijective.2 (Sum.inr t)
          exact ⟨k.castSucc, by simp [Fin.snoc_castSucc, hk]⟩
        · exact ⟨Fin.last _, by simp [Fin.snoc_last]⟩
  matched := by
    intro k s hk
    rcases Fin.eq_castSucc_or_eq_last k with ⟨k, rfl⟩ | rfl
    · simp only [Fin.snoc_castSucc] at hk
      rcases hk' : F.label k with s' | t <;> rw [hk'] at hk <;>
        simp only [Sum.map_inl, Sum.map_inr, id_eq, Sum.inl.injEq,
          reduceCtorEq] at hk
      subst hk
      obtain ⟨e⟩ := F.matched k s' hk'
      exact ⟨(extendStepEquiv K F k).trans e⟩
    · simp only [Fin.snoc_last, reduceCtorEq] at hk
  unmatched_finrank := by
    intro k t hk
    rcases Fin.eq_castSucc_or_eq_last k with ⟨k, rfl⟩ | rfl
    · simp only [Fin.snoc_castSucc] at hk
      rcases hk' : F.label k with s' | t' <;> rw [hk'] at hk <;>
        simp only [Sum.map_inl, Sum.map_inr, id_eq, Sum.inr.injEq,
          reduceCtorEq] at hk
      subst hk
      rw [(extendStepEquiv K F k).restrictScalars ℂ |>.finrank_eq]
      exact F.unmatched_finrank k t' hk'
    · rw [(extendLastEquiv K F).restrictScalars ℂ |>.finrank_eq]
      exact hfin
  unmatched_smul := by
    intro k t hk i x
    rcases Fin.eq_castSucc_or_eq_last k with ⟨k, rfl⟩ | rfl
    · simp only [Fin.snoc_castSucc] at hk
      rcases hk' : F.label k with s' | t' <;> rw [hk'] at hk <;>
        simp only [Sum.map_inl, Sum.map_inr, id_eq, Sum.inr.injEq,
          reduceCtorEq] at hk
      subst hk
      have := F.unmatched_smul k t' hk' i (extendStepEquiv K F k x)
      rw [← map_smul] at this
      exact (extendStepEquiv K F k).map_eq_zero_iff.1 this
    · have := hsmul i (extendLastEquiv K F x)
      rw [← map_smul] at this
      exact (extendLastEquiv K F).map_eq_zero_iff.1 this

/-- Append a matched step `K ⊂ M` labelled by a new slot `s₀ ∉ S'` to a flag of `K`. -/
noncomputable def extendMatched [DecidableEq ι] {S' : Finset ι} (F : FlagData K S' C) (s₀ : ι)
    (hs₀ : s₀ ∉ S')
    (e : (M ⧸ K) ≃ₗ[WordAlgebra d] (C s₀).WordModule) :
    FlagData M (insert s₀ S') C where
  r := F.r + 1
  z := F.z
  H := extendChain K F
  H_zero := extendChain_zero K F
  H_last := extendChain_last K F
  H_mono := extendChain_mono K F
  label := Fin.snoc (fun k => Sum.map (fun s => ⟨s.1, Finset.mem_insert_of_mem s.2⟩) id
    (F.label k)) (Sum.inl ⟨s₀, Finset.mem_insert_self s₀ S'⟩)
  label_bijective := by
    have hinj : Function.Injective
        (fun s : {s // s ∈ S'} =>
      (⟨s.1, Finset.mem_insert_of_mem s.2⟩ : {s // s ∈ insert s₀ S'})) :=
      fun s s' h => Subtype.ext (Subtype.mk.inj h)
    constructor
    · intro k k' h
      rcases Fin.eq_castSucc_or_eq_last k with ⟨k, rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last k' with ⟨k', rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc] at h
        rw [F.label_bijective.1 (Sum.map_injective.2 ⟨hinj, fun _ _ h => h⟩ h)]
      · simp only [Fin.snoc_castSucc, Fin.snoc_last] at h
        rcases hk : F.label k with s | t <;> rw [hk] at h <;>
          simp only [Sum.map_inl, Sum.map_inr, id_eq, Sum.inl.injEq, reduceCtorEq,
            Subtype.mk.injEq] at h
        exact absurd (h ▸ s.2) hs₀
      · simp only [Fin.snoc_castSucc, Fin.snoc_last] at h
        rcases hk : F.label k' with s | t <;> rw [hk] at h <;>
          simp only [Sum.map_inl, Sum.map_inr, id_eq, Sum.inl.injEq, reduceCtorEq,
            Subtype.mk.injEq] at h
        exact absurd (h ▸ s.2) hs₀
      · rfl
    · rintro (⟨s, hs⟩ | t)
      · rcases Finset.mem_insert.1 hs with rfl | hs'
        · exact ⟨Fin.last _, by simp [Fin.snoc_last]⟩
        · obtain ⟨k, hk⟩ := F.label_bijective.2 (Sum.inl ⟨s, hs'⟩)
          exact ⟨k.castSucc, by simp [Fin.snoc_castSucc, hk]⟩
      · obtain ⟨k, hk⟩ := F.label_bijective.2 (Sum.inr t)
        exact ⟨k.castSucc, by simp [Fin.snoc_castSucc, hk]⟩
  matched := by
    intro k s hk
    rcases Fin.eq_castSucc_or_eq_last k with ⟨k, rfl⟩ | rfl
    · simp only [Fin.snoc_castSucc] at hk
      rcases hk' : F.label k with s' | t <;> rw [hk'] at hk <;>
        simp only [Sum.map_inl, Sum.map_inr, id_eq, Sum.inl.injEq,
          reduceCtorEq] at hk
      subst hk
      obtain ⟨e'⟩ := F.matched k s' hk'
      exact ⟨(extendStepEquiv K F k).trans e'⟩
    · simp only [Fin.snoc_last, Sum.inl.injEq] at hk
      subst hk
      exact ⟨(extendLastEquiv K F).trans e⟩
  unmatched_finrank := by
    intro k t hk
    rcases Fin.eq_castSucc_or_eq_last k with ⟨k, rfl⟩ | rfl
    · simp only [Fin.snoc_castSucc] at hk
      rcases hk' : F.label k with s' | t' <;> rw [hk'] at hk <;>
        simp only [Sum.map_inl, Sum.map_inr, id_eq, Sum.inr.injEq,
          reduceCtorEq] at hk
      subst hk
      rw [(extendStepEquiv K F k).restrictScalars ℂ |>.finrank_eq]
      exact F.unmatched_finrank k t' hk'
    · simp only [Fin.snoc_last, reduceCtorEq] at hk
  unmatched_smul := by
    intro k t hk i x
    rcases Fin.eq_castSucc_or_eq_last k with ⟨k, rfl⟩ | rfl
    · simp only [Fin.snoc_castSucc] at hk
      rcases hk' : F.label k with s' | t' <;> rw [hk'] at hk <;>
        simp only [Sum.map_inl, Sum.map_inr, id_eq, Sum.inr.injEq,
          reduceCtorEq] at hk
      subst hk
      have := F.unmatched_smul k t' hk' i (extendStepEquiv K F k x)
      rw [← map_smul] at this
      exact (extendStepEquiv K F k).map_eq_zero_iff.1 this
    · simp only [Fin.snoc_last, reduceCtorEq] at hk

end Extend

end FlagData

end MPSTensor
