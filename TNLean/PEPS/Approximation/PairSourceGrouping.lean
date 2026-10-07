/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourcePreparation
import TNLean.PEPS.Approximation.PairSourceExpansion
import Mathlib.Data.Sym.Sym2

/-!
# Combining sources on the same unordered pair of parties

A finite family of normalized pair sources can be replaced by one normalized source
for each participating unordered pair. Local isometries and exchanges recover all
original registers, in their original order. No bound on the number of parties or
on the ranks of the source vectors is required.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, Lemma 5.1, `04-compression.tex`, lines 68–70 and 125–127;
  fresh-register passage in Theorem 5.2, lines 233–251.
  Revision `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
lem:effects.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8768-pairsourcegrouping-pairsource.partypair
Downstream declaration: TNLean.PEPS.PairEffect.PairSource.partyPair

Provenance-ID: 8768-pairsourcegrouping-pairsource.reverse
Downstream declaration: TNLean.PEPS.PairEffect.PairSource.reverse

Provenance-ID: 8768-pairsourcegrouping-pairsource.partypair_reverse
Downstream declaration: TNLean.PEPS.PairEffect.PairSource.partyPair_reverse

Provenance-ID: 8768-pairsourcegrouping-pairsource.norm_reverse_vector
Downstream declaration: TNLean.PEPS.PairEffect.PairSource.norm_reverse_vector

Provenance-ID: 8768-pairsourcegrouping-pairsource.combine
Downstream declaration: TNLean.PEPS.PairEffect.PairSource.combine

Provenance-ID: 8768-pairsourcegrouping-pairsource.partypair_combine
Downstream declaration: TNLean.PEPS.PairEffect.PairSource.partyPair_combine

Provenance-ID: 8768-pairsourcegrouping-pairsource.norm_combine_vector
Downstream declaration: TNLean.PEPS.PairEffect.PairSource.norm_combine_vector

Provenance-ID: 8768-pairsourcegrouping-sourceinventory.expands
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.Expands

Provenance-ID: 8768-pairsourcegrouping-sourceinventory.isnormalized_cons
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.isNormalized_cons

Provenance-ID: 8768-pairsourcegrouping-sourceinventory.expands.refl
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.Expands.refl

Provenance-ID: 8768-pairsourcegrouping-sourceinventory.expands.trans
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.Expands.trans

Provenance-ID: 8768-pairsourcegrouping-sourceinventory.expands.cons
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.Expands.cons

Provenance-ID: 8768-pairsourcegrouping-sourceinventory.expands.reverse
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.Expands.reverse

Provenance-ID: 8768-pairsourcegrouping-sourceinventory.expands.combine
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.Expands.combine

Provenance-ID: 8768-pairsourcegrouping-sourceinventory.expands.swap
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.Expands.swap

Provenance-ID: 8768-pairsourcegrouping-sourceinventory.exists_combined
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.exists_combined

Provenance-ID: 8768-pairsourcegrouping-sourceinventory.exists_grouped
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.exists_grouped
-/

noncomputable section

open scoped TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect

variable {P : Type}

namespace PairSource

/-- The unordered pair of parties joined by a source. -/
def partyPair (s : PairSource P) : Sym2 P := s(s.left, s.right)

/-- The same source with its endpoint order reversed. -/
def reverse (s : PairSource P) : PairSource P :=
  ⟨s.right, s.left, s.distinct.symm, s.rightSpace, s.leftSpace,
    TensorProduct.commIsometry ℂ s.leftSpace s.rightSpace s.vector⟩

@[simp] theorem partyPair_reverse (s : PairSource P) :
    s.reverse.partyPair = s.partyPair := Sym2.eq_swap

@[simp] theorem norm_reverse_vector (s : PairSource P) :
    ‖s.reverse.vector‖ = ‖s.vector‖ :=
  (TensorProduct.commIsometry ℂ s.leftSpace s.rightSpace).norm_map _

/-- Combine two sources with the same ordered endpoints by tensoring their local spaces.
Source: polynomial-PEPS Lemma 5.1, `04-compression.tex`, lines 125–127. -/
def combine (s t : PairSource P) (_hLeft : s.left = t.left) (_hRight : s.right = t.right) :
    PairSource P :=
  ⟨s.left, s.right, s.distinct, HSpace.of (s.leftSpace ⊗[ℂ] t.leftSpace),
    HSpace.of (s.rightSpace ⊗[ℂ] t.rightSpace),
    pairRegroup s.leftSpace s.rightSpace t.leftSpace t.rightSpace (s.vector ⊗ₜ t.vector)⟩

@[simp] theorem partyPair_combine (s t : PairSource P) (hLeft : s.left = t.left)
    (hRight : s.right = t.right) : (s.combine t hLeft hRight).partyPair = s.partyPair := rfl

@[simp] theorem norm_combine_vector (s t : PairSource P) (hLeft : s.left = t.left)
    (hRight : s.right = t.right) :
    ‖(s.combine t hLeft hRight).vector‖ = ‖s.vector‖ * ‖t.vector‖ := by
  exact (pairRegroup s.leftSpace s.rightSpace t.leftSpace t.rightSpace).norm_map
    (s.vector ⊗ₜ t.vector) |>.trans (TensorProduct.norm_tmul _ _)

end PairSource

namespace SourceInventory

/-- A preparation can be expanded into another by allowed operations containing no
pair sources, uniformly over all spectator registers. Source: polynomial-PEPS
Lemma 5.1, `04-compression.tex`, lines 125–127. -/
def Expands (G S : SourceInventory P) : Prop :=
  ∀ ℓ, ∃ w : Word (G.layout ++ ℓ) (S.layout ++ ℓ),
    w.IsAllowed ∧ w.sources = [] ∧ w.eval ∘L (G.prepare ℓ).eval = (S.prepare ℓ).eval

@[simp] theorem isNormalized_cons (s : PairSource P) (S : SourceInventory P) :
    IsNormalized (s :: S) ↔ ‖s.vector‖ = 1 ∧ S.IsNormalized := by
  simp only [IsNormalized, List.mem_cons, forall_eq_or_imp]

namespace Expands

@[refl] theorem refl (S : SourceInventory P) : S.Expands S := by
  intro ℓ
  exact ⟨.id _, trivial, rfl, rfl⟩

@[trans] theorem trans {G S T : SourceInventory P} (hGS : G.Expands S)
    (hST : S.Expands T) : G.Expands T := by
  intro ℓ
  obtain ⟨w, hw, hs, he⟩ := hGS ℓ
  obtain ⟨w', hw', hs', he'⟩ := hST ℓ
  refine ⟨.comp w w', ⟨hw, hw'⟩, ?_, ?_⟩
  · simp only [Word.sources, hs, hs', List.nil_append]
  · rw [Word.eval_comp, comp_assoc, he, he']

/-- A common source can be retained while the remaining inventory is expanded. -/
theorem cons (s : PairSource P) {G S : SourceInventory P} (h : G.Expands S) :
    Expands (s :: G) (s :: S) := by
  intro ℓ
  obtain ⟨w, hw, hs, he⟩ := h ℓ
  refine ⟨Word.frameList s.layout w, Word.isAllowed_frameList _ hw _, ?_, ?_⟩
  · exact (Word.sources_frameList w s.layout).trans hs
  · ext1 x
    change (Word.frameList s.layout w).eval
      ((prepare [s] (G.layout ++ ℓ)).eval ((G.prepare ℓ).eval x)) =
      (prepare [s] (S.layout ++ ℓ)).eval ((S.prepare ℓ).eval x)
    exact (eval_frameList_prepare [s] w _).trans
      (congrArg (prepare [s] (S.layout ++ ℓ)).eval (DFunLike.congr_fun he x))

/-- Reversing the endpoint order changes only the order of the two registers. -/
theorem reverse (s : PairSource P) (T : SourceInventory P) :
    Expands (s.reverse :: T) (s :: T) := by
  intro ℓ
  refine ⟨Word.swap ⟨s.right, s.rightSpace⟩ ⟨s.left, s.leftSpace⟩ (T.layout ++ ℓ),
    trivial, rfl, ?_⟩
  exact (comp_assoc _ _ _).symm.trans
    (congrArg (· ∘L (T.prepare ℓ).eval)
      (eval_swap_reversedSource s.distinct s.leftSpace s.rightSpace s.vector _))

/-- Splitting a combined source recovers the original two source occurrences. -/
theorem combine (s t : PairSource P) (hLeft : s.left = t.left)
    (hRight : s.right = t.right) (T : SourceInventory P) :
    Expands (s.combine t hLeft hRight :: T) (s :: t :: T) := by
  rcases s with ⟨p, q, hpq, U, V, η⟩
  rcases t with ⟨p', q', hpq', U', V', η'⟩
  cases hLeft
  cases hRight
  intro ℓ
  refine ⟨expandCombinedPair p q U V U' V' (T.layout ++ ℓ),
    isAllowed_expandCombinedPair _ _ _ _ _ _ _, rfl, ?_⟩
  exact (comp_assoc _ _ _).symm.trans
    (congrArg (· ∘L (T.prepare ℓ).eval)
      (eval_expandCombinedPair hpq U V U' V' η η' _))

/-- Exchanging two source blocks changes only their order of preparation. -/
theorem swap (s t : PairSource P) (T : SourceInventory P) :
    Expands (t :: s :: T) (s :: t :: T) := by
  intro ℓ
  refine ⟨Word.exchangeBlocks (layout [t]) (layout [s]) (T.layout ++ ℓ),
    Word.isAllowed_exchangeBlocks _ _ _, Word.sources_exchangeBlocks _ _ _, ?_⟩
  ext1 x
  change (Word.exchangeBlocks (layout [t]) (layout [s]) (T.layout ++ ℓ)).eval
      ((prepare [t] ((layout [s]) ++ (T.layout ++ ℓ))).eval
        ((prepare [s] (T.layout ++ ℓ)).eval ((prepare T ℓ).eval x))) =
    (prepare [s] ((layout [t]) ++ (T.layout ++ ℓ))).eval
      ((prepare [t] (T.layout ++ ℓ)).eval ((prepare T ℓ).eval x))
  simp only [eval_prepare_eq_appendIso_symm, Word.eval_exchangeBlocks_appendIso_symm]

end Expands

/-- Two sources on the same unordered pair can be combined, even if their endpoint
orders differ. Source: polynomial-PEPS Lemma 5.1, `04-compression.tex`, lines 125–127. -/
theorem exists_combined (s t : PairSource P) (h : s.partyPair = t.partyPair)
    (hs : ‖s.vector‖ = 1) (ht : ‖t.vector‖ = 1) :
    ∃ u : PairSource P, ‖u.vector‖ = 1 ∧ u.partyPair = s.partyPair ∧
      ∀ T : SourceInventory P, Expands (u :: T) (s :: t :: T) := by
  change s(s.left, s.right) = s(t.left, t.right) at h
  rcases Sym2.eq_iff.mp h with ⟨hLeft, hRight⟩ | ⟨hLeft, hRight⟩
  · refine ⟨s.combine t hLeft hRight, ?_, rfl, ?_⟩
    · simp only [PairSource.norm_combine_vector, hs, ht, one_mul]
    · exact Expands.combine s t hLeft hRight
  · refine ⟨s.combine t.reverse hLeft hRight, ?_, rfl, ?_⟩
    · exact (PairSource.norm_combine_vector s t.reverse hLeft hRight).trans
        (by rw [PairSource.norm_reverse_vector, hs, ht, one_mul])
    · intro T
      exact (Expands.combine s t.reverse hLeft hRight T).trans
        (Expands.cons s (Expands.reverse t T))

private theorem exists_insert (s : PairSource P) (S : SourceInventory P)
    (hs : ‖s.vector‖ = 1) (hS : S.IsNormalized) (hN : (S.map PairSource.partyPair).Nodup) :
    ∃ G : SourceInventory P, G.IsNormalized ∧ (G.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ G.map PairSource.partyPair ↔ k = s.partyPair ∨ k ∈ S.map PairSource.partyPair) ∧
      Expands G (s :: S) := by
  classical
  induction S with
  | nil =>
      refine ⟨[s], ?_, by simp, ?_, Expands.refl _⟩
      · exact (isNormalized_cons _ _).2 ⟨hs, by simp [IsNormalized]⟩
      · intro k
        simp
  | cons t T ih =>
      obtain ⟨ht, hT⟩ := isNormalized_cons _ _ |>.mp hS
      obtain ⟨htN, hTN⟩ := List.nodup_cons.mp hN
      by_cases hst : s.partyPair = t.partyPair
      · obtain ⟨u, hu, huk, hE⟩ := exists_combined s t hst hs ht
        refine ⟨u :: T, (isNormalized_cons _ _).2 ⟨hu, hT⟩, ?_, ?_, hE T⟩
        · simpa only [List.map_cons, List.nodup_cons, huk, hst] using hN
        · intro k
          simp only [List.map_cons, List.mem_cons, huk, hst]
          tauto
      · obtain ⟨G, hG, hGN, hGK, hGE⟩ := ih hT hTN
        refine ⟨t :: G, (isNormalized_cons _ _).2 ⟨ht, hG⟩, ?_, ?_,
          (Expands.cons t hGE).trans (Expands.swap s t T)⟩
        · refine List.nodup_cons.mpr ⟨?_, hGN⟩
          intro hm
          rcases (hGK t.partyPair).mp hm with he | hm
          · exact hst he.symm
          · exact htN hm
        · intro k
          simp only [List.map_cons, List.mem_cons, hGK]
          tauto

/-- Every normalized finite source inventory is obtained from one normalized source
per participating unordered pair by allowed local operations and exchanges. The set
of participating pairs is unchanged. Source: polynomial-PEPS Lemma 5.1,
`04-compression.tex`, lines 68–70 and 125–127. -/
theorem exists_grouped (S : SourceInventory P) (hS : S.IsNormalized) :
    ∃ G : SourceInventory P, G.IsNormalized ∧ (G.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ G.map PairSource.partyPair ↔ k ∈ S.map PairSource.partyPair) ∧
      G.Expands S := by
  induction S with
  | nil => exact ⟨[], by simp [IsNormalized], by simp, fun _ ↦ Iff.rfl, Expands.refl _⟩
  | cons s S ih =>
      obtain ⟨hs, hS⟩ := (isNormalized_cons _ _).mp hS
      obtain ⟨G, hG, hGN, hGK, hGE⟩ := ih hS
      obtain ⟨H, hH, hHN, hHK, hHE⟩ := exists_insert s G hs hG hGN
      refine ⟨H, hH, hHN, ?_, hHE.trans (Expands.cons s hGE)⟩
      intro k
      rw [hHK, hGK]
      simp only [List.map_cons, List.mem_cons]

end SourceInventory

end TNLean.PEPS.PairEffect
