/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PairSourceGrouping

/-!
# Ordering the source slots of a monomial

Source inventories with the same distinct unordered party pairs can be written
in a common order and with common endpoint orientations. Only whole source
blocks and the two halves of individual sources are exchanged. The resulting
preparation is carried to the original one by allowed operations containing no
sources, uniformly over all spectator registers.

Source: polynomial-PEPS manuscript (September 24, 2026),
`eq:compression-source-gate`, `04-compression.tex`, lines 233–267.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-source-gate.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-commonsource-ordering-sourceinventory.ofslots
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.ofSlots

Provenance-ID: 8769-commonsource-ordering-sourceinventory.ofslots_nil
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.ofSlots_nil

Provenance-ID: 8769-commonsource-ordering-sourceinventory.ofslots_cons
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.ofSlots_cons

Provenance-ID: 8769-commonsource-ordering-sourceinventory.isnormalized_ofslots
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.isNormalized_ofSlots

Provenance-ID: 8769-commonsource-ordering-sourceinventory.layout_ofslots_eq
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.layout_ofSlots_eq

Provenance-ID: 8769-commonsource-ordering-sourceinventory.partypairs_ofslots
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.partyPairs_ofSlots

Provenance-ID: 8769-commonsource-ordering-sourceinventory.expands.of_perm
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.Expands.of_perm

Provenance-ID: 8769-commonsource-ordering-sourceinventory.exists_ofslots_expands
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.exists_ofSlots_expands
-/

noncomputable section

open scoped InnerProductSpace TensorProduct

namespace TNLean.PEPS.PairEffect.SourceInventory

variable {P : Type}

/-- Sources with the endpoint parties and order of a reference inventory, and
with prescribed halfspaces and vectors. Source: polynomial-PEPS manuscript,
`eq:compression-source-gate`, lines 253–267. -/
def ofSlots (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (η : ∀ i, U i ⊗[ℂ] V i) : SourceInventory P :=
  List.ofFn fun i ↦ ⟨(R.get i).left, (R.get i).right, (R.get i).distinct, U i, V i, η i⟩

@[simp] theorem ofSlots_nil (U V : Fin 0 → HSpace) (η : ∀ i, U i ⊗[ℂ] V i) :
    ofSlots ([] : SourceInventory P) U V η = [] := rfl

/-- Separate the first source from the remaining slots. -/
theorem ofSlots_cons (r : PairSource P) (R : SourceInventory P)
    (U V : Fin (r :: R).length → HSpace) (η : ∀ i, U i ⊗[ℂ] V i) :
    ofSlots (r :: R) U V η =
      ⟨r.left, r.right, r.distinct, U 0, V 0, η 0⟩ ::
        ofSlots R (fun i ↦ U i.succ) (fun i ↦ V i.succ) (fun i ↦ η i.succ) := by
  simp [ofSlots, List.ofFn_succ]

/-- Normalized vectors give a normalized source inventory. -/
theorem isNormalized_ofSlots (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (η : ∀ i, U i ⊗[ℂ] V i) (hη : ∀ i, ‖η i‖ = 1) :
    (ofSlots R U V η).IsNormalized := by
  intro s hs
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
  exact hη i

/-- Changing the source vectors leaves the fresh register layout unchanged. -/
theorem layout_ofSlots_eq (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (η η' : ∀ i, U i ⊗[ℂ] V i) :
    (ofSlots R U V η).layout = (ofSlots R U V η').layout := by
  induction R with
  | nil => rfl
  | cons r R ih =>
      simp only [ofSlots_cons, layout_cons, PairSource.layout]
      exact congrArg (List.append _) (ih _ _ _ _)

/-- The source slots have exactly the unordered pairs of the reference inventory. -/
@[simp] theorem partyPairs_ofSlots (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (η : ∀ i, U i ⊗[ℂ] V i) :
    (ofSlots R U V η).map PairSource.partyPair = R.map PairSource.partyPair := by
  simpa only [ofSlots, List.map_ofFn, Function.comp_def, PairSource.partyPair] using
    congrArg (List.map PairSource.partyPair) (List.ofFn_get R)

/-- A permutation of whole source blocks preserves their preparation up to
allowed exchanges, for every spectator layout. -/
theorem Expands.of_perm {S T : SourceInventory P} (h : S.Perm T) : S.Expands T := by
  induction h with
  | nil => exact Expands.refl []
  | cons s _ ih => exact Expands.cons s ih
  | swap s t T => exact Expands.swap s t T
  | trans _ _ ih ih' => exact ih.trans ih'

/-- Orient a normalized source according to a prescribed occurrence of the same
unordered pair. Reversing the pair exchanges its tensor factors.
Source: polynomial-PEPS manuscript, `eq:compression-source-gate`, lines 253–267. -/
private theorem exists_oriented (r s : PairSource P) (hs : ‖s.vector‖ = 1)
    (hk : r.partyPair = s.partyPair) :
    ∃ U V : HSpace, ∃ η : U ⊗[ℂ] V, ‖η‖ = 1 ∧
      ∀ T : SourceInventory P, Expands (⟨r.left, r.right, r.distinct, U, V, η⟩ :: T)
        (s :: T) := by
  rcases r with ⟨p, q, hpq, U₀, V₀, η₀⟩
  rcases s with ⟨a, b, hab, U, V, η⟩
  change s(p, q) = s(a, b) at hk
  rcases Sym2.eq_iff.mp hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨U, V, η, hs, fun _ ↦ Expands.refl _⟩
  · refine ⟨V, U, TensorProduct.commIsometry ℂ U V η, ?_, ?_⟩
    · exact (TensorProduct.commIsometry ℂ U V).norm_map η |>.trans hs
    · exact fun T ↦ Expands.reverse ⟨q, p, hab, U, V, η⟩ T

/-- Reorder normalized sources along a permutation of their unordered pairs.
At each step an actual source is moved to the front and, if necessary, reversed. -/
private theorem exists_ofSlots_expands_of_perm (R S : SourceInventory P)
    (hS : S.IsNormalized) (hk : (R.map PairSource.partyPair).Perm
      (S.map PairSource.partyPair)) :
    ∃ U V : Fin R.length → HSpace, ∃ η : ∀ i, U i ⊗[ℂ] V i,
      (∀ i, ‖η i‖ = 1) ∧ (ofSlots R U V η).Expands S := by
  induction R generalizing S with
  | nil =>
      have hnil : S = [] := by simpa using hk.symm.eq_nil
      subst S
      exact ⟨Fin.elim0, Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, Expands.refl []⟩
  | cons r R ih =>
      have hr : r.partyPair ∈ S.map PairSource.partyPair := hk.mem_iff.mp (by simp)
      obtain ⟨s, hs, hsk⟩ := List.mem_map.mp hr
      obtain ⟨A, B, rfl⟩ := List.mem_iff_append.mp hs
      have hp : (A ++ s :: B).Perm (s :: (A ++ B)) := List.perm_middle
      have hS' : IsNormalized (s :: (A ++ B)) :=
        fun t ht ↦ hS t (hp.mem_iff.mpr ht)
      have hk' : (R.map PairSource.partyPair).Perm ((A ++ B).map PairSource.partyPair) := by
        apply List.Perm.cons_inv (a := r.partyPair)
        simpa only [List.map_cons, hsk] using hk.trans (hp.map PairSource.partyPair)
      obtain ⟨U, V, η, hη, hE⟩ := ih (A ++ B) ((isNormalized_cons _ _).mp hS').2 hk'
      obtain ⟨U₀, V₀, η₀, hη₀, hE₀⟩ := exists_oriented r s
        ((isNormalized_cons _ _).mp hS').1 hsk.symm
      refine ⟨Fin.cons U₀ U, Fin.cons V₀ V, Fin.cons η₀ η, ?_, ?_⟩
      · exact Fin.cases hη₀ hη
      · rw [ofSlots_cons]
        exact (Expands.cons ⟨r.left, r.right, r.distinct, U₀, V₀, η₀⟩ hE).trans
          ((hE₀ (A ++ B)).trans (Expands.of_perm hp.symm))

/-- Inventories with the same distinct unordered pairs admit the same ordered
endpoint slots. The source vectors are normalized, and explicit allowed operations
containing no sources recover the original preparation for every spectator layout.
Source: polynomial-PEPS manuscript, `eq:compression-source-gate`, lines 253–267. -/
theorem exists_ofSlots_expands (R S : SourceInventory P)
    (hR : (R.map PairSource.partyPair).Nodup) (hS : S.IsNormalized)
    (hSN : (S.map PairSource.partyPair).Nodup)
    (hK : ∀ k, k ∈ R.map PairSource.partyPair ↔ k ∈ S.map PairSource.partyPair) :
    ∃ U V : Fin R.length → HSpace, ∃ η : ∀ i, U i ⊗[ℂ] V i,
      (∀ i, ‖η i‖ = 1) ∧ (ofSlots R U V η).Expands S := by
  exact exists_ofSlots_expands_of_perm R S hS ((List.perm_ext_iff_of_nodup hR hSN).mpr hK)

end TNLean.PEPS.PairEffect.SourceInventory
