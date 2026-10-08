/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.CommonSourcePreparation
import TNLean.PEPS.Approximation.CompletePartyMaps

/-!
# Common private source spaces for a finite family of monomials

The monomials of a gate may initially use different private spaces on each pair
of parties. Their source inventories are first completed and put in one common
order, with fixed endpoint orientations. Finite orthogonal sums of the resulting
halfspaces give actual common spaces. Coordinate projections recover each
monomial's sources, so its remaining local maps remain contractions.

The input and output layouts and the prescribed finite party set are unchanged.
The construction does not assume common spaces or an operator factorization.

Source: polynomial-PEPS manuscript, September 24, 2026, Theorem 5.2,
`04-compression.tex`, equation `eq:compression-source-gate` and common private
slot spaces, lines 233–267.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect

variable {P ι : Type} [Finite ι]

/-- A finite family of normalized inventories with the same distinct pairs has
common private halfspaces and normalized vectors recovering each original preparation.
Source: polynomial-PEPS manuscript, `04-compression.tex`, lines 253–267. -/
theorem SourceInventory.exists_common_expansions (R : SourceInventory P)
    (S : ι → SourceInventory P) (hR : (R.map PairSource.partyPair).Nodup)
    (hS : ∀ ξ, (S ξ).IsNormalized)
    (hN : ∀ ξ, ((S ξ).map PairSource.partyPair).Nodup)
    (hK : ∀ ξ k, k ∈ R.map PairSource.partyPair ↔ k ∈ (S ξ).map PairSource.partyPair) :
    ∃ U V : Fin R.length → HSpace, ∃ η : ι → ∀ i, U i ⊗[ℂ] V i,
      (∀ ξ i, ‖η ξ i‖ = 1) ∧
      ∀ ξ, (SourceInventory.ofSlots R U V (η ξ)).Expands (S ξ) := by
  classical
  let := Fintype.ofFinite ι
  choose U V η hη hE using fun ξ ↦
    SourceInventory.exists_ofSlots_expands R (S ξ) hR (hS ξ) (hN ξ) (hK ξ)
  refine ⟨fun i ↦ PairSource.commonSpace (fun ξ ↦ U ξ i),
    fun i ↦ PairSource.commonSpace (fun ξ ↦ V ξ i),
    fun ξ i ↦ PairSource.commonVector (fun ξ ↦ U ξ i) (fun ξ ↦ V ξ i)
      (fun ξ ↦ η ξ i) ξ, ?_, ?_⟩
  · intro ξ i
    exact (PairSource.norm_commonVector _ _ _ _).trans (hη ξ i)
  · intro ξ
    exact (SourceInventory.common_ofSlots_expands R U V η ξ).trans (hE ξ)

/-- Identifying an intermediate register list in both adjacent maps cancels out.
This is the fixed-memory identification in `04-compression.tex`, lines 260–267. -/
private theorem eval_cast_middle {a b c b' : Layout P} (u : Word a b) (v : Word b c)
    (h : b = b') :
    (v.castLayouts h rfl).eval ∘L (u.castLayouts rfl h).eval = v.eval ∘L u.eval := by
  cases h
  rfl

/-- A recovery from the source inventory also acts on its vector-independent layout.
Source: polynomial-PEPS manuscript, `04-compression.tex`, lines 260–267. -/
theorem SourceInventory.exists_prepareSlots_recovery (R S : SourceInventory P)
    (U V : Fin R.length → HSpace) (η : ∀ i, U i ⊗[ℂ] V i)
    (hE : (SourceInventory.ofSlots R U V η).Expands S) (ℓ : Layout P) :
    ∃ d : Word (SourceInventory.slotLayout R U V ++ ℓ) (S.layout ++ ℓ),
      d.IsAllowed ∧ d.sources = [] ∧
        d.eval ∘L (SourceInventory.prepareSlots R U V η ℓ).eval = (S.prepare ℓ).eval := by
  obtain ⟨d, hd, hds, he⟩ := hE ℓ
  let h := congrArg (· ++ ℓ) (SourceInventory.layout_ofSlots_eq R U V η (fun _ ↦ 0))
  refine ⟨d.castLayouts h rfl, (Word.isAllowed_castLayouts _ _ _).mpr hd,
    (Word.sources_castLayouts _ _ _).trans hds, ?_⟩
  exact (eval_cast_middle _ _ h).trans he

/-- Identifying both endpoint layouts of a recovery preserves the recovery identity.
This is the fixed-memory identification in `04-compression.tex`, lines 260–267. -/
private theorem eval_cast_recovery {a b c b' c' : Layout P} (u : Word a b) (d : Word b c)
    (p : Word a c) (h : b = b') (h' : c = c') (he : d.eval ∘L u.eval = p.eval) :
    (d.castLayouts h h').eval ∘L (u.castLayouts rfl h).eval = (p.castLayouts rfl h').eval := by
  cases h
  cases h'
  exact he

/-- An expansion between two slot inventories on the same pairs gives an allowed recovery
between their preparations in the fixed slot layouts.
Source: polynomial-PEPS manuscript, `04-compression.tex`, lines 260–267. -/
theorem SourceInventory.exists_prepareSlots_expands (R : SourceInventory P)
    (U V U' V' : Fin R.length → HSpace) (η : ∀ i, U i ⊗[ℂ] V i)
    (η' : ∀ i, U' i ⊗[ℂ] V' i)
    (hE : (SourceInventory.ofSlots R U V η).Expands (SourceInventory.ofSlots R U' V' η'))
    (ℓ : Layout P) :
    ∃ d : Word (SourceInventory.slotLayout R U V ++ ℓ) (SourceInventory.slotLayout R U' V' ++ ℓ),
      d.IsAllowed ∧ d.sources = [] ∧
        d.eval ∘L (SourceInventory.prepareSlots R U V η ℓ).eval =
          (SourceInventory.prepareSlots R U' V' η' ℓ).eval := by
  obtain ⟨d, hd, hds, he⟩ := hE ℓ
  refine ⟨d.castLayouts (congrArg (· ++ ℓ) (SourceInventory.layout_ofSlots_eq R U V η _))
      (congrArg (· ++ ℓ) (SourceInventory.layout_ofSlots_eq R U' V' η' (fun _ ↦ 0))),
    (Word.isAllowed_castLayouts _ _ _).mpr hd, (Word.sources_castLayouts _ _ _).trans hds, ?_⟩
  exact eval_cast_recovery _ _ _ _ _ he

/-- Prepare every monomial's sources in fixed private spaces, followed by allowed
operations containing no sources. The common spaces are constructed from the monomials.
Source: polynomial-PEPS manuscript, `04-compression.tex`, lines 233–267. -/
theorem Word.exists_common_source_preparation [Finite P] {ℓ ℓ' : Layout P}
    (w : ι → Word ℓ ℓ') (hw : ∀ ξ, (w ξ).IsAllowed) :
    ∃ R : SourceInventory P, (R.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ R.map PairSource.partyPair ↔ ¬ k.IsDiag) ∧
      ∃ U V : Fin R.length → HSpace, ∃ η : ι → ∀ i, U i ⊗[ℂ] V i,
        (∀ ξ i, ‖η ξ i‖ = 1) ∧
        ∃ v : ι → Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ',
          (∀ ξ, (v ξ).IsAllowed) ∧ (∀ ξ, (v ξ).sources = []) ∧
          ∀ ξ, (w ξ).eval = (v ξ).eval ∘L
            (SourceInventory.prepareSlots R U V (η ξ) ℓ).eval := by
  classical
  obtain ⟨R, _, hR, hRK, _⟩ := SourceInventory.exists_complete ([] : SourceInventory P)
    (by simp [SourceInventory.IsNormalized]) (by simp)
  choose S hS hN hK hD v hv hvs he using fun ξ ↦
    (w ξ).exists_complete_source_preparation (hw ξ)
  obtain ⟨U, V, η, hη, hE⟩ := SourceInventory.exists_common_expansions R S hR hS hN
    (fun ξ k ↦ (hRK k).trans (hK ξ k).symm)
  choose d hd hds hde using fun ξ ↦
    SourceInventory.exists_prepareSlots_recovery R (S ξ) U V (η ξ) (hE ξ) ℓ
  refine ⟨R, hR, hRK, U, V, η, hη, fun ξ ↦ .comp (d ξ) (v ξ),
    fun ξ ↦ ⟨hd ξ, hv ξ⟩, ?_, ?_⟩
  · intro ξ
    simp only [Word.sources, hds, hvs, List.nil_append]
  · intro ξ
    rw [Word.eval_comp, comp_assoc, hde, he]

/-- Every monomial of a finite gate expansion admits local contractions on the same
private source spaces, with normalized vectors on every pair of distinct gate parties.
Source: polynomial-PEPS manuscript, `eq:compression-source-gate` and common private
slot spaces, `04-compression.tex`, lines 233–267. -/
theorem Word.exists_common_prepared_tensorPartyMaps [Fintype P] {ℓ ℓ' : Layout P}
    (w : ι → Word ℓ ℓ') (hw : ∀ ξ, (w ξ).IsAllowed) :
    let ps := (Finset.univ : Finset P).toList
    ∃ R : SourceInventory P, (R.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ R.map PairSource.partyPair ↔ ¬ k.IsDiag) ∧
      ∃ U V : Fin R.length → HSpace, ∃ η : ι → ∀ i, U i ⊗[ℂ] V i,
        (∀ ξ i, ‖η ξ i‖ = 1) ∧
        ∃ B : ι → ∀ p,
          Mem (Layout.atParty p (SourceInventory.slotLayout R U V ++ ℓ)) →L[ℂ]
            Mem (Layout.atParty p ℓ'),
          (∀ ξ p, ‖B ξ p‖ ≤ 1) ∧
          ∀ ξ, isoL (groupByPartyIso ps ℓ' (Finset.nodup_toList _) (by simp [ps])) ∘L
              (w ξ).eval =
            tensorPartyMaps (SourceInventory.slotLayout R U V ++ ℓ) ℓ' (B ξ) ps ∘L
              isoL (groupByPartyIso ps (SourceInventory.slotLayout R U V ++ ℓ)
                (Finset.nodup_toList _) (by simp [ps])) ∘L
              (SourceInventory.prepareSlots R U V (η ξ) ℓ).eval := by
  classical
  dsimp only
  obtain ⟨R, hR, hRK, U, V, η, hη, v, hv, hvs, he⟩ :=
    Word.exists_common_source_preparation w hw
  choose B hB hF using fun ξ ↦ (v ξ).exists_tensorPartyMaps (hvs ξ) (hv ξ)
    (Finset.univ : Finset P).toList (Finset.nodup_toList _) (by simp)
  refine ⟨R, hR, hRK, U, V, η, hη, B, hB, ?_⟩
  intro ξ
  rw [he ξ, ← comp_assoc, hF ξ, comp_assoc]

end TNLean.PEPS.PairEffect
