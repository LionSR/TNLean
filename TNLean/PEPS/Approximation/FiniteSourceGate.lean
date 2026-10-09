/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.CommonPartyMaps
import TNLean.PEPS.Approximation.FiniteSourcePreparation

/-!
# Source-gate expansions in common finite coordinates

Every finite family of allowed source-only monomials admits common finite
coordinate spaces for its pair sources. The actual vectors lie in finite tensor
supports, and the coordinate inclusions are local isometries. Their composition
with the original operations therefore preserves the operators and the local
contraction bounds. The resulting weighted expansion retains every coefficient.

The private coordinate dimensions are finite but are not bounded here. Neither
the input nor the output layout is changed. The argument uses algebraic tensor
products and imposes no finite-dimensionality hypothesis on the ambient spaces
of the original words.

Source: polynomial-PEPS manuscript, September 24, 2026, Theorem 5.2,
`04-compression.tex`, equation `eq:compression-source-gate` and the finite
Schmidt decompositions, lines 233–299.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect

/-- The actual monomials have normalized sources in common finite coordinate
spaces, followed by allowed operations with no further sources.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–299. -/
theorem Word.exists_finite_source_preparation {P ι : Type} [Finite P] [Finite ι]
    {ℓ ℓ' : Layout P} (w : ι → Word ℓ ℓ') (hw : ∀ ξ, (w ξ).IsAllowed) :
    ∃ R : SourceInventory P, (R.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ R.map PairSource.partyPair ↔ ¬ k.IsDiag) ∧
      ∃ a b : Fin R.length → ℕ,
        ∃ η : ι → ∀ i, euc (Fin (a i)) ⊗[ℂ] euc (Fin (b i)),
          (∀ ξ i, ‖η ξ i‖ = 1) ∧
          ∃ v : ι → Word (SourceInventory.slotLayout R
            (fun i ↦ euc (Fin (a i))) (fun i ↦ euc (Fin (b i))) ++ ℓ) ℓ',
            (∀ ξ, (v ξ).IsAllowed) ∧ (∀ ξ, (v ξ).sources = []) ∧
            ∀ ξ, (w ξ).eval = (v ξ).eval ∘L
              (SourceInventory.prepareSlots R (fun i ↦ euc (Fin (a i)))
                (fun i ↦ euc (Fin (b i))) (η ξ) ℓ).eval := by
  classical
  obtain ⟨R, hR, hRK, U, V, η, hη, v, hv, hvs, he⟩ :=
    Word.exists_common_source_preparation w hw
  obtain ⟨a, b, _, _, η₀, _, hnorm, hF⟩ :=
    SourceInventory.exists_finite_coordinate_expansions R U V η
  choose d hd hds hde using fun ξ ↦ SourceInventory.exists_prepareSlots_expands R
    (fun i ↦ euc (Fin (a i))) (fun i ↦ euc (Fin (b i))) U V (η₀ ξ) (η ξ) (hF ξ) ℓ
  refine ⟨R, hR, hRK, a, b, η₀, fun ξ i ↦ (hnorm ξ i).trans (hη ξ i),
    fun ξ ↦ .comp (d ξ) (v ξ), fun ξ ↦ ⟨hd ξ, hv ξ⟩, ?_, ?_⟩
  · intro ξ
    simp only [Word.sources, hds, hvs, List.nil_append]
  · intro ξ
    rw [Word.eval_comp, comp_assoc, hde, he]

/-- Collect the local operations at each party after preparing the monomials'
sources in fixed finite coordinates. All party maps remain contractions.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–299. -/
theorem Word.exists_finite_prepared_tensorPartyMaps {P ι : Type} [Fintype P] [Finite ι]
    {ℓ ℓ' : Layout P} (w : ι → Word ℓ ℓ') (hw : ∀ ξ, (w ξ).IsAllowed) :
    let ps := (Finset.univ : Finset P).toList
    ∃ R : SourceInventory P, (R.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ R.map PairSource.partyPair ↔ ¬ k.IsDiag) ∧
      ∃ a b : Fin R.length → ℕ,
        ∃ η : ι → ∀ i, euc (Fin (a i)) ⊗[ℂ] euc (Fin (b i)),
          (∀ ξ i, ‖η ξ i‖ = 1) ∧
          ∃ B : ι → ∀ p,
            Mem (Layout.atParty p (SourceInventory.slotLayout R
              (fun i ↦ euc (Fin (a i))) (fun i ↦ euc (Fin (b i))) ++ ℓ)) →L[ℂ]
              Mem (Layout.atParty p ℓ'),
            (∀ ξ p, ‖B ξ p‖ ≤ 1) ∧
            ∀ ξ, isoL (groupByPartyIso ps ℓ' (Finset.nodup_toList _) (by simp [ps])) ∘L
                (w ξ).eval =
              tensorPartyMaps (SourceInventory.slotLayout R
                (fun i ↦ euc (Fin (a i))) (fun i ↦ euc (Fin (b i))) ++ ℓ) ℓ' (B ξ) ps ∘L
                isoL (groupByPartyIso ps (SourceInventory.slotLayout R
                  (fun i ↦ euc (Fin (a i))) (fun i ↦ euc (Fin (b i))) ++ ℓ)
                    (Finset.nodup_toList _) (by simp [ps])) ∘L
                (SourceInventory.prepareSlots R (fun i ↦ euc (Fin (a i)))
                  (fun i ↦ euc (Fin (b i))) (η ξ) ℓ).eval := by
  classical
  dsimp only
  obtain ⟨R, hR, hRK, a, b, η, hη, v, hv, hvs, he⟩ :=
    Word.exists_finite_source_preparation w hw
  choose B hB hF using fun ξ ↦ (v ξ).exists_tensorPartyMaps (hvs ξ) (hv ξ)
    (Finset.univ : Finset P).toList (Finset.nodup_toList _) (by simp)
  refine ⟨R, hR, hRK, a, b, η, hη, B, hB, ?_⟩
  intro ξ
  rw [he ξ, ← comp_assoc, hF ξ, comp_assoc]

/-- A weighted gate has an exact source expansion in common finite coordinates,
with unchanged coefficients, normalized pair sources and local contractions.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-source-gate`,
`04-compression.tex`, lines 233–299. -/
theorem Word.exists_finite_source_gate {P ι : Type} [Fintype P] [Fintype ι]
    {ℓ ℓ' : Layout P} (c : ι → ℂ) (w : ι → Word ℓ ℓ')
    (hw : ∀ ξ, (w ξ).IsAllowed) :
    let ps := (Finset.univ : Finset P).toList
    ∃ R : SourceInventory P, (R.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ R.map PairSource.partyPair ↔ ¬ k.IsDiag) ∧
      ∃ a b : Fin R.length → ℕ,
        ∃ η : ι → ∀ i, euc (Fin (a i)) ⊗[ℂ] euc (Fin (b i)),
          (∀ ξ i, ‖η ξ i‖ = 1) ∧
          ∃ B : ι → ∀ p,
            Mem (Layout.atParty p (SourceInventory.slotLayout R
              (fun i ↦ euc (Fin (a i))) (fun i ↦ euc (Fin (b i))) ++ ℓ)) →L[ℂ]
              Mem (Layout.atParty p ℓ'),
            (∀ ξ p, ‖B ξ p‖ ≤ 1) ∧
            isoL (groupByPartyIso ps ℓ' (Finset.nodup_toList _) (by simp [ps])) ∘L
                (∑ ξ, c ξ • (w ξ).eval) =
              ∑ ξ, c ξ • (tensorPartyMaps (SourceInventory.slotLayout R
                (fun i ↦ euc (Fin (a i))) (fun i ↦ euc (Fin (b i))) ++ ℓ) ℓ' (B ξ) ps ∘L
                isoL (groupByPartyIso ps (SourceInventory.slotLayout R
                  (fun i ↦ euc (Fin (a i))) (fun i ↦ euc (Fin (b i))) ++ ℓ)
                    (Finset.nodup_toList _) (by simp [ps])) ∘L
                (SourceInventory.prepareSlots R (fun i ↦ euc (Fin (a i)))
                  (fun i ↦ euc (Fin (b i))) (η ξ) ℓ).eval) := by
  classical
  dsimp only
  obtain ⟨R, hR, hRK, a, b, η, hη, B, hB, he⟩ :=
    Word.exists_finite_prepared_tensorPartyMaps w hw
  refine ⟨R, hR, hRK, a, b, η, hη, B, hB, ?_⟩
  simp only [comp_finsetSum, comp_smul, he]

end TNLean.PEPS.PairEffect
