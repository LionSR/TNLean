/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.FiniteSourceGate
import TNLean.PEPS.Approximation.GroupedBlockMap

/-!
# Gates with fixed source positions

A source-prepared gate has one fixed ordered list of pair positions, common
finite coordinate spaces, and a source-free remaining composition for each
monomial. Its scalar coefficients are those of the original gate expansion.
The actual gate operator is the sum of these prepared branch operators.

Every contraction expressed as a finite sum of allowed source-only words yields
such data. In a distributed composition this construction is applied to the
participating parties of each gate, before their labels are embedded into the
full party set. Source positions therefore do not depend on the monomial label.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`eq:compression-source-gate`, `04-compression.tex`, lines 233–299 and 342–381.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

noncomputable section

open scoped TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect

/-- The common finite source data of a contraction, with the original scalar
coefficients fixed as a parameter. Source: polynomial-PEPS Theorem 5.2,
`eq:compression-source-gate`, `04-compression.tex`, lines 233–299. -/
structure PreparedSourceGate {P ι : Type} [Fintype ι]
    (c : ι → ℂ) (a b : Layout P) where
  /-- The ordered pair positions of the gate. -/
  slots : SourceInventory P
  /-- Each unordered distinct party pair occurs once. -/
  pair_nodup : (slots.map PairSource.partyPair).Nodup
  /-- The positions include every unordered pair of distinct participating parties. -/
  pair_complete : ∀ k, k ∈ slots.map PairSource.partyPair ↔ ¬ k.IsDiag
  /-- The finite coordinate dimensions at the first endpoints. -/
  leftDim : Fin slots.length → ℕ
  /-- The finite coordinate dimensions at the second endpoints. -/
  rightDim : Fin slots.length → ℕ
  /-- The prepared source vector at each fixed position and monomial label. -/
  vector : ι → ∀ i, euc (Fin (leftDim i)) ⊗[ℂ] euc (Fin (rightDim i))
  /-- Each branch source is normalized. -/
  vector_norm : ∀ ξ i, ‖vector ξ i‖ = 1
  /-- The actual remaining operations, on the fixed source and external inputs. -/
  remaining : ι → Word (SourceInventory.slotLayout slots
    (fun i ↦ euc (Fin (leftDim i))) (fun i ↦ euc (Fin (rightDim i))) ++ a) b
  /-- All remaining local maps are contractions. -/
  remaining_allowed : ∀ ξ, (remaining ξ).IsAllowed
  /-- All sources are in the recorded preparation. -/
  remaining_sources : ∀ ξ, (remaining ξ).sources = []
  /-- The complete gate, including its scalar coefficients, is a contraction. -/
  contraction : ‖∑ ξ, c ξ • ((remaining ξ).eval ∘L
    (SourceInventory.prepareSlots slots (fun i ↦ euc (Fin (leftDim i)))
      (fun i ↦ euc (Fin (rightDim i))) (vector ξ) a).eval)‖ ≤ 1

namespace PreparedSourceGate

variable {P ι : Type} [Fintype ι] {c : ι → ℂ} {a b : Layout P}

/-- The actual prepared monomial, including its source preparations.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-source-gate`. -/
def branchWord (G : PreparedSourceGate c a b) (ξ : ι) : Word a b :=
  .comp (SourceInventory.prepareSlots G.slots (fun i ↦ euc (Fin (G.leftDim i)))
    (fun i ↦ euc (Fin (G.rightDim i))) (G.vector ξ) a) (G.remaining ξ)

/-- The gate operator is its unchanged weighted monomial sum.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-source-gate`. -/
def eval (G : PreparedSourceGate c a b) : Mem a →L[ℂ] Mem b :=
  ∑ ξ, c ξ • (G.branchWord ξ).eval

/-- Prepared branches are actual allowed compositions.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–267. -/
theorem branchWord_isAllowed (G : PreparedSourceGate c a b) (ξ : ι) :
    (G.branchWord ξ).IsAllowed := by
  refine ⟨?_, G.remaining_allowed ξ⟩
  rw [SourceInventory.prepareSlots, Word.isAllowed_castLayouts,
    SourceInventory.isAllowed_prepare_iff]
  exact SourceInventory.isNormalized_ofSlots _ _ _ _ (G.vector_norm ξ)

/-- The monomial's source inventory has exactly the gate's common ordered slots.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267 and 342–355. -/
theorem sources_branchWord (G : PreparedSourceGate c a b) (ξ : ι) :
    (G.branchWord ξ).sources = SourceInventory.ofSlots G.slots
      (fun i ↦ euc (Fin (G.leftDim i))) (fun i ↦ euc (Fin (G.rightDim i)))
      (G.vector ξ) := by
  simp only [branchWord, Word.sources, G.remaining_sources,
    SourceInventory.prepareSlots, Word.sources_castLayouts, Word.sources_prepare,
    List.nil_append]

/-- The norm bound applies to the complete gate, before choosing monomial labels.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-source-gate`. -/
theorem norm_eval_le_one (G : PreparedSourceGate c a b) : ‖G.eval‖ ≤ 1 :=
  G.contraction

/-- The same complete gate on relabelled owners, before any monomial is selected.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–417. -/
def evalAtOwners {Q : Type} (G : PreparedSourceGate c a b) (f : P → Q) :
    Mem (Layout.mapOwner f a) →L[ℂ] Mem (Layout.mapOwner f b) :=
  isoL (Layout.mapOwnerIso f b) ∘L G.eval ∘L isoL (Layout.mapOwnerIso f a).symm

/-- Relabelling owners retains the original weighted branch expansion exactly.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-source-gate`,
`04-compression.tex`, lines 351–417. -/
theorem evalAtOwners_eq_sum {Q : Type} (G : PreparedSourceGate c a b) (f : P → Q) :
    G.evalAtOwners f = ∑ ξ, c ξ • ((G.branchWord ξ).mapOwner f).eval := by
  ext x
  have he := DFunLike.congr_fun (Word.eval_sum_mapOwner_comp f c G.branchWord)
    ((Layout.mapOwnerIso f a).symm x)
  simpa only [evalAtOwners, eval, comp_apply, isoL_apply,
    LinearIsometryEquiv.apply_symm_apply] using he.symm

/-- The relabelled aggregate gate is a contraction independently of the absolute
coefficient sum. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–417. -/
theorem norm_evalAtOwners_le_one {Q : Type} (G : PreparedSourceGate c a b) (f : P → Q) :
    ‖G.evalAtOwners f‖ ≤ 1 :=
  norm_comp_le_one (LinearIsometry.norm_toContinuousLinearMap_le _)
    (norm_comp_le_one G.norm_eval_le_one (LinearIsometry.norm_toContinuousLinearMap_le _))

end PreparedSourceGate

/-- Construct common finite source positions from the original allowed words,
retaining their scalar coefficients and their exact aggregate operator.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-source-gate`,
`04-compression.tex`, lines 233–299. -/
theorem Word.exists_preparedSourceGate {P ι : Type} [Finite P] [Fintype ι]
    {a b : Layout P} (c : ι → ℂ) (w : ι → Word a b)
    (hw : ∀ ξ, (w ξ).IsAllowed) (hG : ‖∑ ξ, c ξ • (w ξ).eval‖ ≤ 1) :
    ∃ G : PreparedSourceGate c a b, G.eval = ∑ ξ, c ξ • (w ξ).eval := by
  obtain ⟨R, hR, hRK, u, v, η, hη, z, hz, hzs, he⟩ :=
    Word.exists_finite_source_preparation w hw
  let G : PreparedSourceGate c a b :=
    { slots := R, pair_nodup := hR, pair_complete := hRK,
      leftDim := u, rightDim := v, vector := η, vector_norm := hη,
      remaining := z, remaining_allowed := hz, remaining_sources := hzs,
      contraction := by simpa only [← he] using hG }
  refine ⟨G, ?_⟩
  simp only [PreparedSourceGate.eval, PreparedSourceGate.branchWord, Word.eval_comp, G, ← he]

end TNLean.PEPS.PairEffect
