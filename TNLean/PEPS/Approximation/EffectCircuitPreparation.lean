/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.Approximation.WordAppendTail
import TNLean.PEPS.Approximation.DistributedSourceComposition
import TNLean.PEPS.Approximation.SourceCircuitLocations
import TNLean.PEPS.Approximation.PreparedSourceGate
import TNLean.PEPS.Approximation.PartyLayout
import QICLean.Analysis.SourceOnlyDensityError
import QICLean.Analysis.ChronologicalGarbage
import TNLean.PEPS.Approximation.WordEvaluationTransport

/-! # Preparation and private inputs for distributed circuits

The original circuit may use arbitrary private contractions and finite linear
combinations of allowed monomials. The replacement circuit uses prepared pair
sources and local contractions, with additional auxiliary registers retained
until the final partial trace. Its operator differs from the original operator
tensored with one fixed normalized auxiliary vector by at most `2 * δ * M`,
where `M` is the original number of nonprivate gates. Consequently, its physical
density differs by at most `4 * δ * M` in trace norm.

Source: polynomial-PEPS, `04-compression.tex`, `eq:compression-effect-circuit-error`,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-effect-circuit-error; Theorem 5.2, lines 137–151 and 199–251.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-source-resource-effectcircuitpreparation-01
TNLean.PEPS.PairEffect.EffectCircuit
Provenance-ID: 8769-source-resource-effectcircuitpreparation-02
TNLean.PEPS.PairEffect.EffectCircuit.IsAllowed
Provenance-ID: 8769-source-resource-effectcircuitpreparation-03
TNLean.PEPS.PairEffect.EffectCircuit.eval
Provenance-ID: 8769-source-resource-effectcircuitpreparation-04
TNLean.PEPS.PairEffect.EffectCircuit.norm_eval_le_one
Provenance-ID: 8769-source-resource-effectcircuitpreparation-05
TNLean.PEPS.PairEffect.PartyChain.isPreparation_prepStack
Provenance-ID: 8769-source-resource-effectcircuitpreparation-06
TNLean.PEPS.PairEffect.ProductInput
Provenance-ID: 8769-source-resource-effectcircuitpreparation-07
TNLean.PEPS.PairEffect.ProductInput.eval_prepare
Provenance-ID: 8769-source-resource-effectcircuitpreparation-08
TNLean.PEPS.PairEffect.ProductInput.eval_prepare_smul
Provenance-ID: 8769-source-resource-effectcircuitpreparation-09
TNLean.PEPS.PairEffect.ProductInput.isAllowed_prepare
Provenance-ID: 8769-source-resource-effectcircuitpreparation-10
TNLean.PEPS.PairEffect.ProductInput.mapOwner
Provenance-ID: 8769-source-resource-effectcircuitpreparation-11
TNLean.PEPS.PairEffect.ProductInput.mapOwnerIso_vector
Provenance-ID: 8769-source-resource-effectcircuitpreparation-12
TNLean.PEPS.PairEffect.ProductInput.norm_vector
Provenance-ID: 8769-source-resource-effectcircuitpreparation-13
TNLean.PEPS.PairEffect.ProductInput.ofParties
Provenance-ID: 8769-source-resource-effectcircuitpreparation-14
TNLean.PEPS.PairEffect.ProductInput.partitionIso_symm_mapOwner_vector
Provenance-ID: 8769-source-resource-effectcircuitpreparation-15
TNLean.PEPS.PairEffect.ProductInput.partitionIso_symm_vector
Provenance-ID: 8769-source-resource-effectcircuitpreparation-16
TNLean.PEPS.PairEffect.ProductInput.partitionIso_vector
Provenance-ID: 8769-source-resource-effectcircuitpreparation-17
TNLean.PEPS.PairEffect.ProductInput.prepare
Provenance-ID: 8769-source-resource-effectcircuitpreparation-18
TNLean.PEPS.PairEffect.ProductInput.prepareIsometry
Provenance-ID: 8769-source-resource-effectcircuitpreparation-19
TNLean.PEPS.PairEffect.ProductInput.restrict
Provenance-ID: 8769-source-resource-effectcircuitpreparation-20
TNLean.PEPS.PairEffect.ProductInput.sources_prepare
Provenance-ID: 8769-source-resource-effectcircuitpreparation-21
TNLean.PEPS.PairEffect.ProductInput.vector
Provenance-ID: 8769-source-resource-effectcircuitpreparation-22
TNLean.PEPS.PairEffect.SourceCircuit.castLayouts
Provenance-ID: 8769-source-resource-effectcircuitpreparation-23
TNLean.PEPS.PairEffect.SourceCircuit.eval_castLayouts
Provenance-ID: 8769-source-resource-effectcircuitpreparation-24
TNLean.PEPS.PairEffect.SourceCircuit.eval_exchangeBlocks
Provenance-ID: 8769-source-resource-effectcircuitpreparation-25
TNLean.PEPS.PairEffect.SourceCircuit.eval_frameList_tmul
Provenance-ID: 8769-source-resource-effectcircuitpreparation-26
TNLean.PEPS.PairEffect.SourceCircuit.eval_ofLocalWord
Provenance-ID: 8769-source-resource-effectcircuitpreparation-27
TNLean.PEPS.PairEffect.SourceCircuit.exchangeBlocks
Provenance-ID: 8769-source-resource-effectcircuitpreparation-28
TNLean.PEPS.PairEffect.SourceCircuit.frameList
Provenance-ID: 8769-source-resource-effectcircuitpreparation-29
TNLean.PEPS.PairEffect.SourceCircuit.isAllowed_castLayouts
Provenance-ID: 8769-source-resource-effectcircuitpreparation-30
TNLean.PEPS.PairEffect.SourceCircuit.isAllowed_frameList
Provenance-ID: 8769-source-resource-effectcircuitpreparation-31
TNLean.PEPS.PairEffect.SourceCircuit.isAllowed_ofLocalWord
Provenance-ID: 8769-source-resource-effectcircuitpreparation-32
TNLean.PEPS.PairEffect.SourceCircuit.ofLocalWord
Provenance-ID: 8769-source-resource-effectcircuitpreparation-33
TNLean.PEPS.PairEffect.SourceInventory.norm_vector
Provenance-ID: 8769-source-resource-effectcircuitpreparation-34
TNLean.PEPS.PairEffect.Word.IsPreparation
Provenance-ID: 8769-source-resource-effectcircuitpreparation-35
TNLean.PEPS.PairEffect.Word.eval_isPreparation_cast
Provenance-ID: 8769-source-resource-effectcircuitpreparation-36
TNLean.PEPS.PairEffect.Word.eval_isPreparation_heq
Provenance-ID: 8769-source-resource-effectcircuitpreparation-37
TNLean.PEPS.PairEffect.Word.eval_localPrepare
Provenance-ID: 8769-source-resource-effectcircuitpreparation-38
TNLean.PEPS.PairEffect.Word.isAllowed_localPrepare
Provenance-ID: 8769-source-resource-effectcircuitpreparation-39
TNLean.PEPS.PairEffect.Word.localPrepare
Provenance-ID: 8769-source-resource-effectcircuitpreparation-40
TNLean.PEPS.PairEffect.Word.output_of_isPreparation
Provenance-ID: 8769-source-resource-effectcircuitpreparation-41
TNLean.PEPS.PairEffect.exists_prepared_effectReplacement
Provenance-ID: 8769-source-resource-effectcircuitpreparation-42
TNLean.PEPS.PairEffect.isPreparation_prepGate
Provenance-ID: 8769-source-resource-effectcircuitpreparation-43
TNLean.PEPS.PairEffect.isPreparation_prepWord
-/

noncomputable section
open scoped TensorProduct
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect

private theorem sum_get_wordList {P : Type} {a b : Layout P}
    (l : List (ℂ × Word a b)) :
    (∑ i : Fin l.length, (l.get i).1 • (l.get i).2.eval) =
      (l.map fun q => q.1 • q.2.eval).sum := by
  rw [← List.sum_ofFn]
  change (List.ofFn ((fun q : ℂ × Word a b => q.1 • q.2.eval) ∘ l.get)).sum = _
  rw [← List.map_ofFn, List.ofFn_get]
private theorem replaceGate_eq_iso_comp_wordSum {P : Type} {a b : Layout P}
    (m : ℕ) (L : PartyGate a b) :
    replaceGate m (toGate L) = isoL (gateIso m L) ∘L
      ∑ i : Fin (wordList m L).length,
        ((wordList m L).get i).1 • ((wordList m L).get i).2.eval := by
  rw [sum_get_wordList]
  have hc := comp_listSum (isoL (gateIso m L))
    ((wordList m L).map fun q => (q.1, q.2.eval))
  simp only [List.map_map, Function.comp_def] at hc
  rw [hc]
  simpa only [termList_toGate, List.map_map, Function.comp_def] using
    replaceGate_eq_sum_termList m (toGate L)
/-- Construct the actual prepared gate from its original effect expansion.
Source: polynomial-PEPS 04-compression.tex, lines 199–212. -/
theorem exists_prepared_effectReplacement {P : Type} [Finite P] {a b : Layout P}
    {m r : ℕ} (hm : m ≠ 0) (L : PartyGate a b)
    (hL : ∀ q ∈ L, q.2.IsAllowed ∧ q.2.toEffectChain.effectCount ≤ r)
    (hG : ‖gate (toGate L)‖ ≤ 1) {δ : ℝ}
    (hδ : r / Real.sqrt m * (L.map fun q => ‖q.1‖).sum ≤ δ) :
    ∃ G : PreparedSourceGate
      (fun i : Fin (wordList m L).length =>
        (((1 + δ)⁻¹ : ℝ) : ℂ) * ((wordList m L).get i).1) a (gateOut m L),
      isoL (gateIso m L) ∘L G.eval =
        (((1 + δ)⁻¹ : ℝ) : ℂ) • replaceGate m (toGate L) ∧
      ‖isoL (gateIso m L) ∘L G.eval -
        appendRight (inventoryVector m (toGate L)) ∘L gate (toGate L)‖ ≤ 2 * δ := by
  classical
  have hLt : ∀ q ∈ toGate L, q.2.IsAllowed ∧ q.2.effectCount ≤ r := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := mem_toGate hq
    exact ⟨p.2.isAllowed_toEffectChain (hL p hp).1, (hL p hp).2⟩
  have hδt : r / Real.sqrt m * ((toGate L).map fun q => ‖q.1‖).sum ≤ δ := by
    simpa only [map_norm_toGate] using hδ
  obtain ⟨_, _, hnorm, herror⟩ := replaceGate_rescaled hm (toGate L) hLt hG hδt
  let c := fun i : Fin (wordList m L).length =>
    (((1 + δ)⁻¹ : ℝ) : ℂ) * ((wordList m L).get i).1
  let w := fun i : Fin (wordList m L).length => ((wordList m L).get i).2
  have he : isoL (gateIso m L) ∘L (∑ i, c i • (w i).eval) =
      (((1 + δ)⁻¹ : ℝ) : ℂ) • replaceGate m (toGate L) := by
    dsimp only [c, w]
    simp only [mul_smul, ← Finset.smul_sum, comp_smul]
    rw [← replaceGate_eq_iso_comp_wordSum]
  have hsum : ‖∑ i, c i • (w i).eval‖ ≤ 1 := by
    rw [← (gateIso m L).toLinearIsometry.norm_toContinuousLinearMap_comp, he]
    exact hnorm
  have hw : ∀ i, (w i).IsAllowed := by
    intro i
    exact isAllowed_wordList m L (fun q hq => (hL q hq).1) _ (List.get_mem _ _)
  obtain ⟨G, hGe⟩ := Word.exists_preparedSourceGate c w hw hsum
  refine ⟨G, ?_, ?_⟩
  · rw [hGe]
    exact he
  · rw [hGe, he]
    exact herror

variable {P : Type}

/-- Original chronological gates, including the actual effectful expansions.
Source: polynomial-PEPS 04-compression.tex, lines 21–36 and 199–229. -/
inductive EffectCircuit : Layout P → Layout P → Type 1
  | id (a : Layout P) : EffectCircuit a a
  | comp {a b d : Layout P} (w : EffectCircuit a b) (v : EffectCircuit b d) :
      EffectCircuit a d
  | localMap (p : P) {a b : Layout P}
      (ha : ∀ r ∈ a, r.owner = p) (hb : ∀ r ∈ b, r.owner = p)
      (A : Mem a →L[ℂ] Mem b) (tail : Layout P) :
      EffectCircuit (a ++ tail) (b ++ tail)
  | gate {C : Type} [Fintype C] (owner : C ↪ P) {a b : Layout C}
      (L : PartyGate a b) (tail : Layout P) :
      EffectCircuit (Layout.mapOwner owner a ++ tail) (Layout.mapOwner owner b ++ tail)
  | swap (r s : Reg P) (tail : Layout P) : EffectCircuit (r :: s :: tail) (s :: r :: tail)
  | frame (r : Reg P) {a b : Layout P} (w : EffectCircuit a b) :
      EffectCircuit (r :: a) (r :: b)

/-- A normalized product input with independently recorded register occurrences.
Source: polynomial-PEPS 04-compression.tex, lines 137–139. -/
inductive ProductInput : (a : Layout P) → Type 1
  | nil : ProductInput []
  | cons (r : Reg P) (x : r.space) (hx : ‖x‖ = 1) {a : Layout P}
      (rest : ProductInput a) : ProductInput (r :: a)

namespace ProductInput
/-- The actual tensor product of the recorded initial vectors.
Source: polynomial-PEPS 04-compression.tex, lines 137–139. -/
def vector : {a : Layout P} → ProductInput a → Mem a
  | _, .nil => (1 : ℂ)
  | _, .cons _ x _ rest => x ⊗ₜ[ℂ] rest.vector

/-- Normalization of the product input, including the empty layout.
Source: polynomial-PEPS 04-compression.tex, lines 137–139. -/
theorem norm_vector {a : Layout P} (ψ : ProductInput a) : ‖ψ.vector‖ = 1 := by
  induction ψ with
  | nil => exact norm_one
  | cons r x hx rest ih => simp only [vector, TensorProduct.norm_tmul, hx, ih, one_mul]
/-- Initialize one register containing the entire private memory of each party.
The private vectors may be arbitrary within those memories.
Source: polynomial-PEPS 04-compression.tex, lines 137–139. -/
def ofParties (H : P → HSpace) (x : ∀ p, H p) (hx : ∀ p, ‖x p‖ = 1) :
    (ps : List P) → ProductInput (ps.map fun p => (⟨p, H p⟩ : Reg P))
  | [] => .nil
  | p :: ps => .cons ⟨p, H p⟩ (x p) (hx p) (ofParties H x hx ps)
end ProductInput

namespace EffectCircuit
/-- The original actual memory map, with all spectator identities.
Source: polynomial-PEPS 04-compression.tex, lines 21–36. -/
def eval : {a b : Layout P} → EffectCircuit a b → Mem a →L[ℂ] Mem b
  | _, _, .id _ => .id ℂ _
  | _, _, .comp w v => v.eval ∘L w.eval
  | _, _, .localMap p ha hb A tail => (Word.localMap p ha hb A tail).eval
  | _, _, @EffectCircuit.gate _ C _ owner a b L tail =>
      isoL (appendIso (Layout.mapOwner owner b) tail).symm ∘L
        (isoL (Layout.mapOwnerIso owner b) ∘L PairEffect.gate (toGate L) ∘L
          isoL (Layout.mapOwnerIso owner a).symm).rTensor (Mem tail) ∘L
        isoL (appendIso (Layout.mapOwner owner a) tail)
  | _, _, .swap r s tail => (Word.swap r s tail).eval
  | _, _, .frame r w => w.eval.lTensor r.space

/-- These are precisely gate and monomial contraction conditions. Input states
and density comparisons are not fields of this predicate.
Source: polynomial-PEPS 04-compression.tex, lines 28–35 and 55–57. -/
def IsAllowed : {a b : Layout P} → EffectCircuit a b → Prop
  | _, _, .id _ => True
  | _, _, .comp w v => w.IsAllowed ∧ v.IsAllowed
  | _, _, .localMap _ _ _ A _ => ‖A‖ ≤ 1
  | _, _, @EffectCircuit.gate _ _ _ _ _ _ L _ =>
      (∀ q ∈ L, q.2.IsAllowed) ∧ ‖PairEffect.gate (toGate L)‖ ≤ 1
  | _, _, .swap .. => True
  | _, _, .frame _ w => w.IsAllowed
/-- Original chronological evaluation is a contraction.
Source: polynomial-PEPS 04-compression.tex, lines 215–217. -/
theorem norm_eval_le_one {a b : Layout P} (w : EffectCircuit a b)
    (hw : w.IsAllowed) : ‖w.eval‖ ≤ 1 := by
  induction w with
  | id => exact norm_id_le
  | comp w v ihw ihv => exact norm_comp_le_one (ihv hw.2) (ihw hw.1)
  | localMap p ha hb A tail =>
      exact Word.norm_eval_le_one (.localMap p ha hb A tail) (show ‖A‖ ≤ 1 from hw)
  | @gate C _ owner a b L tail =>
      exact norm_comp_le_one (LinearIsometry.norm_toContinuousLinearMap_le _)
        (norm_comp_le_one ((norm_rTensor_le (Mem tail) _).trans
          (norm_comp_le_one (LinearIsometry.norm_toContinuousLinearMap_le _)
            (norm_comp_le_one hw.2 (LinearIsometry.norm_toContinuousLinearMap_le _))))
          (LinearIsometry.norm_toContinuousLinearMap_le _))
  | swap r s tail => exact Word.norm_eval_le_one (.swap r s tail) trivial
  | frame r w ih => exact (norm_lTensor_le r.space _).trans (ih hw)
end EffectCircuit
namespace SourceCircuit
/-- Regard an actual word without sources as a circuit of exact operations.
Source: polynomial-PEPS 04-compression.tex, lines 21–36 and 210–217. -/
def ofLocalWord : {a b : Layout P} → (w : Word a b) → w.sources = [] → SourceCircuit a b
  | _, _, .id a, _ => .id a
  | _, _, .comp w v, h =>
      .comp (ofLocalWord w (List.append_eq_nil_iff.mp h).2)
        (ofLocalWord v (List.append_eq_nil_iff.mp h).1)
  | _, _, .localMap p ha hb A tail, _ => .localMap p ha hb A tail
  | _, _, .source .., h => nomatch h
  | _, _, .swap r s tail, _ => .swap r s tail
  | _, _, .frame r w, h => .frame r (ofLocalWord w h)

/-- This conversion does not change the chronological memory map.
Source: polynomial-PEPS 04-compression.tex, lines 21–36 and 210–217. -/
theorem eval_ofLocalWord {a b : Layout P} (w : Word a b) (h : w.sources = []) :
    (ofLocalWord w h).eval = w.eval := by
  induction w with
  | id => rfl
  | comp w v ihw ihv =>
      simp only [ofLocalWord, SourceCircuit.eval, Word.eval]
      rw [ihw _, ihv _]
  | localMap => rfl
  | source => cases h
  | swap => rfl
  | frame r w ih =>
      simp only [ofLocalWord, SourceCircuit.eval, Word.eval]
      rw [ih h]

/-- Exact local and permutation operations remain allowed after conversion.
Source: polynomial-PEPS 04-compression.tex, lines 21–36 and 210–217. -/
theorem isAllowed_ofLocalWord {a b : Layout P} (w : Word a b)
    (h : w.sources = []) (hw : w.IsAllowed) : (ofLocalWord w h).IsAllowed := by
  induction w with
  | id => trivial
  | comp w v ihw ihv =>
      exact ⟨ihw (List.append_eq_nil_iff.mp h).2 hw.1,
        ihv (List.append_eq_nil_iff.mp h).1 hw.2⟩
  | localMap => exact hw
  | source => cases h
  | swap => trivial
  | frame r w ih => exact ih h hw

/-- Reorder two blocks without adding a prepared gate.
Source: polynomial-PEPS 04-compression.tex, lines 21–36 and 210–217. -/
def exchangeBlocks (a b tail : Layout P) :
    SourceCircuit (a ++ (b ++ tail)) (b ++ (a ++ tail)) :=
  ofLocalWord (Word.exchangeBlocks a b tail) (by simp)

/-- This reordering is exactly the original word operator.
Source: polynomial-PEPS 04-compression.tex, lines 21–36 and 210–217. -/
theorem eval_exchangeBlocks (a b tail : Layout P) :
    (exchangeBlocks a b tail).eval = (Word.exchangeBlocks a b tail).eval :=
  eval_ofLocalWord _ _

/-- All previously retained registers remain spectators of the later circuit.
Source: polynomial-PEPS 04-compression.tex, lines 210–217. -/
def frameList {a b : Layout P} (rs : Layout P) (w : SourceCircuit a b) :
    SourceCircuit (rs ++ a) (rs ++ b) :=
  match rs with
  | [] => w
  | r :: rest => .frame r (frameList rest w)

/-- Retaining registers does not alter allowedness of later gates.
Source: polynomial-PEPS 04-compression.tex, lines 210–217. -/
theorem isAllowed_frameList {a b : Layout P} (w : SourceCircuit a b)
    (hw : w.IsAllowed) (rs : Layout P) : (w.frameList rs).IsAllowed := by
  induction rs with
  | nil => exact hw
  | cons r rs ih => exact ih

/-- The actual evaluation acts as the identity on arbitrary retained vectors.
Source: polynomial-PEPS 04-compression.tex, lines 210–217. -/
theorem eval_frameList_tmul {a b : Layout P} (w : SourceCircuit a b)
    (rs : Layout P) (x : Mem rs) (y : Mem a) :
    (w.frameList rs).eval ((appendIso rs a).symm (x ⊗ₜ[ℂ] y)) =
      (appendIso rs b).symm (x ⊗ₜ[ℂ] w.eval y) := by
  induction rs with
  | nil => exact map_smul w.eval x y
  | cons r rs ih =>
      induction x using TensorProduct.inductionOn with
      | tmul u v => exact congrArg (fun z => u ⊗ₜ[ℂ] z) (ih v)
      | add x z hx hz => simp only [TensorProduct.add_tmul, map_add, hx, hz]
end SourceCircuit
namespace Word
/-- Prepare a normalized private vector without any pair source.
Source: polynomial-PEPS 04-compression.tex, lines 137–139. -/
def localPrepare (r : Reg P) (x : r.space) (a : Layout P) : Word a (r :: a) :=
  .localMap r.owner (ℓ₁ := []) (ℓ₂ := [r])
    (by simp) (by simp) (appendLeft (E := ℂ) x) a

/-- The private preparation is a contraction when its vector is normalized.
Source: polynomial-PEPS 04-compression.tex, lines 137–139. -/
theorem isAllowed_localPrepare (r : Reg P) (x : r.space) (hx : ‖x‖ = 1)
    (a : Layout P) : (localPrepare r x a).IsAllowed :=
  (norm_appendLeft_le x).trans hx.le

/-- The private vector is tensored with the actual spectator state.
Source: polynomial-PEPS 04-compression.tex, lines 137–139. -/
theorem eval_localPrepare (r : Reg P) (x : r.space) (a : Layout P) (y : Mem a) :
    (localPrepare r x a).eval y = x ⊗ₜ[ℂ] y := by
  simp [localPrepare, Word.eval, appendIso, appendLeft,
    LinearIsometryEquiv.symm_lTensor]
end Word

namespace ProductInput
/-- Prepare the recorded private input using only local operations.
Source: polynomial-PEPS 04-compression.tex, lines 137–139. -/
def prepare : {a : Layout P} → ProductInput a → Word [] a
  | _, .nil => .id []
  | _, @ProductInput.cons _ r x _ a rest =>
      .comp rest.prepare (Word.localPrepare r x a)

/-- The actual preparation produces the original product vector.
Source: polynomial-PEPS 04-compression.tex, lines 137–139. -/
theorem eval_prepare {a : Layout P} (ψ : ProductInput a) :
    ψ.prepare.eval (1 : ℂ) = ψ.vector := by
  induction ψ with
  | nil => rfl
  | cons r x hx rest ih =>
      change (Word.localPrepare r x _).eval (rest.prepare.eval (1 : ℂ)) = _
      rw [Word.eval_localPrepare, ih]
      rfl
/-- Every step of the private preparation is a contraction.
Source: polynomial-PEPS 04-compression.tex, lines 137–139. -/
theorem isAllowed_prepare {a : Layout P} (ψ : ProductInput a) :
    ψ.prepare.IsAllowed := by
  induction ψ with
  | nil => trivial
  | cons r x hx rest ih => exact ⟨ih, Word.isAllowed_localPrepare r x hx _⟩

/-- Private preparation introduces no pair source.
Source: polynomial-PEPS 04-compression.tex, lines 137–139. -/
theorem sources_prepare {a : Layout P} (ψ : ProductInput a) :
    ψ.prepare.sources = [] := by
  induction ψ with
  | nil => rfl
  | cons r x hx rest ih =>
      simp only [prepare, Word.sources, Word.localPrepare, List.nil_append, ih]

/-- The preparation map is scalar multiplication by the recorded product vector.
Source: polynomial-PEPS 04-compression.tex, lines 137–139. -/
theorem eval_prepare_smul {a : Layout P} (ψ : ProductInput a) (z : ℂ) :
    ψ.prepare.eval z = z • ψ.vector := by
  rw [← eval_prepare ψ]
  simpa only [smul_eq_mul, mul_one] using map_smul ψ.prepare.eval z (1 : ℂ)

/-- The normalized private input defines an isometric preparation from the scalar space.
Source: polynomial-PEPS 04-compression.tex, lines 137–139. -/
def prepareIsometry {a : Layout P} (ψ : ProductInput a) : ℂ →ₗᵢ[ℂ] Mem a where
  toLinearMap := ψ.prepare.eval.toLinearMap
  norm_map' z := by
    change ‖ψ.prepare.eval z‖ = ‖z‖
    rw [eval_prepare_smul, norm_smul, norm_vector, mul_one]

end ProductInput
namespace Word
/-- Words consisting solely of the preparation of fresh pair sources.
Source: polynomial-PEPS 04-compression.tex, lines 103–112. -/
def IsPreparation : {a b : Layout P} → Word a b → Prop
  | _, _, .id _ => True
  | _, _, .comp w v => w.IsPreparation ∧ v.IsPreparation
  | _, _, .source .. => True
  | _, _, .localMap .. => False
  | _, _, .swap .. => False
  | _, _, .frame .. => False

/-- The output of a pure preparation is its actual sources followed by the input.
Source: polynomial-PEPS 04-compression.tex, lines 103–112. -/
theorem output_of_isPreparation {a b : Layout P} (w : Word a b)
    (hw : w.IsPreparation) : b = w.sources.layout ++ a := by
  induction w with
  | id => rfl
  | comp w v ihw ihv =>
      simpa only [sources, SourceInventory.layout_append, List.append_assoc] using
        (ihv hw.2).trans (congrArg (v.sources.layout ++ ·) (ihw hw.1))
  | source => rfl
  | localMap => exact hw.elim
  | swap => exact hw.elim
  | frame => exact hw.elim
private theorem prepare_eval_heq (S : SourceInventory P) {a b : Layout P}
    (h : a = b) {x : Mem a} {y : Mem b} (hxy : HEq x y) :
    HEq ((S.prepare a).eval x) ((S.prepare b).eval y) := by
  cases h
  cases hxy
  rfl

/-- A pure preparation is exactly preparation of its recorded source list.
Source: polynomial-PEPS 04-compression.tex, lines 103–112. -/
theorem eval_isPreparation_heq {a b : Layout P} (w : Word a b)
    (hw : w.IsPreparation) (x : Mem a) :
    HEq (w.eval x) ((w.sources.prepare a).eval x) := by
  induction w with
  | id => rfl
  | comp w v ihw ihv =>
      exact (ihv hw.2 (w.eval x)).trans
        ((prepare_eval_heq v.sources (w.output_of_isPreparation hw.1)
          (ihw hw.1 x)).trans
          (SourceInventory.eval_prepare_append v.sources w.sources _ x).symm)
  | source => rfl
  | localMap => exact hw.elim
  | swap => exact hw.elim
  | frame => exact hw.elim
end Word
/-- A stack preparation contains only pair sources and identities.
Source: polynomial-PEPS 04-compression.tex, lines 103–112. -/
theorem isPreparation_prepWord {p q : P} (hpq : p ≠ q) {α β : Type}
    [Fintype α] [Fintype β] (η : EuclideanSpace ℂ (α × β))
    (m : ℕ) (a : Layout P) : (prepWord hpq η m a).IsPreparation := by
  induction m with
  | zero => trivial
  | succ m ih => exact ⟨ih, trivial⟩

namespace PartyChain
/-- Every occurrence stack is prepared without acting on the input.
Source: polynomial-PEPS 04-compression.tex, lines 103–112. -/
theorem isPreparation_prepStack {a b : Layout P} (M : PartyChain a b)
    (m : ℕ) (tail : Layout P) : (M.prepStack m tail).IsPreparation := by
  induction M with
  | final => trivial
  | effect hpq α β ls w η rest ih =>
      exact ⟨ih, isPreparation_prepWord hpq η m _⟩
end PartyChain

/-- The common auxiliary output is prepared independently of the gate input.
Source: polynomial-PEPS 04-compression.tex, lines 103–112. -/
theorem isPreparation_prepGate {a b : Layout P} (m : ℕ) (L : PartyGate a b) :
    (prepGate m L).IsPreparation := by
  induction L with
  | nil => trivial
  | cons q L ih => exact ⟨ih, q.2.isPreparation_prepStack m _⟩
namespace Word
/-- The actual preparation equals tensoring by its fixed source vector.
Source: polynomial-PEPS 04-compression.tex, lines 103–112. -/
theorem eval_isPreparation_cast {a b : Layout P} (w : Word a b)
    (hw : w.IsPreparation) (x : Mem a) :
    (w.castLayouts rfl (w.output_of_isPreparation hw)).eval x =
      (appendIso w.sources.layout a).symm (w.sources.vector ⊗ₜ[ℂ] x) := by
  have he := (eval_castLayouts_apply_heq w rfl
    (w.output_of_isPreparation hw) (HEq.rfl : HEq x x)).trans
      (w.eval_isPreparation_heq hw x)
  exact (eq_of_heq he).trans (SourceInventory.eval_prepare_eq_appendIso_symm _ _ _)
end Word

namespace SourceInventory
/-- The tensor product of normalized source vectors is normalized.
Source: polynomial-PEPS 04-compression.tex, lines 103–112. -/
theorem norm_vector (S : SourceInventory P) (hS : S.IsNormalized) : ‖vector S‖ = 1 := by
  induction S with
  | nil => change ‖(1 : ℂ)‖ = 1; exact norm_one
  | cons s S ih =>
      change ‖assocL s.leftSpace s.rightSpace (Mem (layout S)) (s.vector ⊗ₜ[ℂ] vector S)‖ = 1
      rw [show assocL s.leftSpace s.rightSpace (Mem (layout S)) =
        isoL (TensorProduct.assocIsometry ℂ s.leftSpace s.rightSpace (Mem (layout S))) from rfl]
      simp only [isoL_apply, LinearIsometryEquiv.norm_map, TensorProduct.norm_tmul,
        hS s List.mem_cons_self, ih (fun q hq => hS q (List.mem_cons_of_mem _ hq)), one_mul]
end SourceInventory
namespace ProductInput
/-- Retain the actual private input factors on a specified set of parties.
Source: polynomial-PEPS 04-compression.tex, lines 137–139 and 246–251. -/
def restrict (f : P → Bool) : {a : Layout P} → ProductInput a →
    ProductInput (Layout.restrict f a)
  | _, .nil => .nil
  | _, @ProductInput.cons _ r x hx a rest => by
      by_cases h : f r.owner = true
      · rw [Layout.restrict_cons, h]
        exact .cons r x hx (rest.restrict f)
      · have h' : f r.owner = false := Bool.eq_false_iff.mpr h
        rw [Layout.restrict_cons, h']
        exact rest.restrict f

private theorem restrict_cons_true (f : P → Bool) (r : Reg P) (x : r.space)
    (hx : ‖x‖ = 1) {a : Layout P} (rest : ProductInput a) (h : f r.owner = true) :
    HEq ((ProductInput.cons r x hx rest).restrict f)
      (ProductInput.cons r x hx (rest.restrict f)) := by
  simp only [restrict, dite_eq_left h, Eq.mpr, eqRec_heq_iff]
  rfl

private theorem restrict_cons_false (f : P → Bool) (r : Reg P) (x : r.space)
    (hx : ‖x‖ = 1) {a : Layout P} (rest : ProductInput a) (h : f r.owner = false) :
    HEq ((ProductInput.cons r x hx rest).restrict f) (rest.restrict f) := by
  have hn : ¬ f r.owner = true := by simp only [h, Bool.false_eq_true, not_false_eq_true]
  simp only [restrict, dite_eq_right hn, Eq.mpr, eqRec_heq_iff]
  rfl

private theorem vector_heq {a b : Layout P} (h : a = b)
    {ψ : ProductInput a} {χ : ProductInput b} (hψ : HEq ψ χ) :
    HEq ψ.vector χ.vector := by
  cases h
  cases hψ
  rfl
private theorem tmul_heq {a b a' b' : Layout P} (ha : a = a') (hb : b = b')
    {x : Mem a} {x' : Mem a'} {y : Mem b} {y' : Mem b'}
    (hx : HEq x x') (hy : HEq y y') :
    HEq (x ⊗ₜ[ℂ] y) (x' ⊗ₜ[ℂ] y') := by
  cases ha
  cases hb
  cases hx
  cases hy
  rfl

/-- The owner partition splits the actual input into two local product vectors.
Source: polynomial-PEPS 04-compression.tex, lines 137–139 and 246–251. -/
theorem partitionIso_vector (f : P → Bool) {a : Layout P} (ψ : ProductInput a) :
    Layout.partitionIso f a ψ.vector =
      (ψ.restrict f).vector ⊗ₜ[ℂ] (ψ.restrict (fun p => !f p)).vector := by
  induction ψ with
  | nil => rfl
  | @cons r x hx tail rest ih =>
      cases h : f r.owner with
      | false =>
          have ht : (fun p => !f p) r.owner = true := by simp only [h, Bool.not_false]
          have ha : Layout.restrict f (r :: tail) = Layout.restrict f tail := by
            simp only [Layout.restrict_cons, h, Bool.false_eq_true, ite_false]
          have hb : Layout.restrict (fun p => !f p) (r :: tail) =
              r :: Layout.restrict (fun p => !f p) tail := by
            simp only [Layout.restrict_cons, ht, ite_true]
          have he := tmul_heq ha hb
            (vector_heq ha (restrict_cons_false f r x hx rest h))
            (vector_heq hb (restrict_cons_true (fun p => !f p) r x hx rest ht))
          apply eq_of_heq
          refine (Layout.partitionIso_cons_false_tmul f r _ h x rest.vector).trans ?_
          refine HEq.trans ?_ he.symm
          rw [ih]
          rfl
      | true =>
          have ht : (fun p => !f p) r.owner = false := by simp only [h, Bool.not_true]
          have ha : Layout.restrict f (r :: tail) = r :: Layout.restrict f tail := by
            simp only [Layout.restrict_cons, h, ite_true]
          have hb : Layout.restrict (fun p => !f p) (r :: tail) =
              Layout.restrict (fun p => !f p) tail := by
            simp only [Layout.restrict_cons, ht, Bool.false_eq_true, ite_false]
          have he := tmul_heq ha hb
            (vector_heq ha (restrict_cons_true f r x hx rest h))
            (vector_heq hb (restrict_cons_false (fun p => !f p) r x hx rest ht))
          apply eq_of_heq
          refine (Layout.partitionIso_cons_true_tmul f r _ h x rest.vector).trans ?_
          refine HEq.trans ?_ he.symm
          rw [ih]
          rfl
/-- Recombine the two actual local input vectors in the original register order.
Source: polynomial-PEPS 04-compression.tex, lines 137–139 and 246–251. -/
theorem partitionIso_symm_vector (f : P → Bool) {a : Layout P} (ψ : ProductInput a) :
    (Layout.partitionIso f a).symm
      ((ψ.restrict f).vector ⊗ₜ[ℂ] (ψ.restrict (fun p => !f p)).vector) = ψ.vector := by
  rw [← partitionIso_vector, LinearIsometryEquiv.symm_apply_apply]

/-- Change only the party names of the actual private input registers.
Source: polynomial-PEPS 04-compression.tex, lines 137–139 and 246–251. -/
def mapOwner {Q : Type} (f : P → Q) : {a : Layout P} → ProductInput a →
    ProductInput (Layout.mapOwner f a)
  | _, .nil => .nil
  | _, .cons r x hx rest => .cons ⟨f r.owner, r.space⟩ x hx (rest.mapOwner f)

/-- The mapped product input is the original vector in the owner coordinates.
Source: polynomial-PEPS 04-compression.tex, lines 137–139 and 246–251. -/
theorem mapOwnerIso_vector {Q : Type} (f : P → Q) {a : Layout P} (ψ : ProductInput a) :
    Layout.mapOwnerIso f a ψ.vector = (ψ.mapOwner f).vector := by
  induction ψ with
  | nil => rfl
  | cons r x hx rest ih =>
      change x ⊗ₜ[ℂ] Layout.mapOwnerIso f _ rest.vector =
        x ⊗ₜ[ℂ] (rest.mapOwner f).vector
      rw [ih]

/-- Group the actual private input after reassigning its parties. Both local
vectors are normalized by `norm_vector`, and have the derived private preparation isometries.
Source: polynomial-PEPS 04-compression.tex, lines 137–139 and 246–251. -/
theorem partitionIso_symm_mapOwner_vector {Q : Type} (g : P → Q) (f : Q → Bool)
    {a : Layout P} (ψ : ProductInput a) :
    (Layout.partitionIso f (Layout.mapOwner g a)).symm
      (((ψ.mapOwner g).restrict f).vector ⊗ₜ[ℂ]
        ((ψ.mapOwner g).restrict (fun p => !f p)).vector) =
      Layout.mapOwnerIso g a ψ.vector := by
  rw [partitionIso_symm_vector, mapOwnerIso_vector]
end ProductInput
namespace SourceCircuit
/-- Identify equal register layouts without adding a gate or changing its parties.
Source: polynomial-PEPS 04-compression.tex, lines 210–217. -/
def castLayouts {a b a' b' : Layout P} (w : SourceCircuit a b)
    (h : a = a') (h' : b = b') : SourceCircuit a' b' := h ▸ h' ▸ w

/-- Layout identification preserves the original contraction conditions.
Source: polynomial-PEPS 04-compression.tex, lines 210–217. -/
theorem isAllowed_castLayouts {a b a' b' : Layout P} (w : SourceCircuit a b)
    (h : a = a') (h' : b = b') : (w.castLayouts h h').IsAllowed ↔ w.IsAllowed := by
  cases h
  cases h'
  rfl

/-- Equal layouts are identified by their canonical isometries in the actual evaluation.
Source: polynomial-PEPS 04-compression.tex, lines 210–217. -/
theorem eval_castLayouts {a b a' b' : Layout P} (w : SourceCircuit a b)
    (h : a = a') (h' : b = b') : (w.castLayouts h h').eval =
      isoL (Layout.memCongr h') ∘L w.eval ∘L isoL (Layout.memCongr h).symm := by
  cases h
  cases h'
  rfl
end SourceCircuit

end TNLean.PEPS.PairEffect
