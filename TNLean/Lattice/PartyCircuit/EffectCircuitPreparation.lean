/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Lattice.PartyCircuit.WordAppendTail
import TNLean.Lattice.PartyCircuit.DistributedSourceComposition
import TNLean.Lattice.PartyCircuit.SourceCircuitLocations
import TNLean.Lattice.PartyCircuit.PreparedSourceGate
import TNLean.Lattice.PartyCircuit.PartyLayout
import QICLean.Analysis.SourceOnlyDensityError
import QICLean.Analysis.ChronologicalGarbage
import TNLean.Lattice.PartyCircuit.WordEvaluationTransport

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
-/

noncomputable section
open scoped TensorProduct
open ContinuousLinearMap
namespace TNLean.Lattice.PartyCircuit

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

/-- A nonprivate gate: a weighted list of party chains on the registers of the participating
parties `C`, embedded among all parties by `owner`, next to the untouched registers `tail`.
Source: polynomial-PEPS 04-compression.tex, lines 21–36 and 199–229. -/
inductive EffectGate : Layout P → Layout P → Type 1
  | mk {C : Type} [Fintype C] (owner : C ↪ P) {a b : Layout C}
      (L : PartyGate a b) (tail : Layout P) :
      EffectGate (Layout.mapOwner owner a ++ tail) (Layout.mapOwner owner b ++ tail)

namespace EffectGate

/-- The original actual memory map of a nonprivate gate, with all spectator identities.
Source: polynomial-PEPS 04-compression.tex, lines 21–36. -/
@[simp] def eval : {a b : Layout P} → EffectGate a b → (Mem a →L[ℂ] Mem b)
  | _, _, @EffectGate.mk _ _ _ owner a b L tail =>
      isoL (appendIso (Layout.mapOwner owner b) tail).symm ∘L
        (isoL (Layout.mapOwnerIso owner b) ∘L PartyCircuit.gate (toGate L) ∘L
          isoL (Layout.mapOwnerIso owner a).symm).rTensor (Mem tail) ∘L
        isoL (appendIso (Layout.mapOwner owner a) tail)

/-- A nonprivate gate is allowed when its monomials are allowed and its operator is a
contraction. These are precisely gate and monomial contraction conditions; input states
and density comparisons are not part of this predicate.
Source: polynomial-PEPS 04-compression.tex, lines 28–35 and 55–57. -/
@[simp] def IsAllowed : {a b : Layout P} → EffectGate a b → Prop
  | _, _, @EffectGate.mk _ _ _ _ _ _ L _ =>
      (∀ q ∈ L, q.2.IsAllowed) ∧ ‖PartyCircuit.gate (toGate L)‖ ≤ 1

/-- The participating parties of a nonprivate gate.
Source: polynomial-PEPS 04-compression.tex, lines 25–27 and 229. -/
@[simp] def participants : {a b : Layout P} → EffectGate a b → Finset P
  | _, _, @EffectGate.mk _ _ _ owner _ _ _ _ => Finset.univ.map owner

/-- An allowed nonprivate gate is a contraction.
Source: polynomial-PEPS 04-compression.tex, lines 215–217. -/
theorem norm_eval_le_one : {a b : Layout P} → (g : EffectGate a b) → g.IsAllowed →
    ‖g.eval‖ ≤ 1
  | _, _, @EffectGate.mk _ _ _ _ _ _ _ tail, hw =>
      norm_comp_le_one (LinearIsometry.norm_toContinuousLinearMap_le _)
        (norm_comp_le_one ((norm_rTensor_le (Mem tail) _).trans
          (norm_comp_le_one (LinearIsometry.norm_toContinuousLinearMap_le _)
            (norm_comp_le_one hw.2 (LinearIsometry.norm_toContinuousLinearMap_le _))))
          (LinearIsometry.norm_toContinuousLinearMap_le _))

end EffectGate

/-- Nonprivate gates as a gate family.
Source: polynomial-PEPS 04-compression.tex, lines 21–36 and 215–217. -/
instance : GateFamily (EffectGate (P := P)) where
  eval := EffectGate.eval
  IsAllowed := EffectGate.IsAllowed
  norm_eval_le_one := EffectGate.norm_eval_le_one
  participants := EffectGate.participants

@[simp] theorem EffectGate.gateFamily_eval {a b : Layout P} (g : EffectGate a b) :
    GateFamily.eval g = g.eval :=
  rfl

@[simp] theorem EffectGate.gateFamily_isAllowed {a b : Layout P} (g : EffectGate a b) :
    GateFamily.IsAllowed g ↔ g.IsAllowed :=
  Iff.rfl

@[simp] theorem EffectGate.gateFamily_participants {a b : Layout P} (g : EffectGate a b) :
    GateFamily.participants g = g.participants :=
  rfl

/-- Original chronological gates, including the actual effectful expansions: circuits whose
gates are nonprivate gates, with arbitrary local maps.
Source: polynomial-PEPS 04-compression.tex, lines 21–36 and 199–229. -/
abbrev EffectCircuit : Layout P → Layout P → Type 1 := Circuit LocalCondition.any EffectGate

namespace EffectCircuit

/-- The empty circuit. -/
@[match_pattern] abbrev id (ℓ : Layout P) : EffectCircuit ℓ ℓ := Circuit.id ℓ

/-- Composition, in chronological order. -/
@[match_pattern] abbrev comp {ℓ₁ ℓ₂ ℓ₃ : Layout P} (w : EffectCircuit ℓ₁ ℓ₂) (w'
    : EffectCircuit ℓ₂ ℓ₃) :
    EffectCircuit ℓ₁ ℓ₃ :=
  Circuit.comp w w'

/-- A local map on registers of one party, next to untouched registers. -/
@[match_pattern] abbrev localMap (p : P) {ℓ₁ ℓ₂ : Layout P} (h₁ : ∀ r ∈ ℓ₁, r.owner = p)
    (h₂ : ∀ r ∈ ℓ₂, r.owner = p) (U : Mem ℓ₁ →L[ℂ] Mem ℓ₂) (ℓ : Layout P) :
    EffectCircuit (ℓ₁ ++ ℓ) (ℓ₂ ++ ℓ) :=
  Circuit.localMap p h₁ h₂ U ℓ True.intro

/-- Exchange of two adjacent tensor factors. -/
@[match_pattern] abbrev swap (r r' : Reg P) (ℓ : Layout P) : EffectCircuit (r :: r' :: ℓ)
    (r' :: r :: ℓ) :=
  Circuit.swap r r' ℓ

/-- A circuit next to an untouched register. -/
@[match_pattern] abbrev frame (r : Reg P) {ℓ ℓ' : Layout P} (w : EffectCircuit ℓ ℓ') :
    EffectCircuit (r :: ℓ) (r :: ℓ') :=
  Circuit.frame r w

/-- A nonprivate gate as a circuit. -/
@[match_pattern] abbrev gate {C : Type} [Fintype C] (owner : C ↪ P) {a b : Layout C}
    (L : PartyGate a b) (tail : Layout P) :
    EffectCircuit (Layout.mapOwner owner a ++ tail) (Layout.mapOwner owner b ++ tail) :=
  Circuit.gate (EffectGate.mk owner L tail)

/-- A circuit framed by a list of untouched registers. -/
abbrev frameList {ℓ ℓ' : Layout P} (ℓ₀ : Layout P) (w : EffectCircuit ℓ ℓ') :
    EffectCircuit (ℓ₀ ++ ℓ) (ℓ₀ ++ ℓ') :=
  Circuit.frameList ℓ₀ w

/-- Identify equal input and output layouts without adding an operation. -/
abbrev castLayouts {ℓ ℓ' a b : Layout P} (w : EffectCircuit ℓ ℓ') (h : ℓ = a) (h' : ℓ' = b) :
    EffectCircuit a b :=
  Circuit.castLayouts w h h'

/-- Induction on the constructors of `EffectCircuit`. -/
@[induction_eliminator, elab_as_elim]
theorem induction {motive : {ℓ ℓ' : Layout P} → EffectCircuit ℓ ℓ' → Prop}
    (id : ∀ ℓ : Layout P, motive (EffectCircuit.id ℓ))
    (comp : ∀ {ℓ₁ ℓ₂ ℓ₃ : Layout P} (w : EffectCircuit ℓ₁ ℓ₂) (w' : EffectCircuit ℓ₂ ℓ₃),
      motive w → motive w' → motive (EffectCircuit.comp w w'))
    (localMap : ∀ (p : P) {ℓ₁ ℓ₂ : Layout P} (h₁ : ∀ r ∈ ℓ₁, r.owner = p)
      (h₂ : ∀ r ∈ ℓ₂, r.owner = p) (U : Mem ℓ₁ →L[ℂ] Mem ℓ₂) (ℓ : Layout P),
      motive (EffectCircuit.localMap p h₁ h₂ U ℓ))
    (gate : ∀ {C : Type} [Fintype C] (owner : C ↪ P) {a b : Layout C} (L : PartyGate a b)
      (tail : Layout P), motive (EffectCircuit.gate owner L tail))
    (swap : ∀ (r r' : Reg P) (ℓ : Layout P), motive (EffectCircuit.swap r r' ℓ))
    (frame : ∀ (r : Reg P) {ℓ ℓ' : Layout P} (w : EffectCircuit ℓ ℓ'),
      motive w → motive (EffectCircuit.frame r w))
    {ℓ ℓ' : Layout P} (w : EffectCircuit ℓ ℓ') : motive w := by
  induction w with
  | id ℓ₀ => exact id ℓ₀
  | comp w w' ih ih' => exact comp w w' ih ih'
  | localMap p h₁ h₂ U ℓ => exact localMap p h₁ h₂ U ℓ
  | gate g => cases g with | mk owner L tail => exact gate owner L tail
  | swap r r' ℓ => exact swap r r' ℓ
  | frame r w ih => exact frame r w ih

theorem eval_gate {C : Type} [Fintype C] (owner : C ↪ P) {a b : Layout C}
    (L : PartyGate a b) (tail : Layout P) :
    (gate owner L tail).eval =
      isoL (appendIso (Layout.mapOwner owner b) tail).symm ∘L
        (isoL (Layout.mapOwnerIso owner b) ∘L PartyCircuit.gate (toGate L) ∘L
          isoL (Layout.mapOwnerIso owner a).symm).rTensor (Mem tail) ∘L
        isoL (appendIso (Layout.mapOwner owner a) tail) :=
  rfl

end EffectCircuit

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

namespace SourceCircuit
/-- Regard an actual word without sources as a circuit of exact operations.
Source: polynomial-PEPS 04-compression.tex, lines 21–36 and 210–217. -/
def ofLocalWord : {a b : Layout P} → (w : Word a b) → w.sources = [] → SourceCircuit a b
  | _, _, .id a, _ => .id a
  | _, _, .comp w v, h =>
      .comp (ofLocalWord w (List.append_eq_nil_iff.mp h).2)
        (ofLocalWord v (List.append_eq_nil_iff.mp h).1)
  | _, _, .localMap p ha hb A tail, _ => .localMap p ha hb A tail
  | _, _, Word.source .., h => nomatch h
  | _, _, .swap r s tail, _ => .swap r s tail
  | _, _, .frame r w, h => .frame r (ofLocalWord w h)

/-- This conversion does not change the chronological memory map.
Source: polynomial-PEPS 04-compression.tex, lines 21–36 and 210–217. -/
theorem eval_ofLocalWord {a b : Layout P} (w : Word a b) (h : w.sources = []) :
    (ofLocalWord w h).eval = w.eval := by
  induction w with
  | id => rfl
  | comp w v ihw ihv =>
      simp only [ofLocalWord, Circuit.eval, Circuit.eval]
      rw [ihw _, ihv _]
  | localMap => rfl
  | source => cases h
  | swap => rfl
  | frame r w ih =>
      simp only [ofLocalWord, Circuit.eval, Circuit.eval]
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
  simp [localPrepare, Circuit.eval, appendIso, appendLeft,
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
  | _, _, Word.source .. => True
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
end SourceCircuit

end TNLean.Lattice.PartyCircuit
