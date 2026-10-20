/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.GateReexpansion
import TNLean.Lattice.Compression.MessageGateExpansion
import TNLean.Lattice.Compression.EffectCircuitTermwiseCoefficientBounds

/-!
# Message expansions on one fixed original chronology

Each original nonprivate occurrence is assigned an ordered expansion of
monomials containing finite-dimensional messages. Expanding these messages
chooses lists for the existing chronology; it does not introduce another
chronology. Private operations, owner embeddings, spectator registers and
original gate operators are retained. Original monomial counts, individual
coefficients and message dimensions imply polynomial bounds before effect
elimination.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 32–43,
74–125, 137–175 and 590–600. Manuscript revision:
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.EffectCircuit
variable {P : Type}

/-- One actual message-containing expansion on the original local input and
output spaces of each nonprivate gate occurrence.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 32–43 and 137–149. -/
@[reducible] def MessageGateLists : {a b : Layout P} → EffectCircuit a b → Type 1
  | _, _, .id _ => PUnit
  | _, _, .comp w v => MessageGateLists w × MessageGateLists v
  | _, _, .localMap .. => PUnit
  | _, _, @EffectCircuit.gate _ _ _ _ a b _ _ => MessageGate a b
  | _, _, .swap .. => PUnit
  | _, _, .frame _ w => MessageGateLists w

/-- Expand messages into the existing gate-list assignment on this same
chronology. Each message uses its constructed orthonormal-basis expansion.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 32–43 and 137–149. -/
def expandMessageGateLists : {a b : Layout P} → (w : EffectCircuit a b) →
    w.MessageGateLists → w.GateLists
  | _, _, .id _, _ => PUnit.unit
  | _, _, .comp w v, lists =>
      (w.expandMessageGateLists lists.1, v.expandMessageGateLists lists.2)
  | _, _, .localMap .., _ => PUnit.unit
  | _, _, @EffectCircuit.gate _ _ _ _ _ _ _ _, lists => lists.expand
  | _, _, .swap .., _ => PUnit.unit
  | _, _, .frame _ w, lists => w.expandMessageGateLists lists

/-- The original private maps and prescribed original gates are contractions;
each message monomial is allowed; and the literal local expansion approximates
its original gate in operator norm. No whole-circuit comparison is assumed.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–149 and 590–600. -/
def IsMessageGateApproximation (δ : ℝ) : {a b : Layout P} → (w : EffectCircuit a b) →
    w.MessageGateLists → w.GateMaps → Prop
  | _, _, .id _, _, _ => True
  | _, _, .comp w v, lists, G =>
      w.IsMessageGateApproximation δ lists.1 G.1 ∧
        v.IsMessageGateApproximation δ lists.2 G.2
  | _, _, .localMap _ _ _ A _, _, _ => ‖A‖ ≤ 1
  | _, _, @EffectCircuit.gate _ C _ _ a b _ _, lists, G =>
      Fintype.card C ≠ 1 ∧ (∀ term ∈ lists, term.2.IsAllowed) ∧
        ‖(G : Mem a →L[ℂ] Mem b)‖ ≤ 1 ∧
          ‖lists.eval - (G : Mem a →L[ℂ] Mem b)‖ ≤ δ
  | _, _, .swap .., _, _ => True
  | _, _, .frame _ w, lists, G => w.IsMessageGateApproximation δ lists G

/-- Bounds on the original ordered monomial lists, before expanding either
messages or pair effects. Every message dimension is the dimension of its
actual transferred register; repeated occurrences remain separate.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–149 and 199–208. -/
def IsMessageResourceBounded (r m K : ℕ) (D C : ℝ) :
    {a b : Layout P} → (w : EffectCircuit a b) → w.MessageGateLists → Prop
  | _, _, .id _, _ => True
  | _, _, .comp w v, lists =>
      w.IsMessageResourceBounded r m K D C lists.1 ∧
        v.IsMessageResourceBounded r m K D C lists.2
  | _, _, .localMap .., _ => True
  | _, _, @EffectCircuit.gate _ _ _ _ _ _ _ _, lists =>
      lists.length ≤ K ∧ ∀ term ∈ lists,
        term.2.effectCount ≤ r ∧ ‖term.1‖ ≤ C ∧
          term.2.messageDimensions.length ≤ m ∧
            ∀ d ∈ term.2.messageDimensions, (d : ℝ) ≤ D
  | _, _, .swap .., _ => True
  | _, _, .frame _ w, lists => w.IsMessageResourceBounded r m K D C lists

/-- Increasing a local gate-error budget preserves the same message lists and
original gate operators.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 590–600. -/
theorem IsMessageGateApproximation.mono {a b : Layout P} {w : EffectCircuit a b}
    {lists : w.MessageGateLists} {G : w.GateMaps} {δ ε : ℝ}
    (h : w.IsMessageGateApproximation δ lists G) (hδε : δ ≤ ε) :
    w.IsMessageGateApproximation ε lists G := by
  induction w with
  | id => trivial
  | comp w v ihw ihv => exact ⟨ihw h.1, ihv h.2⟩
  | localMap => exact h
  | gate => exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans hδε⟩
  | swap => trivial
  | frame r w ih => exact ih h

/-- Enlarging the message-dimension bound preserves the same original lists,
monomial counts, scalar coefficients and pair-effect bounds.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–175. -/
theorem IsMessageResourceBounded.mono_dimension {a b : Layout P}
    {w : EffectCircuit a b} {lists : w.MessageGateLists} {r m K : ℕ} {D D' C : ℝ}
    (h : w.IsMessageResourceBounded r m K D C lists) (hD : D ≤ D') :
    w.IsMessageResourceBounded r m K D' C lists := by
  induction w with
  | id => trivial
  | comp w v ihw ihv => exact ⟨ihw h.1, ihv h.2⟩
  | localMap => trivial
  | gate =>
      exact ⟨h.1, fun term hterm ↦
        ⟨(h.2 term hterm).1, (h.2 term hterm).2.1, (h.2 term hterm).2.2.1,
          fun d hd ↦ ((h.2 term hterm).2.2.2 d hd).trans hD⟩⟩
  | swap => trivial
  | frame r w ih => exact ih h

/-- Enlarging the coefficient bound preserves the same original lists,
monomial counts, message dimensions and pair-effect bounds.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–175. -/
theorem IsMessageResourceBounded.mono_coefficient {a b : Layout P}
    {w : EffectCircuit a b} {lists : w.MessageGateLists} {r m K : ℕ} {D C C' : ℝ}
    (h : w.IsMessageResourceBounded r m K D C lists) (hC : C ≤ C') :
    w.IsMessageResourceBounded r m K D C' lists := by
  induction w with
  | id => trivial
  | comp w v ihw ihv => exact ⟨ihw h.1, ihv h.2⟩
  | localMap => trivial
  | gate =>
      exact ⟨h.1, fun term hterm ↦
        ⟨(h.2 term hterm).1, (h.2 term hterm).2.1.trans hC, (h.2 term hterm).2.2⟩⟩
  | swap => trivial
  | frame r w ih => exact ih h

/-- Enlarging an individual coefficient majorant preserves the original
pair-effect bound and the actual ordered monomial lists.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–175. -/
theorem IsTermwiseBounded.mono_coefficient {a b : Layout P} {w : EffectCircuit a b}
    {r : ℕ} {C C' : ℝ} (h : w.IsTermwiseBounded r C) (hC : C ≤ C') :
    w.IsTermwiseBounded r C' := by
  induction w with
  | id => trivial
  | comp w v ihw ihv => exact ⟨ihw h.1, ihv h.2⟩
  | localMap => trivial
  | gate => exact fun term hterm ↦ ⟨(h term hterm).1, (h term hterm).2.trans hC⟩
  | swap => trivial
  | frame r w ih => exact ih h

/-- Exact message expansion preserves the local comparison with every original
gate. Original operators are transported by the existing occurrence-preserving
assignment, rather than replaced by the expanded sums.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 32–43,
137–149 and 590–600. -/
theorem isGateApproximation_expandMessageGateLists {a b : Layout P}
    (w : EffectCircuit a b) {δ : ℝ} :
    ∀ (lists : w.MessageGateLists) (G : w.GateMaps),
      w.IsMessageGateApproximation δ lists G →
        (w.reexpand (w.expandMessageGateLists lists)).IsGateApproximation δ
          (w.reexpandGateMaps (w.expandMessageGateLists lists) G) := by
  induction w with
  | id => intro lists G h; trivial
  | comp w v ihw ihv =>
      intro lists G h
      exact ⟨ihw lists.1 G.1 h.1, ihv lists.2 G.2 h.2⟩
  | localMap => intro lists G h; exact h
  | gate owner L tail =>
      intro lists G h
      exact ⟨h.1, lists.isAllowed_expand h.2.1, h.2.2.1,
        (by
          change ‖PairEffect.gate (toGate lists.expand) - G‖ ≤ δ
          rw [lists.eval_expand]
          exact h.2.2.2)⟩
  | swap => intro lists G h; trivial
  | frame r w ih => intro lists G h; exact ih lists G h

/-- At most `K` original monomials, each with at most `m` messages of dimension
at most `D`, produce at most the indicated number of terms at each same original
gate occurrence. Empty expansions and zero-dimensional messages are included.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 32–43 and 137–175. -/
theorem monomialCount_expandMessageGateLists_le {a b : Layout P}
    (w : EffectCircuit a b) {r m K : ℕ} {D C : ℝ} (hD : 1 ≤ D) :
    ∀ lists : w.MessageGateLists, w.IsMessageResourceBounded r m K D C lists →
      ∀ g, (w.reexpand (w.expandMessageGateLists lists)).monomialCount g ≤
        ⌈(K : ℝ) * D ^ m⌉₊ := by
  induction w with
  | id => intro lists hb g; exact nomatch g
  | comp w v ihw ihv =>
      intro lists hb g
      cases g with
      | inl g => exact ihw lists.1 hb.1 g
      | inr g => exact ihv lists.2 hb.2 g
  | localMap => intro lists hb g; exact nomatch g
  | gate owner L tail =>
      intro lists hb g
      have hs := lists.expansion_size_le D m K hD hb.1
        (fun term hterm ↦ (hb.2 term hterm).2.2.2)
        (fun term hterm ↦ (hb.2 term hterm).2.2.1)
      change lists.expand.length ≤ ⌈(K : ℝ) * D ^ m⌉₊
      exact_mod_cast hs.1.trans (Nat.le_ceil ((K : ℝ) * D ^ m))
  | swap => intro lists hb g; exact nomatch g
  | frame r w ih => intro lists hb g; exact ih lists hb g

/-- Original individual coefficient bounds give individual bounds after
message expansion. The estimate uses the derived coefficient sum as a
nonnegative majorant; it introduces no coefficient-sum assumption. The number
of pair effects remains bounded by the original constant.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 32–43,
137–175 and 199–208. -/
theorem isTermwiseBounded_expandMessageGateLists {a b : Layout P}
    (w : EffectCircuit a b) {δ D C : ℝ} {r m K : ℕ} (hD : 1 ≤ D) (hC : 0 ≤ C) :
    ∀ (lists : w.MessageGateLists) (G : w.GateMaps),
      w.IsMessageGateApproximation δ lists G →
      w.IsMessageResourceBounded r m K D C lists →
        (w.reexpand (w.expandMessageGateLists lists)).IsTermwiseBounded r
          ((K : ℝ) * C * D ^ m) := by
  induction w with
  | id => intro lists G ha hb; trivial
  | comp w v ihw ihv =>
      intro lists G ha hb
      exact ⟨ihw lists.1 G.1 ha.1 hb.1, ihv lists.2 G.2 ha.2 hb.2⟩
  | localMap => intro lists G ha hb; trivial
  | gate owner L tail =>
      intro lists G ha hb
      have hs := lists.expansion_size_le_of_coeff_le D C m K hD hC hb.1
        (fun term hterm ↦ (hb.2 term hterm).2.2.2)
        (fun term hterm ↦ (hb.2 term hterm).2.2.1)
        (fun term hterm ↦ (hb.2 term hterm).2.1)
      intro term hterm
      refine ⟨lists.effectCount_expand_le ha.2.1
        (fun t ht ↦ (hb.2 t ht).1) term hterm, ?_⟩
      apply le_trans ?_ hs.2
      apply List.single_le_sum _ _ (List.mem_map.mpr ⟨term, hterm, rfl⟩)
      intro x hx
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
      exact norm_nonneg t.1
  | swap => intro lists G ha hb; trivial
  | frame r w ih => intro lists G ha hb; exact ih lists G ha hb

end TNLean.PEPS.PairEffect.EffectCircuit
