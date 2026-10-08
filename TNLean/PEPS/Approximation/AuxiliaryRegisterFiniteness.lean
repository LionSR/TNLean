/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.EffectCircuitDensity
import TNLean.PEPS.Approximation.FiniteRegisterMemories

/-!
# Finite-dimensional registers retained by pair-effect replacement

Each retained auxiliary register is finite-dimensional because it is an actual
Euclidean pair-source register. This is proved through the preparations and circuit
composition. Original private registers require only the manuscript's individual
finite-dimensionality assumption, without a numerical dimension bound.

Source: polynomial-PEPS, `04-compression.tex`, lines 17–19 and 199–227.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-effect-circuit-error; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-approximate-physical-auxiliaryregisterfiniteness-01
TNLean.PEPS.PairEffect.EffectCircuit.finiteDimensional_auxiliary_private_mem
Provenance-ID: 8769-approximate-physical-auxiliaryregisterfiniteness-02
TNLean.PEPS.PairEffect.EffectCircuit.finiteDimensional_auxiliary_private_registers
Provenance-ID: 8769-approximate-physical-auxiliaryregisterfiniteness-03
TNLean.PEPS.PairEffect.EffectCircuit.finiteDimensional_auxiliary_registers
Provenance-ID: 8769-approximate-physical-auxiliaryregisterfiniteness-04
TNLean.PEPS.PairEffect.Layout.finiteDimensional_registers_append
Provenance-ID: 8769-approximate-physical-auxiliaryregisterfiniteness-05
TNLean.PEPS.PairEffect.Layout.finiteDimensional_registers_mapOwner
Provenance-ID: 8769-approximate-physical-auxiliaryregisterfiniteness-06
TNLean.PEPS.PairEffect.PartyChain.finiteDimensional_registers_sources_prepStack
Provenance-ID: 8769-approximate-physical-auxiliaryregisterfiniteness-07
TNLean.PEPS.PairEffect.finiteDimensional_registers_sources_comp
Provenance-ID: 8769-approximate-physical-auxiliaryregisterfiniteness-08
TNLean.PEPS.PairEffect.finiteDimensional_registers_sources_prepGate
Provenance-ID: 8769-approximate-physical-auxiliaryregisterfiniteness-09
TNLean.PEPS.PairEffect.finiteDimensional_registers_sources_prepWord
-/


noncomputable section
namespace TNLean.PEPS.PairEffect
variable {P Q : Type}

namespace Layout
/-- Concatenation preserves finite-dimensionality of each actual register.
Source: polynomial-PEPS, `04-compression.tex:18–28` and `210–227`. -/
theorem finiteDimensional_registers_append (a b : Layout P)
    (ha : ∀ t ∈ a, FiniteDimensional ℂ t.space.carrier)
    (hb : ∀ t ∈ b, FiniteDimensional ℂ t.space.carrier) :
    ∀ t ∈ a ++ b, FiniteDimensional ℂ t.space.carrier := by
  intro t ht
  exact (List.mem_append.mp ht).elim (ha t) (hb t)

/-- Owner relabelling preserves the actual space of every register.
Source: polynomial-PEPS, `04-compression.tex:18–28` and `210–227`. -/
theorem finiteDimensional_registers_mapOwner (f : P → Q) (a : Layout P)
    (ha : ∀ t ∈ a, FiniteDimensional ℂ t.space.carrier) :
    ∀ t ∈ Layout.mapOwner f a, FiniteDimensional ℂ t.space.carrier := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact ha s hs
end Layout

/-- Composing source preparations concatenates finite-dimensional source registers.
Source: polynomial-PEPS, `04-compression.tex:103–112` and `210–227`. -/
theorem finiteDimensional_registers_sources_comp {a b c : Layout P}
    (w : Word a b) (v : Word b c)
    (hw : ∀ t ∈ w.sources.layout, FiniteDimensional ℂ t.space.carrier)
    (hv : ∀ t ∈ v.sources.layout, FiniteDimensional ℂ t.space.carrier) :
    ∀ t ∈ (Word.comp w v).sources.layout, FiniteDimensional ℂ t.space.carrier := by
  simpa only [Word.sources, SourceInventory.layout_append] using
    Layout.finiteDimensional_registers_append v.sources.layout w.sources.layout hv hw

/-- Each retained register of an actual prepared pair stack is a finite
Euclidean space, including the empty-stack case. Source: polynomial-PEPS,
`04-compression.tex:103–112` and `210–227`. -/
theorem finiteDimensional_registers_sources_prepWord {p q : P} (hpq : p ≠ q)
    {α β : Type} [Fintype α] [Fintype β]
    (η : EuclideanSpace ℂ (α × β)) (m : ℕ) (a : Layout P) :
    ∀ t ∈ (prepWord hpq η m a).sources.layout, FiniteDimensional ℂ t.space.carrier := by
  induction m with
  | zero => simp [prepWord, Word.sources]
  | succ m ih =>
      apply finiteDimensional_registers_sources_comp _ _ ih
      intro t ht
      change t ∈ ([⟨p, euc α⟩, ⟨q, euc β⟩] : Layout P) at ht
      rcases List.mem_cons.mp ht with rfl | ht
      · infer_instance
      · cases List.mem_singleton.mp ht
        infer_instance

namespace PartyChain
/-- Every actual source register in a monomial's prepared stack is finite-dimensional.
Source: polynomial-PEPS, `04-compression.tex:103–112` and `210–227`. -/
theorem finiteDimensional_registers_sources_prepStack {a b : Layout P}
    (M : PartyChain a b) (m : ℕ) : ∀ tail : Layout P,
    ∀ t ∈ (M.prepStack m tail).sources.layout, FiniteDimensional ℂ t.space.carrier := by
  induction M with
  | final => intro tail; simp [PartyChain.prepStack, Word.sources]
  | effect hpq α β ℓS w η rest ih =>
      intro tail
      exact finiteDimensional_registers_sources_comp (rest.prepStack m tail)
        (prepWord hpq η m _) (ih tail)
        (finiteDimensional_registers_sources_prepWord hpq η m _)
end PartyChain

/-- All actual source registers in the preparation of a gate's retained
auxiliary vector are finite-dimensional. Source: polynomial-PEPS,
`04-compression.tex:103–112` and `199–217`. -/
theorem finiteDimensional_registers_sources_prepGate {a b : Layout P}
    (m : ℕ) (L : PartyGate a b) :
    ∀ t ∈ (prepGate m L).sources.layout, FiniteDimensional ℂ t.space.carrier := by
  induction L with
  | nil => simp [prepGate, Word.sources]
  | cons q L ih =>
      exact finiteDimensional_registers_sources_comp (prepGate m L)
        (q.2.prepStack m _) ih (q.2.finiteDimensional_registers_sources_prepStack m _)

namespace EffectCircuit
/-- Every actual retained auxiliary register is finite-dimensional by its
Euclidean source construction; no assumption on private dimensions is used.
Source: polynomial-PEPS, `04-compression.tex:199–217`. -/
theorem finiteDimensional_auxiliary_registers {a b : Layout P}
    (w : EffectCircuit a b) (m : ℕ) :
    ∀ t ∈ w.auxiliary m, FiniteDimensional ℂ t.space.carrier := by
  induction w with
  | id => simp [auxiliary]
  | comp w v ihw ihv =>
      exact Layout.finiteDimensional_registers_append (w.auxiliary m) (v.auxiliary m) ihw ihv
  | localMap => simp [auxiliary]
  | @gate C _ owner a b L tail =>
      exact Layout.finiteDimensional_registers_mapOwner owner (prepGate m L).sources.layout
        (finiteDimensional_registers_sources_prepGate m L)
  | swap => simp [auxiliary]
  | frame t w ih => exact ih

/-- The physical-first discarded block contains only the constructed finite
auxiliary registers and the original finite private registers.
Source: polynomial-PEPS, `04-compression.tex:18–28` and `210–227`. -/
theorem finiteDimensional_auxiliary_private_registers {a b : Layout P}
    (w : EffectCircuit a b) (m : ℕ) (priv : Layout P)
    (hpriv : ∀ t ∈ priv, FiniteDimensional ℂ t.space.carrier) :
    ∀ t ∈ w.auxiliary m ++ priv, FiniteDimensional ℂ t.space.carrier :=
  Layout.finiteDimensional_registers_append (w.auxiliary m) priv
    (w.finiteDimensional_auxiliary_registers m) hpriv
/-- The actual discarded auxiliary and private memory is finite-dimensional.
Only the original register-wise finite-dimensionality is assumed; the auxiliary
part follows from the Euclidean source construction. Source: polynomial-PEPS,
`04-compression.tex:17–19` and `210–227`. -/
theorem finiteDimensional_auxiliary_private_mem {a b : Layout P}
    (w : EffectCircuit a b) (m : ℕ) (priv : Layout P)
    (hpriv : ∀ t ∈ priv, FiniteDimensional ℂ t.space.carrier) :
    FiniteDimensional ℂ (Mem (w.auxiliary m ++ priv)).carrier :=
  Layout.finiteDimensional_mem_of_registers _
    (w.finiteDimensional_auxiliary_private_registers m priv hpriv)
end EffectCircuit

end TNLean.PEPS.PairEffect
