/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.Feedforward

/-!
# Adaptive local channel conversions

A finite adaptive protocol is a tree of local quantum operations. Onsite instruments cost no
circuit depth, their complete outcome tuple is communicated classically, and the continuation
may depend on that tuple. A layer of nearest-neighbor channels costs one unit of depth. The
depth bound holds on every branch; histories can affect all subsequent instruments and layers.
Averaging over all outcomes gives a trace-preserving completely positive map on arbitrary
input operators.

This finite adaptive model is motivated by Piroli, Styliaris and Cirac
(arXiv:2103.13367, paragraph "State transformations with QC and LOCC"). Intermediate onsite
dimensions are unrestricted and gates on enlarged sites still cost one layer. The source
instead counts gates on fixed-dimensional physical qudits with separate onsite ancillas;
no uniform-depth simulation or inclusion in the source model is proved here. Furthermore,
there is no system-size-independent bound on the number of measurement rounds. See
`docs/paper-gaps/psc21_adaptive_channel_round_scope.tex`.

## Main results

* `QuantumCircuit.IsAdaptiveChannelProtocol.isKrausCPTP` — averaged adaptive protocols
  are channels.
* `QuantumCircuit.IsAdaptiveChannelProtocol.comp` — protocols compose with additive depth.
* `QuantumCircuit.IsLocalChannelProtocol.adaptive` — deterministic local channels are included.
* `QuantumCircuit.IsAdaptiveChannelConversion.trans` — adaptive conversions compose.

## References

* Piroli, Styliaris and Cirac, arXiv:2103.13367, paragraphs "Quantum circuits and LOCC"
  and "State transformations with QC and LOCC".
-/

open Matrix
open scoped ComplexOrder

namespace QuantumCircuit

variable {N : ℕ} [NeZero N]

/-- A finite adaptive local protocol of depth at most `T`. Each onsite instrument records
its local Kraus indices and communicates them globally; subsequent operations can depend on
the full outcome history. Depth counts only nearest-neighbor layers, along the longest branch.

Motivated by arXiv:2103.13367, paragraph "State transformations with QC and LOCC". This model
allows unrestricted intermediate onsite dimensions at unit intersite gate cost. It supplies
neither a source-depth simulation nor the fixed-round bound of the source phase relation. -/
inductive IsAdaptiveChannelProtocol : {d e : ℕ} → ℕ →
    (Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ) → Prop
  /-- An onsite channel needs no nearest-neighbor layer. -/
  | onsite {d e : ℕ} (Φ : OnsiteChannel d e (Fin N)) :
      IsAdaptiveChannelProtocol 0 Φ.map
  /-- A layer before an adaptive continuation adds one to every branch depth. -/
  | layer {d e T : ℕ} (L : ChannelLayer d N)
      {Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
        Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
      (hΨ : IsAdaptiveChannelProtocol T Ψ) :
      IsAdaptiveChannelProtocol (T + 1) (Ψ ∘ₗ L.map)
  /-- Onsite measurement and classical communication are free. Every outcome has a
  continuation of depth at most the same bound, including outcomes of zero probability. -/
  | instrument {d e f T : ℕ} (Φ : OnsiteChannel d e (Fin N))
      {Ψ : ((i : Fin N) → Fin (Φ.r i)) →
        Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ →ₗ[ℂ]
          Matrix (Fin N → Fin f) (Fin N → Fin f) ℂ}
      (hΨ : ∀ J, IsAdaptiveChannelProtocol T (Ψ J)) :
      IsAdaptiveChannelProtocol T (Φ.feedforwardMap Ψ)
  /-- A protocol remains within any larger depth bound. -/
  | mono {d e T T' : ℕ}
      {Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
        Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
      (hΨ : IsAdaptiveChannelProtocol T Ψ) (hT : T ≤ T') :
      IsAdaptiveChannelProtocol T' Ψ

namespace IsAdaptiveChannelProtocol

/-- The average over the leaves of an adaptive protocol is a channel. -/
theorem isKrausCPTP {d e T : ℕ}
    {Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    (hΨ : IsAdaptiveChannelProtocol T Ψ) : IsKrausCPTP Ψ := by
  induction hΨ with
  | onsite Φ => exact Φ.map_isKrausCPTP
  | layer L _ ih => exact isKrausCPTP_comp L.map_isKrausCPTP ih
  | instrument Φ _ ih => exact Φ.feedforwardMap_isKrausCPTP _ ih
  | mono _ _ ih => exact ih

/-- Prepending an onsite operation to an adaptive protocol has zero depth cost. -/
theorem onsite_comp {d e f T : ℕ} (Φ : OnsiteChannel d e (Fin N))
    {Ψ : Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin f) (Fin N → Fin f) ℂ}
    (hΨ : IsAdaptiveChannelProtocol T Ψ) : IsAdaptiveChannelProtocol T (Ψ ∘ₗ Φ.map) := by
  rw [← Φ.feedforwardMap_const Ψ]
  exact .instrument Φ fun _ ↦ hΨ

/-- Adaptive protocols compose with additive depth. Each leaf of the first protocol is
replaced by the second protocol, so its outcomes remain part of the classical history. -/
theorem comp {d e f T₁ T₂ : ℕ}
    {Ψ₁ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    {Ψ₂ : Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin f) (Fin N → Fin f) ℂ}
    (h₁ : IsAdaptiveChannelProtocol T₁ Ψ₁) (h₂ : IsAdaptiveChannelProtocol T₂ Ψ₂) :
    IsAdaptiveChannelProtocol (T₁ + T₂) (Ψ₂ ∘ₗ Ψ₁) := by
  induction h₁ with
  | onsite Φ => simpa using h₂.onsite_comp Φ
  | @layer d e T L Ψ hΨ ih =>
    simpa only [Nat.add_right_comm, LinearMap.comp_assoc] using (ih h₂).layer L
  | instrument Φ _ ih =>
    rw [Φ.comp_feedforwardMap]
    exact .instrument Φ fun J ↦ ih J h₂
  | mono _ hT ih => exact (ih h₂).mono (Nat.add_le_add_right hT _)

/-- A single nearest-neighbor layer is an adaptive protocol of depth one. -/
theorem channelLayer {d : ℕ} (L : ChannelLayer d N) : IsAdaptiveChannelProtocol 1 L.map := by
  have h := (IsAdaptiveChannelProtocol.onsite (OnsiteChannel.id d (Fin N))).layer L
  simpa only [OnsiteChannel.id_map, LinearMap.id_comp] using h

end IsAdaptiveChannelProtocol

/-- Every deterministic local channel protocol is an adaptive protocol of the same depth. -/
theorem IsLocalChannelProtocol.adaptive {d e T : ℕ}
    {Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    (hΨ : IsLocalChannelProtocol T Ψ) : IsAdaptiveChannelProtocol T Ψ := by
  induction hΨ with
  | onsite Φ => exact .onsite Φ
  | layer _ L ih => exact ih.comp (.channelLayer L)
  | onsite_comp _ Φ ih => exact ih.comp (.onsite Φ)

/-- Exact conversion by a finite adaptive local protocol of depth at most `T`. -/
def IsAdaptiveChannelConversion {d e : ℕ} (T : ℕ)
    (ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (σ : Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ) : Prop :=
  ∃ Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ,
    IsAdaptiveChannelProtocol T Ψ ∧ Ψ ρ = σ

namespace IsAdaptiveChannelConversion

/-- The identity channel converts every input to itself. -/
theorem refl {d : ℕ} (ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) :
    IsAdaptiveChannelConversion 0 ρ ρ :=
  ⟨_, .onsite (OnsiteChannel.id d (Fin N)),
    by rw [OnsiteChannel.id_map, LinearMap.id_apply]⟩

/-- Increasing the allowed depth preserves adaptive conversion. -/
theorem mono {d e T T' : ℕ}
    {ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    {σ : Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    (h : IsAdaptiveChannelConversion T ρ σ) (hT : T ≤ T') :
    IsAdaptiveChannelConversion T' ρ σ := by
  obtain ⟨Ψ, hΨ, hρ⟩ := h
  exact ⟨Ψ, hΨ.mono hT, hρ⟩

/-- Adaptive conversions compose with additive depth. -/
theorem trans {d e f T₁ T₂ : ℕ}
    {ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    {σ : Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    {τ : Matrix (Fin N → Fin f) (Fin N → Fin f) ℂ}
    (h₁ : IsAdaptiveChannelConversion T₁ ρ σ)
    (h₂ : IsAdaptiveChannelConversion T₂ σ τ) :
    IsAdaptiveChannelConversion (T₁ + T₂) ρ τ := by
  obtain ⟨Ψ₁, hΨ₁, rfl⟩ := h₁
  obtain ⟨Ψ₂, hΨ₂, rfl⟩ := h₂
  exact ⟨_, hΨ₁.comp hΨ₂, rfl⟩

/-- Adaptive conversion preserves positive semidefiniteness and trace one. -/
theorem density {d e T : ℕ}
    {ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    {σ : Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    (h : IsAdaptiveChannelConversion T ρ σ) (hρ : ρ.PosSemidef ∧ trace ρ = 1) :
    σ.PosSemidef ∧ trace σ = 1 := by
  obtain ⟨Ψ, hΨ, rfl⟩ := h
  exact ⟨hΨ.isKrausCPTP.map_posSemidef hρ.1, (hΨ.isKrausCPTP.trace_map ρ).trans hρ.2⟩

end IsAdaptiveChannelConversion

/-- Deterministic local conversion is a special case of adaptive conversion. -/
theorem IsLocalChannelConversion.adaptive {d e T : ℕ}
    {ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    {σ : Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    (h : IsLocalChannelConversion T ρ σ) : IsAdaptiveChannelConversion T ρ σ := by
  obtain ⟨S, hS, Ψ, hΨ, hρ⟩ := h
  exact ⟨Ψ, hΨ.adaptive.mono hS, hρ⟩

end QuantumCircuit
