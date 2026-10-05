/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.Conversion

/-!
# Local-channel protocols with a common intermediate dimension bound

The bound records every intermediate local Hilbert space, including spaces carrying
ancillas. For a family, it must be chosen before the chain length to give a uniform
physical-port communication overhead. A finite protocol having some finite bound does
not supply a bound uniform over a family of protocols.

This is a resource-refined version of `IsLocalChannelProtocol`, not a new assumption
about every witness of that unrestricted relation. Positive dimensions exclude the
zero-dimensional operator algebra, which has no density matrices.
-/

open Matrix
open scoped BigOperators

namespace QuantumCircuit

variable {N B C d e f : ℕ} [NeZero N]

/-- A native local-channel protocol whose input, output, and every intermediate local
space have positive dimension at most one common bound `B`. -/
inductive IsDimensionBoundedLocalChannelProtocol (B : ℕ) :
    {d e : ℕ} → ℕ →
    (Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ) → Prop
  /-- Both endpoints of the initial onsite operation obey the resource bound. -/
  | onsite {d e : ℕ} (Φ : OnsiteChannel d e (Fin N))
      (hd : 0 < d ∧ d ≤ B) (he : 0 < e ∧ e ≤ B) :
      IsDimensionBoundedLocalChannelProtocol B 0 Φ.map
  /-- A native pair-channel layer preserves the current local dimension. -/
  | layer {d e T : ℕ}
      {Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
        Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
      (hΨ : IsDimensionBoundedLocalChannelProtocol B T Ψ) (L : ChannelLayer e N) :
      IsDimensionBoundedLocalChannelProtocol B (T + 1) (L.map ∘ₗ Ψ)
  /-- Every new onsite output space is explicitly checked against the same bound. -/
  | onsite_comp {d e f T : ℕ}
      {Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
        Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
      (hΨ : IsDimensionBoundedLocalChannelProtocol B T Ψ)
      (Φ : OnsiteChannel e f (Fin N)) (hf : 0 < f ∧ f ≤ B) :
      IsDimensionBoundedLocalChannelProtocol B T (Φ.map ∘ₗ Ψ)

namespace IsDimensionBoundedLocalChannelProtocol

/-- Forgetting the dimension certificate gives the original native protocol. -/
theorem toIsLocalChannelProtocol {T : ℕ}
    {Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    (h : IsDimensionBoundedLocalChannelProtocol B T Ψ) : IsLocalChannelProtocol T Ψ := by
  induction h with
  | onsite Φ _ _ => exact .onsite Φ
  | layer _ L ih => exact ih.layer L
  | onsite_comp _ Φ _ ih => exact ih.onsite_comp Φ

/-- The endpoint dimensions are among the checked resources. -/
theorem dimension_bounds {T : ℕ}
    {Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    (h : IsDimensionBoundedLocalChannelProtocol B T Ψ) :
    (0 < d ∧ d ≤ B) ∧ (0 < e ∧ e ≤ B) := by
  induction h with
  | onsite _ hd he => exact ⟨hd, he⟩
  | layer _ _ ih => exact ih
  | onsite_comp _ _ hf ih => exact ⟨ih.1, hf⟩

/-- Increasing the dimension budget preserves every intermediate certificate. -/
theorem mono_bound {T : ℕ}
    {Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    (h : IsDimensionBoundedLocalChannelProtocol B T Ψ) (hBC : B ≤ C) :
    IsDimensionBoundedLocalChannelProtocol C T Ψ := by
  induction h with
  | onsite Φ hd he => exact .onsite Φ ⟨hd.1, hd.2.trans hBC⟩ ⟨he.1, he.2.trans hBC⟩
  | layer _ L ih => exact ih.layer L
  | onsite_comp _ Φ hf ih => exact ih.onsite_comp Φ ⟨hf.1, hf.2.trans hBC⟩

/-- Composing protocols with the same resource budget adds only their layer depths. -/
theorem comp {T S : ℕ}
    {Φ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    {Ψ : Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin f) (Fin N → Fin f) ℂ}
    (hΦ : IsDimensionBoundedLocalChannelProtocol B T Φ)
    (hΨ : IsDimensionBoundedLocalChannelProtocol B S Ψ) :
    IsDimensionBoundedLocalChannelProtocol B (T + S) (Ψ ∘ₗ Φ) := by
  induction hΨ with
  | onsite Ψ _ hf => exact hΦ.onsite_comp Ψ hf
  | layer _ L ih => exact ih.layer L
  | onsite_comp _ Ψ hf ih => exact ih.onsite_comp Ψ hf

end IsDimensionBoundedLocalChannelProtocol

namespace OnsiteChannel

/-- An onsite channel cannot send a positive-dimensional site to the empty space. -/
theorem output_dimension_pos (Φ : OnsiteChannel d e (Fin N)) (hd : 0 < d) : 0 < e := by
  by_contra he
  have he0 : e = 0 := Nat.eq_zero_of_not_pos he
  subst e
  have h := congrArg (fun A => A ⟨0, hd⟩ ⟨0, hd⟩) (Φ.sum_kraus 0)
  simp at h

end OnsiteChannel

/-- Every finite positive-input native protocol admits some finite dimension bound.
For a family this gives only a potentially chain-length-dependent bound; it does not
supply the uniformly quantified resource hypothesis needed for constant overhead. -/
theorem IsLocalChannelProtocol.exists_dimension_bound {T : ℕ}
    {Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    (h : IsLocalChannelProtocol T Ψ) (hd : 0 < d) :
    ∃ B, IsDimensionBoundedLocalChannelProtocol B T Ψ := by
  induction h with
  | onsite Φ =>
    exact ⟨_, .onsite Φ ⟨hd, Nat.le_max_left _ _⟩
      ⟨Φ.output_dimension_pos hd, Nat.le_max_right _ _⟩⟩
  | layer _ L ih =>
    obtain ⟨B, hB⟩ := ih
    exact ⟨B, hB.layer L⟩
  | onsite_comp _ Φ ih =>
    obtain ⟨B, hB⟩ := ih
    exact ⟨_, (hB.mono_bound (Nat.le_max_left _ _)).onsite_comp Φ
      ⟨Φ.output_dimension_pos hB.dimension_bounds.2.1, Nat.le_max_right _ _⟩⟩

end QuantumCircuit
