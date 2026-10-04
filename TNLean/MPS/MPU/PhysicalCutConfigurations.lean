/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.MinimalCutRepresentationCuts

/-!
# Physical configurations at operator cuts

Sitewise pairing identifies an operator coefficient configuration with its
output and input configurations. Splitting these configurations at a cut
commutes with pairing. These equivalences preserve the coefficients when
an open-boundary representation is regrouped as an operator factorization.

Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

open Matrix

namespace MPUCircuit

/-- Pairing the physical output and input letters site by site.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def pairPhysicalConfig {ι : Type*} {d : ℕ} (x y : ι → Fin d) : ι → Fin (d * d) :=
  fun s ↦ finProdFinEquiv (x s, y s)

/-- Sitewise pairing identifies a configuration of paired letters with
a pair of physical output and input configurations.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def physicalPairConfigEquiv (ι : Type*) (d : ℕ) :
    (ι → Fin (d * d)) ≃ ((ι → Fin d) × (ι → Fin d)) where
  toFun σ := (fun s ↦ (finProdFinEquiv.symm (σ s)).1,
    fun s ↦ (finProdFinEquiv.symm (σ s)).2)
  invFun xy := pairPhysicalConfig xy.1 xy.2
  left_inv σ := by
    funext s
    exact finProdFinEquiv.apply_symm_apply (σ s)
  right_inv xy := by
    apply Prod.ext <;> funext s <;> simp [pairPhysicalConfig]

/-- A physical configuration is equivalent to its prefix and suffix
configurations at any cut.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def physicalCutConfigEquiv (d N k : ℕ) : (Fin N → Fin d) ≃
    (MPSPreparation.CutPrefixConfig d N k × MPSPreparation.CutSuffixConfig d N k) where
  toFun σ := (MPSPreparation.cutPrefixRestriction σ k,
    MPSPreparation.cutSuffixRestriction σ k)
  invFun uv := fun s ↦ if h : s.val < k then uv.1 ⟨s, h⟩
    else uv.2 ⟨s, Nat.le_of_not_lt h⟩
  left_inv σ := by
    funext s
    change (if _h : s.val < k then σ s else σ s) = σ s
    split_ifs <;> rfl
  right_inv uv := by
    apply Prod.ext
    · funext s
      simp [MPSPreparation.cutPrefixRestriction, s.2]
    · funext s
      simp [MPSPreparation.cutSuffixRestriction, Nat.not_lt_of_ge s.2]

/-- Splitting a physical configuration and pairing its two letters
commute. This preserves the operator input and output coordinates at a cut.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem physicalCutConfigEquiv_pair {d N k : ℕ}
    (x₁ y₁ : MPSPreparation.CutPrefixConfig d N k)
    (x₂ y₂ : MPSPreparation.CutSuffixConfig d N k) :
    (physicalCutConfigEquiv (d * d) N k).symm
      (pairPhysicalConfig x₁ y₁, pairPhysicalConfig x₂ y₂) =
      pairPhysicalConfig ((physicalCutConfigEquiv d N k).symm (x₁, x₂))
        ((physicalCutConfigEquiv d N k).symm (y₁, y₂)) := by
  funext s
  change (if h : s.val < k then finProdFinEquiv (x₁ ⟨s, h⟩, y₁ ⟨s, h⟩)
    else finProdFinEquiv (x₂ ⟨s, Nat.le_of_not_lt h⟩, y₂ ⟨s, Nat.le_of_not_lt h⟩)) = _
  by_cases h : s.val < k <;> simp [physicalCutConfigEquiv, pairPhysicalConfig, h]

end MPUCircuit
