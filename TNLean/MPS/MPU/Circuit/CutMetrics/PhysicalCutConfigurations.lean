/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.VaryingBond.MinimalCutRepresentationCuts

/-!
# Physical configurations at operator cuts

Sitewise pairing identifies an operator coefficient configuration with its
output and input configurations. Splitting these configurations at a cut
along `ManyBody.cutEquiv` commutes with pairing. These equivalences preserve the coefficients when
an open-boundary representation is regrouped as an operator factorization.

Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

open Matrix

open ManyBody (interval RegionConfig ComplConfig cutEquiv cutEquiv_symm_apply_mem
  cutEquiv_symm_apply_not_mem)

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

/-- Splitting a physical configuration at the cut after `k` sites and pairing its two letters
commute. This preserves the operator input and output coordinates at a cut.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutEquiv_symm_pairPhysicalConfig {d N k : ℕ}
    (x₁ y₁ : RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k))
    (x₂ y₂ : ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k)) :
    (cutEquiv (fun _ : Fin N ↦ Fin (d * d)) (interval N 0 k)).symm
      (pairPhysicalConfig x₁ y₁, pairPhysicalConfig x₂ y₂) =
      pairPhysicalConfig ((cutEquiv (fun _ : Fin N ↦ Fin d) (interval N 0 k)).symm (x₁, x₂))
        ((cutEquiv (fun _ : Fin N ↦ Fin d) (interval N 0 k)).symm (y₁, y₂)) := by
  funext s
  by_cases h : s ∈ interval N 0 k
  · simp only [pairPhysicalConfig, cutEquiv_symm_apply_mem _ _ h]
  · simp only [pairPhysicalConfig, cutEquiv_symm_apply_not_mem _ _ h]

end MPUCircuit
