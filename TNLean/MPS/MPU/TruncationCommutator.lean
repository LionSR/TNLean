/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinKronecker

/-!
# The commutator of two truncated symmetries and its expectation value

Garre-Rubio and Schuch (arXiv:2405.00439, Section V, `Papers/2405.00439/MPU-DW.tex` lines
2069--2118) detect the anomaly of a matrix product unitary symmetry by truncating it to two
intervals `[i₁, j₁]` and `[i₂, j₂]` with `i₂ < i₁ < j₁ < j₂`. The expectation value of the group
commutator of the two truncations `U^{[i₁,j₁]}` and `U^{[i₂,j₂]}` on a ground state,

`⟨ψ_A| (U^{[i₂,j₂]})† (U^{[i₁,j₁]})† U^{[i₂,j₂]} U^{[i₁,j₁]} |ψ_A⟩ = ω`  (`detecZ2`),

"precisely measures the commutator" of the two truncations (line 2102). For on-site symmetries
`U = ⊗_{i ∈ Λ} u`, the truncation is `U^{[a,b]} = ⊗_{i ∈ [a,b]} u`, the commutator is the
identity and its expectation value is `+1` (lines 2104--2106).

This file formalizes two parts of this discussion.

* The commutator of two unitaries `U₁`, `U₂` acts on a vector `ψ` by the scalar `c` whenever
  `U₂ U₁ ψ = c U₁ U₂ ψ`, so its expectation value is `c ⟨ψ|ψ⟩`. With the exchange relation of
  the two truncations on `|ψ_A⟩` and `c = ω`, this is the last step of `detecZ2`.
* For an on-site symmetry `u^{⊗N}` with `u† u = 1`, the truncations to any two sets of sites
  have the identity as their commutator, and the expectation value is `⟨ψ|ψ⟩`, which is `1` on
  a normalized state.

The exchange relation `U^{[i₂,j₂]} U^{[i₁,j₁]} |ψ_A⟩ = ω U^{[i₁,j₁]} U^{[i₂,j₂]} |ψ_A⟩` of two
truncations of an anomalous matrix product unitary, and the general-group detection
`detectG` (lines 2108--2114), are not formalized here.

## Main definitions

* `Matrix.groupCommutator`: the operator `U₂† U₁† U₂ U₁`.
* `Matrix.onSiteTruncation`: the truncation `⊗_{i ∈ S} u` of an on-site symmetry to a set of
  sites `S`.

## Main results

* `Matrix.groupCommutator_mulVec_eq_smul`: the commutator acts on `ψ` by `c` when
  `U₂ U₁ ψ = c U₁ U₂ ψ`.
* `Matrix.star_dotProduct_groupCommutator_mulVec`: the expectation value of the commutator is
  `c ⟨ψ|ψ⟩`.
* `Matrix.groupCommutator_onSiteTruncation`: the commutator of two truncations of an on-site
  symmetry is the identity.
* `Matrix.star_dotProduct_groupCommutator_onSiteTruncation_mulVec`: its expectation value on a
  normalized state is `1`.

## References
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- Garre-Rubio, Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
-/

open scoped Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The group commutator** `U₂† U₁† U₂ U₁` of two operators, the operator whose expectation
value detects the anomaly in arXiv:2405.00439, `detecZ2`, `Papers/2405.00439/MPU-DW.tex`
lines 2097--2102, with `U₁ = U^{[i₁,j₁]}` and `U₂ = U^{[i₂,j₂]}`. -/
def groupCommutator (U₁ U₂ : Matrix n n ℂ) : Matrix n n ℂ :=
  U₂ᴴ * U₁ᴴ * U₂ * U₁

/-- **The commutator of two unitaries acts by the exchange phase.** If `U₁† U₁ = 1`,
`U₂† U₂ = 1` and `U₂ U₁ ψ = c U₁ U₂ ψ`, then `U₂† U₁† U₂ U₁ ψ = c ψ`.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 2097--2102 (the expectation
value of the commutator "precisely measures the commutator between `U^{[i₁,j₁]}` and
`U^{[i₂,j₂]}`"). -/
theorem groupCommutator_mulVec_eq_smul {U₁ U₂ : Matrix n n ℂ} (hU₁ : U₁ᴴ * U₁ = 1)
    (hU₂ : U₂ᴴ * U₂ = 1) {ψ : n → ℂ} {c : ℂ} (h : U₂ *ᵥ (U₁ *ᵥ ψ) = c • (U₁ *ᵥ (U₂ *ᵥ ψ))) :
    groupCommutator U₁ U₂ *ᵥ ψ = c • ψ := by
  have hc : groupCommutator U₁ U₂ *ᵥ ψ = U₂ᴴ *ᵥ (U₁ᴴ *ᵥ (U₂ *ᵥ (U₁ *ᵥ ψ))) := by
    simp only [groupCommutator, mulVec_mulVec, Matrix.mul_assoc]
  rw [hc, h, mulVec_smul, mulVec_smul, mulVec_mulVec _ U₁ᴴ U₁, hU₁, one_mulVec,
    mulVec_mulVec _ U₂ᴴ U₂, hU₂, one_mulVec]

/-- **The expectation value of the commutator** (arXiv:2405.00439, `detecZ2`,
`Papers/2405.00439/MPU-DW.tex` lines 2097--2102): if `U₁`, `U₂` are unitary and
`U₂ U₁ ψ = c U₁ U₂ ψ`, then `⟨ψ| U₂† U₁† U₂ U₁ |ψ⟩ = c ⟨ψ|ψ⟩`. -/
theorem star_dotProduct_groupCommutator_mulVec {U₁ U₂ : Matrix n n ℂ} (hU₁ : U₁ᴴ * U₁ = 1)
    (hU₂ : U₂ᴴ * U₂ = 1) {ψ : n → ℂ} {c : ℂ} (h : U₂ *ᵥ (U₁ *ᵥ ψ) = c • (U₁ *ᵥ (U₂ *ᵥ ψ))) :
    star ψ ⬝ᵥ (groupCommutator U₁ U₂ *ᵥ ψ) = c * (star ψ ⬝ᵥ ψ) := by
  rw [groupCommutator_mulVec_eq_smul hU₁ hU₂ h, dotProduct_smul, smul_eq_mul]

section OnSite

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- **The truncation of an on-site symmetry** `⊗_{i ∈ S} u` to a set `S` of sites of a chain of
`N` sites: `u` on the sites of `S` and the identity elsewhere.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 2104--2105 (truncating
`U = ⊗_{i ∈ Λ} u^{[i]}` gives `U^{[a,b]} = ⊗_{i ∈ [a,b]} u^{[i]}`). -/
noncomputable def onSiteTruncation (u : Matrix ι ι ℂ) (S : Finset (Fin N)) :
    Matrix (Fin N → ι) (Fin N → ι) ℂ :=
  finKronecker fun k ↦ if k ∈ S then u else 1

/-- The truncation of an on-site symmetry to all sites is the symmetry `u^{⊗N}`. -/
theorem onSiteTruncation_univ (u : Matrix ι ι ℂ) :
    onSiteTruncation u (Finset.univ : Finset (Fin N)) = finKronecker fun _ : Fin N ↦ u := by
  simp [onSiteTruncation]

/-- A truncation of an on-site symmetry with `u† u = 1` satisfies the same relation. -/
theorem onSiteTruncation_conjTranspose_mul_self {u : Matrix ι ι ℂ} (hu : uᴴ * u = 1)
    (S : Finset (Fin N)) : (onSiteTruncation u S)ᴴ * onSiteTruncation u S = 1 := by
  rw [onSiteTruncation, finKronecker_conjTranspose, finKronecker_mul]
  convert finKronecker_one (α := fun _ : Fin N ↦ ι) using 2
  funext k
  split_ifs <;> simp [hu]

/-- **Truncations of an on-site symmetry commute up to the identity** (arXiv:2405.00439,
`Papers/2405.00439/MPU-DW.tex` lines 2104--2106): for `u† u = 1` and any two sets of sites,
`(U^{S₂})† (U^{S₁})† U^{S₂} U^{S₁} = 1`. On every site the four factors are powers of `u`
and `u†`, and they cancel. -/
theorem groupCommutator_onSiteTruncation {u : Matrix ι ι ℂ} (hu : uᴴ * u = 1)
    (S₁ S₂ : Finset (Fin N)) :
    groupCommutator (onSiteTruncation u S₁) (onSiteTruncation u S₂) = 1 := by
  rw [groupCommutator, onSiteTruncation, onSiteTruncation, finKronecker_conjTranspose,
    finKronecker_conjTranspose, finKronecker_mul, finKronecker_mul, finKronecker_mul]
  convert finKronecker_one (α := fun _ : Fin N ↦ ι) using 2
  funext k
  split_ifs <;> simp [hu, Matrix.mul_assoc]

/-- **The anomaly detector of an on-site symmetry is one** (arXiv:2405.00439,
`Papers/2405.00439/MPU-DW.tex` lines 2104--2106): for `u† u = 1`, any two sets of sites and a
normalized state `ψ`, `⟨ψ| (U^{S₂})† (U^{S₁})† U^{S₂} U^{S₁} |ψ⟩ = 1`, in agreement with the
trivial anomaly `ω = 1` of on-site symmetries. -/
theorem star_dotProduct_groupCommutator_onSiteTruncation_mulVec {u : Matrix ι ι ℂ}
    (hu : uᴴ * u = 1) (S₁ S₂ : Finset (Fin N)) {ψ : (Fin N → ι) → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    star ψ ⬝ᵥ (groupCommutator (onSiteTruncation u S₁) (onSiteTruncation u S₂) *ᵥ ψ) = 1 := by
  rw [groupCommutator_onSiteTruncation hu, one_mulVec, hψ]

end OnSite

end Matrix
