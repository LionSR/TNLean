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

This file formalizes three parts of this discussion.

* The commutator of two unitaries `U₁`, `U₂` acts on a vector `ψ` by the scalar `c` whenever
  `U₂ U₁ ψ = c U₁ U₂ ψ`, so its expectation value is `c ⟨ψ|ψ⟩`. With the exchange relation of
  the two truncations on `|ψ_A⟩` and `c = ω`, this is the last step of `detecZ2`.
* For an on-site symmetry `u^{⊗N}` with `u† u = 1`, the truncations to any two sets of sites
  have the identity as their commutator, and the expectation value is `⟨ψ|ψ⟩`, which is `1` on
  a normalized state.

* The value of the detector depends on the choice of truncation. For the on-site symmetry
  `X^{⊗N}`, the truncations `Z_j X^{⊗[i,j]}`, which are circuit truncations of `X^{⊗N}` in the
  sense of the source, have commutator `-1` on overlapping intervals, although the anomaly is
  trivial. So `detecZ2` is false for an arbitrary circuit truncation; this is recorded in
  `docs/paper-gaps/gs24_truncation_detector_endpoint_dependence.tex`.

The detection for unitaries acting on `|ψ_A⟩` as domain-wall strings is
`TNLean/MPS/Symmetry/MPOSymmetry/DomainWallDetector.lean`. The general-group detection `detectG`
(lines 2108--2114) is not formalized.

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
* `Matrix.groupCommutator_dressed_onSiteTruncation_pauliX`,
  `Matrix.star_dotProduct_groupCommutator_dressed_onSiteTruncation_pauliX`: truncations of
  `X^{⊗N}` dressed by `Z` at one endpoint have commutator `-1`.

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

/-! ### Truncations dressed at one endpoint -/

/-- The Pauli matrix `X`. -/
local notation "σX" => !![(0 : ℂ), 1; 1, 0]

/-- The Pauli matrix `Z`. -/
local notation "σZ" => !![(1 : ℂ), 0; 0, -1]

/-- A truncation of an on-site symmetry dressed by a unitary `w` at one site is still unitary. -/
theorem dressed_onSiteTruncation_conjTranspose_mul_self {u w : Matrix ι ι ℂ} (hu : uᴴ * u = 1)
    (hw : wᴴ * w = 1) (S : Finset (Fin N)) (j : Fin N) :
    (onSiteTruncation w {j} * onSiteTruncation u S)ᴴ *
        (onSiteTruncation w {j} * onSiteTruncation u S) = 1 := by
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (onSiteTruncation w {j})ᴴ,
    onSiteTruncation_conjTranspose_mul_self hw, Matrix.one_mul,
    onSiteTruncation_conjTranspose_mul_self hu]

/-- **The anomaly detector depends on the endpoints of the truncations.** For the on-site
symmetry `X^{⊗N}`, whose anomaly is trivial, take the truncations
`U₁ = Z_{j₁} X^{S₁}` and `U₂ = Z_{j₂} X^{S₂}`, each dressed by the Pauli matrix `Z` at one
endpoint. If `j₁ ∈ S₂`, `j₂ ∉ S₁` and `j₁ ≠ j₂`, then `U₂† U₁† U₂ U₁ = -1`.

These are circuit truncations in the sense of arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex`
lines 2081--2087. The symmetry `X^{⊗N}` is the depth-two circuit whose first layer applies
`X ⊗ ZX` to the pairs of sites `(2k, 2k+1)` and whose second layer applies `Z` to every odd site,
a gate on the pair `(2k+1, 2k+2)`; indeed `Z · ZX = X`. Dropping the gates that are not
contained in an interval `[i, j]` with `i` even and `j` odd keeps both factors on every odd
site of `[i, j]` except `j`, which keeps only `ZX`, so the truncation is `Z_j X^{⊗[i,j]}`; this
identification of the circuit truncation is not formalized.
For `i₂ < i₁ < j₁ < j₂` of these parities the hypotheses hold, and the expectation value of the
commutator on every normalized state is `-1`, not the trivial anomaly `1`
(`star_dotProduct_groupCommutator_dressed_onSiteTruncation_pauliX`).

Project result: a counterexample to arXiv:2405.00439, `detecZ2`, lines 2097--2102, read for an
arbitrary circuit truncation; documented in
`docs/paper-gaps/gs24_truncation_detector_endpoint_dependence.tex`. -/
theorem groupCommutator_dressed_onSiteTruncation_pauliX {S₁ S₂ : Finset (Fin N)} {j₁ j₂ : Fin N}
    (hj₁ : j₁ ∈ S₂) (hj₂ : j₂ ∉ S₁) (hj : j₁ ≠ j₂) :
    groupCommutator (onSiteTruncation σZ {j₁} * onSiteTruncation σX S₁)
        (onSiteTruncation σZ {j₂} * onSiteTruncation σX S₂) = -1 := by
  simp only [groupCommutator, onSiteTruncation, finKronecker_mul, finKronecker_conjTranspose]
  rw [← neg_one_smul ℂ (1 : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ),
    ← finKronecker_ite_smul_one (α := fun _ ↦ Fin 2) j₁]
  congr 1
  funext k
  simp only [Finset.mem_singleton]
  by_cases hk₁ : k = j₁
  · subst hk₁
    simp only [hj₁, hj, ite_true, ite_false]
    split_ifs <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  · by_cases hk₂ : k = j₂
    · subst hk₂
      simp only [hj₂, hk₁, ite_true, ite_false]
      split_ifs <;> ext a b <;> fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two]
    · simp only [hk₁, hk₂, ite_false]
      split_ifs <;> ext a b <;> fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **The detector of the dressed truncations is `-1`** (arXiv:2405.00439, `detecZ2`,
`Papers/2405.00439/MPU-DW.tex` lines 2097--2102): for the truncations of
`groupCommutator_dressed_onSiteTruncation_pauliX` and every normalized state `ψ`,
`⟨ψ| U₂† U₁† U₂ U₁ |ψ⟩ = -1`, although the on-site symmetry `X^{⊗N}` has trivial anomaly.

Project result: documented in
`docs/paper-gaps/gs24_truncation_detector_endpoint_dependence.tex`. -/
theorem star_dotProduct_groupCommutator_dressed_onSiteTruncation_pauliX {S₁ S₂ : Finset (Fin N)}
    {j₁ j₂ : Fin N} (hj₁ : j₁ ∈ S₂) (hj₂ : j₂ ∉ S₁) (hj : j₁ ≠ j₂)
    {ψ : (Fin N → Fin 2) → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    star ψ ⬝ᵥ (groupCommutator (onSiteTruncation σZ {j₁} * onSiteTruncation σX S₁)
        (onSiteTruncation σZ {j₂} * onSiteTruncation σX S₂) *ᵥ ψ) = -1 := by
  rw [groupCommutator_dressed_onSiteTruncation_pauliX hj₁ hj₂ hj, neg_mulVec, one_mulVec,
    dotProduct_neg, hψ]

end OnSite

end Matrix
