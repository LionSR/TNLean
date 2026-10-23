/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.SchmidtDiagonalChain
import TNLean.MPS.AreaLaw.Hastings.ProjectorFactorization

/-!
# Hastings' Lemma 3 on the chain

Lemma 3 of Hastings, *An area law for one-dimensional quantum systems* (arXiv:0705.2024v4,
`References/0705.2024/law16.tex`, lines 627–646, eq. `fwdback`), bounds the correlation between
an operator `A` supported away from the `l` sites on either side of a cut and an operator `B_L`
that is diagonal in the left Schmidt vectors of the ground state `Ψ₀`:
`⟨Ψ₀, A B_L Ψ₀⟩ − ⟨Ψ₀, A Ψ₀⟩⟨Ψ₀, B_L Ψ₀⟩ ≤ 3 √(2ε(l)) + ε(l)` with `ε(l) = C₁ e^{-l/ξ'}`.
Its proof uses the Hamiltonian only through the positive operators `O_B`, `O_L`, `O_R` of
Lemma 1.

This file discharges the factorization hypothesis of `norm_inner_mul_sub_le_of_factorization` with
the positive form of Lemma 1, `exists_projectorFactorization_posSemidef`. The result is a
quantitatively restricted Lemma 3 on Hastings' own hypotheses: a chain Hamiltonian of finite range
and finite interaction strength with a unique gapped ground state. The constant `C₁` depends on the
range, the interaction strength, the gap and `ξ'`, and not on the length of the chain, the cut, the
Schmidt data or `A`. The bound is on the modulus of the difference, which is stronger than the
printed one-sided bound.

**Local fix (positivity rate):** the proof of Lemma 3 needs `O_B` positive, and the positive
form of Lemma 1 decays at half its rate, so eq. `fwdback` holds with `ε(l) = C₁ e^{-l/ξ'}` for
every `ξ' > 12ξ` rather than `ξ' > 6ξ`. Documented in
`docs/paper-gaps/hastings07_lemma1_positivity_rate.tex`.

**Scope restriction (quantitative bounds):** `exists_norm_inner_mul_sub_le` inherits the
quantitative restrictions of the formalized Lemma 1. Its length is `ξ = 8 max(2v₀/ΔE, 1)`,
with `v₀` the velocity of the chain localization estimate, which is not shown to be the
source's `max(2v/ΔE, ξ_C)` (lines 96–112, 139–142); the printed `ξ' = 6ξ` is not reached; and
`C₁` is not shown to be bounded by a polynomial in `ξ` (lines 258–262). Documented in
`docs/paper-gaps/hastings07_lemma1_decay_length.tex` and
`docs/paper-gaps/hastings07_gaussian_average_exponent.tex`.

## Main results

* `Matrix.IsStarProjection.posSemidef`: an orthogonal projection is positive semidefinite.
* `exists_norm_inner_mul_sub_le`: Lemma 3.
-/

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator ComplexOrder

theorem IsStarProjection.posSemidef {n : Type*} [Fintype n] {P : Matrix n n ℂ}
    (hP : IsStarProjection P) : P.PosSemidef := by
  have h : P = Pᴴ * P := by
    rw [← star_eq_conjTranspose, hP.isSelfAdjoint.star_eq, hP.isIdempotentElem.eq]
  rw [h]
  exact posSemidef_conjTranspose_mul_self P

namespace TNLean.MPS.AreaLaw

open Hastings

local notation "T" => toEuclideanCLM (𝕜 := ℂ)

/-- **Hastings' Lemma 3 (eq. `fwdback`).** Let `H` be a chain Hamiltonian of range `R` and term
norm at most `J ≥ 0` with a unique ground state `Ω` and gap `ΔE > 0`, and let `ξ' > 12ξ` with
`ξ = lemmaOneLength R J ΔE`. There is a constant `C₁ ≥ 0`, depending only on `R`, `J`, `ΔE` and
`ξ'`, with the following property. For every such chain of `L` sites, every cut `j` and length
`l`, every Schmidt decomposition `Ω = ∑ a_α ψ_L(α) ⊗ ψ_R(α)` across the cut with orthonormal
`ψ_L`, `ψ_R`, every `B_L = ∑ O(α) |ψ_L(α)⟩⟨ψ_L(α)| ⊗ 1` with `|O(α)| ≤ 1`, and every `A` with
`‖A‖ ≤ 1` supported away from the sites `j − l, …, j + l − 1`,
`|⟨Ω, A B_L Ω⟩ − ⟨Ω, A Ω⟩⟨Ω, B_L Ω⟩| ≤ 3 √(2ε) + ε` with `ε = C₁ e^{-l/ξ'}`.
Hastings, arXiv:0705.2024v4, Lemma 3, lines 627–646, with the decay length of the module
docstring. -/
theorem exists_norm_inner_mul_sub_le (R : ℕ) {J ΔE : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < ΔE) {ξ' : ℝ}
    (hξ' : 12 * lemmaOneLength R J ΔE < ξ') :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ {L q : ℕ} [NeZero q] (h : ChainHamiltonian L q R J) {E₀ : ℝ}
      {Ω : EuclideanSpace ℂ (Fin L → Fin q)}, IsGappedGroundState h.operator E₀ Ω ΔE →
      ∀ (j l : ℕ) {κ : Type*} [Fintype κ] (a : κ → ℂ)
        {ψL : κ → EuclideanSpace ℂ (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L j))}
        {ψR : κ → EuclideanSpace ℂ ((v : {v // v ∉ leftBlock L j}) → Fin q)},
        Orthonormal ℂ ψL → Orthonormal ℂ ψR →
        WithLp.ofLp (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L j) Ω) =
          (fun p ↦ ∑ α, a α * (WithLp.ofLp (ψL α) p.1 * WithLp.ofLp (ψR α) p.2)) →
        ∀ {O : κ → ℂ}, (∀ α, ‖O α‖ ≤ 1) →
        ∀ {A : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} {SA : Finset (Fin L)},
        Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) A SA →
        Disjoint SA (interval L (j - l) (j + l)) → ‖A‖ ≤ 1 →
        ‖⟪Ω, T (A * Entropy.localLift (leftBlock L j) (schmidtDiagonal O ψL)) Ω⟫_ℂ -
            ⟪Ω, T A Ω⟫_ℂ *
              ⟪Ω, T (Entropy.localLift (leftBlock L j) (schmidtDiagonal O ψL)) Ω⟫_ℂ‖ ≤
          3 * Real.sqrt (2 * (C₁ * Real.exp (-(l / ξ')))) + C₁ * Real.exp (-(l / ξ')) := by
  obtain ⟨C, hC, hF⟩ :=
    exists_projectorFactorization_posSemidef R hJ hΔ (ξ' := ξ' / 2) (by linarith)
  refine ⟨C, hC, ?_⟩
  intro L q _ h E₀ Ω hgs j l κ _ a ψL ψR hψL hψR hdec O hO A SA hA hSA hA1
  obtain ⟨OB, OL, OR, hOB, hOL, hOR, -, hOB1, hsB, hsL, hsR, herr⟩ := hF h hgs j l
  have hrate : C * Real.exp (-(l / (2 * (ξ' / 2)))) = C * Real.exp (-(l / ξ')) := by
    rw [mul_div_cancel₀ _ two_ne_zero]
  rw [hrate] at herr
  exact norm_inner_mul_sub_le_of_factorization hgs.1 a hψL hψR hdec hO hA hSA hA1
    ⟨OB, OL, OR, _, _, _, hOB, hOL.posSemidef, hOR.posSemidef, hOB1, hOL.norm_le, hOR.norm_le,
      hsB, subset_rfl, hsL, subset_rfl, hsR, disjoint_compl_left, herr⟩

end TNLean.MPS.AreaLaw
