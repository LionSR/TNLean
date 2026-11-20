/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.TheoremStatements
import TNLean.PEPS.AreaLaw.FrustrationFree.RangeProjection
import QICLean.ManyBody.Hamiltonian.FrustrationFree

/-!
# Frustration-free gapped Hamiltonians on planar domains

The model of the frustration-free area-law note, `eq:model`: on a finite domain `Λ ⊂ ℤ²` with
local dimension `q`, one term `h_X` for each support `X` of graph diameter at most `R`, with

`0 ≤ h_X ≤ J`, `h_X Ω = 0`, `‖Ω‖ = 1`, `Δ (1 - |Ω⟩⟨Ω|) ≤ H = ∑_X h_X`.

The goal of the note, `eq:goal`, is the uniform bound `S_Ω(A) ≤ C(q, R, J, Δ) |∂_Λ A|`. This
module states the model and the goal, and shows that the model is a gapped Hamiltonian with
unique ground vector `Ω` at energy zero, so that the goal is a special case of the general
Theorem 1.1 (`UniformAreaLaw.frustrationFreeAreaLaw`). The point of the note is a shorter proof
of the special case, assembled in later modules of this directory.

## Main definitions

* `TNLean.PEPS.AreaLaw.FrustrationFree.IsFrustrationFreeGapped`: the model `eq:model`.
* `TNLean.PEPS.AreaLaw.FrustrationFree.FrustrationFreeAreaLaw`: the goal `eq:goal`.

## Main statements

* `IsFrustrationFreeGapped.isGapped`, `IsFrustrationFreeGapped.groundSpace_eq`: the model has
  gap `Δ` at energy zero and ground space `span {Ω}`.
* `IsFrustrationFreeGapped.norm_term_le`: `‖h_X‖ ≤ J`.
* `IsFrustrationFreeGapped.smul_sub_le_sum_supportProj`: the range projections of the terms keep
  the gap, `(Δ/J) (1 - P) ≤ ∑_X Π_{h_X}`.
* `UniformAreaLaw.frustrationFreeAreaLaw`: the general area law implies the goal.

## References

* Reading note *Entanglement across a cut in two-dimensional frustration-free ground states*,
  November 18, 2026, `docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`,
  "Setting", `eq:model` and `eq:goal`.
* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Theorem 1.1 (`00-introduction.tex`, lines 39–53).
-/

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open TNLean.Lattice
open ManyBody (IsGapped groundSpace PlaneInteraction)

namespace TNLean.PEPS.AreaLaw.FrustrationFree

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ}

/-- **The frustration-free model** (`eq:model` of the frustration-free area-law note,
`docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`, "Setting"): every term
satisfies `0 ≤ h_X ≤ J`, `Ω` is a unit vector, and the Hamiltonian is gapped at energy zero with
gap `Δ` and ground space the line through `Ω`. The terms then annihilate `Ω`
(`mulVec_eq_zero`), the interaction is frustration free in the sense of
`ManyBody.Interaction.IsFrustrationFree` (`isFrustrationFree`), and for `Δ > 0` these are
exactly the conditions `0 ≤ h_X ≤ J`, `h_X Ω = 0`, `‖Ω‖ = 1`, `H ≥ Δ (1 - |Ω⟩⟨Ω|)` of the note
(`iff_model`). -/
structure IsFrustrationFreeGapped (h : PlaneInteraction Λ q R) (J Δ : ℝ) (Ω : StateSpace Λ q) :
    Prop where
  /-- Every term is positive semidefinite. -/
  posSemidef : ∀ X, (h.term X).PosSemidef
  /-- Every term is at most `J`. -/
  le_bound : ∀ X, h.term X ≤ J • (1 : Matrix (Configuration Λ q) (Configuration Λ q) ℂ)
  /-- `Ω` is a unit vector. -/
  norm_eq_one : ‖Ω‖ = 1
  /-- The Hamiltonian is gapped at energy zero with gap `Δ`. -/
  isGapped : IsGapped h.hamiltonian 0 Δ
  /-- The ground space at energy zero is the line through `Ω`. -/
  groundSpace_eq : groundSpace h.hamiltonian 0 = Submodule.span ℂ {Ω}

/-- **The frustration-free area law** (`eq:goal` of the frustration-free area-law note): for
`q ≥ 1`, `R`, and `J, Δ > 0` there is a constant `C`, chosen before the domain, the Hamiltonian
and the cut, with `S_Ω(A) ≤ C |∂_Λ A|` for every instance of `eq:model`. -/
def FrustrationFreeAreaLaw : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∀ R : ℕ, ∀ J Δ : ℝ, 0 < J → 0 < Δ →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ Λ : Finset (ℤ × ℤ), ∀ h : PlaneInteraction Λ q R, ∀ Ω : StateSpace Λ q,
        IsFrustrationFreeGapped h J Δ Ω →
          ∀ A : Finset (Site Λ), ManyBody.regionEntropy Ω A ≤ C * (edgeBoundary Λ A).card

namespace IsFrustrationFreeGapped

variable {h : PlaneInteraction Λ q R} {J Δ : ℝ} {Ω : StateSpace Λ q}

/-- The terms are Hermitian. -/
theorem isHermitian (hff : IsFrustrationFreeGapped h J Δ Ω) (X) : (h.term X).IsHermitian :=
  (hff.posSemidef X).isHermitian

/-- The Hamiltonian annihilates `Ω`. -/
theorem hamiltonian_mulVec_eq_zero (hff : IsFrustrationFreeGapped h J Δ Ω) :
    h.hamiltonian *ᵥ WithLp.ofLp Ω = 0 := by
  have hmem : Ω ∈ groundSpace h.hamiltonian 0 :=
    hff.groundSpace_eq ▸ Submodule.mem_span_singleton_self Ω
  simpa using ManyBody.mem_groundSpace_iff_mulVec.mp hmem

/-- Every term annihilates `Ω`, since the terms are positive and their sum annihilates `Ω`
(`ManyBody.Interaction.hamiltonian_mulVec_eq_zero_iff`). -/
theorem mulVec_eq_zero (hff : IsFrustrationFreeGapped h J Δ Ω) (X) :
    h.term X *ᵥ WithLp.ofLp Ω = 0 :=
  (ManyBody.Interaction.hamiltonian_mulVec_eq_zero_iff hff.posSemidef).mp
    hff.hamiltonian_mulVec_eq_zero X

/-- The model is a frustration-free interaction: `Ω` is a common ground vector of the terms,
all at energy zero. -/
theorem isFrustrationFree (hff : IsFrustrationFreeGapped h J Δ Ω) : h.IsFrustrationFree := by
  refine ManyBody.Interaction.isFrustrationFree_of_groundSpace_hamiltonian_zero_ne_bot
    hff.posSemidef ?_
  rw [hff.groundSpace_eq, Ne, Submodule.span_singleton_eq_bot]
  intro h0
  have h1 := hff.norm_eq_one
  simp [h0] at h1

/-- The gap inequality `H ≥ Δ (1 - |Ω⟩⟨Ω|)` of the note, for `Δ > 0`. -/
theorem gap (hff : IsFrustrationFreeGapped h J Δ Ω) (hΔ : 0 < Δ) :
    (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤ h.hamiltonian := by
  have hH : h.hamiltonian.IsHermitian :=
    ManyBody.Interaction.isHermitian_hamiltonian hff.isHermitian
  obtain ⟨-, -, hpsd⟩ := (ManyBody.isGapped_and_groundSpace_eq_span_iff (H := h.hamiltonian)
    (E₀ := 0) hΔ Ω).mpr ⟨hH, hff.norm_eq_one, hff.isGapped, hff.groundSpace_eq⟩
  rw [Matrix.le_iff]
  simpa using hpsd

/-- **Faithfulness of the model.** For `Δ > 0` the model is exactly `eq:model` of the note:
`0 ≤ h_X ≤ J`, `h_X Ω = 0`, `‖Ω‖ = 1` and `H ≥ Δ (1 - |Ω⟩⟨Ω|)`. Source:
`docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`, "Setting". -/
theorem iff_model (hΔ : 0 < Δ) :
    IsFrustrationFreeGapped h J Δ Ω ↔
      (∀ X, (h.term X).PosSemidef) ∧
        (∀ X, h.term X ≤ J • (1 : Matrix (Configuration Λ q) (Configuration Λ q) ℂ)) ∧
        (∀ X, h.term X *ᵥ WithLp.ofLp Ω = 0) ∧ ‖Ω‖ = 1 ∧
        (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤ h.hamiltonian := by
  refine ⟨fun hff ↦ ⟨hff.posSemidef, hff.le_bound, hff.mulVec_eq_zero, hff.norm_eq_one,
    hff.gap hΔ⟩, fun ⟨hpos, hle, hzero, hΩ, hgap⟩ ↦ ?_⟩
  have hiff := (ManyBody.isGapped_and_groundSpace_eq_span_iff (H := h.hamiltonian) (E₀ := 0)
    hΔ Ω).mp ⟨hΩ, ?_, ?_⟩
  · exact ⟨hpos, hle, hΩ, hiff.2.2.1, hiff.2.2.2⟩
  · rw [Complex.ofReal_zero, zero_smul]
    change WithLp.toLp 2 (h.hamiltonian *ᵥ WithLp.ofLp Ω) = 0
    rw [(ManyBody.Interaction.hamiltonian_mulVec_eq_zero_iff hpos).mpr hzero]
    rfl
  · simpa using Matrix.le_iff.mp hgap

/-- Every term has operator norm at most `J`. -/
theorem norm_term_le (hff : IsFrustrationFreeGapped h J Δ Ω) (hJ : 0 ≤ J) (X) :
    ‖h.term X‖ ≤ J :=
  (CStarAlgebra.norm_le_iff_le_algebraMap _ hJ (hff.posSemidef X).nonneg).mpr
    (by simpa [Algebra.algebraMap_eq_smul_one] using hff.le_bound X)

/-- **The range projections keep the gap.** With `Π_X` the range projection of `h_X`,
`(Δ / J) (1 - |Ω⟩⟨Ω|) ≤ ∑_X Π_X`. Source:
`docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`, "Contraction in one sweep",
where `∑_i k_i ≥ g (1 - P)` with `g = Δ / J`; here `Π_X ≥ h_X / J`. -/
theorem smul_sub_le_sum_supportProj (hff : IsFrustrationFreeGapped h J Δ Ω) (hJ : 0 < J)
    (hΔ : 0 < Δ) :
    ((Δ / J : ℝ) : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
      ∑ X, (hff.posSemidef X).supportProj := by
  have hsum : h.hamiltonian ≤ J • ∑ X, (hff.posSemidef X).supportProj := by
    rw [ManyBody.Interaction.hamiltonian, Finset.smul_sum]
    exact Finset.sum_le_sum fun X _ ↦ (hff.posSemidef X).le_smul_supportProj (hff.le_bound X)
  have h1 := (hff.gap hΔ).trans hsum
  have hJ' : (0 : ℝ) < J⁻¹ := inv_pos.mpr hJ
  have h2 := smul_le_smul_of_nonneg_left h1 hJ'.le
  rw [smul_smul, inv_mul_cancel₀ hJ.ne', one_smul] at h2
  convert h2 using 1
  rw [div_eq_inv_mul, Complex.ofReal_mul, mul_smul, Complex.coe_smul]

end IsFrustrationFreeGapped

/-- **The general area law implies the frustration-free area law.** Every instance of
`eq:model` is gapped at energy zero with unique ground vector `Ω`, Hermitian terms and
`‖h_X‖ ≤ J`, so Theorem 1.1 applies. This proof passes through the filtered constraints of the
general theorem; the short route of the note is assembled separately. -/
theorem _root_.TNLean.PEPS.AreaLaw.UniformAreaLaw.frustrationFreeAreaLaw
    (hU : UniformAreaLaw) : FrustrationFreeAreaLaw := by
  intro q hq R J Δ hJ hΔ
  obtain ⟨C, hC, hbound⟩ := hU q hq R J Δ hJ hΔ
  exact ⟨C, hC, fun Λ h Ω hff A ↦ hbound Λ h hff.isHermitian (hff.norm_term_le hJ.le) 0 Ω
    hff.norm_eq_one hff.isGapped hff.groundSpace_eq A⟩

end TNLean.PEPS.AreaLaw.FrustrationFree
