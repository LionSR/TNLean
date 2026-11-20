/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.TheoremStatements
import TNLean.PEPS.AreaLaw.FrustrationFree.RangeProjection

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
satisfies `0 ≤ h_X ≤ J` and annihilates the unit vector `Ω`, and the Hamiltonian satisfies
`H ≥ Δ (1 - |Ω⟩⟨Ω|)`. -/
structure IsFrustrationFreeGapped (h : PlaneInteraction Λ q R) (J Δ : ℝ) (Ω : StateSpace Λ q) :
    Prop where
  /-- Every term is positive semidefinite. -/
  posSemidef : ∀ X, (h.term X).PosSemidef
  /-- Every term is at most `J`. -/
  le_bound : ∀ X, h.term X ≤ J • (1 : Matrix (Configuration Λ q) (Configuration Λ q) ℂ)
  /-- Every term annihilates `Ω`. -/
  mulVec_eq_zero : ∀ X, h.term X *ᵥ WithLp.ofLp Ω = 0
  /-- `Ω` is a unit vector. -/
  norm_eq_one : ‖Ω‖ = 1
  /-- The gap inequality `H ≥ Δ (1 - |Ω⟩⟨Ω|)`. -/
  gap : (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤ h.hamiltonian

/-- **The frustration-free area law** (`eq:goal` of the frustration-free area-law note): for
`q ≥ 1`, `R`, and `J, Δ > 0` there is a constant `C`, chosen before the domain, the Hamiltonian
and the cut, with `S_Ω(A) ≤ C |∂_Λ A|` for every instance of `eq:model`. -/
def FrustrationFreeAreaLaw : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∀ R : ℕ, ∀ J Δ : ℝ, 0 < J → 0 < Δ →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ Λ : Finset (ℤ × ℤ), ∀ h : PlaneInteraction Λ q R, ∀ Ω : StateSpace Λ q,
        IsFrustrationFreeGapped h J Δ Ω →
          ∀ A : Finset (Site Λ), regionalEntropy Λ q Ω A ≤ C * (edgeBoundary Λ A).card

namespace IsFrustrationFreeGapped

variable {h : PlaneInteraction Λ q R} {J Δ : ℝ} {Ω : StateSpace Λ q}

/-- The terms are Hermitian. -/
theorem isHermitian (hff : IsFrustrationFreeGapped h J Δ Ω) (X) : (h.term X).IsHermitian :=
  (hff.posSemidef X).isHermitian

/-- The Hamiltonian annihilates `Ω`. -/
theorem hamiltonian_mulVec_eq_zero (hff : IsFrustrationFreeGapped h J Δ Ω) :
    h.hamiltonian *ᵥ WithLp.ofLp Ω = 0 := by
  rw [ManyBody.Interaction.hamiltonian, sum_mulVec]
  exact Finset.sum_eq_zero fun X _ ↦ hff.mulVec_eq_zero X

/-- The model is gapped at energy zero with gap `Δ` and has the ground space `span {Ω}`, in the
form of `ManyBody.isGapped_and_groundSpace_eq_span_iff`. -/
theorem isGapped_and_groundSpace_eq (hff : IsFrustrationFreeGapped h J Δ Ω) (hΔ : 0 < Δ) :
    IsGapped h.hamiltonian 0 Δ ∧ groundSpace h.hamiltonian 0 = Submodule.span ℂ {Ω} := by
  have hiff := (ManyBody.isGapped_and_groundSpace_eq_span_iff (H := h.hamiltonian) (E₀ := 0)
    hΔ Ω).mp ⟨hff.norm_eq_one, ?_, ?_⟩
  · exact ⟨hiff.2.2.1, hiff.2.2.2⟩
  · rw [Complex.ofReal_zero, zero_smul]
    change WithLp.toLp 2 (h.hamiltonian *ᵥ WithLp.ofLp Ω) = 0
    rw [hff.hamiltonian_mulVec_eq_zero]
    rfl
  · have := Matrix.le_iff.mp hff.gap
    simpa using this

/-- The model is gapped at energy zero with gap `Δ`. -/
theorem isGapped (hff : IsFrustrationFreeGapped h J Δ Ω) (hΔ : 0 < Δ) :
    IsGapped h.hamiltonian 0 Δ :=
  (hff.isGapped_and_groundSpace_eq hΔ).1

/-- The ground space of the model is the line through `Ω`. -/
theorem groundSpace_eq (hff : IsFrustrationFreeGapped h J Δ Ω) (hΔ : 0 < Δ) :
    groundSpace h.hamiltonian 0 = Submodule.span ℂ {Ω} :=
  (hff.isGapped_and_groundSpace_eq hΔ).2

/-- Every term has operator norm at most `J`. -/
theorem norm_term_le (hff : IsFrustrationFreeGapped h J Δ Ω) (hJ : 0 ≤ J) (X) :
    ‖h.term X‖ ≤ J :=
  (CStarAlgebra.norm_le_iff_le_algebraMap _ hJ (hff.posSemidef X).nonneg).mpr
    (by simpa [Algebra.algebraMap_eq_smul_one] using hff.le_bound X)

/-- **The range projections keep the gap.** With `Π_X` the range projection of `h_X`,
`(Δ / J) (1 - |Ω⟩⟨Ω|) ≤ ∑_X Π_X`. Source:
`docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`, "Contraction in one sweep",
where `∑_i k_i ≥ g (1 - P)` with `g = Δ / J`; here `Π_X ≥ h_X / J`. -/
theorem smul_sub_le_sum_supportProj (hff : IsFrustrationFreeGapped h J Δ Ω) (hJ : 0 < J) :
    ((Δ / J : ℝ) : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
      ∑ X, (hff.posSemidef X).supportProj := by
  have hsum : h.hamiltonian ≤ J • ∑ X, (hff.posSemidef X).supportProj := by
    rw [ManyBody.Interaction.hamiltonian, Finset.smul_sum]
    exact Finset.sum_le_sum fun X _ ↦ (hff.posSemidef X).le_smul_supportProj (hff.le_bound X)
  have h1 := hff.gap.trans hsum
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
    hff.norm_eq_one (hff.isGapped hΔ) (hff.groundSpace_eq hΔ) A⟩

end TNLean.PEPS.AreaLaw.FrustrationFree
