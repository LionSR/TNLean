/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.TheoremStatements
import TNLean.PEPS.AreaLaw.FrustrationFree.Family

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

* `TNLean.PEPS.AreaLaw.FrustrationFree.IsFrustrationFreeGapped`: the model `eq:model`, the
  frustration-free family (`IsFrustrationFree`) of the terms of a finite-range interaction.
* `TNLean.PEPS.AreaLaw.FrustrationFree.FrustrationFreeAreaLaw`: the goal `eq:goal`.

## Main statements

* `IsFrustrationFreeGapped.isGapped`, `IsFrustrationFreeGapped.groundSpace_eq`: the model has
  gap `Δ` at energy zero and ground space `span {Ω}`.
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
`docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`, "Setting"): the terms of a
finite-range interaction form a frustration-free family, `0 ≤ h_X ≤ J`, `h_X Ω = 0` for the unit
vector `Ω`, and `H ≥ Δ (1 - |Ω⟩⟨Ω|)`. -/
abbrev IsFrustrationFreeGapped (h : PlaneInteraction Λ q R) (J Δ : ℝ) (Ω : StateSpace Λ q) :
    Prop :=
  IsFrustrationFree h.term J Δ Ω

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

/-- The Hamiltonian annihilates `Ω`. -/
theorem hamiltonian_mulVec_eq_zero (hff : IsFrustrationFreeGapped h J Δ Ω) :
    h.hamiltonian *ᵥ WithLp.ofLp Ω = 0 :=
  IsFrustrationFree.sum_mulVec_eq_zero hff

/-- The model is gapped at energy zero with gap `Δ`. -/
theorem isGapped (hff : IsFrustrationFreeGapped h J Δ Ω) (hΔ : 0 < Δ) :
    IsGapped h.hamiltonian 0 Δ :=
  IsFrustrationFree.isGapped hff hΔ

/-- The ground space of the model is the line through `Ω`. -/
theorem groundSpace_eq (hff : IsFrustrationFreeGapped h J Δ Ω) (hΔ : 0 < Δ) :
    groundSpace h.hamiltonian 0 = Submodule.span ℂ {Ω} :=
  IsFrustrationFree.groundSpace_eq hff hΔ

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
