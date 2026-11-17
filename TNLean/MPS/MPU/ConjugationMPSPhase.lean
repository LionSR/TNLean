/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.ConjugationCaseEquivalence

/-!
# The MPS sign labels the phases under conjugation

For a conjugation-invariant MPU, the sign `G conj(G) = ±1` of the gauge relating the
MPU tensor to its conjugate (arXiv:1703.09188, eq. `eq:mps-class-gauge-trafo`) labels
the two phases under equivalence: two such MPUs are equivalent under conjugation
symmetry exactly when their signs agree. This is Proposition
`prop:mps-class-eq-mpu-class-for-conjugation`, lines 1791--1805. Its proof combines
the first half, the agreement of the sign with the case of Proposition `corconj`,
with Corollary `cor:equiv-under-conjugation`.

When one of the ranks is odd, only Case I occurs and all such MPUs are equivalent
(Corollary `cor:all-equivalent-under-conjugation`), so the proposition needs no
parity hypothesis.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D₁ D₂ ℓ r : ℕ}

private theorem sign_iff_case {D : ℕ} {𝒰 : MPOTensor d D} (h : IsMPUCanonicalFormII 𝒰)
    (hc : IsInvariantUnderSymmetry (conjugationSymmetry d) 𝒰)
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ} {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData (blockTwo 𝒰) u v) (G : Matrix.unitaryGroup (Fin D) ℂ) (ζ : ℂ)
    (hg : ∀ i j, (𝒰 i j).map (starRingEnd ℂ) =
      ζ • ((G : Matrix (Fin D) (Fin D) ℂ)ᴴ * 𝒰 i j * G)) :
    (IsConjugationCaseI u v ↔
        (G : Matrix (Fin D) (Fin D) ℂ) * (G : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = 1) ∧
      (IsConjugationCaseII u v ↔
        (G : Matrix (Fin D) (Fin D) ℂ) * (G : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) =
          -1) := by
  have : NeZero D := h.neZero_bond
  have hg₂ := blockTwo_map_star_eq_of_gauge (G : Matrix (Fin D) (Fin D) ℂ)
    (by simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp G.2) ζ hg
  exact S.isConjugationCase_iff_sign
    (S.isConjugationCase_of_conjugation fun N hN ↦ (hc.blockTwo_conjugation hN).symm) G _ hg₂
    (h.mul_map_star_eq_one_or_neg_one_of_conjugation_gauge G hg₂)

/-- **The MPS sign labels the phases under conjugation.** Let `𝒰₁, 𝒰₂` be simple,
conjugation-invariant MPUs in canonical form II whose two-site blocks have standard
forms of the same ranks, and let `G_i` be unitary gauges with
`conj(𝒰_iʲᵏ) = ζ_i G_i† 𝒰_iʲᵏ G_i`. Then `𝒰₁` and `𝒰₂` are equivalent under
conjugation symmetry exactly when their MPS signs `G_i conj(G_i) = ±1` agree.

The hypotheses are those of Corollary `cor:equiv-under-conjugation`, with its
standing conventions recorded at `equivalentUnderSymmetry_conjugation_iff_same_case`.
No parity hypothesis is needed: if `ℓ` or `r` is odd, both standard forms are in
Case I, both signs are `1`, and the MPUs are equivalent by
`equivalentUnderSymmetry_conjugation_of_odd`.

**Local fix (missing argument):** the "only if" direction of
Corollary `cor:equiv-under-conjugation` is used; see
`docs/paper-gaps/mpu_symmetry_path_criterion_blocking.tex`.

Source: arXiv:1703.09188, Proposition `prop:mps-class-eq-mpu-class-for-conjugation`,
lines 1791--1805, with eq. `eq:mps-class-gauge-trafo` (lines 1761--1782). -/
theorem equivalentUnderSymmetry_conjugation_iff_mps_sign
    {𝒰₁ : MPOTensor d D₁} {𝒰₂ : MPOTensor d D₂}
    (h₁ : IsMPUCanonicalFormII 𝒰₁) (h₂ : IsMPUCanonicalFormII 𝒰₂)
    (hs₁ : IsMPUSimple 𝒰₁) (hs₂ : IsMPUSimple 𝒰₂)
    (hc₁ : IsInvariantUnderSymmetry (conjugationSymmetry d) 𝒰₁)
    (hc₂ : IsInvariantUnderSymmetry (conjugationSymmetry d) 𝒰₂)
    {u₁ u₂ : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v₁ v₂ : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S₁ : TwoSiteStandardFormData (blockTwo 𝒰₁) u₁ v₁)
    (S₂ : TwoSiteStandardFormData (blockTwo 𝒰₂) u₂ v₂)
    (G₁ : Matrix.unitaryGroup (Fin D₁) ℂ) (ζ₁ : ℂ)
    (hg₁ : ∀ i j, (𝒰₁ i j).map (starRingEnd ℂ) =
      ζ₁ • ((G₁ : Matrix (Fin D₁) (Fin D₁) ℂ)ᴴ * 𝒰₁ i j * G₁))
    (G₂ : Matrix.unitaryGroup (Fin D₂) ℂ) (ζ₂ : ℂ)
    (hg₂ : ∀ i j, (𝒰₂ i j).map (starRingEnd ℂ) =
      ζ₂ • ((G₂ : Matrix (Fin D₂) (Fin D₂) ℂ)ᴴ * 𝒰₂ i j * G₂)) :
    EquivalentUnderSymmetry conjugationSymmetryFamily 𝒰₁ 𝒰₂ ↔
      ((G₁ : Matrix (Fin D₁) (Fin D₁) ℂ) * (G₁ : Matrix (Fin D₁) (Fin D₁) ℂ).map
          (starRingEnd ℂ) = 1 ↔
        (G₂ : Matrix (Fin D₂) (Fin D₂) ℂ) * (G₂ : Matrix (Fin D₂) (Fin D₂) ℂ).map
          (starRingEnd ℂ) = 1) := by
  have : NeZero ℓ := ⟨S₁.left_pos.ne'⟩
  have : NeZero r := ⟨S₁.right_pos.ne'⟩
  obtain ⟨hI₁, hII₁⟩ := sign_iff_case h₁ hc₁ S₁ G₁ ζ₁ hg₁
  obtain ⟨hI₂, hII₂⟩ := sign_iff_case h₂ hc₂ S₂ G₂ ζ₂ hg₂
  have hcase₁ := S₁.isConjugationCase_of_conjugation fun N hN ↦
    (hc₁.blockTwo_conjugation hN).symm
  have hcase₂ := S₂.isConjugationCase_of_conjugation fun N hN ↦
    (hc₂.blockTwo_conjugation hN).symm
  have hex₁ := not_isConjugationCaseI_and_isConjugationCaseII (v := v₁) S₁.u_unitary.2
  have hex₂ := not_isConjugationCaseI_and_isConjugationCaseII (v := v₂) S₂.u_unitary.2
  by_cases hpar : Even ℓ ∧ Even r
  · rw [equivalentUnderSymmetry_conjugation_iff_same_case h₁ h₂ hs₁ hs₂ hc₁ hc₂ S₁ S₂
      hpar.1 hpar.2, ← hI₁, ← hI₂]
    constructor
    · rintro (⟨a, b⟩ | ⟨a, b⟩)
      · exact ⟨fun _ ↦ b, fun _ ↦ a⟩
      · exact ⟨fun h ↦ absurd ⟨h, a⟩ hex₁, fun h ↦ absurd ⟨h, b⟩ hex₂⟩
    · intro h
      rcases hcase₁ with a | a
      · exact Or.inl ⟨a, h.mp a⟩
      · exact Or.inr ⟨a, hcase₂.resolve_left fun b ↦ hex₁ ⟨h.mpr b, a⟩⟩
  · -- One rank is odd: only Case I occurs.
    have hodd : Odd ℓ ∨ Odd r := by
      rw [not_and_or, Nat.not_even_iff_odd, Nat.not_even_iff_odd] at hpar
      exact hpar
    have hnotII : ∀ {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
        {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}, ¬IsConjugationCaseII u v := by
      rintro u v ⟨x, y, hx, hy, hxT, hyT, -, -⟩
      have hℓ := Matrix.UnitaryGroup.even_dimension_of_transpose_eq_neg (R := ℂ) ⟨x, hx⟩ hxT
      have hr := Matrix.UnitaryGroup.even_dimension_of_transpose_eq_neg (R := ℂ) ⟨y, hy⟩ hyT
      rcases hodd with h | h
      · exact (Nat.not_even_iff_odd.mpr h) (by simpa using hℓ)
      · exact (Nat.not_even_iff_odd.mpr h) (by simpa using hr)
    have e₁ := hI₁.mp (hcase₁.resolve_right hnotII)
    have e₂ := hI₂.mp (hcase₂.resolve_right hnotII)
    exact ⟨fun _ ↦ ⟨fun _ ↦ e₂, fun _ ↦ e₁⟩, fun _ ↦
      equivalentUnderSymmetry_conjugation_of_odd h₁ h₂ hc₁ hc₂ S₁ S₂ hodd⟩

end MPOTensor
