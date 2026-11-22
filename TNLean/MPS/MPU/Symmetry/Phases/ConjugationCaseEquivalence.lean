/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Symmetry.Phases.ConjugationGaugeSign
import TNLean.MPS.MPU.Symmetry.Phases.SymmetryPathCriterion

/-!
# Equivalence under conjugation is the case of `corconj`

Two conjugation-invariant MPUs whose standard forms have the same even ranks are
equivalent under conjugation symmetry exactly when they lie in the same case of
Proposition `corconj` (arXiv:1703.09188, Corollary `cor:equiv-under-conjugation`,
lines 1548--1567).

The "if" direction is `MPOTensor.equivalentUnderSymmetry_conjugation_of_same_case`.
For the "only if" direction, equivalence gives strict equivalence of blocks, and
the forward direction of the symmetry path criterion gives a continuous path of
gates on longer blocks, each generating a conjugation-invariant MPU. The case is
constant along that path (`MPOTensor.isConjugationCase_const_of_path`), and it is
the same on every block as on the original tensor, since it is the sign of one
conjugation gauge (`MPOTensor.TwoSiteStandardFormData.isConjugationCase_iff_sign`).

**Local fix (missing argument):** the source proves only the "if" direction
(lines 1556--1567). The "only if" direction combines the "only if" argument of
Theorem `prop:conjsym-strict-equiv` (lines 1493--1532) with the invariance of the
case under blocking, which the source does not state; the latter follows from
the sign of the conjugation gauge (lines 1761--1797). See
`docs/paper-gaps/mpu_symmetry_path_criterion_blocking.tex`.

## The MPS sign labels the phases under conjugation

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

section

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D₁ D₂ ℓ r : ℕ}

/-- **The case of a tensor and of its blocks.** For a conjugation-invariant tensor
in canonical form II, the case of a standard form of its two-site block is the
case of a standard form of the two-site block of the block of `k` sites, blocked
again `k'` times. Source: arXiv:1703.09188, line 1774 (the conjugation gauge is
invariant under blocking) and Proposition
`prop:mps-class-eq-mpu-class-for-conjugation`, lines 1791--1797. -/
theorem isConjugationCaseI_iff_of_blockTensor {D : ℕ} {𝒰 : MPOTensor d D}
    (h : IsMPUCanonicalFormII 𝒰) (hc : IsInvariantUnderSymmetry (conjugationSymmetry d) 𝒰)
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ} {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData (blockTwo 𝒰) u v) (k k' : ℕ) {ℓ' r' : ℕ}
    {u' : Matrix (Fin ℓ' × Fin r') (Fin (Kraus.blockPhysDim (Kraus.blockPhysDim d k) k') ×
      Fin (Kraus.blockPhysDim (Kraus.blockPhysDim d k) k')) ℂ}
    {v' : Matrix (Fin (Kraus.blockPhysDim (Kraus.blockPhysDim d k) k') ×
      Fin (Kraus.blockPhysDim (Kraus.blockPhysDim d k) k')) (Fin r' × Fin ℓ') ℂ}
    (S' : TwoSiteStandardFormData (blockTwo (blockTensor (blockTensor 𝒰 k) k')) u' v')
    (hcase' : IsConjugationCaseI u' v' ∨ IsConjugationCaseII u' v') :
    (IsConjugationCaseI u v ↔ IsConjugationCaseI u' v') ∧
      (IsConjugationCaseII u v ↔ IsConjugationCaseII u' v') := by
  have : NeZero D := h.neZero_bond
  obtain ⟨X, hX⟩ := h.exists_conjugation_gauge fun N hN ↦ (hc (by omega : 0 < N)).symm
  have hg := blockTwo_map_star_of_conjugation_gauge X.2 hX
  have hs := h.mul_map_star_eq_one_or_neg_one_of_conjugation_gauge X hg
  have hcase := S.isConjugationCase_of_conjugation fun N hN ↦
    (hc.blockTwo_conjugation hN).symm
  have hg' := blockTwo_map_star_of_conjugation_gauge X.2
    (blockTensor_map_star_of_conjugation_gauge X.2
      (blockTensor_map_star_of_conjugation_gauge X.2 hX k) k')
  obtain ⟨hI, hII⟩ := S.isConjugationCase_iff_sign hcase X 1 hg hs
  obtain ⟨hI', hII'⟩ := S'.isConjugationCase_iff_sign hcase' X 1 hg' hs
  exact ⟨hI.trans hI'.symm, hII.trans hII'.symm⟩

/-- **Equivalent conjugation-invariant MPUs are in the same case.** Let
`𝒰₁, 𝒰₂` be simple, conjugation-invariant MPUs in canonical form II whose two-site
blocks have standard forms of the same ranks. If they are equivalent under
conjugation symmetry, both standard forms are in Case I or both are in Case II of
Proposition `corconj`.

Source: arXiv:1703.09188, Corollary `cor:equiv-under-conjugation`,
lines 1548--1554, "only if" direction. -/
theorem same_case_of_equivalentUnderSymmetry_conjugation
    {𝒰₁ : MPOTensor d D₁} {𝒰₂ : MPOTensor d D₂}
    (h₁ : IsMPUCanonicalFormII 𝒰₁) (h₂ : IsMPUCanonicalFormII 𝒰₂)
    (hs₁ : IsMPUSimple 𝒰₁) (hs₂ : IsMPUSimple 𝒰₂)
    (hc₁ : IsInvariantUnderSymmetry (conjugationSymmetry d) 𝒰₁)
    (hc₂ : IsInvariantUnderSymmetry (conjugationSymmetry d) 𝒰₂)
    {u₁ u₂ : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v₁ v₂ : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S₁ : TwoSiteStandardFormData (blockTwo 𝒰₁) u₁ v₁)
    (S₂ : TwoSiteStandardFormData (blockTwo 𝒰₂) u₂ v₂)
    (hE : EquivalentUnderSymmetry conjugationSymmetryFamily 𝒰₁ 𝒰₂) :
    (IsConjugationCaseI u₁ v₁ ∧ IsConjugationCaseI u₂ v₂) ∨
      (IsConjugationCaseII u₁ v₁ ∧ IsConjugationCaseII u₂ v₂) := by
  have : NeZero d := h₁.neZero_phys
  obtain ⟨-, -, k, pa, pb, hk, hpa, hpb, hcop, hphys, H⟩ := hE
  -- Equal physical dimensions force trivial ancillas.
  obtain rfl : pa = pb := Nat.eq_of_mul_eq_mul_right (NeZero.pos d) hphys
  obtain rfl : pa = 1 := by simpa [Nat.Coprime] using hcop
  rw [conjugationSymmetryFamily_at, conjugationSymmetry_block hk, tensorPhysicalId_one,
    tensorPhysicalId_one] at H
  have H' := (strictlyEquivalentUnderSymmetry_conjugation_finCongr_iff (Nat.mul_one d) k).mp H
  -- The forward direction of the symmetry path criterion.
  obtain ⟨k', hk', ℓ', r', u, v, hu, hv, hu', hv', ⟨T₁⟩, ⟨T₂⟩, hinv⟩ :=
    exists_gate_path_of_strictlyEquivalentUnderSymmetry (fun N hN ↦ hN)
      (h₁.blockTensor k hk) (h₂.blockTensor k hk) (hs₁.blockTensor k hk) (hs₂.blockTensor k hk) H'
  have : NeZero ℓ' := ⟨T₁.left_pos.ne'⟩
  have : NeZero r' := ⟨T₁.right_pos.ne'⟩
  -- Every point of the path is in some case.
  have hcase : ∀ p, IsConjugationCaseI (u p) (v p) ∨ IsConjugationCaseII (u p) (v p) := by
    intro p
    have hp := hinv p
    rw [conjugationSymmetry_block (by omega)] at hp
    have hG := isInvariantUnderSymmetry_conjugation_reindexPhysical
      (twoSiteDirectBlockEquiv (Kraus.blockPhysDim d k) k').symm hp
    rw [reindexPhysical_symm_reindexPhysical] at hG
    exact (standardFormTensorOfGatesData (u p) (v p) (hu' p)
      (hv' p)).isConjugationCase_of_conjugation fun N hN ↦ (hG hN).symm
  have hconst := isConjugationCase_const_of_path hu (fun p ↦ (hu' p).2) hcase
  -- The case is the same at the endpoints as on the original tensors.
  obtain ⟨hI₁, hII₁⟩ := isConjugationCaseI_iff_of_blockTensor h₁ hc₁ S₁ k k' T₁ (hcase 0)
  obtain ⟨hI₂, hII₂⟩ := isConjugationCaseI_iff_of_blockTensor h₂ hc₂ S₂ k k' T₂ (hcase 1)
  rcases hconst with h | h
  · exact Or.inl ⟨hI₁.mpr (h 0), hI₂.mpr (h 1)⟩
  · exact Or.inr ⟨hII₁.mpr (h 0), hII₂.mpr (h 1)⟩

/-- **Equivalence under conjugation is the case of `corconj`.** Let `𝒰₁, 𝒰₂` be
simple, conjugation-invariant MPUs in canonical form II whose two-site blocks have
standard forms of the same even ranks `ℓ, r`. Then `𝒰₁` and `𝒰₂` are equivalent
under conjugation symmetry if and only if their standard forms lie in the same case
of Proposition `corconj`.

The common ranks `ℓ, r` and physical dimension `d` are the standing convention of
the section (lines 1388--1398). They are also forced: equivalence preserves the
index (Theorem `IndexTh`), and with a common `d` the index and `ℓ r = d²`
determine `ℓ` and `r`. The evenness of `ℓ, r` is the standing hypothesis of the
subsection "$r$ and $\ell$ are both even" (line 1464); the source repeats it at the
comparable Theorem `prop:conjsym-strict-equiv` (line 1482). Conjugation invariance
is the standing hypothesis of the section (lines 1008--1010), and simplicity in
canonical form II is the reading of a tensor in standard form recorded in
`docs/paper-gaps/mpu_standard_form_canonical_convention.tex`.

Source: arXiv:1703.09188, Corollary `cor:equiv-under-conjugation`,
lines 1548--1567. -/
theorem equivalentUnderSymmetry_conjugation_iff_same_case
    {𝒰₁ : MPOTensor d D₁} {𝒰₂ : MPOTensor d D₂}
    (h₁ : IsMPUCanonicalFormII 𝒰₁) (h₂ : IsMPUCanonicalFormII 𝒰₂)
    (hs₁ : IsMPUSimple 𝒰₁) (hs₂ : IsMPUSimple 𝒰₂)
    (hc₁ : IsInvariantUnderSymmetry (conjugationSymmetry d) 𝒰₁)
    (hc₂ : IsInvariantUnderSymmetry (conjugationSymmetry d) 𝒰₂)
    {u₁ u₂ : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v₁ v₂ : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S₁ : TwoSiteStandardFormData (blockTwo 𝒰₁) u₁ v₁)
    (S₂ : TwoSiteStandardFormData (blockTwo 𝒰₂) u₂ v₂)
    (hℓ : Even ℓ) (hr : Even r) :
    EquivalentUnderSymmetry conjugationSymmetryFamily 𝒰₁ 𝒰₂ ↔
      (IsConjugationCaseI u₁ v₁ ∧ IsConjugationCaseI u₂ v₂) ∨
        (IsConjugationCaseII u₁ v₁ ∧ IsConjugationCaseII u₂ v₂) :=
  ⟨same_case_of_equivalentUnderSymmetry_conjugation h₁ h₂ hs₁ hs₂ hc₁ hc₂ S₁ S₂,
    equivalentUnderSymmetry_conjugation_of_same_case h₁ h₂ S₁ S₂ hℓ hr⟩

end MPOTensor

end

section

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

The gauges `G_i` are the objects the source statement speaks about
(eq. `eq:mps-class-gauge-trafo`), chosen unitary as at lines 1780--1782, so taking
them as data adds no hypothesis; such gauges always exist by
`IsMPUCanonicalFormII.exists_conjugation_gauge`. The remaining hypotheses are those
of Corollary `cor:equiv-under-conjugation`, with its
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

end
