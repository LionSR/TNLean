/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Symmetry.Phases.ConjugationCaseInvariance
import TNLean.MPS.MPU.Symmetry.Conjugation.ConjugationMPSClass
import TNLean.MPS.MPU.StandardForm.ConjugationSourceFactors
import TNLean.MPS.MPU.CanonicalForm.VirtualUnitaryGauge

/-!
# The conjugation gauge of a conjugation-invariant MPU and its sign

A conjugation-invariant MPU tensor `𝒰` in canonical form II and its entrywise
conjugate generate the same MPU. They therefore differ by a unitary gauge
`conj(𝒰ⁱʲ) = X† 𝒰ⁱʲ X` (arXiv:1703.09188, eq. `eq:mps-class-gauge-trafo` and
lines 1761--1782). The same `X` is a gauge for every block of `𝒰`: the source notes
that `G` is invariant under blocking (line 1774). The sign `X conj(X) = ±1` is
the case of every standard form of every block (Proposition
`prop:mps-class-eq-mpu-class-for-conjugation`, lines 1791--1797). In particular,
blocking does not change the case of Proposition `corconj`.

## Main results

* `MPOTensor.IsMPUCanonicalFormII.exists_conjugation_gauge`: the unitary gauge.
* `MPOTensor.evalWord_map_star_of_conjugation_gauge`: the gauge on words, hence on blocks.
* `MPOTensor.TwoSiteStandardFormData.isConjugationCase_iff_sign`: the case is the sign.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D ℓ r : ℕ}

/-- **The conjugation gauge.** A tensor in canonical form II whose MPU is
invariant under complex conjugation is related to its entrywise conjugate by a
unitary gauge, `conj(𝒰ⁱʲ) = X† 𝒰ⁱʲ X`. Source: arXiv:1703.09188,
eq. `eq:mps-class-gauge-trafo` (lines 1761--1770), with the unitary choice of the
gauge (lines 1780--1782). -/
theorem IsMPUCanonicalFormII.exists_conjugation_gauge {V : MPOTensor d D}
    (hV : IsMPUCanonicalFormII V)
    (hc : ∀ N : ℕ, 1 < N → mpo V N = (mpo V N).map (starRingEnd ℂ)) :
    ∃ X : Matrix.unitaryGroup (Fin D) ℂ, ∀ i j,
      (V (i, j)).map (starRingEnd ℂ) =
        (X : Matrix (Fin D) (Fin D) ℂ)ᴴ * V (i, j) * (X : Matrix (Fin D) (Fin D) ℂ) := by
  obtain ⟨hdim, z, hz⟩ := hV.exists_unitary_virtual_gauge_of_mpo_eq hV.mapStar fun N hN ↦ by
    rw [mpo_map_star]
    exact hc N hN
  refine ⟨star z, fun i j ↦ ?_⟩
  have h := hz i j
  simp only [cast_eq] at h
  change (MPOTensor.mapStar V) (i, j) = _
  rw [h]
  simp [Matrix.star_eq_conjTranspose]

/-- **The gauge on words.** A conjugation gauge of `𝒰` is a conjugation gauge of
every word, hence of every block of `𝒰`. Source: arXiv:1703.09188, line 1774. -/
theorem evalWord_map_star_of_conjugation_gauge {V : MPOTensor d D}
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hg : ∀ i j, (V (i, j)).map (starRingEnd ℂ) = Xᴴ * V (i, j) * X) :
    ∀ w w' : List (Fin d), (evalWord V w w').map (starRingEnd ℂ) = Xᴴ * evalWord V w w' * X := by
  have hXX : X * Xᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hX
  have hXX' : Xᴴ * X = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hX
  intro w
  induction w with
  | nil =>
    intro w'
    cases w' with
    | nil => simp [hXX']
    | cons j js => simp [evalWord]
  | cons i is ih =>
    intro w'
    cases w' with
    | nil => simp [evalWord]
    | cons j js =>
      rw [evalWord_cons, Matrix.map_mul, hg, ih]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc X, hXX, Matrix.one_mul]

/-- A conjugation gauge of `𝒰` is a conjugation gauge of the block of `m` sites. -/
theorem blockTensor_map_star_of_conjugation_gauge {V : MPOTensor d D}
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hg : ∀ i j, (V (i, j)).map (starRingEnd ℂ) = Xᴴ * V (i, j) * X) (m : ℕ) :
    ∀ i j, (blockTensor V m (i, j)).map (starRingEnd ℂ) = Xᴴ * blockTensor V m (i, j) * X :=
  fun i j ↦ by
    rw [blockTensor_apply]
    exact evalWord_map_star_of_conjugation_gauge hX hg _ _

/-- A conjugation gauge of `𝒰` is a conjugation gauge of its two-site block. -/
theorem blockTwo_map_star_of_conjugation_gauge {V : MPOTensor d D}
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hg : ∀ i j, (V (i, j)).map (starRingEnd ℂ) = Xᴴ * V (i, j) * X) :
    ∀ i j, (blockTwo V (i, j)).map (starRingEnd ℂ) = (1 : ℂ) • (Xᴴ * blockTwo V (i, j) * X) := by
  intro i j
  have h := blockTwo_map_star_eq_of_gauge X
    (by simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hX) 1
    (fun i j ↦ by rw [one_smul]; exact hg i j) i j
  simpa using h

/-- **The sign of the conjugation gauge.** For a tensor in canonical form II, a
unitary conjugation gauge of its two-site block satisfies `X conj(X) = ±1`.
Source: arXiv:1703.09188, eq. `eq:mps-class-gauge-trafo`, lines 1761--1770. -/
theorem IsMPUCanonicalFormII.mul_map_star_eq_one_or_neg_one_of_conjugation_gauge
    {V : MPOTensor d D} (hV : IsMPUCanonicalFormII V) (X : Matrix.unitaryGroup (Fin D) ℂ)
    {ζ : ℂ} (hg : ∀ i j, (MPOTensor.blockTwo V (i, j)).map (starRingEnd ℂ) =
      ζ • ((X : Matrix (Fin D) (Fin D) ℂ)ᴴ * MPOTensor.blockTwo V (i, j) * X)) :
    (X : Matrix (Fin D) (Fin D) ℂ) * (X : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = 1 ∨
      (X : Matrix (Fin D) (Fin D) ℂ) * (X : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) =
        -1 := by
  let : NeZero d := hV.neZero_phys
  let : NeZero D := hV.neZero_bond
  have hN : Kraus.IsNormal (MPOTensor.blockTwo V).normalizedFlattening :=
    hV.blockTwo.isNormalTensor_normalizedFlattening.isNormal
  exact MPSTensor.mul_map_star_eq_one_or_neg_one_of_timeReversal_gauge hN
    (P := 1) (by simp) X (ζ := ζ) (fun i => by
      simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
      simp only [normalizedFlattening, toMPSTensor, map_star_smul, hg, Matrix.mul_smul,
        Matrix.smul_mul, smul_comm ζ]
      congr 1
      simp)

/-- **The case is the sign of the conjugation gauge.** Let `𝒲` have standard form
`u, v`, in Case I or Case II, and let `X` be a unitary gauge with
`conj(𝒲ⁱʲ) = ζ X† 𝒲ⁱʲ X` and `X conj(X) = ±1`. Then Case I holds exactly when
`X conj(X) = 1`, and Case II exactly when `X conj(X) = -1`. Source:
arXiv:1703.09188, the first half of Proposition
`prop:mps-class-eq-mpu-class-for-conjugation`, lines 1791--1797. -/
theorem TwoSiteStandardFormData.isConjugationCase_iff_sign [NeZero D]
    {W : MPOTensor (d * d) D} {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ} (T : TwoSiteStandardFormData W u v)
    (hcase : IsConjugationCaseI u v ∨ IsConjugationCaseII u v)
    (X : Matrix.unitaryGroup (Fin D) ℂ) (ζ : ℂ)
    (hg : ∀ i j, (W (i, j)).map (starRingEnd ℂ) =
      ζ • ((X : Matrix (Fin D) (Fin D) ℂ)ᴴ * W (i, j) * X))
    (hs : (X : Matrix (Fin D) (Fin D) ℂ) * (X : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = 1 ∨
      (X : Matrix (Fin D) (Fin D) ℂ) * (X : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = -1) :
    (IsConjugationCaseI u v ↔
        (X : Matrix (Fin D) (Fin D) ℂ) * (X : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = 1) ∧
      (IsConjugationCaseII u v ↔
        (X : Matrix (Fin D) (Fin D) ℂ) * (X : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) =
          -1) := by
  have : NeZero ℓ := ⟨T.left_pos.ne'⟩
  have : NeZero r := ⟨T.right_pos.ne'⟩
  have hne : (1 : Matrix (Fin D) (Fin D) ℂ) ≠ -1 := by
    intro h
    have := congrFun (congrFun h 0) 0
    norm_num at this
  have hI : IsConjugationCaseI u v →
      (X : Matrix (Fin D) (Fin D) ℂ) * (X : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = 1 := by
    rintro ⟨x, y, hx, hy, hxT, -, hu, -⟩
    rcases hs with h | h
    · exact h
    · have := T.sign_eq_of_conjugation_gauge hx hy hu X.2 ζ hg (Or.inl rfl) (Or.inr rfl)
        (by rw [hxT, one_smul]) (by rw [h, neg_one_smul])
      norm_num at this
  have hII : IsConjugationCaseII u v →
      (X : Matrix (Fin D) (Fin D) ℂ) * (X : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) =
        -1 := by
    rintro ⟨x, y, hx, hy, hxT, -, hu, -⟩
    rcases hs with h | h
    · have := T.sign_eq_of_conjugation_gauge hx hy hu X.2 ζ hg (Or.inr rfl) (Or.inl rfl)
        (by rw [hxT, neg_one_smul]) (by rw [h, one_smul])
      norm_num at this
    · exact h
  refine ⟨⟨hI, fun h ↦ hcase.resolve_right fun h₂ ↦ hne (h.symm.trans (hII h₂))⟩,
    ⟨hII, fun h ↦ hcase.resolve_left fun h₁ ↦ hne ((hI h₁).symm.trans h)⟩⟩

end MPOTensor
