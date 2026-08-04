/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.LorentzNormalForm.Basic
import TNLean.Channel.LorentzNormalForm.Infimum
import TNLean.Analysis.MarginalSupport

/-!
# Lorentz normal form: the generic normal form for CP maps

This module proves Wolf Proposition 2.9
(`Notes/WolfNoteTexSource/ch02_representations.tex`, lines 894–929): a
completely positive map with full Kraus rank (positive-definite Choi matrix)
admits SL-filterings on the input and output factors making the composition
doubly-stochastic.  The square and rectangular forms are both given; the
square form is the equal-dimension specialization.

## Main results

* `Wolf.exists_normal_form_generic` — the generic normal form for
  `T : M_D(ℂ) → M_D(ℂ)`
* `Wolf.exists_normal_form_generic_rect` — the generic normal form for
  `T : M_{d₁}(ℂ) → M_{d₂}(ℂ)` with independent dimensions

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 2.3,
  Proposition 2.9][Wolf2012QChannels]
-/

open scoped Matrix BigOperators ComplexOrder Kronecker
open Matrix Finset
open ChoiJamiolkowski

namespace Wolf

/-! ### Generic normal form (Wolf Proposition 2.9) -/

section GenericNormalForm

variable {D : ℕ}

-- Source: Notes/WolfNoteTexSource/ch02_representations.tex lines 923–929 (Wolf Proposition 2.9).
/-- **Wolf Proposition 2.9: generic normal form for CP maps with full Kraus rank.**

Let `T : M_D(ℂ) → M_D(ℂ)` be a completely positive map with full Kraus rank
(equivalently, its Choi matrix is positive-definite).  Then there exist
SL(D, ℂ)-filterings Φ₁, Φ₂ such that `Φ₂ ∘ T ∘ Φ₁` is doubly-stochastic.

This is the CP-map version (Wolf Proposition 2.9), the corollary of the τ-level
statement Wolf Proposition 2.8.  The Lorentz normal form for qubit channels
(Wolf Proposition 2.11) is the D = 2 specialisation with the complete
classification of the possible doubly-stochastic normal forms.

**Scope restriction (square case):** this is the equal-dimension case
`T : Mₚ(ℂ) → Mₚ(ℂ)` (here `D × D → D × D`) of Wolf Proposition 2.9; the source
(Wolf, *Quantum Channels & Operations*, Section 2.3) states it for a general
`T : M_{d₁}(ℂ) → M_{d₂}(ℂ)` with separate filterings on each factor.  Documented
in `docs/paper-gaps/wolf_prop28_square_case.tex`. -/
theorem exists_normal_form_generic
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (_hCP : IsCPMap T)
    (_hFullRank : (choiMatrix T).PosDef) :
    ∃ (Φ₁ Φ₂ : SLFiltering D),
      DoublyStochastic (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map) := by
  classical
  rcases Nat.eq_zero_or_pos D with hD0 | hDpos
  · subst hD0
    exact ⟨SLFiltering.id 0, SLFiltering.id 0,
      ⟨0, Subsingleton.elim _ _⟩, ⟨0, Subsingleton.elim _ _⟩⟩
  haveI : NeZero D := ⟨hDpos.ne'⟩
  obtain ⟨S₁, S₂, hS₁det, hS₂det, hmin⟩ :=
    infimum_is_attained (τ := choiMatrix T) _hFullRank
  let Φ₁ : SLFiltering D :=
    { S := S₁ᵀ
      det_eq_one := by rw [Matrix.det_transpose, hS₁det]
      map := unitaryConjLM S₁ᵀ
      map_eq := rfl
      cp := unitaryConjLM_isCPMap S₁ᵀ }
  let Φ₂ : SLFiltering D :=
    { S := S₂
      det_eq_one := hS₂det
      map := unitaryConjLM S₂
      map_eq := rfl
      cp := unitaryConjLM_isCPMap S₂ }
  -- The Choi matrix of the filtered channel is the minimised matrix.
  have hC : choiMatrix (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map)
      = (S₂ ⊗ₖ S₁) * choiMatrix T * (S₂ ⊗ₖ S₁)ᴴ := by
    change choiMatrix (unitaryConjLM S₂ ∘ₗ (T ∘ₗ unitaryConjLM S₁ᵀ)) = _
    rw [choiMatrix_unitaryConj_comp, choiMatrix_comp_unitaryConj, Matrix.transpose_transpose,
      show (S₂ ⊗ₖ S₁) = (S₂ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) *
          ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ S₁) by
        rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul],
      Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  -- Invertibility of the kronecker factors.
  have hU2 : IsUnit (S₂ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_kronecker, hS₂det, Matrix.det_one]; simp
  have hU1 : IsUnit ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ S₁) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_kronecker, hS₁det, Matrix.det_one]; simp
  -- The two reduced matrices and their key properties.
  set ρ₂ := (S₂ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) * choiMatrix T *
    (S₂ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))ᴴ with hρ₂
  set ρ₁ := ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ S₁) * choiMatrix T *
    ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ S₁)ᴴ with hρ₁
  have hρ₂pd : ρ₂.PosDef :=
    _hFullRank.mul_mul_conjTranspose_same (Matrix.vecMul_injective_iff_isUnit.mpr hU2)
  have hρ₁pd : ρ₁.PosDef :=
    _hFullRank.mul_mul_conjTranspose_same (Matrix.vecMul_injective_iff_isUnit.mpr hU1)
  -- Conjugation/partial-trace reductions.
  have hX : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      Matrix.traceLeft ((S₂ ⊗ₖ X) * choiMatrix T * (S₂ ⊗ₖ X)ᴴ)
        = X * Matrix.traceLeft ρ₂ * Xᴴ := by
    intro X
    have hsplit : (S₂ ⊗ₖ X) * choiMatrix T * (S₂ ⊗ₖ X)ᴴ
        = ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ X) * ρ₂ *
            ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ X)ᴴ := by
      rw [hρ₂, show (S₂ ⊗ₖ X) = ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ X) *
          (S₂ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) by
            rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one],
        Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [hsplit, traceLeft_one_kron_conj]
  have hY : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      Matrix.traceRight ((X ⊗ₖ S₁) * choiMatrix T * (X ⊗ₖ S₁)ᴴ)
        = X * Matrix.traceRight ρ₁ * Xᴴ := by
    intro X
    have hsplit : (X ⊗ₖ S₁) * choiMatrix T * (X ⊗ₖ S₁)ᴴ
        = (X ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) * ρ₁ *
            (X ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))ᴴ := by
      rw [hρ₁, show (X ⊗ₖ S₁) = (X ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) *
          ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ S₁) by
            rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul],
        Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [hsplit, traceRight_kron_one_conj]
  have hM₁pd : (Matrix.traceLeft ρ₂).PosDef := by
    rw [traceLeft_eq_traceLeftA]; exact traceLeftA_posDef hρ₂pd
  have hM₂pd : (Matrix.traceRight ρ₁).PosDef := Matrix.traceRight_posDef hρ₁pd
  refine ⟨Φ₁, Φ₂, ?_, ?_⟩
  · -- Clause 1: (Φ₂ ∘ T ∘ Φ₁)(1) ∝ 1.
    have hN₂ : ∃ κ : ℂ,
        Matrix.traceRight (choiMatrix (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map)) = κ • 1 := by
      apply posDef_orbit_min_isScalar hM₂pd
      · rw [hC]; exact Matrix.traceRight_posSemidef
          (_hFullRank.posSemidef.mul_mul_conjTranspose_same _)
      · rw [hC, hY S₂, Matrix.det_mul, Matrix.det_mul, hS₂det, Matrix.det_conjTranspose,
          hS₂det]; simp
      · intro S hS
        have e1 : (Matrix.trace (Matrix.traceRight (choiMatrix
            (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map)))).re
            = (Matrix.trace ((S₂ ⊗ₖ S₁) * choiMatrix T * (S₂ ⊗ₖ S₁)ᴴ)).re := by
          rw [hC, ← trace_eq_trace_traceRight]
        have e2 : (Matrix.trace (S * Matrix.traceRight ρ₁ * Sᴴ)).re
            = (Matrix.trace ((S ⊗ₖ S₁) * choiMatrix T * (S ⊗ₖ S₁)ᴴ)).re := by
          rw [← hY S, ← trace_eq_trace_traceRight]
        rw [e1, e2]
        exact hmin S₁ S hS₁det hS
    obtain ⟨κ, hκ⟩ := hN₂
    rw [traceRight_choiMatrix] at hκ
    set cc : ℂ := ((1 : ℂ) / ((D : ℝ).sqrt : ℂ)) *
    star ((1 : ℂ) / ((D : ℝ).sqrt : ℂ)) with hcc
    have hcc_ne : cc ≠ 0 := by rw [hcc]; exact omega_coeff_ne_zero hDpos
    refine ⟨cc⁻¹ * κ, ?_⟩
    have h := congrArg (fun M => cc⁻¹ • M) hκ
    simp only [smul_smul, inv_mul_cancel₀ hcc_ne, one_smul] at h
    exact h
  · -- Clause 2: tr_A(choi(Φ₂ ∘ T ∘ Φ₁)) ∝ 1.
    apply posDef_orbit_min_isScalar hM₁pd
    · rw [hC, hX S₁]
      exact (hM₁pd.posSemidef.mul_mul_conjTranspose_same S₁)
    · rw [hC, hX S₁, Matrix.det_mul, Matrix.det_mul, hS₁det, Matrix.det_conjTranspose,
        hS₁det]; simp
    · intro S hS
      have e1 : (Matrix.trace (Matrix.traceLeft (choiMatrix
          (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map)))).re
          = (Matrix.trace ((S₂ ⊗ₖ S₁) * choiMatrix T * (S₂ ⊗ₖ S₁)ᴴ)).re := by
        rw [hC, ← Matrix.trace_eq_trace_traceLeft]
      have e2 : (Matrix.trace (S * Matrix.traceLeft ρ₂ * Sᴴ)).re
          = (Matrix.trace ((S₂ ⊗ₖ S) * choiMatrix T * (S₂ ⊗ₖ S)ᴴ)).re := by
        rw [← hX S, ← Matrix.trace_eq_trace_traceLeft]
      rw [e1, e2]
      exact hmin S S₂ hS hS₂det

end GenericNormalForm

/-! ### Generic normal form for rectangular CP maps (Wolf Proposition 2.9) -/

section RectangularNormalForm

variable {d₁ d₂ : ℕ}

-- Source: Notes/WolfNoteTexSource/ch02_representations.tex lines 923–929 (Wolf Proposition 2.9).
/-- **Wolf Proposition 2.9: generic normal form for rectangular CP maps.**

Let `T : M_{d₁}(ℂ) → M_{d₂}(ℂ)` be a completely positive map with full Kraus
rank (equivalently, its Choi matrix is positive-definite).  Then there exist
SL-filterings Φ₁ on `M_{d₁}(ℂ)` and Φ₂ on `M_{d₂}(ℂ)` — invertible CP maps of
Kraus rank one — such that `Φ₂ ∘ T ∘ Φ₁` is doubly-stochastic: both
`(Φ₂TΦ₁)(𝟙)` and `(Φ₂TΦ₁)*(𝟙)` are proportional to the identity matrix.

The proof follows the source: the infimum of
`tr[(S₂ ⊗ₖ S₁) τ (S₂ ⊗ₖ S₁)†]` over `SL(d₁) × SL(d₂)` is attained
(`infimum_is_attained`), and at the minimiser each partial trace saturates the
trace–determinant AM–GM bound, so both reduced operators are scalar
(`posDef_orbit_min_isScalar`).  The square case `d₁ = d₂` is
`exists_normal_form_generic` above. -/
theorem exists_normal_form_generic_rect [NeZero d₁] [NeZero d₂]
    (T : Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] Matrix (Fin d₂) (Fin d₂) ℂ)
    (_hCP : IsKrausCP T)
    (_hFullRank : (ChoiRectangular.choiMatrix T).PosDef) :
    ∃ (Φ₁ : SLFiltering d₁) (Φ₂ : SLFiltering d₂),
      DoublyStochasticRect (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map) := by
  classical
  obtain ⟨S₁, S₂, hS₁det, hS₂det, hmin⟩ :=
    infimum_is_attained (τ := ChoiRectangular.choiMatrix T) _hFullRank
  let Φ₁ : SLFiltering d₁ :=
    { S := S₁ᵀ
      det_eq_one := by rw [Matrix.det_transpose, hS₁det]
      map := unitaryConjLM S₁ᵀ
      map_eq := rfl
      cp := unitaryConjLM_isCPMap S₁ᵀ }
  let Φ₂ : SLFiltering d₂ :=
    { S := S₂
      det_eq_one := hS₂det
      map := unitaryConjLM S₂
      map_eq := rfl
      cp := unitaryConjLM_isCPMap S₂ }
  -- The Choi matrix of the filtered map is the minimised operator.
  have hC : ChoiRectangular.choiMatrix (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map)
      = (S₂ ⊗ₖ S₁) * ChoiRectangular.choiMatrix T * (S₂ ⊗ₖ S₁)ᴴ := by
    change ChoiRectangular.choiMatrix (unitaryConjLM S₂ ∘ₗ (T ∘ₗ unitaryConjLM S₁ᵀ))
        = _
    rw [choiMatrixRect_unitaryConj_comp, choiMatrixRect_comp_unitaryConj,
      Matrix.transpose_transpose,
      show (S₂ ⊗ₖ S₁) = (S₂ ⊗ₖ (1 : Matrix (Fin d₁) (Fin d₁) ℂ)) *
          ((1 : Matrix (Fin d₂) (Fin d₂) ℂ) ⊗ₖ S₁) by
        rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul],
      Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  -- Invertibility of the Kronecker factors.
  have hU2 : IsUnit (S₂ ⊗ₖ (1 : Matrix (Fin d₁) (Fin d₁) ℂ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_kronecker, hS₂det, Matrix.det_one]; simp
  have hU1 : IsUnit ((1 : Matrix (Fin d₂) (Fin d₂) ℂ) ⊗ₖ S₁) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_kronecker, hS₁det, Matrix.det_one]; simp
  -- The two partially filtered operators and their positivity.
  set ρ₂ := (S₂ ⊗ₖ (1 : Matrix (Fin d₁) (Fin d₁) ℂ)) * ChoiRectangular.choiMatrix T *
    (S₂ ⊗ₖ (1 : Matrix (Fin d₁) (Fin d₁) ℂ))ᴴ with hρ₂
  set ρ₁ := ((1 : Matrix (Fin d₂) (Fin d₂) ℂ) ⊗ₖ S₁) * ChoiRectangular.choiMatrix T *
    ((1 : Matrix (Fin d₂) (Fin d₂) ℂ) ⊗ₖ S₁)ᴴ with hρ₁
  have hρ₂pd : ρ₂.PosDef :=
    _hFullRank.mul_mul_conjTranspose_same (Matrix.vecMul_injective_iff_isUnit.mpr hU2)
  have hρ₁pd : ρ₁.PosDef :=
    _hFullRank.mul_mul_conjTranspose_same (Matrix.vecMul_injective_iff_isUnit.mpr hU1)
  -- Conjugation/partial-trace reductions.
  have hX : ∀ X : Matrix (Fin d₁) (Fin d₁) ℂ,
      Matrix.traceLeft ((S₂ ⊗ₖ X) * ChoiRectangular.choiMatrix T * (S₂ ⊗ₖ X)ᴴ)
        = X * Matrix.traceLeft ρ₂ * Xᴴ := by
    intro X
    have hsplit : (S₂ ⊗ₖ X) * ChoiRectangular.choiMatrix T * (S₂ ⊗ₖ X)ᴴ
        = ((1 : Matrix (Fin d₂) (Fin d₂) ℂ) ⊗ₖ X) * ρ₂ *
            ((1 : Matrix (Fin d₂) (Fin d₂) ℂ) ⊗ₖ X)ᴴ := by
      rw [hρ₂, show (S₂ ⊗ₖ X) = ((1 : Matrix (Fin d₂) (Fin d₂) ℂ) ⊗ₖ X) *
          (S₂ ⊗ₖ (1 : Matrix (Fin d₁) (Fin d₁) ℂ)) by
            rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one],
        Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [hsplit, traceLeft_one_kron_conj]
  have hY : ∀ X : Matrix (Fin d₂) (Fin d₂) ℂ,
      Matrix.traceRight ((X ⊗ₖ S₁) * ChoiRectangular.choiMatrix T * (X ⊗ₖ S₁)ᴴ)
        = X * Matrix.traceRight ρ₁ * Xᴴ := by
    intro X
    have hsplit : (X ⊗ₖ S₁) * ChoiRectangular.choiMatrix T * (X ⊗ₖ S₁)ᴴ
        = (X ⊗ₖ (1 : Matrix (Fin d₁) (Fin d₁) ℂ)) * ρ₁ *
            (X ⊗ₖ (1 : Matrix (Fin d₁) (Fin d₁) ℂ))ᴴ := by
      rw [hρ₁, show (X ⊗ₖ S₁) = (X ⊗ₖ (1 : Matrix (Fin d₁) (Fin d₁) ℂ)) *
          ((1 : Matrix (Fin d₂) (Fin d₂) ℂ) ⊗ₖ S₁) by
            rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul],
        Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [hsplit, traceRight_kron_one_conj]
  have hM₁pd : (Matrix.traceLeft ρ₂).PosDef := hρ₂pd.partialTraceLeft
  have hM₂pd : (Matrix.traceRight ρ₁).PosDef := hρ₁pd.partialTraceRight
  have hd₁ : (d₁ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d₁)
  refine ⟨Φ₁, Φ₂, ?_, ?_⟩
  · -- Clause 1: `(Φ₂ ∘ T ∘ Φ₁)(𝟙) ∝ 𝟙`, from the input-side minimisation.
    have hN₂ : ∃ κ : ℂ,
        Matrix.traceRight (ChoiRectangular.choiMatrix (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map)) =
          κ • 1 := by
      apply posDef_orbit_min_isScalar hM₂pd
      · rw [hC]
        exact (_hFullRank.posSemidef.mul_mul_conjTranspose_same _).partialTraceRight
      · rw [hC, hY S₂, Matrix.det_mul, Matrix.det_mul, hS₂det, Matrix.det_conjTranspose,
          hS₂det]; simp
      · intro S hS
        have e1 : (Matrix.trace (Matrix.traceRight (ChoiRectangular.choiMatrix
            (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map)))).re
            = (Matrix.trace ((S₂ ⊗ₖ S₁) * ChoiRectangular.choiMatrix T *
                (S₂ ⊗ₖ S₁)ᴴ)).re := by
          rw [hC, ← trace_eq_trace_traceRight]
        have e2 : (Matrix.trace (S * Matrix.traceRight ρ₁ * Sᴴ)).re
            = (Matrix.trace ((S ⊗ₖ S₁) * ChoiRectangular.choiMatrix T *
                (S ⊗ₖ S₁)ᴴ)).re := by
          rw [← hY S, ← trace_eq_trace_traceRight]
        rw [e1, e2]
        exact hmin S₁ S hS₁det hS
    obtain ⟨κ, hκ⟩ := hN₂
    rw [ChoiRectangular.traceRight_choiMatrix] at hκ
    refine ⟨(d₁ : ℂ) * κ, ?_⟩
    calc (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map) 1
        = (1 : ℂ) • ((Φ₂.map ∘ₗ T ∘ₗ Φ₁.map) 1) := by rw [one_smul]
      _ = ((d₁ : ℂ) * (1 / (d₁ : ℂ))) • ((Φ₂.map ∘ₗ T ∘ₗ Φ₁.map) 1) := by
            rw [mul_one_div_cancel hd₁]
      _ = (d₁ : ℂ) • ((1 / (d₁ : ℂ)) • ((Φ₂.map ∘ₗ T ∘ₗ Φ₁.map) 1)) :=
            (smul_smul _ _ _).symm
      _ = (d₁ : ℂ) • (κ • (1 : Matrix (Fin d₂) (Fin d₂) ℂ)) := by rw [← hκ]
      _ = ((d₁ : ℂ) * κ) • (1 : Matrix (Fin d₂) (Fin d₂) ℂ) := smul_smul _ _ _
  · -- Clause 2: `(Φ₂ ∘ T ∘ Φ₁)*(𝟙) ∝ 𝟙`, from the output-side minimisation.
    have hN₁ : ∃ κ : ℂ,
        Matrix.traceLeft (ChoiRectangular.choiMatrix (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map)) =
          κ • 1 := by
      apply posDef_orbit_min_isScalar hM₁pd
      · rw [hC, hX S₁]
        exact (hM₁pd.posSemidef.mul_mul_conjTranspose_same S₁)
      · rw [hC, hX S₁, Matrix.det_mul, Matrix.det_mul, hS₁det, Matrix.det_conjTranspose,
          hS₁det]; simp
      · intro S hS
        have e1 : (Matrix.trace (Matrix.traceLeft (ChoiRectangular.choiMatrix
            (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map)))).re
            = (Matrix.trace ((S₂ ⊗ₖ S₁) * ChoiRectangular.choiMatrix T *
                (S₂ ⊗ₖ S₁)ᴴ)).re := by
          rw [hC, ← Matrix.trace_eq_trace_traceLeft]
        have e2 : (Matrix.trace (S * Matrix.traceLeft ρ₂ * Sᴴ)).re
            = (Matrix.trace ((S₂ ⊗ₖ S) * ChoiRectangular.choiMatrix T *
                (S₂ ⊗ₖ S)ᴴ)).re := by
          rw [← hX S, ← Matrix.trace_eq_trace_traceLeft]
        rw [e1, e2]
        exact hmin S S₂ hS hS₂det
    obtain ⟨κ, hκ⟩ := hN₁
    rw [ChoiRectangular.traceLeft_choiMatrix] at hκ
    refine ⟨(d₁ : ℂ) * κ, ?_⟩
    have hT : (Matrix.traceAdjointMap (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map) 1).transpose =
        ((d₁ : ℂ) * κ) • (1 : Matrix (Fin d₁) (Fin d₁) ℂ) := by
      calc (Matrix.traceAdjointMap (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map) 1).transpose
          = (1 : ℂ) •
              (Matrix.traceAdjointMap (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map) 1).transpose := by
            rw [one_smul]
        _ = ((d₁ : ℂ) * (1 / (d₁ : ℂ))) •
              (Matrix.traceAdjointMap (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map) 1).transpose := by
            rw [mul_one_div_cancel hd₁]
        _ = (d₁ : ℂ) • ((1 / (d₁ : ℂ)) •
              (Matrix.traceAdjointMap (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map) 1).transpose) :=
              (smul_smul _ _ _).symm
        _ = (d₁ : ℂ) • (κ • (1 : Matrix (Fin d₁) (Fin d₁) ℂ)) := by rw [← hκ]
        _ = ((d₁ : ℂ) * κ) • (1 : Matrix (Fin d₁) (Fin d₁) ℂ) := smul_smul _ _ _
    calc Matrix.traceAdjointMap (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map) 1
        = (((d₁ : ℂ) * κ) • (1 : Matrix (Fin d₁) (Fin d₁) ℂ)).transpose := by
          rw [← Matrix.transpose_transpose
            (Matrix.traceAdjointMap (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map) 1), hT]
      _ = ((d₁ : ℂ) * κ) • (1 : Matrix (Fin d₁) (Fin d₁) ℂ) := by
          rw [Matrix.transpose_smul, Matrix.transpose_one]

end RectangularNormalForm

end Wolf
