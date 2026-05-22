/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.NormalReduction.TPGauge

/-!
# Positive-weight normalization for the PGVWC07 witness

This module records the finite-family scalar normalization of the positive
weights in the positive-length PGVWC07 canonical-form witness.

Pérez-García, Verstraete, Wolf, and Cirac, Theorem Th:TIcanonical, proof
lines 765--766, says that the spectral radius may be normalized without loss
of generality.  The theorem below proves the finite positive-weight part of
that convention: divide all weights by their largest value, so that every
normalized weight has norm at most one and one has norm one.  The statement
also records the global scalar factor on every positive-length MPV
coefficient.

The remaining source-facing boundary is not the finite maximum argument, but
the state-equivalence convention under which the global length-dependent
scalar is treated as a projective normalization.  This boundary is recorded in
`docs/paper-gaps/pgvwc07_ti_canonical_form_scope.tex`.

The projective formulation below makes that convention explicit: after the
maximum normalization, the original tensor and the normalized weighted block
tensor are `NonzeroProportionalMPV₂`.
-/

open scoped Matrix ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- Normalize the positive weights in a nonempty PGVWC07 positive-length
witness by their largest value.

Pérez-García, Verstraete, Wolf, and Cirac, Theorem Th:TIcanonical, proof
lines 765--766, says that the spectral radius may be normalized without loss
of generality.  This theorem records the corresponding scalar convention for
the positive-length witness: after dividing all weights by their maximum, every
new weight has norm at most one and one weight has norm one.  The conclusion
also records the global factor `scale ^ N` on length-`N` MPV coefficients. -/
theorem PGVWC07PositiveLengthWitness.exists_weight_normalization
    {A : MPSTensor d D} (W : PGVWC07PositiveLengthWitness (d := d) (D := D) A)
    (hr : 0 < W.r) :
    ∃ (scale : ℝ) (ν : Fin W.r → ℂ),
      0 < scale ∧
      (∀ k, ∃ a : ℝ, 0 < a ∧ ν k = (a : ℂ)) ∧
      (∀ k, ‖ν k‖ ≤ 1) ∧
      (∃ k, ‖ν k‖ = 1) ∧
      (∀ k, W.weights k = (scale : ℂ) * ν k) ∧
      (∀ (N : ℕ), 0 < N → ∀ σ : Fin N → Fin d,
        mpv A σ =
          (scale : ℂ) ^ N *
            mpv (toTensorFromBlocks (d := d) (μ := ν) W.blocks) σ) := by
  classical
  letI : Nonempty (Fin W.r) := ⟨⟨0, hr⟩⟩
  let a : Fin W.r → ℝ := fun k => Classical.choose (W.weight_pos k)
  have ha_pos : ∀ k, 0 < a k := by
    intro k
    exact (Classical.choose_spec (W.weight_pos k)).1
  have ha_weight : ∀ k, W.weights k = (a k : ℂ) := by
    intro k
    exact (Classical.choose_spec (W.weight_pos k)).2
  have hImageNonempty : (Finset.univ.image a).Nonempty :=
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin W.r)).Nonempty).image a
  let scale : ℝ := (Finset.univ.image a).max' hImageNonempty
  have hle : ∀ k, a k ≤ scale := by
    intro k
    exact Finset.le_max' _ _ (by simp [a])
  have hscale_pos : 0 < scale := by
    let k0 : Fin W.r := ⟨0, hr⟩
    exact lt_of_lt_of_le (ha_pos k0) (hle k0)
  have hscale_mem : scale ∈ Finset.univ.image a := by
    exact Finset.max'_mem _ _
  obtain ⟨kmax, _, hkmax⟩ := Finset.mem_image.mp hscale_mem
  let ν : Fin W.r → ℂ := fun k => (((a k / scale) : ℝ) : ℂ)
  have hscale_ne : scale ≠ 0 := ne_of_gt hscale_pos
  have hweight_eq : ∀ k, W.weights k = (scale : ℂ) * ν k := by
    intro k
    calc
      W.weights k = (a k : ℂ) := ha_weight k
      _ = (scale : ℂ) * (((a k / scale : ℝ) : ℂ)) := by
            rw [← Complex.ofReal_mul]
            have hmul : scale * (a k / scale) = a k := by
              field_simp [hscale_ne]
            rw [hmul]
      _ = (scale : ℂ) * ν k := rfl
  refine ⟨scale, ν, hscale_pos, ?_, ?_, ?_, hweight_eq, ?_⟩
  · intro k
    exact ⟨a k / scale, div_pos (ha_pos k) hscale_pos, rfl⟩
  · intro k
    have hdiv_le : a k / scale ≤ 1 := (div_le_one hscale_pos).mpr (hle k)
    calc
      ‖ν k‖ = |a k| / |scale| := by simp [ν]
      _ = a k / scale := by rw [abs_of_pos (ha_pos k), abs_of_pos hscale_pos]
      _ ≤ 1 := hdiv_le
  · refine ⟨kmax, ?_⟩
    have hratio : a kmax / scale = 1 := by
      rw [hkmax]
      exact div_self hscale_ne
    calc
      ‖ν kmax‖ = |a kmax| / |scale| := by simp [ν]
      _ = a kmax / scale := by
        rw [abs_of_pos (ha_pos kmax), abs_of_pos hscale_pos]
      _ = 1 := hratio
  · intro N hN σ
    calc
      mpv A σ = mpv (toTensorFromBlocks (d := d) (μ := W.weights) W.blocks) σ :=
        W.sameMPV_pos N hN σ
      _ = mpv (toTensorFromBlocks (d := d) (μ := fun k => (scale : ℂ) * ν k)
            W.blocks) σ := by
          have hfun : W.weights = fun k => (scale : ℂ) * ν k := funext hweight_eq
          rw [hfun]
      _ = (scale : ℂ) ^ N *
            mpv (toTensorFromBlocks (d := d) (μ := ν) W.blocks) σ :=
          mpv_toTensorFromBlocks_weight_mul_left (d := d) (c := (scale : ℂ))
            (μ := ν) W.blocks σ

/-- Normalized positive weights give the same projective finite-ring state
family.

Pérez-García, Verstraete, Wolf, and Cirac, Theorem Th:TIcanonical, proof
lines 765--766, treats the spectral-radius normalization as a convention on the
state family.  After the finite maximum normalization above, exact coefficients
are multiplied by the global factor `scale ^ N` at positive length.  This
theorem records the corresponding projective statement using
`NonzeroProportionalMPV₂`: the proportionality scalar is nonzero at every
length. -/
theorem PGVWC07PositiveLengthWitness.exists_weight_normalization_projective
    {A : MPSTensor d D} (W : PGVWC07PositiveLengthWitness (d := d) (D := D) A)
    (hr : 0 < W.r) :
    ∃ (scale : ℝ) (ν : Fin W.r → ℂ),
      0 < scale ∧
      (∀ k, ∃ a : ℝ, 0 < a ∧ ν k = (a : ℂ)) ∧
      (∀ k, ‖ν k‖ ≤ 1) ∧
      (∃ k, ‖ν k‖ = 1) ∧
      (∀ k, W.weights k = (scale : ℂ) * ν k) ∧
      NonzeroProportionalMPV₂ A (toTensorFromBlocks (d := d) (μ := ν) W.blocks) := by
  classical
  obtain ⟨scale, ν, hscale_pos, hν_pos, hν_le, hν_unit, hweight, hMPV⟩ :=
    W.exists_weight_normalization hr
  refine ⟨scale, ν, hscale_pos, hν_pos, hν_le, hν_unit, hweight, ?_⟩
  have htotal_pos : 0 < ∑ k : Fin W.r, W.dim k := by
    let k0 : Fin W.r := ⟨0, hr⟩
    have hle : W.dim k0 ≤ ∑ k : Fin W.r, W.dim k :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)
    exact lt_of_lt_of_le (W.dim_pos k0) hle
  have htotal_ne : ((∑ k : Fin W.r, W.dim k : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt htotal_pos
  have hD_pos : 0 < D := lt_of_lt_of_le htotal_pos W.bondDim_le
  have hD_ne : (D : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hD_pos
  intro N
  by_cases hN : N = 0
  · subst N
    refine ⟨(D : ℂ) / ((∑ k : Fin W.r, W.dim k : ℕ) : ℂ),
      div_ne_zero hD_ne htotal_ne, fun σ => ?_⟩
    calc
      mpv A σ = (D : ℂ) := mpv_zero_length A σ
      _ = ((D : ℂ) / ((∑ k : Fin W.r, W.dim k : ℕ) : ℂ)) *
            ((∑ k : Fin W.r, W.dim k : ℕ) : ℂ) := by
              field_simp [htotal_ne]
      _ = ((D : ℂ) / ((∑ k : Fin W.r, W.dim k : ℕ) : ℂ)) *
            mpv (toTensorFromBlocks (d := d) (μ := ν) W.blocks) σ := by
              simp
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    refine ⟨(scale : ℂ) ^ N, pow_ne_zero N ?_, fun σ => ?_⟩
    · exact Complex.ofReal_ne_zero.mpr (ne_of_gt hscale_pos)
    · exact hMPV N hNpos σ

/-- A nonzero positive-length MPV coefficient forces the PGVWC07 witness to
have at least one block.

Pérez-García, Verstraete, Wolf, and Cirac, Theorem Th:TIcanonical, lines
742--763, describes the nonzero canonical-form blocks.  In the positive-length
witness, an empty block family would make the weighted nonzero-block tensor
have zero positive-length MPV coefficients.  Thus a tensor with a nonzero
positive-length coefficient has a nonempty witness. -/
theorem PGVWC07PositiveLengthWitness.block_count_pos_of_exists_ne_zero_mpv
    {A : MPSTensor d D} (W : PGVWC07PositiveLengthWitness (d := d) (D := D) A)
    (hA : ∃ (N : ℕ), 0 < N ∧ ∃ σ : Fin N → Fin d, mpv A σ ≠ 0) :
    0 < W.r := by
  classical
  obtain ⟨N, hN, σ, hσ⟩ := hA
  by_contra hnot
  have hr0 : W.r = 0 := Nat.eq_zero_of_not_pos hnot
  have hblock :
      mpv (toTensorFromBlocks (d := d) (μ := W.weights) W.blocks) σ = 0 := by
    haveI : IsEmpty (Fin W.r) := by
      rw [hr0]
      infer_instance
    rw [mpv_toTensorFromBlocks_eq_sum]
    simp
  have hAeq : mpv A σ = 0 := by
    calc
      mpv A σ =
          mpv (toTensorFromBlocks (d := d) (μ := W.weights) W.blocks) σ :=
            W.sameMPV_pos N hN σ
      _ = 0 := hblock
  exact hσ hAeq

/-- Normalized projective PGVWC07 canonical-form blocks and weights for a
nonzero positive-length state family.

Pérez-García, Verstraete, Wolf, and Cirac, Theorem Th:TIcanonical, lines
742--763 and proof lines 765--766.  This theorem composes the arbitrary-input
positive-length PGVWC07 witness with the projective weight normalization above.

**Scope restriction:** The statement assumes that some positive-length MPV
coefficient of the original tensor is nonzero.  This excludes the empty
nonzero-block case and lets the normalization include a block of unit weight.
The remaining source-facing choice for the unrestricted theorem is recorded in
`docs/paper-gaps/pgvwc07_ti_canonical_form_scope.tex`. -/
theorem exists_pgvwc07_normalized_projective_form_of_exists_ne_zero_mpv
    (A : MPSTensor d D)
    (hA : ∃ (N : ℕ), 0 < N ∧ ∃ σ : Fin N → Fin d, mpv A σ ≠ 0) :
    ∃ (r : ℕ) (dim : Fin r → ℕ)
      (ν : Fin r → ℂ)
      (blocks : (k : Fin r) → MPSTensor d (dim k)),
      0 < r ∧
      (∀ k,
        ∃ Λ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
          Λ.PosDef ∧
          Λ.IsDiag ∧
          (∑ i : Fin d, blocks k i * (blocks k i)ᴴ = 1) ∧
          transferMap (d := d) (D := dim k) (fun i => (blocks k i)ᴴ) Λ = Λ) ∧
      (∀ k,
        ∀ X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
          transferMap (d := d) (D := dim k) (blocks k) X = X →
            ∃ c : ℂ, X = c • (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) ∧
      (∀ k, ∃ a : ℝ, 0 < a ∧ ν k = (a : ℂ)) ∧
      (∀ k, ‖ν k‖ ≤ 1) ∧
      (∃ k, ‖ν k‖ = 1) ∧
      (∀ k, 0 < dim k) ∧
      NonzeroProportionalMPV₂ A (toTensorFromBlocks (d := d) (μ := ν) blocks) ∧
      ∑ k : Fin r, dim k ≤ D := by
  classical
  obtain ⟨W⟩ := exists_pgvwc07_positiveLengthWitness (d := d) (D := D) A
  have hr : 0 < W.r := W.block_count_pos_of_exists_ne_zero_mpv hA
  obtain ⟨_scale, ν, _hscale_pos, hν_pos, hν_le, hν_unit, _hweight, hMPV⟩ :=
    W.exists_weight_normalization_projective hr
  exact ⟨W.r, W.dim, ν, W.blocks, hr, W.dual_fixed, W.scalar_fixed, hν_pos,
    hν_le, hν_unit, W.dim_pos, hMPV, W.bondDim_le⟩

/-- Normalized PGVWC07 canonical-form blocks with exact positive-length MPV
equality after the global tensor rescaling.

Pérez-García, Verstraete, Wolf, and Cirac, Theorem Th:TIcanonical, proof
lines 765--766, says that the spectral radius may be normalized without loss
of generality.  This theorem records the exact-coefficient version of that
convention: for a tensor with a nonzero positive-length MPV coefficient, the
finite positive weights may be divided by their maximum, and the original
tensor may be divided by the same positive scalar.  After this global tensor
rescaling, the normalized block tensor has exactly the same positive-length MPV
coefficients. -/
theorem exists_pgvwc07_normalized_exact_form_after_rescaling_of_exists_ne_zero_mpv
    (A : MPSTensor d D)
    (hA : ∃ (N : ℕ), 0 < N ∧ ∃ σ : Fin N → Fin d, mpv A σ ≠ 0) :
    ∃ (scale : ℝ) (r : ℕ) (dim : Fin r → ℕ)
      (ν : Fin r → ℂ)
      (blocks : (k : Fin r) → MPSTensor d (dim k)),
      0 < scale ∧
      0 < r ∧
      (∀ k,
        ∃ Λ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
          Λ.PosDef ∧
          Λ.IsDiag ∧
          (∑ i : Fin d, blocks k i * (blocks k i)ᴴ = 1) ∧
          transferMap (d := d) (D := dim k) (fun i => (blocks k i)ᴴ) Λ = Λ) ∧
      (∀ k,
        ∀ X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
          transferMap (d := d) (D := dim k) (blocks k) X = X →
            ∃ c : ℂ, X = c • (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) ∧
      (∀ k, ∃ a : ℝ, 0 < a ∧ ν k = (a : ℂ)) ∧
      (∀ k, ‖ν k‖ ≤ 1) ∧
      (∃ k, ‖ν k‖ = 1) ∧
      (∀ k, 0 < dim k) ∧
      SameMPV₂Pos
        (fun i => (((scale : ℂ)⁻¹) • A i))
        (toTensorFromBlocks (d := d) (μ := ν) blocks) ∧
      ∑ k : Fin r, dim k ≤ D := by
  classical
  obtain ⟨W⟩ := exists_pgvwc07_positiveLengthWitness (d := d) (D := D) A
  have hr : 0 < W.r := W.block_count_pos_of_exists_ne_zero_mpv hA
  obtain ⟨scale, ν, hscale_pos, hν_pos, hν_le, hν_unit, _hweight, hMPV⟩ :=
    W.exists_weight_normalization hr
  have hscale_ne : (scale : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hscale_pos)
  refine ⟨scale, W.r, W.dim, ν, W.blocks, hscale_pos, hr, W.dual_fixed,
    W.scalar_fixed, hν_pos, hν_le, hν_unit, W.dim_pos, ?_, W.bondDim_le⟩
  intro N hN σ
  have hpow : ((scale : ℂ) ^ N)⁻¹ * (scale : ℂ) ^ N = 1 := by
    simp [pow_ne_zero N hscale_ne]
  calc
    mpv (fun i => (((scale : ℂ)⁻¹) • A i)) σ
        = ((scale : ℂ)⁻¹) ^ N * mpv A σ := mpv_smul ((scale : ℂ)⁻¹) A σ
    _ = ((scale : ℂ)⁻¹) ^ N *
          ((scale : ℂ) ^ N *
            mpv (toTensorFromBlocks (d := d) (μ := ν) W.blocks) σ) := by
        rw [hMPV N hN σ]
    _ = (((scale : ℂ)⁻¹) ^ N * (scale : ℂ) ^ N) *
          mpv (toTensorFromBlocks (d := d) (μ := ν) W.blocks) σ := by
        ring
    _ = mpv (toTensorFromBlocks (d := d) (μ := ν) W.blocks) σ := by
        simp [hpow]

/-- Arbitrary-input zero/nonzero dichotomy for the projective PGVWC07
canonical-form statement.

Pérez-García, Verstraete, Wolf, and Cirac, Theorem Th:TIcanonical, lines
742--763 and proof lines 765--766.  This is a scope-separating formulation of
the nonzero positive-length theorem above: either all positive-length MPV
coefficients vanish, or the tensor has a nonempty normalized projective
PGVWC07 block form.

**Scope restriction:** This is not the unrestricted source theorem.  It records
the zero positive-length branch explicitly; the source-facing convention for
the length-zero/all-zero case is recorded in
`docs/paper-gaps/pgvwc07_ti_canonical_form_scope.tex`. -/
theorem exists_pgvwc07_normalized_projective_form_or_forall_pos_mpv_eq_zero
    (A : MPSTensor d D) :
    (∀ (N : ℕ), 0 < N → ∀ σ : Fin N → Fin d, mpv A σ = 0) ∨
    ∃ (r : ℕ) (dim : Fin r → ℕ)
      (ν : Fin r → ℂ)
      (blocks : (k : Fin r) → MPSTensor d (dim k)),
      0 < r ∧
      (∀ k,
        ∃ Λ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
          Λ.PosDef ∧
          Λ.IsDiag ∧
          (∑ i : Fin d, blocks k i * (blocks k i)ᴴ = 1) ∧
          transferMap (d := d) (D := dim k) (fun i => (blocks k i)ᴴ) Λ = Λ) ∧
      (∀ k,
        ∀ X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
          transferMap (d := d) (D := dim k) (blocks k) X = X →
            ∃ c : ℂ, X = c • (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) ∧
      (∀ k, ∃ a : ℝ, 0 < a ∧ ν k = (a : ℂ)) ∧
      (∀ k, ‖ν k‖ ≤ 1) ∧
      (∃ k, ‖ν k‖ = 1) ∧
      (∀ k, 0 < dim k) ∧
      NonzeroProportionalMPV₂ A (toTensorFromBlocks (d := d) (μ := ν) blocks) ∧
      ∑ k : Fin r, dim k ≤ D := by
  classical
  by_cases hA : ∃ (N : ℕ), 0 < N ∧ ∃ σ : Fin N → Fin d, mpv A σ ≠ 0
  · exact Or.inr (exists_pgvwc07_normalized_projective_form_of_exists_ne_zero_mpv A hA)
  · refine Or.inl ?_
    intro N hN σ
    by_contra hσ
    exact hA ⟨N, hN, σ, hσ⟩

end MPSTensor
