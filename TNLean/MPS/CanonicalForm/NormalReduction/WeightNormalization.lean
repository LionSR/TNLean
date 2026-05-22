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
scalar is harmless.  This boundary is recorded in
`docs/paper-gaps/pgvwc07_ti_canonical_form_scope.tex`.
-/

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

end MPSTensor
