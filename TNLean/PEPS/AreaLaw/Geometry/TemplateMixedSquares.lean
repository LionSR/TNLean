/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.TemplateDyadicRows

/-!
# Mixed-square estimates for actual templates and their shells

Finite-union and difference subadditivity turn the proved piece estimate into
quantitative counts for Definition 9.3 templates. The existing scale inequality
absorbs piece diameters. The capped partition then bounds selected squares at
every scale below the cap. All dilations are of the sampled integer sets.

Original proofs from `scanner:mixed-piece` and `scanner:templates`, lines
622–649 of `08-scanner.tex`, OpenAI, *A two-dimensional area law from a global
spectral gap*, September 24, 2026, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
No upstream Lean proof text is reused. Safe clearance and entropy are separate.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

private theorem template_scale_nat {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl) :
    24 * T.pieceCount * (s₀ + 1) ≤ n := by
  have hscale : (24 : ℝ) * T.pieceCount * (s₀ + 1) ≤ n := by
    calc
      (24 : ℝ) * T.pieceCount * (s₀ + 1) ≤ Ctpl * T.pieceCount * (s₀ + 1) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hC)
          (show 0 ≤ (T.pieceCount : ℝ) * (s₀ + 1) by positivity)]
      _ ≤ n := T.scale
  exact_mod_cast hscale

/-- Before using the template scale inequality, mixed-square counts sum over
the actual sampled pieces, with no disjointness assumption. -/
theorem Template.card_mixedDyadicIndices_dilation_pieceCount_le {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (r k : ℕ) :
    2 ^ k * (mixedDyadicIndices (ambientDilation T.points r) k).card ≤
      24 * T.pieceCount * (s₀ + r + 2 ^ k) := by
  have heq : ambientDilation T.points r =
      Finset.univ.biUnion (fun i ↦ ambientDilation (T.sample i) r) := by
    rw [T.cover]
    ext x
    simp only [mem_ambientDilation_iff, Finset.mem_biUnion, Finset.mem_univ, true_and]
    aesop
  rw [heq]
  calc
    _ ≤ 2 ^ k * ∑ i ∈ Finset.univ,
        (mixedDyadicIndices (ambientDilation (T.sample i) r) k).card :=
      Nat.mul_le_mul_left _ (card_mixedDyadicIndices_biUnion_le _ _ k)
    _ = ∑ i ∈ Finset.univ,
        2 ^ k * (mixedDyadicIndices (ambientDilation (T.sample i) r) k).card := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin T.pieceCount)), 24 * (s₀ + r + 2 ^ k) :=
      Finset.sum_le_sum (fun i _ ↦ T.card_mixedDyadicIndices_sample_dilation_le i r k)
    _ = _ := by simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- The scaled mixed-square count of the undilated actual template. -/
theorem Template.card_mixedDyadicIndices_le {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl) (k : ℕ) :
    2 ^ k * (mixedDyadicIndices T.points k).card ≤ n + 24 * T.pieceCount * 2 ^ k := by
  have h := T.card_mixedDyadicIndices_dilation_pieceCount_le 0 k
  simp only [ambientDilation_zero, Nat.add_zero] at h
  have hn := template_scale_nat T hC
  nlinarith

/-- At every dyadic scale, integer dilation up to the template scale has
`O(N₀ + n/u)` mixed squares, written without rounding or division. -/
theorem Template.card_mixedDyadicIndices_dilation_le {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl) (r k : ℕ) (hr : r ≤ s₀) :
    2 ^ k * (mixedDyadicIndices (ambientDilation T.points r) k).card ≤
      2 * n + 24 * T.pieceCount * 2 ^ k := by
  have h := T.card_mixedDyadicIndices_dilation_pieceCount_le r k
  have hn := template_scale_nat T hC
  nlinarith [Nat.mul_le_mul_left (24 * T.pieceCount) hr]

/-- The actual shell inherits the mixed-square bound from its two defining
unions. This includes radius zero and disconnected or overlapping pieces. -/
theorem Template.card_mixedDyadicIndices_shell_le {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl) (r k : ℕ) (hr : r ≤ s₀) :
    2 ^ k * (mixedDyadicIndices (ambientDilation T.points r \ T.points) k).card ≤
      3 * n + 48 * T.pieceCount * 2 ^ k := by
  have hd := T.card_mixedDyadicIndices_dilation_le hC r k hr
  have hc := T.card_mixedDyadicIndices_le hC k
  have h := Nat.mul_le_mul_left (2 ^ k)
    (card_mixedDyadicIndices_sdiff_le (ambientDilation T.points r) T.points k)
  nlinarith

/-- Below the cap and at sides at most `s₀`, the actual shell partition has
at most `14*n/u` selected squares. The mixed-parent count is proved above. -/
theorem Template.card_cappedDyadicPartition_shell_below_cap_le {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl) (r K k : ℕ)
    (hr : r ≤ s₀) (hk : k < K) (hu : 2 ^ k ≤ s₀) :
    2 ^ k * ((cappedDyadicPartition (ambientDilation T.points r \ T.points) K).filter
      (fun c ↦ c.1 = k)).card ≤ 14 * n := by
  have hparent := T.card_mixedDyadicIndices_shell_le hC r (k + 1) hr
  have hchildren := Nat.mul_le_mul_left (2 ^ k)
    (card_cappedDyadicPartition_below_cap_le
      (ambientDilation T.points r \ T.points) K k hk)
  have hn := template_scale_nat T hC
  have hsize := Nat.mul_le_mul_left (24 * T.pieceCount) hu
  rw [pow_succ] at hparent
  nlinarith

end TNLean.PEPS.AreaLaw.Geometry
