/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.TemplateLayers
import TNLean.PEPS.AreaLaw.EntropyDimension

/-!
# Entropy cost of a partial template depth row

Adding an arbitrary part of one template depth row changes the actual regional
entropy by at most `n * log q`. This uses only purity, normalization and the
geometric layer bound. Separation, a spectral gap and a safe-box estimate are
not needed for this step.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
2026, Lemma 9.4 (`scanner:templates`), proof, `08-scanner.tex`, lines 666–667,
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.AreaLaw

/-- Adding a disjoint region changes entropy by at most its entropy.
Source: Lemma 9.4, partial-row step; both signs follow from subadditivity and
pure-state complementarity of the actual regional reductions. -/
theorem abs_regionalEntropy_union_sub_le (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1) (R B : Finset (Site Λ))
    (hRB : Disjoint R B) :
    |regionalEntropy Λ q Ω (R ∪ B) - regionalEntropy Λ q Ω R| ≤
      regionalEntropy Λ q Ω B := by
  classical
  simp only [regionalEntropy_eq_finiteProduct]
  let β := fun _ : Site Λ ↦ Fin q
  have hu := FiniteProduct.entropy_union_le β Ω hΩ R B hRB
  have hd : Disjoint (R ∪ B)ᶜ B := by
    apply Finset.disjoint_left.mpr
    intro x hx hb
    exact Finset.mem_compl.mp hx (Finset.mem_union_right R hb)
  have he : (R ∪ B)ᶜ ∪ B = Rᶜ := by
    ext x
    have hn : x ∈ R → x ∉ B := fun hx ↦ Finset.disjoint_left.mp hRB hx
    simp only [Finset.mem_union, Finset.mem_compl]
    tauto
  have hl := FiniteProduct.entropy_union_le β Ω hΩ (R ∪ B)ᶜ B hd
  rw [he, FiniteProduct.entropy_compl, FiniteProduct.entropy_compl] at hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

namespace Geometry

/-- Lemma 9.4's partial-final-row cost, with its explicit `n log q` constant.
Here filtering `A` by an ambient set is exactly its physical intersection with
that set. Thus the two regions are `A ∩ ((T_{j-1} \ T) ∪ Y)` and
`A ∩ (T_{j-1} \ T)`, with arbitrary `Y ⊆ T_j \ T_{j-1}`.
This is the partial-row step only, not the safe-box shell estimate. -/
theorem template_partial_row_entropy_le (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (hq : 1 ≤ q) (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1)
    {Ctpl : ℝ} {n s₀ : ℕ} (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl)
    (A : Finset (Site Λ)) (j : ℕ) (hj : 1 ≤ j) (hjs : j ≤ s₀)
    (Y : Finset (ℤ × ℤ))
    (hY : Y ⊆ ambientDilation T.points j \ ambientDilation T.points (j - 1)) :
    |regionalEntropy Λ q Ω
        (A.filter fun x ↦ x.val ∈ (ambientDilation T.points (j - 1) \ T.points) ∪ Y) -
      regionalEntropy Λ q Ω
        (A.filter fun x ↦ x.val ∈ ambientDilation T.points (j - 1) \ T.points)| ≤
      n * Real.log q := by
  classical
  let R := A.filter fun x ↦ x.val ∈ ambientDilation T.points (j - 1) \ T.points
  let B := A.filter fun x ↦ x.val ∈ Y
  have hd : Disjoint R B := by
    apply Finset.disjoint_left.mpr
    intro x hx hb
    have hx' := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).2).1
    exact (Finset.mem_sdiff.mp (hY (Finset.mem_filter.mp hb).2)).2 hx'
  have he : (A.filter fun x ↦
      x.val ∈ (ambientDilation T.points (j - 1) \ T.points) ∪ Y) = R ∪ B := by
    ext x
    simp only [R, B, Finset.mem_filter, Finset.mem_union]
    tauto
  rw [he]
  have hcard : B.card ≤ n := by
    have hBY : B.image Subtype.val ⊆ Y := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hz).2
    calc
      B.card = (B.image Subtype.val).card :=
        (Finset.card_image_of_injective B Subtype.val_injective).symm
      _ ≤ Y.card := Finset.card_le_card hBY
      _ ≤ (ambientDilation T.points j \ ambientDilation T.points (j - 1)).card :=
        Finset.card_le_card hY
      _ ≤ n := template_layer_card_le T hC j hj hjs
  calc
    |regionalEntropy Λ q Ω (R ∪ B) - regionalEntropy Λ q Ω R| ≤
        regionalEntropy Λ q Ω B := abs_regionalEntropy_union_sub_le Λ q Ω hΩ R B hd
    _ ≤ B.card * Real.log q := regionalEntropy_le_card_mul_log Λ q Ω hΩ B
    _ ≤ n * Real.log q := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      (Real.log_nonneg (by exact_mod_cast hq))

end Geometry
end TNLean.PEPS.AreaLaw
