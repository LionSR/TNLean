/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.Lattice.IntegerRectangle
import TNLean.PEPS.AreaLaw.Templates.LatticeDyadicRect
import TNLean.PEPS.AreaLaw.Templates.CappedDyadicEntropyCover
import TNLean.PEPS.AreaLaw.Templates.RectangleShellCounts
import TNLean.PEPS.AreaLaw.SafeRectangles.InitialBoxEstimate
import Mathlib.Data.Nat.Log
import QICLean.ManyBody.Hamiltonian.GroundSpace

/-!
# Safety inside a dilated parent rectangle

A safe parent controls every smaller rectangle contained in its dilation,
provided the smaller rectangle's safety radius plus the dilation radius
fits inside the parent's safety radius.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, proof of Proposition 9.5 (`prop:small-box`),
`08-scanner.tex`, lines 707–729, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This is the geometric clearance step for the rectangle bootstrap.
Original formalization from the manuscript; no upstream Lean proof text reused.

## Safety of selected squares in a weak-rectangle shell

A safe rectangle controls the selected squares in its dilated shell
whenever the square and dilation radii fit in its original clearance.
This uses the safe-box condition and does not require template separation.

Source: OpenAI, A two-dimensional area law from a global spectral gap,
September 24, 2026, proof of Proposition 9.5, 08-scanner.tex, lines 717–729,
at openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
The scalar clearance condition is stated explicitly for this auxiliary lemma.
Original formalization from the manuscript; no upstream Lean proof text reused.

## Entropy of a weak-rectangle shell from a safe-box estimate

A pointwise safe-box estimate and the parent's safe-box clearance bound
the entropy of its actual physical shell. The weighted partition and
the safety of all selected squares are derived from the rectangle.

Source: OpenAI, A two-dimensional area law from a global spectral gap,
September 24, 2026, proof of Proposition 9.5,
08-scanner.tex, lines 717–729,
at openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
This is a conditional shell estimate, not the one-step entropy improvement
or Proposition 9.5 itself.
Original formalization from the manuscript; no upstream Lean proof text reused.

## Uniform weak-rectangle shell entropy at the initial exponent

The initial safe-rectangle estimate bounds the entropy of the actual shell
of the same ground vector. One nonnegative constant and one initial exponent
are chosen before every safety parameter, domain, Hamiltonian, energy,
vector, cut, parent rectangle and shell scale.

This is an auxiliary consequence at the initial existential exponent.
The pointwise safe-rectangle estimate is derived from the gapped-ground-state
hypothesis, and both the pointwise and shell estimates concern the original
vector. The arbitrary-exponent shell estimate and physical exponent
improvement remain separate results.

### References

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
2026, Proposition 3.3 (`prop:initial-box`), `02-initial.tex`, lines 590–604,
and the rectangle-shell entropy input in the proof of Proposition 9.5
(`prop:small-box`), `08-scanner.tex`, lines 717–729, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Original formalization from the manuscript; no upstream Lean proof text reused.
-/

open ManyBody (IntRect IsSafe rectRegion supDist)

section

namespace TNLean.PEPS.AreaLaw

/-- Safety passes from a parent to a rectangle in its dilation when the two
radii fit inside the parent's safety radius. Source: `08-scanner.tex`,
lines 723–729, in the proof of Proposition 9.5 (`prop:small-box`). -/
theorem IsSafe.of_subset_dilate {Λ : Finset (ℤ × ℤ)} {A : Finset ↥Λ}
    {D₀ j : ℕ} {Q Q' : IntRect} (hsafe : IsSafe Λ A D₀ Q)
    (hsub : Q'.toFinset ⊆ (Q.dilate j).toFinset)
    (hbudget : D₀ * Q'.size + j ≤ D₀ * Q.size) : IsSafe Λ A D₀ Q' := by
  intro e he z hz p hp
  by_contra! hnear
  have hzparent : z.1 ∈ (Q.dilate (D₀ * Q.size)).toFinset :=
    Q.toFinset_dilate_mono (d := j + D₀ * Q'.size) (by omega)
      (IntRect.mem_dilate_of_supDist_le (hsub hp) hnear)
  rw [IntRect.toFinset_dilate] at hzparent
  obtain ⟨v, hv, hvz⟩ := Finset.mem_biUnion.mp hzparent
  have hfar := hsafe e he z hz v hv
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hvz
  simp only [Finset.mem_Icc, supDist] at hx hy hfar
  omega

end TNLean.PEPS.AreaLaw

end

section

namespace TNLean.PEPS.AreaLaw

/-- Every selected square is safe when the cap and dilation radii fit in the
parent clearance. Source: proof of Proposition 9.5, 08-scanner.tex,
lines 723–729. -/
theorem IsSafe.isSafe_cappedDyadicPartition_shell
    {Λ : Finset (ℤ × ℤ)} {A : Finset ↥Λ} {D₀ : ℕ} {Q : IntRect}
    (hsafe : IsSafe Λ A D₀ Q) (j L K k : ℕ) (z : ℤ × ℤ)
    (hj : j ≤ L) (hcap : 2 ^ K ≤ L)
    (hbudget : D₀ * L + L ≤ D₀ * Q.size)
    (hcell : (k, z) ∈ Geometry.cappedDyadicPartition
      ((Q.dilate j).toFinset \ Q.toFinset) K) :
    IsSafe Λ A D₀ (Geometry.latticeDyadicRect k z) := by
  obtain ⟨hk, hsub, _⟩ := (Geometry.mem_cappedDyadicPartition _ _ _ _).mp hcell
  have hsize : (Geometry.latticeDyadicRect k z).size ≤ L := by
    rw [Geometry.size_latticeDyadicRect]
    exact (Nat.pow_le_pow_right (n := 2) (by decide) hk).trans hcap
  have hcellBudget : D₀ * (Geometry.latticeDyadicRect k z).size + j ≤ D₀ * Q.size :=
    (Nat.add_le_add (Nat.mul_le_mul_left D₀ hsize) hj).trans hbudget
  apply hsafe.of_subset_dilate (j := j) ?_ hcellBudget
  simpa only [Geometry.toFinset_latticeDyadicRect] using
    hsub.trans Finset.sdiff_subset

end TNLean.PEPS.AreaLaw

end

section

namespace TNLean.PEPS.AreaLaw

/-- The actual shell entropy under a pointwise estimate on safe rectangles.
Source: proof of Proposition 9.5, 08-scanner.tex, lines 717–729.
The explicit scalar budget supplies the selected squares' clearance. -/
theorem IntRect.regionEntropy_shell_le_of_safe_box
    (Λ : Finset (ℤ × ℤ)) (q D₀ : ℕ) (Ω : EuclideanSpace ℂ (↥Λ → Fin q)) (hΩ : ‖Ω‖ = 1)
    (A : Finset ↥Λ) (Q : IntRect) (hsafe : IsSafe Λ A D₀ Q)
    (j L K : ℕ) (hj : j ≤ L) (hL : L ≤ Q.size)
    (hlo : 2 ^ K ≤ L) (hhi : L < 2 ^ (K + 1))
    (hbudget : D₀ * L + L ≤ D₀ * Q.size)
    (e C : ℝ) (he : 0 < e) (hC : 0 ≤ C)
    (hbox : ∀ Q' : IntRect, IsSafe Λ A D₀ Q' →
      ManyBody.regionEntropy Ω (rectRegion A Q') ≤ C * (Q'.size : ℝ) ^ (1 + e)) :
    ManyBody.regionEntropy Ω
      (A.filter fun x ↦ x.1 ∈ (Q.dilate j).toFinset \ Q.toFinset) ≤
      C * (24 + 64 / ((2 : ℝ) ^ e - 1)) * (Q.size : ℝ) * (L : ℝ) ^ e := by
  have hsafeCells : ∀ c ∈ Geometry.cappedDyadicPartition
      ((Q.dilate j).toFinset \ Q.toFinset) K,
      IsSafe Λ A D₀ (Geometry.latticeDyadicRect c.1 c.2) := by
    intro c hc
    exact hsafe.isSafe_cappedDyadicPartition_shell j L K c.1 c.2 hj hlo hbudget hc
  have hcover := Geometry.regionEntropy_filter_le_weighted_cover
    Λ q D₀ Ω hΩ A ((Q.dilate j).toFinset \ Q.toFinset) K e C hsafeCells hbox
  have hweighted := mul_le_mul_of_nonneg_left
    (Q.sum_rpow_cappedDyadicPartition_shell_le j L K hj hL hlo hhi e he) hC
  exact hcover.trans (by simpa only [mul_assoc] using hweighted)

end TNLean.PEPS.AreaLaw

end

section

open scoped Matrix.Norms.L2Operator

open ManyBody (IsGapped groundSpace PlaneInteraction)

namespace TNLean.PEPS.AreaLaw

/-- One initial safe-box constant and exponent control all actual weak-rectangle
shells satisfying the clearance conditions. The dyadic cap is chosen inside
the proof; the zero-thickness shell is included. The physical vector is the
original gapped ground vector throughout.
Source: `02-initial.tex`, lines 590–604, and `08-scanner.tex`, lines 717–729,
at the pinned manuscript revision stated above. -/
theorem exists_regionEntropy_weak_rectangle_shell_le_rpow
    (q R : ℕ) (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ C e₀ : ℝ, 0 ≤ C ∧ 0 < e₀ ∧ e₀ < 1 ∧
      ∀ D₀ : ℕ, 2 * R + 10 < D₀ →
        ∀ (Λ : Finset (ℤ × ℤ)) (h : PlaneInteraction Λ q R) (_ : ∀ X, (h.term X).IsHermitian)
            (_ : ∀ X, ‖h.term X‖ ≤ J)
          (E₀ : ℝ) (Ω : EuclideanSpace ℂ (↥Λ → Fin q)),
          ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
          groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
          ∀ (A : Finset ↥Λ) (Q : IntRect), IsSafe Λ A D₀ Q →
            ∀ j L : ℕ, j ≤ L → L ≤ Q.size →
              D₀ * L + L ≤ D₀ * Q.size →
              ManyBody.regionEntropy Ω
                (A.filter fun x ↦ x.1 ∈ (Q.dilate j).toFinset \ Q.toFinset) ≤
                C * (24 + 64 / ((2 : ℝ) ^ e₀ - 1)) *
                  (Q.size : ℝ) * (L : ℝ) ^ e₀ := by
  obtain ⟨C, e₀, hC, he₀, he₀₁, hrect⟩ :=
    exists_regionEntropy_safe_rect_le_rpow q R hq hJ hΔ
  refine ⟨C, e₀, hC, he₀, he₀₁, ?_⟩
  intro D₀ hD₀ Λ h hh hhJ E₀ Ω hΩ hgap hspan A Q hsafe j L hj hL hbudget
  by_cases hLzero : L = 0
  · have hjzero : j = 0 := by omega
    simp [hjzero, hLzero, ManyBody.regionEntropy_empty _ Ω hΩ,
      Real.zero_rpow (ne_of_gt he₀)]
  · exact IntRect.regionEntropy_shell_le_of_safe_box
      Λ q D₀ Ω hΩ A Q hsafe j L (Nat.log 2 L) hj hL
      (Nat.pow_log_le_self 2 hLzero)
      (Nat.lt_pow_succ_log_self (b := 2) (by decide) L) hbudget
      e₀ C he₀ hC (hrect D₀ hD₀ Λ h hh hhJ E₀ Ω hΩ hgap hspan A)

end TNLean.PEPS.AreaLaw

end
