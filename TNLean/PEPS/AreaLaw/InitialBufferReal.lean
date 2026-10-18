/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.InitialBuffer
import TNLean.PEPS.AreaLaw.Geometry.CellCounting

/-!
# Conditional entropy in a rectangle with real clearance

The buffered-rectangle estimate holds for every real safety parameter greater
than twice the interaction range plus ten. The padding and entropy constants
depend only on the local dimension, interaction range, interaction bound and
spectral gap, and are chosen before the safety parameter and physical data.

Real clearance implies the integer clearance at the interaction range plus
one used in the explicit-constant buffered-rectangle estimate. Thus the same
entropy argument applies without restricting the source's safety parameter
to natural numbers. The clearance is stated on the existing boundary endpoint
set; no additional safety predicate is introduced.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Lemma 3.2 (`lem:initial-buffer`), `02-initial.tex`,
lines 240–256; the safety parameter and definition are in lines 223–228.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized; no upstream Lean proof text reused.
-/

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw

/-- Conditional entropy in a buffered rectangle for every admissible real
clearance. The two constants precede the clearance and all physical instances.
Source: area-law Lemma 3.2 (`lem:initial-buffer`), `02-initial.tex`,
lines 240–256, with the safety convention in lines 223–228. -/
theorem exists_condEntropy_le_initialBuffer_real
    (q R : ℕ) (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ Cpad : ℕ, 1 ≤ Cpad ∧ ∃ Cbuf : ℝ, 0 ≤ Cbuf ∧
      ∀ D₀ : ℝ, 2 * (R : ℝ) + 10 < D₀ →
      ∀ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
        (E₀ : ℝ) (Ω : StateSpace Λ q),
        IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        ∀ (A : Finset (Site Λ)) (Q : IntRect),
          (∀ t ∈ Q.toFinset, ∀ z ∈ Geometry.boundaryEndpoints Λ A,
            D₀ * (Q.size : ℝ) < (supDist t z : ℝ)) →
          ∀ r : ℕ, 1 ≤ r → ∀ Q₀ : IntRect, Q₀.size ≤ r →
            (Q₀.dilate (Cpad * r)).toFinset ⊆ Q.toFinset →
            regionalEntropy Λ q Ω (rectRegion A Q₀ ∪
                (rectRegion A (Q₀.dilate (Cpad * r)) \ rectRegion A Q₀)) -
              regionalEntropy Λ q Ω (rectRegion A (Q₀.dilate (Cpad * r)) \ rectRegion A Q₀) ≤
            regionalEntropy Λ q Ω (rectRegion A Q₀) / 2 + Cbuf * r := by
  set Zmin : ℝ := max 4 (max
    (32 * bufferCrossConst R * (q : ℝ) ^ (2 * (1 + 2 * R * (R + 1))) * J / Δ)
    (128 * Real.sqrt ((1 + J / Δ) * bufferBudgetConst q R)))
  set Cpad : ℕ := ⌈(2 + ((R + 1 : ℕ) : ℝ)) * Real.exp ((R + 1 : ℕ) * Zmin)⌉₊ + R + 3
  have hCZ : (2 + ((R + 1 : ℕ) : ℝ)) * Real.exp ((R + 1 : ℕ) * Zmin) ≤ Cpad + 1 := by
    refine (Nat.le_ceil _).trans ?_
    exact_mod_cast (show
      ⌈(2 + ((R + 1 : ℕ) : ℝ)) * Real.exp ((R + 1 : ℕ) * Zmin)⌉₊ ≤ Cpad + 1 by omega)
  have hK : 0 ≤ bufferBudgetConst q R := zero_le_one.trans (one_le_bufferBudgetConst q R)
  refine ⟨Cpad, by omega,
    (1024 * Real.exp 1 * (J / Δ) * bufferBudgetConst q R + Cpad) / 2, by positivity, ?_⟩
  intro D₀ hD₀ Λ h E₀ Ω hgs A Q hclear r hr Q₀ hQ₀ hpad
  have hRD : ((R + 1 : ℕ) : ℝ) ≤ D₀ := by
    push_cast
    linarith [show (0 : ℝ) ≤ R from Nat.cast_nonneg R]
  have hsafe : IsSafe Λ A (R + 1) Q := by
    intro e he z hz p hp
    exact_mod_cast (mul_le_mul_of_nonneg_right hRD (Nat.cast_nonneg Q.size)).trans_lt
      (hclear p hp z.1 (Geometry.mem_boundaryEndpoints_of_mem_edgeBoundary he hz))
  exact condEntropy_le_initialBuffer_of_constants hq hJ hΔ (le_max_left _ _)
    ((le_max_left _ _).trans (le_max_right _ _))
    ((le_max_right _ _).trans (le_max_right _ _))
    (by omega) hCZ (Nat.lt_succ_self R) h hgs hsafe hr hQ₀ hpad

end TNLean.PEPS.AreaLaw
