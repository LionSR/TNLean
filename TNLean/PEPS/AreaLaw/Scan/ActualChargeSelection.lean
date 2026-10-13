/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.AreaLaw.Scan.ActualParameterIntegral
import TNLean.PEPS.AreaLaw.Scan.Selection

/-!
# Selection of an actual charge defect

An integrated bound for the literal actual charge defects selects a charge
stage and a parameter in the prescribed interval. Interval integrability is
derived for the same supplied vector and energy terms.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  `08-scanner.tex`, lines 480–490, revision
  `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open scoped BigOperators
open Matrix Set Filter Topology MeasureTheory PermutationRepresentation Entropy
open TensorPower TensorPower.ReplicaTransport

/-- Averaging the actual charge defects selects one stage and one common
parameter in the prescribed interval. The interval integrability of the literal
defects is derived, rather than assumed. The positive stage count is necessary
for the finite selection; no symmetry or positive replica count is required.
Source: area-law manuscript, `08-scanner.tex`, lines 480–490. -/
theorem exists_actualCharge_point_of_sum_integral_le
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
    (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (hn : 0 < S.n)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)]
    (E : EnergyTerms (V ⊕ Bool) n I) {a : ℝ} (ha : 0 ≤ a) (k : ℕ)
    (pre : Config k (fun v => Fin (n v)) → ℂ)
    {p₀ p₁ ρ B : ℝ} (h0 : 0 ≤ p₀) (h01 : p₀ < p₁) (h1 : p₁ ≤ 1)
    (hρ : 0 < ρ)
    (hbound : ρ * (∑ s : Fin (S.n * S.m),
      ∫ p in p₀..p₁, S.actualChargeEntropyDefect hm hM s.val n E (a / 2) k pre p) ≤ B) :
    ∃ s : Fin (S.n * S.m), ∃ p ∈ Icc p₀ p₁,
      S.actualChargeEntropyDefect hm hM s.val n E (a / 2) k pre p ≤
        B / (ρ * ((S.n * S.m : ℕ) : ℝ) * (p₁ - p₀)) := by
  suffices ∃ s ∈ (Finset.univ : Finset (Fin (S.n * S.m))), ∃ p ∈ Icc p₀ p₁,
      S.actualChargeEntropyDefect hm hM s.val n E (a / 2) k pre p ≤
        B / (ρ * ((S.n * S.m : ℕ) : ℝ) * (p₁ - p₀)) by
    simpa only [Finset.mem_univ, true_and] using this
  have hscale : ((S.n * S.m : ℕ) : ℝ) *
      ((p₁ - p₀) * (B / (ρ * ((S.n * S.m : ℕ) : ℝ) * (p₁ - p₀)))) = B / ρ := by
    field_simp [hρ.ne', Nat.cast_ne_zero.mpr (Nat.mul_pos hn hm).ne',
      (sub_pos.mpr h01).ne']
  have hint (s : Fin (S.n * S.m)) : IntervalIntegrable
      (S.actualChargeEntropyDefect hm hM s.val n E (a / 2) k pre) volume p₀ p₁ :=
    (S.intervalIntegrable_actualChargeEntropyDefect hm hM s.val n E
      (div_nonneg ha (by norm_num)) k pre).mono_set
        (by simpa only [Set.uIcc_of_le h01.le, Set.uIcc_of_le zero_le_one] using
          Set.Icc_subset_Icc h0 h1)
  have hsel := exists_mem_Icc_le_of_sum_integral_le
    (fun s : Fin (S.n * S.m) => S.actualChargeEntropyDefect hm hM s.val n E (a / 2) k pre)
    Finset.univ ⟨⟨0, Nat.mul_pos hn hm⟩, Finset.mem_univ _⟩ h01 (fun s _ => hint s)
    (c := B / (ρ * ((S.n * S.m : ℕ) : ℝ) * (p₁ - p₀)))
    (by simpa only [Finset.card_univ, Fintype.card_fin, hscale] using
      (le_div_iff₀ hρ).mpr (by simpa only [mul_comm] using hbound))
  exact hsel

end TNLean.PEPS.AreaLaw.Scan.CollarScan
