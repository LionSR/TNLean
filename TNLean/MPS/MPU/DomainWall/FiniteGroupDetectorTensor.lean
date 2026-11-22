/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.DomainWall.FiniteGroupDetectorClock
import QICLean.Algebra.Kronecker.FiniteKroneckerProduct

/-!
# The complete tensor detector at every even cyclic order

The explicit interval word of arXiv:2405.00439, Section V, `detectG`,
lines 2108–2117, is evaluated as an ordinary product of matrices on all sites.
Cells have an even and an odd leg. Only the even leg of each left endpoint
is dressed. This module lifts the spatial calculation through the actual
tensor products and instantiates the result with QICLean's clock and shift.
The circuit realization is handled separately in `FiniteGroupDetectorCircuit`.
-/

open Matrix
open scoped BigOperators

namespace MPOTensor.FiniteGroupDetector

variable {α ν β : Type*} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

private theorem rectKronecker_prod_map (l : List β) (A : β → ν → Matrix α α ℂ) :
    (l.map fun r ↦ rectKronecker (A r)).prod =
      rectKronecker fun s ↦ (l.map fun r ↦ A r s).prod := by
  induction l with
  | nil => simp
  | cons r l ih =>
    simp only [List.map_cons, List.prod_cons, ih, rectKronecker_mul]

private theorem unitary_coe_prod_map (l : List β) (A : β → unitary (Matrix α α ℂ)) :
    ((l.map A).prod : Matrix α α ℂ) = (l.map fun r ↦ (A r : Matrix α α ℂ)).prod := by
  induction l with
  | nil => rfl
  | cons r l ih => simp only [List.map_cons, List.prod_cons, Submonoid.coe_mul, ih]

omit [Fintype α] [DecidableEq ν] in
private theorem rectKronecker_scalar (f : ν → ℂ) :
    rectKronecker (fun s ↦ f s • (1 : Matrix α α ℂ)) = (∏ s, f s) • 1 := by
  conv_rhs => rw [← rectKronecker_one (ν := ν) (ι := α)]
  ext x y
  simp only [rectKronecker_apply, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

private theorem prod_powers (ζ : ℂ) (m : ℕ) :
    (∏ r : Fin m, ζ ^ r.val) = ζ ^ (m.choose 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih, ← pow_add]
    congr 1
    simp [Nat.choose_succ_succ, Nat.add_comm]

private theorem prod_cut_phase (ζ : ℂ) (m N : ℕ) (hN : m + 1 ≤ N) :
    (∏ r : Fin N, if 0 < r.val ∧ r.val ≤ m then ζ ^ (r.val - 1) else 1) =
      ζ ^ (m.choose 2) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hN
  clear hN
  induction t with
  | zero =>
    rw [Nat.add_zero, Fin.prod_univ_succ]
    simp only [Fin.val_zero, Nat.lt_irrefl, false_and, ite_false, one_mul, Fin.val_succ,
      Nat.zero_lt_succ, true_and, Nat.add_sub_cancel]
    have hle : ∀ r : Fin m, r.val + 1 ≤ m := fun r ↦ by omega
    simp only [hle, ite_true]
    exact prod_powers ζ m
  | succ t ih =>
    rw [Nat.add_succ, Fin.prod_univ_castSucc]
    have hnot : ¬ (0 < m + 1 + t ∧ m + 1 + t ≤ m) := by omega
    simp only [Fin.val_castSucc, Fin.val_last, ih, hnot, ite_false, mul_one]

/-- The actual tensor interval operator with a left dressing on its even leg.
Source context: the fixed-circuit endpoint audit of arXiv:2405.00439,
Section V, lines 2081–2087 and 2108–2117. -/
noncomputable def detectorIntervalTensor (u w : unitary (Matrix α α ℂ)) (N a b : ℕ) :
    Matrix (Fin N × Bool → α) (Fin N × Bool → α) ℂ :=
  rectKronecker fun s ↦ (intervalSiteFactor (Γ := unitary (Matrix α α ℂ))
    u (if s.2 then 1 else w) a b s.1.val : Matrix α α ℂ)

/-- The complete chronological interval word, as an ordinary product of
matrices on the entire finite chain. Source: arXiv:2405.00439, `detectG`,
lines 2108–2117, with the forward action order fixed in the endpoint audit. -/
noncomputable def detectorTensorWord (u w : unitary (Matrix α α ℂ)) (m N : ℕ) :
    Matrix (Fin N × Bool → α) (Fin N × Bool → α) ℂ :=
  (detectorIntervalTensor u w N 0 (2 * m + 1))ᴴ *
    ((List.range m).map fun r ↦ (detectorIntervalTensor u w N (r + 1) (2 * m - r))ᴴ).prod *
    ((List.range m).map fun r ↦ detectorIntervalTensor u w N (r + 1) (m + 2 + r)).prod *
    detectorIntervalTensor u w N 0 (m + 1)

/-- Multiplying the actual interval matrices gives the tensor product of the
complete spatial words. No endpoint identification is an input hypothesis.
Source context: arXiv:2405.00439, `detectG`, lines 2108–2117. -/
theorem detectorTensorWord_eq_rectKronecker (u w : unitary (Matrix α α ℂ)) (m N : ℕ) :
    detectorTensorWord u w m N = rectKronecker fun s : Fin N × Bool ↦
      (spatialEndpointWord (Γ := unitary (Matrix α α ℂ))
        u (if s.2 then 1 else w) m s.1.val : Matrix α α ℂ) := by
  simp only [detectorTensorWord, detectorIntervalTensor, rectKronecker_conjTranspose]
  rw [rectKronecker_prod_map, rectKronecker_prod_map,
    rectKronecker_mul, rectKronecker_mul, rectKronecker_mul]
  congr 1
  funext s
  simp only [spatialEndpointWord, Submonoid.coe_mul, unitary_coe_prod_map]
  rfl

/-- The full tensor word is the triangular scalar conjugation phase.
All spatial sites, including the odd legs and right endpoints, are included.
The chain has room for every printed cut and an exterior cell. Source context:
the explicit interval-family audit of arXiv:2405.00439, `detectG`. -/
theorem detectorTensorWord_eq_smul (u w c : unitary (Matrix α α ℂ)) (ζ : ℂ)
    (hc : Commute c u) (hconj : w⁻¹ * u * w = c * u)
    (hscalar : (c : Matrix α α ℂ) = ζ • 1) (m N : ℕ) (hN : 2 * m + 2 < N) :
    detectorTensorWord u w m N = ζ ^ (m.choose 2) • 1 := by
  let f : Fin N × Bool → ℂ := fun s ↦
    if s.2 then 1 else if 0 < s.1.val ∧ s.1.val ≤ m then ζ ^ (s.1.val - 1) else 1
  have hsite : ∀ s : Fin N × Bool,
      (spatialEndpointWord (Γ := unitary (Matrix α α ℂ))
        u (if s.2 then 1 else w) m s.1.val : Matrix α α ℂ) =
        f s • 1 := by
    rintro ⟨k, b⟩
    cases b
    · change (spatialEndpointWord (Γ := unitary (Matrix α α ℂ)) u w m k.val : Matrix α α ℂ) =
        (if 0 < k.val ∧ k.val ≤ m then ζ ^ (k.val - 1) else 1) • 1
      rw [spatialEndpointWord_eq u w c hc hconj]
      by_cases hk : 0 < k.val ∧ k.val ≤ m
      · simp [hk, SubmonoidClass.coe_pow, hscalar, smul_pow]
      · simp [hk]
    · have h := spatialEndpointWord_eq u 1 1 (Commute.one_left u) (by simp) m k.val
      simp [h, f]
  rw [detectorTensorWord_eq_rectKronecker]
  simp_rw [hsite]
  rw [rectKronecker_scalar]
  congr 1
  rw [Fintype.prod_prod_type]
  simpa [f, Fintype.prod_bool] using prod_cut_phase ζ m N (by omega)

/-- The complete finite tensor detector equals minus the identity at every
positive even cyclic order, for the existing QICLean clock and shift matrices.
This evaluates the actual tensor interval word, rather than a list of supplied
endpoint factors. Source context: the counterexample family in the endpoint
audit of arXiv:2405.00439, `detectG`, lines 2108–2117. -/
theorem detectorTensorWord_clock_even {k : ℕ} [NeZero (2 * k)] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * k)) (N : ℕ) (hN : 2 * (2 * k) + 2 < N) :
    detectorTensorWord (detectorShift (2 * k)) (detectorClock hζ) (2 * k) N = -1 := by
  have hk : k ≠ 0 := by
    intro h
    exact NeZero.ne (2 * k) (by simp [h])
  have hm : 1 < 2 * k := by omega
  rw [detectorTensorWord_eq_smul _ _ (detectorClockPhase hζ) ζ
    (detectorClockPhase_commute hζ hm) (detectorClock_conjugation hζ)
    (detectorClockPhase_coe hζ hm) (2 * k) N hN,
    detectorRoot_triangular_even hζ, neg_one_smul]

end MPOTensor.FiniteGroupDetector
