/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.DomainWall.FiniteGroupDetectorPhase
import Mathlib.Tactic.Group

/-!
# Spatial factors of the chronological finite-group detector

For the printed geometry in arXiv:2405.00439, Section V, `detectG`
(`Papers/2405.00439/MPU-DW.tex`, lines 2108–2117), place the left cuts at
`0,1,…,m` and the right cuts at `m+1,…,2m+1`. Reindex the positive left cuts
by their spatial order, rather than their chronological creation labels.
The forward intervals are `[s,m+1+s]`, `1 ≤ s ≤ m`, followed in written
order by `[0,m+1]`. The undo intervals are `[0,2m+1]`, then
`[s,2m+1-s]`, `1 ≤ s ≤ m`, all adjointed.

This module computes the factor at every spatial position. No value of a full
detector, no supplied endpoint-word identity, and no symmetry of a reference
state is a hypothesis. The local conjugation relation is explicit. Tensoring
these factors and realizing the interval family by retained two-site gates are
separate constructions.
-/

namespace MPOTensor.FiniteGroupDetector

variable {Γ : Type*} [Group Γ]

private theorem prod_range_spike (v z : Γ) (n p : ℕ) :
    ((List.range n).map fun r ↦ if r + 1 = p then z else if r + 1 < p then v else 1).prod =
      if p = 0 then 1 else if p ≤ n then v ^ (p - 1) * z else v ^ n := by
  induction n with
  | zero => by_cases hp : p = 0 <;> simp [hp]
  | succ n ih =>
    rw [List.prod_range_succ, ih]
    by_cases hp : p = 0
    · subst p
      simp
    by_cases hpn : p ≤ n
    · have hne : n + 1 ≠ p := by omega
      have hnlt : ¬ n + 1 < p := by omega
      simp [hp, hpn, hne, hnlt, show p ≤ n + 1 by omega]
    by_cases heq : n + 1 = p
    · subst p
      simp
    · have hlt : n + 1 < p := by omega
      simp [hp, hpn, heq, hlt, show ¬ p ≤ n + 1 by omega, pow_succ]

private theorem prod_range_prefix (v : Γ) (n p : ℕ) :
    ((List.range n).map fun r ↦ if r < p then v else 1).prod = v ^ min n p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.prod_range_succ, ih]
    by_cases h : n < p
    · simp [h, Nat.min_eq_left (Nat.le_of_lt h),
        Nat.min_eq_left (show n + 1 ≤ p by omega), pow_succ]
    · simp [h, Nat.min_eq_right (show p ≤ n by omega),
        Nat.min_eq_right (show p ≤ n + 1 by omega)]

private theorem prod_range_suffix (v : Γ) (n p : ℕ) :
    ((List.range n).map fun r ↦ if p ≤ r then v else 1).prod = v ^ (n - p) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.prod_range_succ, ih]
    by_cases h : p ≤ n
    · simp [h, show n + 1 - p = (n - p) + 1 by omega, pow_succ]
    · simp [h, Nat.sub_eq_zero_of_le (show n ≤ p by omega),
        Nat.sub_eq_zero_of_le (show n + 1 ≤ p by omega)]

/-- The one-site factor of the explicitly left-dressed interval operator.
Source context: arXiv:2405.00439, `detectG`, lines 2108–2117; the dressing is
chosen explicitly and is not an assumption implicit in the printed claim. -/
def intervalSiteFactor (u w : Γ) (a b k : ℕ) : Γ :=
  (if k = a then w else 1) * (if a ≤ k ∧ k ≤ b then u else 1)

private theorem intervalSiteFactor_of_le_right (u w : Γ) (a b k : ℕ) (hkb : k ≤ b) :
    intervalSiteFactor u w a b k = if a = k then w * u else if a < k then u else 1 := by
  by_cases hak : a = k
  · subst a
    simp [intervalSiteFactor, hkb]
  · by_cases hlt : a < k
    · simp [intervalSiteFactor, Ne.symm hak, hkb, hak, hlt, Nat.le_of_lt hlt]
    · have hnle : ¬ a ≤ k := by omega
      simp [intervalSiteFactor, Ne.symm hak, hnle, hak, hlt]

/-- The factor at spatial position `k` of the complete chronological detector
word on the printed uniformly spaced cuts. Source: arXiv:2405.00439,
`detectG`, lines 2108–2117, with the forward product ordering stated explicitly
in this module's documentation. -/
def spatialEndpointWord (u w : Γ) (m k : ℕ) : Γ :=
  (intervalSiteFactor u w 0 (2 * m + 1) k)⁻¹ *
    ((List.range m).map fun r ↦ (intervalSiteFactor u w (r + 1) (2 * m - r) k)⁻¹).prod *
    ((List.range m).map fun r ↦ intervalSiteFactor u w (r + 1) (m + 2 + r) k).prod *
    intervalSiteFactor u w 0 (m + 1) k

private theorem spatialEndpointWord_left (u w : Γ) {m k : ℕ}
    (hk0 : 0 < k) (hkm : k ≤ m) :
    spatialEndpointWord u w m k = endpointConjugationWord u w (k - 1) := by
  have hf : ((List.range m).map fun r ↦
      intervalSiteFactor u w (r + 1) (m + 2 + r) k).prod = u ^ (k - 1) * (w * u) := by
    trans ((List.range m).map fun r ↦
      if r + 1 = k then w * u else if r + 1 < k then u else 1).prod
    · refine congrArg List.prod (List.map_congr_left fun r hr ↦ ?_)
      have hrm := List.mem_range.mp hr
      exact intervalSiteFactor_of_le_right u w _ _ _ (by omega)
    · simpa [Nat.ne_of_gt hk0, hkm] using prod_range_spike u (w * u) m k
  have hb : ((List.range m).map fun r ↦
      (intervalSiteFactor u w (r + 1) (2 * m - r) k)⁻¹).prod =
        (u⁻¹) ^ (k - 1) * (w * u)⁻¹ := by
    trans ((List.range m).map fun r ↦
      if r + 1 = k then (w * u)⁻¹ else if r + 1 < k then u⁻¹ else 1).prod
    · refine congrArg List.prod (List.map_congr_left fun r hr ↦ ?_)
      have hrm := List.mem_range.mp hr
      rw [intervalSiteFactor_of_le_right u w _ _ _ (by omega)]
      split_ifs <;> simp
    · simpa [Nat.ne_of_gt hk0, hkm] using prod_range_spike u⁻¹ (w * u)⁻¹ m k
  have hfirst : intervalSiteFactor u w 0 (2 * m + 1) k = u := by
    simp [intervalSiteFactor, Nat.ne_of_gt hk0, show k ≤ 2 * m + 1 by omega]
  have hlast : intervalSiteFactor u w 0 (m + 1) k = u := by
    simp [intervalSiteFactor, Nat.ne_of_gt hk0, show k ≤ m + 1 by omega]
  rw [spatialEndpointWord, hf, hb, hfirst, hlast, endpointConjugationWord]
  have hu2 : u ^ (2 : ℤ) = u * u := by
    rw [show (2 : ℤ) = 1 + 1 from rfl, zpow_add, zpow_one]
  rw [hu2]
  group

private theorem spatialEndpointWord_zero (u w : Γ) (m : ℕ) :
    spatialEndpointWord u w m 0 = 1 := by
  simp [spatialEndpointWord, intervalSiteFactor]

private theorem spatialEndpointWord_right (u w : Γ) {m k : ℕ} (hkm : m < k) :
    spatialEndpointWord u w m k = 1 := by
  have hk0 : k ≠ 0 := by omega
  have hf : ((List.range m).map fun r ↦
      intervalSiteFactor u w (r + 1) (m + 2 + r) k).prod = u ^ (m - (k - (m + 2))) := by
    refine Eq.trans (congrArg List.prod (List.map_congr_left fun r hr ↦ ?_))
      (prod_range_suffix u m (k - (m + 2)))
    have hrm := List.mem_range.mp hr
    simp only [intervalSiteFactor]
    split_ifs <;> first | omega | simp_all
  have hb : ((List.range m).map fun r ↦
      (intervalSiteFactor u w (r + 1) (2 * m - r) k)⁻¹).prod =
        (u⁻¹) ^ min m (2 * m + 1 - k) := by
    refine Eq.trans (congrArg List.prod (List.map_congr_left fun r hr ↦ ?_))
      (prod_range_prefix u⁻¹ m (2 * m + 1 - k))
    have hrm := List.mem_range.mp hr
    simp only [intervalSiteFactor]
    split_ifs <;> first | omega | simp_all
  rw [spatialEndpointWord, hf, hb]
  simp only [intervalSiteFactor, hk0, ite_false, one_mul, Nat.zero_le, true_and]
  by_cases hk1 : k ≤ m + 1
  · have hfirst : k ≤ 2 * m + 1 := by omega
    have hmin : min m (2 * m + 1 - k) = m := by omega
    have hexp : m - (k - (m + 2)) = m := by omega
    simp only [hfirst, hk1, ite_true, hmin, hexp]
    group
  by_cases hk2 : k ≤ 2 * m + 1
  · have hmin : min m (2 * m + 1 - k) = 2 * m + 1 - k := by omega
    have hexp : m - (k - (m + 2)) = (2 * m + 1 - k) + 1 := by omega
    simp only [hk1, hk2, ite_false, ite_true, hmin, hexp]
    group
  · have hmin : min m (2 * m + 1 - k) = 0 := by omega
    have hexp : m - (k - (m + 2)) = 0 := by omega
    simp [hk1, hk2, hmin, hexp]

/-- The complete spatial word has phase `c^(k-1)` at each positive left cut
`1 ≤ k ≤ m` and is the identity at every other site. This is derived from
the actual interval factors and the actual forward/undo products, with only
the local conjugation relation assumed. Project result for the endpoint audit
of arXiv:2405.00439, `detectG`, lines 2108–2117. -/
theorem spatialEndpointWord_eq (u w c : Γ) (hc : Commute c u)
    (hconj : w⁻¹ * u * w = c * u) (m k : ℕ) :
    spatialEndpointWord u w m k = if 0 < k ∧ k ≤ m then c ^ (k - 1) else 1 := by
  by_cases hk0 : k = 0
  · subst k
    simp [spatialEndpointWord_zero]
  by_cases hkm : k ≤ m
  · rw [spatialEndpointWord_left u w (by omega) hkm,
      endpointConjugationWord_eq_pow u w c hc hconj]
    simp [show 0 < k by omega, hkm]
  · rw [spatialEndpointWord_right u w (by omega)]
    simp [hkm]

/-- Multiplying the nontrivial spatial factors of the complete interval word
gives the triangular conjugation phase. The factors at all other positions
are identities by `spatialEndpointWord_eq`. Project result for the endpoint
audit of arXiv:2405.00439, `detectG`, lines 2108–2117. -/
theorem prod_spatialEndpointWord_eq_pow (u w c : Γ) (hc : Commute c u)
    (hconj : w⁻¹ * u * w = c * u) (m : ℕ) :
    ((List.range m).map fun r ↦ spatialEndpointWord u w m (r + 1)).prod =
      c ^ (m.choose 2) := by
  trans ((List.range m).map (endpointConjugationWord u w)).prod
  · refine congrArg List.prod (List.map_congr_left fun r hr ↦ ?_)
    have hrm := List.mem_range.mp hr
    simpa using spatialEndpointWord_left u w (by omega : 0 < r + 1) (by omega : r + 1 ≤ m)
  · exact prod_endpointConjugationWord_eq_pow u w c hc hconj m

/-- At even cyclic order the complete spatial word has total conjugation
phase `c^k`, provided `c^(2k)=1`. This result evaluates the actual interval
factors before multiplying their spatial phases; it does not assume an
endpoint-word identification. Project result for the audit of
arXiv:2405.00439, `detectG`, lines 2108–2117. -/
theorem prod_spatialEndpointWord_even (u w c : Γ) (hc : Commute c u)
    (hconj : w⁻¹ * u * w = c * u) (k : ℕ) (hperiod : c ^ (2 * k) = 1) :
    ((List.range (2 * k)).map fun r ↦ spatialEndpointWord u w (2 * k) (r + 1)).prod =
      c ^ k := by
  rw [prod_spatialEndpointWord_eq_pow u w c hc hconj]
  exact (prod_endpointConjugationWord_eq_pow u w c hc hconj (2 * k)).symm.trans
    (prod_endpointConjugationWord_even u w c hc hconj k hperiod)

end MPOTensor.FiniteGroupDetector
