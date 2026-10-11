/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ChargeAncestry
import Mathlib.Tactic.Linarith

/-!
# Cross-band nesting of actual physical partitions

Initial side assignments survive every fill and charge. Thus the near side
and middle of an earlier band stay below its initial far cutoff, whereas
every later band's initial near prefix already contains that whole region.
The resulting inclusion holds across arbitrary histories and times, without
a good-history assumption or a bound on the number of charges.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, Lemma 9.1, lines 262–270, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

omit [Fintype I] [LinearOrder I] in
private theorem fill_preserves_assigned (A : Finset V) (depth : V → ℤ)
    (n : ℕ) (lo hi : ℤ) (k : ℕ) (σ : PhysicalPartition V) {x : V} {side : Bool}
    (hx : σ x = some side) : fill A depth n lo hi k σ x = some side := by
  cases he : fillSlot A depth n lo hi (fillSide k) (fillCount k (fillSide k)) with
  | none => simpa only [fill, he] using hx
  | some y => simpa only [fill, he] using assign_of_assigned σ (fillSide k) side {y} hx

namespace CollarScan

variable (S : CollarScan V I)

/-- Initial assignments also survive the deterministic fill preceding a charge. -/
theorem oldChargeState_of_initial_assigned {k : ℕ} (h : History S.K S.m S.M k)
    (g : Fin S.K) {x : V} {side : Bool}
    (hx : initialPartition S.A S.depth (S.lower g (h.1 g)) (S.upper g (h.1 g)) x =
      some side) : S.oldChargeState h g x = some side :=
  fill_preserves_assigned S.A S.depth S.n _ _ k _
    (S.bandState_of_initial_assigned g (h.1 g) k (fun t ↦ h.2 t g) x side hx)

omit [Fintype V] [Fintype I] [LinearOrder I] in
private theorem initial_near_of_not_far {g g' r r' : ℕ} (hg : g < g') (hr : r < S.m)
    {x : V}
    (hx : initialPartition S.A S.depth (S.lower g r) (S.upper g r) x ≠ some true) :
    initialPartition S.A S.depth (S.lower g' r') (S.upper g' r') x = some false := by
  have hA : x ∈ S.A := by
    by_contra h; exact hx (by simp [initialPartition, h])
  have hlu : S.lower g r ≤ S.upper g r := by simp only [lower, upper]; omega
  have hdepth : S.depth x ≤ S.upper g r := by
    by_contra h
    have : ¬ S.depth x ≤ S.lower g r := by omega
    exact hx (by simp [initialPartition, hA, this, show S.upper g r < S.depth x by omega])
  have hsep : S.upper g r ≤ S.lower g' r' := by
    have hg' : (g : ℤ) + 1 ≤ g' := by exact_mod_cast hg
    have hr' : (r : ℤ) < S.m := by exact_mod_cast hr
    have hm : (0 : ℤ) ≤ S.m := by positivity
    have hrr : (0 : ℤ) ≤ r' := by positivity
    simp only [upper, lower, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  simp [initialPartition, hA, hdepth.trans hsep]

omit [Fintype I] [LinearOrder I] in
private theorem near_middle_subset_later_near (g g' r r' : ℕ)
    (hg : g < g') (hr : r < S.m) (σ σ' : PhysicalPartition V)
    (hσ : ∀ x side,
      initialPartition S.A S.depth (S.lower g r) (S.upper g r) x = some side →
        σ x = some side)
    (hσ' : ∀ x side,
      initialPartition S.A S.depth (S.lower g' r') (S.upper g' r') x = some side →
        σ' x = some side) : receiving σ false ∪ middle σ ⊆ receiving σ' false := by
  intro x hx
  have hnot : σ x ≠ some true := by
    rcases Finset.mem_union.mp hx with hx | hx
    · have := (Finset.mem_filter.mp hx).2; simp_all
    · have := (Finset.mem_filter.mp hx).2; simp_all
  have hi : initialPartition S.A S.depth (S.lower g r) (S.upper g r) x ≠ some true :=
    fun hi ↦ hnot (hσ x true hi)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    hσ' x false (S.initial_near_of_not_far hg hr hi)⟩

/-- The entire physical near side and middle of an earlier band lie in the near side
of a later band, for arbitrary independent histories and times. -/
theorem state_near_middle_subset_later_near {k k' : ℕ}
    (h : History S.K S.m S.M k) (h' : History S.K S.m S.M k')
    (g g' : Fin S.K) (hg : g < g') :
    receiving (S.state h g) false ∪ middle (S.state h g) ⊆
      receiving (S.state h' g') false := by
  apply S.near_middle_subset_later_near g g' (h.1 g) (h'.1 g') hg (h.1 g).isLt
  · exact fun x side hx ↦ S.bandState_of_initial_assigned g (h.1 g) k (fun t ↦ h.2 t g) x side hx
  · exact fun x side hx ↦ S.bandState_of_initial_assigned g' (h'.1 g') k'
      (fun t ↦ h'.2 t g') x side hx

/-- Cross-band nesting holds at the old statuses immediately before charges,
for arbitrary independent histories and times. -/
theorem oldChargeState_near_middle_subset_later_near {k k' : ℕ}
    (h : History S.K S.m S.M k) (h' : History S.K S.m S.M k')
    (g g' : Fin S.K) (hg : g < g') :
    receiving (S.oldChargeState h g) false ∪ middle (S.oldChargeState h g) ⊆
      receiving (S.oldChargeState h' g') false := by
  apply S.near_middle_subset_later_near g g' (h.1 g) (h'.1 g') hg (h.1 g).isLt
  · exact fun _ _ hx ↦ S.oldChargeState_of_initial_assigned h g hx
  · exact fun _ _ hx ↦ S.oldChargeState_of_initial_assigned h' g' hx

/-- A completed earlier band is nested inside a pre-charge later band,
with unrelated histories and times. -/
theorem state_near_middle_subset_later_old_near {k k' : ℕ}
    (h : History S.K S.m S.M k) (h' : History S.K S.m S.M k')
    (g g' : Fin S.K) (hg : g < g') :
    receiving (S.state h g) false ∪ middle (S.state h g) ⊆
      receiving (S.oldChargeState h' g') false := by
  apply S.near_middle_subset_later_near g g' (h.1 g) (h'.1 g') hg (h.1 g).isLt
  · exact fun x side hx ↦ S.bandState_of_initial_assigned g (h.1 g) k (fun t ↦ h.2 t g) x side hx
  · exact fun _ _ hx ↦ S.oldChargeState_of_initial_assigned h' g' hx

/-- A pre-charge earlier band is nested inside a completed later band,
with unrelated histories and times. -/
theorem old_near_middle_subset_later_state_near {k k' : ℕ}
    (h : History S.K S.m S.M k) (h' : History S.K S.m S.M k')
    (g g' : Fin S.K) (hg : g < g') :
    receiving (S.oldChargeState h g) false ∪ middle (S.oldChargeState h g) ⊆
      receiving (S.state h' g') false := by
  apply S.near_middle_subset_later_near g g' (h.1 g) (h'.1 g') hg (h.1 g).isLt
  · exact fun _ _ hx ↦ S.oldChargeState_of_initial_assigned h g hx
  · exact fun x side hx ↦ S.bandState_of_initial_assigned g' (h'.1 g') k'
      (fun t ↦ h'.2 t g') x side hx


end CollarScan
end TNLean.PEPS.AreaLaw.Scan
