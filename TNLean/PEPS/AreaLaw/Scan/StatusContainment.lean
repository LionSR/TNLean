/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.DesignatedDilution
import TNLean.PEPS.AreaLaw.Scan.BandNesting

/-!
# Compact containment of the nonfar physical sites

Initial far assignments persist through every fill and charge. Every site
outside the actual far side therefore lies in the chosen color and below the
initial upper depth. This bounds the near side together with the middle by
the same compact truncation set, without a time-horizon or row hypothesis.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 32–58 and 225–233, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
    (S : CollarScan V I)

omit [Fintype V] [Fintype I] [LinearOrder I] in
/-- A site outside the far side lies in the compact set whenever initial far
assignments persist. The upper cutoff is at most `8Km`. -/
theorem mem_truncationSet_of_not_far {L : ℕ} (g : Fin S.K) (r : Fin S.m)
    (σ : PhysicalPartition V) (hL : 8 * S.K * S.m ≤ L)
    (hfar : ∀ x, initialPartition S.A S.depth (S.lower g r) (S.upper g r) x =
      some true → σ x = some true) {x : V} (hx : σ x ≠ some true) :
    x ∈ S.truncationSet L := by
  have hi : initialPartition S.A S.depth (S.lower g r) (S.upper g r) x ≠ some true :=
    fun hi ↦ hx (hfar x hi)
  have hxA : x ∈ S.A := by
    by_contra h
    exact hi (by simp [initialPartition, h])
  have hlu : S.lower g r ≤ S.upper g r := by simp only [lower, upper]; omega
  have hxd : S.depth x ≤ S.upper g r := by
    by_contra h
    exact hi (by simp [initialPartition, hxA, show ¬ S.depth x ≤ S.lower g r by omega,
      show S.upper g r < S.depth x by omega])
  have hu : 8 * g.val * S.m + 5 * S.m + r.val ≤ L := by
    calc
      _ ≤ 8 * g.val * S.m + 8 * S.m := by have := r.isLt; omega
      _ = 8 * (g.val + 1) * S.m := by ring
      _ ≤ 8 * S.K * S.m := Nat.mul_le_mul_right S.m (Nat.mul_le_mul_left 8 g.isLt)
      _ ≤ L := hL
  refine Finset.mem_filter.mpr ⟨hxA, hxd.trans ?_⟩
  simpa only [upper] using (show ((8 * g.val * S.m + 5 * S.m + r.val : ℕ) : ℤ) ≤ L by
    exact_mod_cast hu)

/-- The complement of the actual far side is compact at every completed status. -/
theorem state_far_compl_subset_truncationSet {k L : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) (hL : 8 * S.K * S.m ≤ L) :
    (receiving (S.state h g) true)ᶜ ⊆ S.truncationSet L := by
  intro x hx
  apply S.mem_truncationSet_of_not_far g (h.1 g) (S.state h g) hL
    (fun x hx ↦ S.bandState_of_initial_assigned g (h.1 g) k (fun t ↦ h.2 t g) x true hx)
  simpa only [Finset.mem_compl, receiving, Finset.mem_filter, Finset.mem_univ,
    true_and] using hx

/-- The same containment holds immediately before a charge. -/
theorem oldChargeState_far_compl_subset_truncationSet {k L : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) (hL : 8 * S.K * S.m ≤ L) :
    (receiving (S.oldChargeState h g) true)ᶜ ⊆ S.truncationSet L := by
  intro x hx
  apply S.mem_truncationSet_of_not_far g (h.1 g) (S.oldChargeState h g) hL
    (fun _ hx ↦ S.oldChargeState_of_initial_assigned h g hx)
  simpa only [Finset.mem_compl, receiving, Finset.mem_filter, Finset.mem_univ,
    true_and] using hx

end TNLean.PEPS.AreaLaw.Scan.CollarScan
