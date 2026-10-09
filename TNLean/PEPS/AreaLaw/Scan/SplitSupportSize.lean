/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SubsystemSize
import TNLean.PEPS.AreaLaw.Scan.BandNesting

/-!
# Size of every non-contained actual designated support

Initial far-side assignments never change. Hence any site that is not on the
actual far side lies in the truncation set. If a designated support is not
contained in a single physical part, it contains such a site and a distinct
second site. It crosses the first site's singleton, which lies in the
truncation set, so the established crossing-radius theorem gives radius `r₀`.

Consequently the logarithmic dimension condition for a nonempty set of split
leaves does not need support compatibility again. In particular, no row,
clearance, good-history or time-horizon hypothesis is used for this size bound.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`03-quasilocal.tex`, lines 439–440 and 507–510; `06-transport.tex`, lines
336–352; and `08-scanner.tex`, lines 225–233, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
    (S : CollarScan V I)

omit [Fintype I] [LinearOrder I] in
private theorem designatedSupport_eq_ball_of_not_constant {L : ℕ}
    (g : Fin S.K) (r : Fin S.m) (σ : PhysicalPartition V) (i : I)
    (hL : 8 * S.K * S.m ≤ L)
    (hfar : ∀ x, initialPartition S.A S.depth (S.lower g r) (S.upper g r) x = some true →
      σ x = some true)
    (hnc : ¬ ∃ part : Option Bool, ∀ x ∈
      designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i), σ x = part) :
    designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) = S.ball i := by
  classical
  have hex : ∃ x ∈ designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i),
      σ x ≠ some true := by
    by_contra hh
    push Not at hh
    exact hnc ⟨some true, hh⟩
  obtain ⟨x, hxD, hx⟩ := hex
  have hi : initialPartition S.A S.depth (S.lower g r) (S.upper g r) x ≠ some true :=
    fun hi ↦ hx (hfar x hi)
  have hxA : x ∈ S.A := by
    by_contra hh
    exact hi (by simp [initialPartition, hh])
  have hlu : S.lower g r ≤ S.upper g r := by simp only [lower, upper]; omega
  have hxd : S.depth x ≤ S.upper g r := by
    by_contra hh
    exact hi (by simp [initialPartition, hxA, show ¬ S.depth x ≤ S.lower g r by omega,
      show S.upper g r < S.depth x by omega])
  have hu : 8 * g.val * S.m + 5 * S.m + r.val ≤ L := by
    calc
      _ ≤ 8 * g.val * S.m + 8 * S.m := by have := r.isLt; omega
      _ = 8 * (g.val + 1) * S.m := by ring
      _ ≤ 8 * S.K * S.m := Nat.mul_le_mul_right S.m (Nat.mul_le_mul_left 8 g.isLt)
      _ ≤ L := hL
  have hxT : x ∈ S.truncationSet L := by
    refine Finset.mem_filter.mpr ⟨hxA, hxd.trans ?_⟩
    simpa only [upper] using (show ((8 * g.val * S.m + 5 * S.m + r.val : ℕ) : ℤ) ≤ L by
      exact_mod_cast hu)
  have hey : ∃ y ∈ designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i),
      σ y ≠ σ x := by
    by_contra hh
    push Not at hh
    exact hnc ⟨σ x, hh⟩
  obtain ⟨y, hyD, hy⟩ := hey
  have hcross : () ∈ crossingLabels S.graph (S.truncationSet L) S.r₀
      (fun _ : Unit ↦ S.anchor i) {x} := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ⟨x, hxD, by simp⟩, y, hyD, ?_⟩
    simpa using (fun he : y = x ↦ hy (congrArg σ he))
  simpa only [QuantumCircuit.graphBall, ball] using
    (truncationRadius_eq_of_mem_crossingLabels (Finset.singleton_subset_iff.mpr hxT) hcross).2.2

/-- At a completed status, any designated support not contained in one physical
part equals the radius-`r₀` ball. No support-classification assumption is needed. -/
theorem designatedSupport_eq_ball_of_state_not_constant {k L : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) (i : I)
    (hL : 8 * S.K * S.m ≤ L)
    (hnc : ¬ ∃ part : Option Bool, ∀ x ∈
      designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i), S.state h g x = part) :
    designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) = S.ball i :=
  S.designatedSupport_eq_ball_of_not_constant g (h.1 g) (S.state h g) i hL
    (fun x hx ↦ S.bandState_of_initial_assigned g (h.1 g) k (fun t ↦ h.2 t g) x true hx) hnc

/-- The same radius reduction holds at a pre-charge status. -/
theorem designatedSupport_eq_ball_of_old_not_constant {k L : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) (i : I)
    (hL : 8 * S.K * S.m ≤ L)
    (hnc : ¬ ∃ part : Option Bool, ∀ x ∈
      designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i),
        S.oldChargeState h g x = part) :
    designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) = S.ball i :=
  S.designatedSupport_eq_ball_of_not_constant g (h.1 g) (S.oldChargeState h g) i hL
    (fun _ hx ↦ S.oldChargeState_of_initial_assigned h g hx) hnc

end TNLean.PEPS.AreaLaw.Scan.CollarScan
