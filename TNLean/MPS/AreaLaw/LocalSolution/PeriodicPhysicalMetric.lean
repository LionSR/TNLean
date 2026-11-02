/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.RoundedPeriodicGeometry
import TNLean.Lattice.MetricInteractionGraph
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Data.Int.Interval
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Tactic.Abel

/-!
# The metric of the physical periodic chain

The cyclic distance `min(|i-j|,M-|i-j|)` is the least absolute residue of the
difference in `ZMod M`. Its triangle inequality therefore follows from the
triangle inequality for least absolute residues. This defines the actual metric
of the physical cycle, and every radius-`R` ball has at most `2 ceil(R)+1` sites,
independently of the total chain length.

The metric is named explicitly, rather than replacing an ambient metric on `Fin M`.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 169–190 and 609–628.
-/

namespace TNLean.MPS.AreaLaw.LocalSolution

private theorem val_finEquiv {M : ℕ} [NeZero M] (i : Fin M) :
    (ZMod.finEquiv M i).val = (i : ℕ) := by
  cases M
  · exact (NeZero.ne 0 rfl).elim
  · rfl

/-- The physical cyclic distance is the least absolute residue of the difference.
Hastings, arXiv:cond-mat/0508554v3, lines 169–190 and 609–743. -/
theorem roundedPeriodicDistance_eq_valMinAbs {M : ℕ} [NeZero M] (i v : Fin M) :
    roundedPeriodicDistance i v =
      ((ZMod.finEquiv M i - ZMod.finEquiv M v).valMinAbs).natAbs := by
  rcases le_total (i : ℕ) (v : ℕ) with hiv | hvi
  · have hv : (ZMod.finEquiv M i).val ≤ (ZMod.finEquiv M v).val := by
      simpa only [val_finEquiv] using hiv
    rw [← ZMod.natAbs_valMinAbs_neg, neg_sub, ZMod.valMinAbs_natAbs_eq_min,
      ZMod.val_sub hv, val_finEquiv, val_finEquiv]
    simp only [roundedPeriodicDistance, Nat.dist_eq_sub_of_le hiv]
  · have hv : (ZMod.finEquiv M v).val ≤ (ZMod.finEquiv M i).val := by
      simpa only [val_finEquiv] using hvi
    rw [ZMod.valMinAbs_natAbs_eq_min, ZMod.val_sub hv, val_finEquiv, val_finEquiv]
    simp only [roundedPeriodicDistance, Nat.dist_eq_sub_of_le_right hvi]

/-- The physical cyclic distance satisfies the triangle inequality.
Hastings, arXiv:cond-mat/0508554v3, lines 169–190 and 609–743. -/
theorem roundedPeriodicDistance_triangle {M : ℕ} [NeZero M] (i v k : Fin M) :
    roundedPeriodicDistance i k ≤ roundedPeriodicDistance i v + roundedPeriodicDistance v k := by
  simp only [roundedPeriodicDistance_eq_valMinAbs]
  have hid : ZMod.finEquiv M i - ZMod.finEquiv M k =
      (ZMod.finEquiv M i - ZMod.finEquiv M v) +
        (ZMod.finEquiv M v - ZMod.finEquiv M k) := by abel
  rw [hid]
  exact (ZMod.natAbs_valMinAbs_add_le _ _).trans (Int.natAbs_add_le _ _)

/-- The metric of the original physical periodic chain.
Hastings, arXiv:cond-mat/0508554v3, lines 169–190 and 609–743. -/
@[instance_reducible]
noncomputable def periodicPhysicalMetricSpace (M : ℕ) [NeZero M] : MetricSpace (Fin M) where
  dist i v := roundedPeriodicDistance i v
  dist_self i := by simp [roundedPeriodicDistance]
  dist_comm i v := by simp only [roundedPeriodicDistance, Nat.dist_comm]
  dist_triangle i v k := by
    exact_mod_cast roundedPeriodicDistance_triangle i v k
  eq_of_dist_eq_zero {i v} hi := by
    have hzero : roundedPeriodicDistance i v = 0 := by exact_mod_cast hi
    rw [roundedPeriodicDistance_eq_valMinAbs, Int.natAbs_eq_zero,
      ZMod.valMinAbs_eq_zero, sub_eq_zero] at hzero
    exact (ZMod.finEquiv M).injective hzero

/-- Every physical cyclic ball has at most twice the rounded radius plus one sites.
Hastings, arXiv:cond-mat/0508554v3, lines 169–190 and 609–743. -/
theorem card_periodicPhysical_metricRangeBall_le {M : ℕ} [NeZero M] (R : ℝ) (i : Fin M) :
    letI := periodicPhysicalMetricSpace M
    (TNLean.Lattice.metricRangeBall R i).card ≤ 2 * Nat.ceil R + 1 := by
  let _ := periodicPhysicalMetricSpace M
  let f : Fin M → ℤ := fun v ↦ (ZMod.finEquiv M v - ZMod.finEquiv M i).valMinAbs
  have hf : Set.MapsTo f (↑(TNLean.Lattice.metricRangeBall R i) : Set (Fin M))
      (↑(Finset.Icc (-(Nat.ceil R : ℤ)) (Nat.ceil R : ℤ)) : Set ℤ) := by
    intro v hv
    have hvR : (roundedPeriodicDistance i v : ℝ) ≤ R :=
      TNLean.Lattice.mem_metricRangeBall.mp hv
    have hvceil : roundedPeriodicDistance i v ≤ Nat.ceil R := by
      exact_mod_cast hvR.trans (Nat.le_ceil R)
    have hd : roundedPeriodicDistance v i = roundedPeriodicDistance i v := by
      simp only [roundedPeriodicDistance, Nat.dist_comm]
    have hnat : (f v).natAbs ≤ Nat.ceil R := by
      simpa only [f, ← roundedPeriodicDistance_eq_valMinAbs, hd] using hvceil
    have hcast : ((f v).natAbs : ℤ) ≤ (Nat.ceil R : ℤ) := by exact_mod_cast hnat
    have hpos : f v ≤ ((f v).natAbs : ℤ) := Int.le_natAbs
    have hneg : -f v ≤ ((f v).natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -f v))
    simp only [Finset.mem_coe, Finset.mem_Icc]
    omega
  have hinj : Function.Injective f := by
    intro a b hab
    have hd := ZMod.injective_valMinAbs hab
    have he : ZMod.finEquiv M a = ZMod.finEquiv M b := by
      simpa using congrArg (fun x ↦ x + ZMod.finEquiv M i) hd
    exact (ZMod.finEquiv M).injective he
  have hc := Finset.card_le_card_of_injOn f hf hinj.injOn
  have hcard : (Finset.Icc (-(Nat.ceil R : ℤ)) (Nat.ceil R : ℤ)).card =
      2 * Nat.ceil R + 1 := by
    rw [Int.card_Icc]
    omega
  exact hc.trans_eq hcard


end TNLean.MPS.AreaLaw.LocalSolution
