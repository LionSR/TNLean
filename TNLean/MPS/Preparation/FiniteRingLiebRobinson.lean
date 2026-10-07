/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.LiebRobinson.CommutatorRecursion
import TNLean.Circuit.LiebRobinson.Volterra
import TNLean.MPS.Overlap.Basic
import TNLean.MPS.Preparation.CyclicOperatorSupport
import TNLean.MPS.Preparation.EmbedLocalOperatorNorm
import TNLean.MPS.Symmetry.GappedInteractionPath
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import TNLean.Circuit.LocalCircuit
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Lieb–Robinson estimate on finite periodic chains

For Hermitian nearest-neighbor terms of operator norm at most one, the
commutator of observables supported on disjoint sets satisfies an exponential
propagation estimate. The velocity is at most `8 exp a` for any nonnegative
spatial weight `a`. All constants are independent of the chain length and the
local Hilbert-space dimension. Distinct oriented bonds are counted separately,
including on a two-site ring. The ground energy is unrestricted.

This is the finite-periodic nearest-neighbor specialization of Hastings–Koma,
arXiv:math-ph/0507008, Appendix A, Theorem A.2. The proof uses the local
commutator recursion and a weighted integral comparison. No spectral-gap or
frustration-free hypothesis is used. Exponential clustering is a separate step.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open Set NormedSpace


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

namespace MPSPreparation

open QuantumCircuit

open Fin.CommRing

variable {N : ℕ} [NeZero N]

private def reaches (X Y : Set (Fin N)) (r : ℕ) : Prop :=
  ∃ x ∈ X, ∃ y ∈ Y, ∃ m : ℤ, |m| ≤ r ∧ y = x + (m : Fin N)

private theorem exists_reaches (X Y : Set (Fin N)) (hX : X.Nonempty) (hY : Y.Nonempty) :
    ∃ r, reaches X Y r := by
  obtain ⟨x, hx⟩ := hX
  obtain ⟨y, hy⟩ := hY
  refine ⟨(y - x).val, x, hx, y, hy, (y - x).val, by simp, ?_⟩
  simp only [Int.cast_natCast, Fin.cast_val_eq_self]
  ring

open Classical in
/-- Shortest-path separation of two nonempty supports on the periodic chain,
expressed through integer displacements modulo the ring length. -/
noncomputable def ringSupportDistance (X Y : Set (Fin N))
    (hX : X.Nonempty) (hY : Y.Nonempty) : ℕ :=
  Nat.find (exists_reaches X Y hX hY)

private theorem reaches_ringSupportDistance (X Y : Set (Fin N))
    (hX : X.Nonempty) (hY : Y.Nonempty) :
    reaches X Y (ringSupportDistance X Y hX hY) := by
  classical
  exact Nat.find_spec (exists_reaches X Y hX hY)

/-- The displacement-based separation predicate agrees with the strict
shortest-path distance inequality. -/
theorem isSeparatedBy_iff_lt_ringSupportDistance
    (X Y : Set (Fin N)) (hX : X.Nonempty) (hY : Y.Nonempty) (r : ℕ) :
    IsSeparatedBy X Y r ↔ r < ringSupportDistance X Y hX hY := by
  classical
  constructor
  · intro h
    by_contra hlt
    have hle := Nat.le_of_not_gt hlt
    obtain ⟨x, hx, y, hy, m, hm, heq⟩ := reaches_ringSupportDistance X Y hX hY
    exact h x hx y hy m (hm.trans (by exact_mod_cast hle)) heq
  · intro hr x hx y hy m hm heq
    have hReach : reaches X Y r := ⟨x, hx, y, hy, m, hm, heq⟩
    have hle : ringSupportDistance X Y hX hY ≤ r :=
      Nat.find_min' (exists_reaches X Y hX hY) hReach
    exact (Nat.not_lt_of_ge hle) hr


/-- Distance zero is precisely overlap of the two supports. -/
private theorem ringSupportDistance_eq_zero_iff
    (X Y : Set (Fin N)) (hX : X.Nonempty) (hY : Y.Nonempty) :
    ringSupportDistance X Y hX hY = 0 ↔ (X ∩ Y).Nonempty := by
  classical
  constructor
  · intro hZero
    obtain ⟨x, hx, y, hy, m, hm, heq⟩ := reaches_ringSupportDistance X Y hX hY
    have hmZero : m = 0 := abs_nonpos_iff.mp (by simpa only [hZero, Nat.cast_zero] using hm)
    rw [hmZero, Int.cast_zero, add_zero] at heq
    exact ⟨x, hx, heq ▸ hy⟩
  · rintro ⟨x, hx, hy⟩
    have hReach : reaches X Y 0 := ⟨x, hx, x, hy, 0, by simp, by simp⟩
    exact Nat.eq_zero_of_le_zero (Nat.find_min' (exists_reaches X Y hX hY) hReach)

/-- Passing from a support to an overlapping edge decreases its distance to
another support by at most one. This is the weighted path estimate for a
nearest-neighbor ring. -/
private theorem ringSupportDistance_le_bond_add_one
    (X Y : Set (Fin N)) (hX : X.Nonempty) (hY : Y.Nonempty)
    (j : Fin N) (hTouch : (X ∩ ringBond j).Nonempty) :
    ringSupportDistance X Y hX hY ≤
      ringSupportDistance (ringBond j) Y (ringBond_nonempty j) hY + 1 := by
  classical
  apply Nat.find_min' (exists_reaches X Y hX hY)
  obtain ⟨x, hx, hxb⟩ := hTouch
  obtain ⟨z, hzb, y, hy, m, hm, heq⟩ :=
    reaches_ringSupportDistance (ringBond j) Y (ringBond_nonempty j) hY
  have hmOld : |m| ≤
      (ringSupportDistance (ringBond j) Y (ringBond_nonempty j) hY + 1 : ℕ) :=
    hm.trans (by omega)
  have hmPlus : |m + 1| ≤
      (ringSupportDistance (ringBond j) Y (ringBond_nonempty j) hY + 1 : ℕ) := by
    simpa only [Nat.cast_add, Nat.cast_one, abs_one] using
      (abs_add_le m 1).trans (add_le_add hm (le_refl |(1 : ℤ)|))
  have hmMinus : |m - 1| ≤
      (ringSupportDistance (ringBond j) Y (ringBond_nonempty j) hY + 1 : ℕ) := by
    simpa only [Nat.cast_add, Nat.cast_one, abs_one] using
      (abs_sub m 1).trans (add_le_add hm (le_refl |(1 : ℤ)|))
  simp only [ringBond, Set.mem_insert_iff, Set.mem_singleton_iff] at hxb hzb
  rcases hxb with hxj | hxj
  · rcases hzb with hzj | hzj
    · refine ⟨x, hx, y, hy, m, hmOld, ?_⟩
      simpa only [hxj, hzj] using heq
    · refine ⟨x, hx, y, hy, m + 1, hmPlus, ?_⟩
      rw [heq, hxj, hzj]
      push_cast
      ring
  · rcases hzb with hzj | hzj
    · refine ⟨x, hx, y, hy, m - 1, hmMinus, ?_⟩
      rw [heq, hxj, hzj]
      push_cast
      ring
    · refine ⟨x, hx, y, hy, m, hmOld, ?_⟩
      simpa only [hxj, hzj] using heq

end MPSPreparation

namespace MPSPreparation

open QuantumCircuit
open Fin.CommRing

open Classical in
/-- At most twice the number of sites in a support are nearest-neighbor
oriented bonds meeting that support. This remains valid for one- and two-site
periodic chains, where distinct bonds may have the same support. -/
private theorem card_bonds_meeting_le {N : ℕ} [NeZero N] (X : Finset (Fin N)) :
    (Finset.univ.filter fun j => ((X : Set (Fin N)) ∩ ringBond j).Nonempty).card ≤ 2 * X.card := by
  classical
  have hSub : (Finset.univ.filter fun j => ((X : Set (Fin N)) ∩ ringBond j).Nonempty) ⊆
      X ∪ X.image (fun x => x - 1) := by
    intro j hj
    obtain ⟨x, hx, hxb⟩ := (Finset.mem_filter.mp hj).2
    simp only [ringBond, Set.mem_insert_iff, Set.mem_singleton_iff] at hxb
    rcases hxb with hxj | hxj
    · exact Finset.mem_union_left _ (hxj ▸ hx)
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨x, hx, ?_⟩
      rw [hxj]
      ring
  calc
    _ ≤ (X ∪ X.image (fun x => x - 1)).card := Finset.card_le_card hSub
    _ ≤ X.card + (X.image (fun x => x - 1)).card := Finset.card_union_le _ _
    _ ≤ X.card + X.card := Nat.add_le_add_left Finset.card_image_le _
    _ = 2 * X.card := by omega

end MPSPreparation

namespace MPSPreparation

open QuantumCircuit
open Fin.CommRing

open Classical in
/-- Exponentially weighted nearest-neighbor incidences obey a bound
independent of the ring length. -/
private theorem sum_bond_distance_exp_le {N : ℕ} [NeZero N]
    (X Y : Finset (Fin N)) (hX : X.Nonempty) (hY : Y.Nonempty)
    (a : ℝ) (ha : 0 ≤ a) :
    (∑ j : Fin N, if ((X : Set (Fin N)) ∩ ringBond j).Nonempty then
      Real.exp (-a * ringSupportDistance (ringBond j) (Y : Set (Fin N))
        ⟨j, by simp [ringBond]⟩ hY) else 0) ≤
    2 * X.card * Real.exp a *
      Real.exp (-a * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY) := by
  classical
  let R := Real.exp a *
    Real.exp (-a * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY)
  have hR : 0 ≤ R := mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hPoint (j : Fin N) (hj : ((X : Set (Fin N)) ∩ ringBond j).Nonempty) :
      Real.exp (-a * ringSupportDistance (ringBond j) (Y : Set (Fin N))
        ⟨j, by simp [ringBond]⟩ hY) ≤ R := by
    have hDist : (ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY : ℝ) ≤
        ringSupportDistance (ringBond j) (Y : Set (Fin N)) ⟨j, by simp [ringBond]⟩ hY + 1 := by
      exact_mod_cast ringSupportDistance_le_bond_add_one (X : Set (Fin N))
        (Y : Set (Fin N)) hX hY j hj
    calc
      _ ≤ Real.exp (a +
          (-a * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = R := by rw [Real.exp_add]
  calc
    _ ≤ ∑ j : Fin N, if ((X : Set (Fin N)) ∩ ringBond j).Nonempty then R else 0 := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs with hj
      · exact hPoint j hj
      · exact le_rfl
    _ = ((Finset.univ.filter fun j =>
          ((X : Set (Fin N)) ∩ ringBond j).Nonempty).card : ℝ) * R := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * X.card : ℝ) * R := by
      apply mul_le_mul_of_nonneg_right _ hR
      exact_mod_cast card_bonds_meeting_le X
    _ = _ := by dsimp only [R]; ring

end MPSPreparation

namespace MPSPreparation

open QuantumCircuit
open Fin.CommRing

open Classical in
private theorem ring_weighted_row_le {N : ℕ} [NeZero N]
    (X Y : Finset (Fin N)) (hX : X.Nonempty) (hY : Y.Nonempty)
    (a : ℝ) (ha : 0 ≤ a) (k : Fin N → ℝ)
    (hkOne : ∀ j, k j ≤ 1) :
    (∑ j : Fin N, (if Disjoint (X : Set (Fin N)) (ringBond j) then 0 else 2 * k j) *
      (({j, j + 1} : Finset (Fin N)).card * Real.exp
        (-a * ringSupportDistance (ringBond j) (Y : Set (Fin N))
          ⟨j, by simp [ringBond]⟩ hY))) ≤
      (8 * Real.exp a) * (X.card * Real.exp
        (-a * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY)) := by
  classical
  have hPoint (j : Fin N) :
      (if Disjoint (X : Set (Fin N)) (ringBond j) then 0 else 2 * k j) *
        (({j, j + 1} : Finset (Fin N)).card * Real.exp
          (-a * ringSupportDistance (ringBond j) (Y : Set (Fin N))
            ⟨j, by simp [ringBond]⟩ hY)) ≤
      4 * (if ((X : Set (Fin N)) ∩ ringBond j).Nonempty then
        Real.exp (-a * ringSupportDistance (ringBond j) (Y : Set (Fin N))
          ⟨j, by simp [ringBond]⟩ hY) else 0) := by
    by_cases hj : Disjoint (X : Set (Fin N)) (ringBond j)
    · have hNo := Set.not_disjoint_iff_nonempty_inter.not.mp (not_not.mpr hj)
      simp only [ite_eq_left hj, zero_mul, ite_eq_right hNo, mul_zero]
      exact le_rfl
    · have hTouch := Set.not_disjoint_iff_nonempty_inter.mp hj
      simp only [ite_eq_right hj, ite_eq_left hTouch]
      have hCard : (({j, j + 1} : Finset (Fin N)).card : ℝ) ≤ 2 := by
        exact_mod_cast (Finset.card_pair_eq_one_or_two (a := j) (b := j + 1)).elim
          (fun h => by omega) (fun h => by omega)
      have hCoeff : 2 * k j * ({j, j + 1} : Finset (Fin N)).card ≤ (4 : ℝ) := by
        have h := mul_le_mul (hkOne j) hCard (Nat.cast_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
        nlinarith
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hCoeff
        (Real.exp_pos (-a * ringSupportDistance (ringBond j) (Y : Set (Fin N))
          ⟨j, by simp [ringBond]⟩ hY)).le
  calc
    _ ≤ ∑ j : Fin N, 4 * (if ((X : Set (Fin N)) ∩ ringBond j).Nonempty then
          Real.exp (-a * ringSupportDistance (ringBond j) (Y : Set (Fin N))
            ⟨j, by simp [ringBond]⟩ hY) else 0) := Finset.sum_le_sum (fun j _ => hPoint j)
    _ = 4 * ∑ j : Fin N, if ((X : Set (Fin N)) ∩ ringBond j).Nonempty then
          Real.exp (-a * ringSupportDistance (ringBond j) (Y : Set (Fin N))
            ⟨j, by simp [ringBond]⟩ hY) else 0 := by rw [Finset.mul_sum]
    _ ≤ 4 * (2 * X.card * Real.exp a *
          Real.exp (-a * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY)) :=
      mul_le_mul_of_nonneg_left (sum_bond_distance_exp_le X Y hX hY a ha) (by norm_num)
    _ = _ := by ring

end MPSPreparation

namespace MPSPreparation

open QuantumCircuit
open Fin.CommRing
open scoped Matrix.Norms.L2Operator

/-- The finite-periodic nearest-neighbor Lieb–Robinson bound. The interaction
terms have norm at most one; no condition is imposed on the ground energy.
The velocity `8 exp a` counts the two oriented bonds incident to each site.
Source context: Hastings–Koma, arXiv:math-ph/0507008, Appendix A,
Theorem A.2 and (A.12)–(A.16). -/
private theorem ringCommutatorNorm_le_exp_of_disjoint
    {d N : ℕ} [NeZero N]
    (h : Fin N → Matrix (MPSTensor.Cfg d N) (MPSTensor.Cfg d N) ℂ)
    (hHerm : ∀ j, (h j).IsHermitian)
    (hSupport : ∀ j, h j ∈ supportedOperators d (ringBond j))
    (hNorm : ∀ j, ‖h j‖ ≤ 1)
    (B : Matrix (MPSTensor.Cfg d N) (MPSTensor.Cfg d N) ℂ)
    (X Y : Finset (Fin N)) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hB : B ∈ supportedOperators d Y)
    (hXY : Disjoint (X : Set (Fin N)) (Y : Set (Fin N)))
    (a : ℝ) (ha : 0 ≤ a) (t : ℝ) (ht : 0 ≤ t) :
    heisenbergCommutatorNorm (∑ j, h j) B X t ≤
      2 * ‖B‖ * X.card *
        Real.exp (-a * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY) *
        (Real.exp ((8 * Real.exp a) * t) - 1) := by
  classical
  let ι := {Z : Finset (Fin N) // Z.Nonempty}
  let e (j : Fin N) : ι := ⟨{j, j + 1}, by simp⟩
  let f (s : ℝ) (Z : ι) := heisenbergCommutatorNorm (∑ j, h j) B Z.val s
  let w (Z : ι) := (Z.val.card : ℝ) *
    Real.exp (-a * ringSupportDistance (Z.val : Set (Fin N))
      (Y : Set (Fin N)) Z.property hY)
  let coeff (Z : ι) (j : Fin N) :=
    if Disjoint (Z.val : Set (Fin N)) (ringBond j) then 0 else 2 * ‖h j‖
  let b (Z : ι) := f 0 Z
  have hFinite : Finite ι := inferInstance
  have hf : Continuous f := by
    apply continuous_pi
    intro Z
    exact continuous_heisenbergCommutatorNorm (∑ j, h j) B Z.val
  have hCoeff : ∀ Z j, 0 ≤ coeff Z j := by
    intro Z j
    dsimp only [coeff]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (by norm_num) (norm_nonneg _)
  have hw : ∀ Z, 0 < w Z := by
    intro Z
    exact mul_pos (by exact_mod_cast Finset.card_pos.mpr Z.property) (Real.exp_pos _)
  have hb : ∀ Z, b Z ≤ (2 * ‖B‖) * w Z := by
    intro Z
    by_cases hDis : Disjoint (Z.val : Set (Fin N)) (Y : Set (Fin N))
    · have hbZero : b Z = 0 :=
        heisenbergCommutatorNorm_zero_of_disjoint (∑ j, h j) B Z.val Y hB hDis
      rw [hbZero]
      exact mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (hw Z).le
    · have hdZero : ringSupportDistance (Z.val : Set (Fin N))
          (Y : Set (Fin N)) Z.property hY = 0 :=
        (ringSupportDistance_eq_zero_iff (Z.val : Set (Fin N))
          (Y : Set (Fin N)) Z.property hY).mpr
          (Set.not_disjoint_iff_nonempty_inter.mp hDis)
      have hCard : (1 : ℝ) ≤ Z.val.card := by
        exact_mod_cast Finset.card_pos.mpr Z.property
      calc
        b Z ≤ 2 * ‖B‖ := heisenbergCommutatorNorm_zero_le (∑ j, h j) B Z.val
        _ ≤ (2 * ‖B‖) * w Z := by
          dsimp only [w]
          rw [hdZero]
          simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
          nlinarith [norm_nonneg B]
  have hRow : ∀ Z, ∑ j, coeff Z j * w (e j) ≤ (8 * Real.exp a) * w Z := by
    intro Z
    simpa only [coeff, w, e, Finset.coe_pair, ringBond] using
      ring_weighted_row_le Z.val Y Z.property hY a ha (fun j => ‖h j‖)
        hNorm
  have hNonneg : ∀ s ∈ Set.Icc 0 t, ∀ Z, 0 ≤ f s Z := by
    intro s _ Z
    exact norm_nonneg _
  have hBound : ∀ s ∈ Set.Icc 0 t, ∀ Z,
      f s Z ≤ b Z + ∑ j, coeff Z j * ∫ u in (0 : ℝ)..s, f u (e j) := by
    intro s hs Z
    have hRec := heisenbergCommutatorNorm_le_integral h bond hHerm hSupport B Z.val s hs.1
    have hEq : (∑ j, coeff Z j * ∫ u in (0 : ℝ)..s, f u (e j)) =
        2 * ∑ j, if Disjoint (Z.val : Set (Fin N)) (ringBond j) then 0 else
          ‖h j‖ * ∫ u in (0 : ℝ)..s,
            heisenbergCommutatorNorm (∑ j, h j) B (ringBond j) u := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have he : ((e j).val : Set (Fin N)) = ringBond j := by
        simp only [e, Finset.coe_pair, ringBond]
      dsimp only [coeff, f]
      rw [he]
      simp only [ite_mul, mul_ite, zero_mul, mul_zero, mul_assoc]
    rw [hEq]
    exact hRec
  have hCompare := finite_rectangular_volterra_zero_le_weight_mul_exp_sub_one f hf
    e coeff hCoeff w hw b (2 * ‖B‖) (8 * Real.exp a) t
    (mul_nonneg (by norm_num) (norm_nonneg _))
    (mul_pos (by norm_num) (Real.exp_pos _)) hb hRow hNonneg hBound
  have hbX : b ⟨X, hX⟩ = 0 :=
    heisenbergCommutatorNorm_zero_of_disjoint (∑ j, h j) B X Y hB hXY
  simpa only [f, w, mul_assoc] using hCompare t ⟨ht, le_rfl⟩ ⟨X, hX⟩ hbX

end MPSPreparation

namespace MPSPreparation

open QuantumCircuit
open Fin.CommRing
open scoped Matrix.Norms.L2Operator

/-- The finite-ring propagation estimate holds for either sign of time.
Its constants depend only on the nearest-neighbor interaction bound. -/
private theorem ringCommutatorNorm_le_exp_abs_of_disjoint
    {d N : ℕ} [NeZero N]
    (h : Fin N → Matrix (MPSTensor.Cfg d N) (MPSTensor.Cfg d N) ℂ)
    (hHerm : ∀ j, (h j).IsHermitian)
    (hSupport : ∀ j, h j ∈ supportedOperators d (ringBond j))
    (hNorm : ∀ j, ‖h j‖ ≤ 1)
    (B : Matrix (MPSTensor.Cfg d N) (MPSTensor.Cfg d N) ℂ)
    (X Y : Finset (Fin N)) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hB : B ∈ supportedOperators d Y)
    (hXY : Disjoint (X : Set (Fin N)) (Y : Set (Fin N)))
    (a : ℝ) (ha : 0 ≤ a) (t : ℝ) :
    heisenbergCommutatorNorm (∑ j, h j) B X t ≤
      2 * ‖B‖ * X.card *
        Real.exp (-a * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY) *
        (Real.exp ((8 * Real.exp a) * |t|) - 1) := by
  by_cases ht : 0 ≤ t
  · simpa only [abs_of_nonneg ht] using
      ringCommutatorNorm_le_exp_of_disjoint h hHerm hSupport hNorm B X Y hX hY hB
        hXY a ha t ht
  · have ht' : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge ht)
    have hHerm' : ∀ j, (-h j).IsHermitian := fun j => (hHerm j).neg
    have hSupport' : ∀ j, -h j ∈ supportedOperators d (ringBond j) :=
      fun j => Submodule.neg_mem _ (hSupport j)
    have hNorm' : ∀ j, ‖-h j‖ ≤ 1 := fun j => (norm_neg _).trans_le (hNorm j)
    have hBound := ringCommutatorNorm_le_exp_of_disjoint (fun j => -h j)
      hHerm' hSupport' hNorm' B X Y hX hY hB hXY a ha (-t) ht'
    rw [Finset.sum_neg_distrib, ← heisenbergCommutatorNorm_neg_time, neg_neg] at hBound
    simpa only [abs_of_nonpos (le_of_not_ge ht)] using hBound

/-- A local observable satisfies the same propagation estimate, with its
operator norm multiplying the restricted commutator norm. -/
theorem norm_heisenberg_commutator_le_exp_abs_of_disjoint
    {d N : ℕ} [NeZero N]
    (h : Fin N → Matrix (MPSTensor.Cfg d N) (MPSTensor.Cfg d N) ℂ)
    (hHerm : ∀ j, (h j).IsHermitian)
    (hSupport : ∀ j, h j ∈ supportedOperators d (ringBond j))
    (hNorm : ∀ j, ‖h j‖ ≤ 1)
    (A B : Matrix (MPSTensor.Cfg d N) (MPSTensor.Cfg d N) ℂ)
    (X Y : Finset (Fin N)) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hA : A ∈ supportedOperators d X) (hB : B ∈ supportedOperators d Y)
    (hXY : Disjoint (X : Set (Fin N)) (Y : Set (Fin N)))
    (a : ℝ) (ha : 0 ≤ a) (t : ℝ) :
    ‖(exp (t • (Complex.I • ∑ j, h j)) * A *
        exp ((-t) • (Complex.I • ∑ j, h j))) * B -
      B * (exp (t • (Complex.I • ∑ j, h j)) * A *
        exp ((-t) • (Complex.I • ∑ j, h j)))‖ ≤
      2 * ‖A‖ * ‖B‖ * X.card *
        Real.exp (-a * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY) *
        (Real.exp ((8 * Real.exp a) * |t|) - 1) := by
  have hMap := norm_heisenberg_commutator_le_heisenbergCommutatorNorm
    (∑ j, h j) B X t hA
  have hBound := ringCommutatorNorm_le_exp_abs_of_disjoint h hHerm hSupport hNorm
    B X Y hX hY hB hXY a ha t
  calc
    _ ≤ heisenbergCommutatorNorm (∑ j, h j) B X t * ‖A‖ := hMap
    _ ≤ (2 * ‖B‖ * X.card *
        Real.exp (-a * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY) *
        (Real.exp ((8 * Real.exp a) * |t|) - 1)) * ‖A‖ :=
      mul_le_mul_of_nonneg_right hBound (norm_nonneg _)
    _ = _ := by ring

end MPSPreparation

namespace MPSTensor
open MPSPreparation NormedSpace QuantumCircuit
open scoped Matrix.Norms.L2Operator

/-- A bounded Hermitian two-site interaction satisfies the finite-ring
Lieb–Robinson estimate after cyclic embedding. The estimate is uniform in
the ring length and local Hilbert-space dimension, and allows arbitrary ground
energy. Source context: Hastings–Koma, arXiv:math-ph/0507008, Appendix A. -/
theorem norm_interactionHamiltonian_commutator_le_exp_abs_of_disjoint
    {d N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (h : MPOTensor.ChainOperator d 2) (hHerm : h.IsHermitian) (hNorm : ‖h‖ ≤ 1)
    (A B : MPOTensor.ChainOperator d N)
    (X Y : Finset (Fin N)) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hA : A ∈ supportedOperators d X) (hB : B ∈ supportedOperators d Y)
    (hXY : Disjoint (X : Set (Fin N)) (Y : Set (Fin N)))
    (a : ℝ) (ha : 0 ≤ a) (t : ℝ) :
    ‖(exp (t • (Complex.I • interactionHamiltonian h hN)) * A *
        exp ((-t) • (Complex.I • interactionHamiltonian h hN))) * B -
      B * (exp (t • (Complex.I • interactionHamiltonian h hN)) * A *
        exp ((-t) • (Complex.I • interactionHamiltonian h hN)))‖ ≤
      2 * ‖A‖ * ‖B‖ * X.card *
        Real.exp (-a * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY) *
        (Real.exp ((8 * Real.exp a) * |t|) - 1) := by
  apply norm_heisenberg_commutator_le_exp_abs_of_disjoint
    (fun j => MPOTensor.embedLocalOperator 2 N hN j h)
    (fun j => MPOTensor.embedLocalOperator_isHermitian 2 N hN j hHerm)
    (fun j => embedLocalOperator_twoSite_mem_supportedOperators hN j h)
    (fun j => (MPOTensor.norm_embedLocalOperator_le 2 N hN j h).trans hNorm)
    A B X Y hX hY hA hB hXY a ha t

end MPSTensor
