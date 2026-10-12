/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLeanTest.ActualBandGeometryData
import TNLean.PEPS.AreaLaw.Scan.SubsystemDimensionScale

/-!
# Actual physical-size and logarithmic-dimension regressions

The existing two-band domain supplies genuine split incidences and repeated
anchor labels. Empty, singleton, radius-zero, already assigned, dimension-one,
and arbitrary auxiliary-dimension cases are included independently.
-/

set_option autoImplicit false

open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan
open TNLeanTest.ActualBandGeometryData

noncomputable section

namespace TNLeanTest.ActualSubsystemDimension

example (g : Fin 2) :
    (designatedSupport scan.graph (scan.truncationSet 192) scan.r₀
      (scan.anchor (if g = 0 then 0 else 2))).card ≤ 9 := by
  exact scan.card_designatedSupport_le_of_state_split_domainGraph rfl history g false _
    (by norm_num) (initial_split g)

example (g : Fin 2) :
    Real.log (Real.exp 1 * (2 : ℝ) ^
      (designatedSupport scan.graph (scan.truncationSet 192) scan.r₀
        (scan.anchor (if g = 0 then 0 else 2))).card) ≤ transportLogDimBound 2 1 := by
  exact scan.log_designatedSupport_dimension_le_of_old_split_domainGraph rfl history
    g false _ (by norm_num) (by norm_num) (old_split g)

-- The stronger reduction needs neither terminal classification nor clearance.
example (g : Fin 2) :
    designatedSupport scan.graph (scan.truncationSet 192) scan.r₀
      (scan.anchor (if g = 0 then 0 else 2)) = scan.ball (if g = 0 then 0 else 2) := by
  apply scan.designatedSupport_eq_ball_of_state_not_constant history g _ (by norm_num)
  rintro ⟨part, hp⟩
  obtain ⟨x, hx⟩ := (initial_split g).1
  obtain ⟨y, hy⟩ := (initial_split g).2
  have hxpart := hp x (Finset.mem_inter.mp hx).1
  have hypart := hp y (Finset.mem_inter.mp hy).1
  have hxnear := (Finset.mem_filter.mp (Finset.mem_inter.mp hx).2).2
  have hymiddle := (Finset.mem_filter.mp (Finset.mem_inter.mp hy).2).2
  rw [hxnear] at hxpart
  rw [hymiddle] at hypart
  have hh : (some false : Option Bool) = none := hxpart.trans hypart.symm
  cases hh

-- Distinct labels at the same anchor receive their own identical size estimate.
example : (scan.ball 0).card ≤ 9 ∧ (scan.ball 1).card ≤ 9 :=
  ⟨scan.card_ball_le_domainGraph rfl 0, scan.card_ball_le_domainGraph rfl 1⟩

example {Λ : Finset (ℤ × ℤ)} (a : Site Λ) :
    (Finset.univ.filter fun x ↦ (domainGraph Λ).edist a x ≤ (0 : ℕ∞)).card ≤ 1 := by
  simpa using card_domainGraph_ball_le Λ a 0

example (r : ℕ) : transportLogDimBound 1 r = 1 := by simp [transportLogDimBound]

example (B : Finset Bool) : Real.log (Real.exp 1 * (1 : ℝ) ^ B.card) = 1 := by
  simp

example : Real.log (Real.exp 1 * (2 : ℝ) ^ (∅ : Finset Bool).card) = 1 := by simp

-- Both auxiliary sizes may be arbitrary, including zero in this algebraic identity.
example (B : Finset Bool) (c r : ℕ) :
    (∏ v ∈ B.map (⟨Sum.inl, Sum.inl_injective⟩ : Bool ↪ Bool ⊕ Bool),
      ((Sum.elim (fun _ ↦ 2) (fun side ↦ if side then r else c) v : ℕ) : ℝ)) =
        (2 : ℝ) ^ B.card :=
  prod_physical_subsystem_dimension B _ 2 (fun _ ↦ rfl)

example (σ : PhysicalPartition Bool) : ∃ part : Option Bool,
    ∀ x ∈ (∅ : Finset Bool), σ x = part := by simp

example (σ : PhysicalPartition Bool) (x : Bool) : ∃ part : Option Bool,
    ∀ y ∈ ({x} : Finset Bool), σ y = part := ⟨σ x, by simp⟩

example (B : Finset Bool) : ∃ part : Option Bool,
    ∀ _x ∈ B, (some true : Option Bool) = part := ⟨some true, by simp⟩

example (side : Bool) :
    (middle (fun _ : Bool ↦ none) \
      middle (assign (fun _ : Bool ↦ none) side {false})).card = 1 := by
  rw [middle_sdiff_middle_assign]
  simp [middle]

example (side old : Bool) :
    (middle (fun _ : Bool ↦ some old) \
      middle (assign (fun _ : Bool ↦ some old) side {false})).card = 0 := by
  rw [middle_sdiff_middle_assign]
  simp [middle]

example (σ : PhysicalPartition Bool) (k : ℕ) :
    (middle σ \ middle (fill ∅ (fun _ ↦ 0) 1 0 10 k σ)).card = 0 := by
  simp [fill, fillSlot]

-- A wholly far support can exceed the radius-zero cap: it is not a split support.
example : (designatedSupport (⊤ : SimpleGraph Bool) ∅ 0 false).card = 2 ∧
    ∃ part : Option Bool, ∀ _x ∈ designatedSupport (⊤ : SimpleGraph Bool) ∅ 0 false,
      (some true : Option Bool) = part := by
  constructor
  · simp [designatedSupport, setDist, componentFinset]
  · exact ⟨some true, by simp⟩

-- One common choice precedes n and every subsystem, with no sign restrictions.
example {q : ℕ} {Cr : ℝ} (hq : 1 ≤ q) (hCr : 0 ≤ Cr)
    (Cent eent Cen een : ℝ) :
    ∃ C Cl : ℝ, 1 ≤ C ∧ 0 ≤ Cl ∧ ∀ n : ℕ, 1 ≤ Real.log n →
      ∀ ℓ : ℝ, 1 ≤ ℓ → ℓ ≤ transportLogDimBound q (roundedLogRadius Cr n) →
        Cent * ℓ ^ eent ≤ C * (Real.log n) ^ Cl ∧
          Cen * ℓ ^ een ≤ C * (Real.log n) ^ Cl :=
  exists_transport_coefficients_log_bound hq hCr Cent eent Cen een

-- Dimension one and zero radius coefficient still allow mixed-sign exponents.
example : ∃ C Cl : ℝ, 1 ≤ C ∧ 0 ≤ Cl ∧ ∀ n : ℕ, 1 ≤ Real.log n →
    (-3 : ℝ) * (1 : ℝ) ^ (-2 : ℝ) ≤ C * (Real.log n) ^ Cl ∧
      (2 : ℝ) * (1 : ℝ) ^ (3 : ℝ) ≤ C * (Real.log n) ^ Cl := by
  obtain ⟨C, Cl, hC, hCl, hbound⟩ := exists_transport_coefficients_log_bound
    (q := 1) (Cr := 0) (by norm_num) (by norm_num) (-3) (-2) 2 3
  refine ⟨C, Cl, hC, hCl, fun n hn ↦ ?_⟩
  exact hbound n hn 1 le_rfl (by simp [transportLogDimBound])

-- Negative powers reverse base monotonicity; normalizing the exponent is essential.
example : (4 : ℝ) ^ (-1 : ℝ) < (1 : ℝ) ^ (-1 : ℝ) := by
  norm_num [Real.rpow_neg_one]

-- The lower bound on the subsystem cannot be dropped for negative exponents.
example : (1 : ℝ) ^ (-1 : ℝ) < (1 / 2 : ℝ) ^ (-1 : ℝ) := by
  norm_num [Real.rpow_neg_one]

-- The large-log guard excludes n = 1, where every positive log power vanishes.
example (C : ℝ) : C * (Real.log (1 : ℕ)) ^ (2 : ℝ) < transportLogDimBound 1 0 := by
  norm_num [transportLogDimBound]

-- The physical upper bound cannot be inferred merely from admissibility ℓ ≥ 1.
example : 1 ≤ (2 : ℝ) ∧ transportLogDimBound 1 1 < 2 := by
  norm_num [transportLogDimBound]

-- The positive-radius bound is exact at radius one, including q = 1.
example {q : ℕ} : transportLogDimBound q 1 = 1 + 9 * Real.log q := by
  norm_num [transportLogDimBound]

example {q : ℕ} {Cr c₀ : ℝ} (hq : 1 ≤ q) (hCr : 0 < Cr) (hc₀ : 0 < c₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ∀ a : ℝ, 0 ≤ a → a * (roundedLogRadius Cr n : ℝ) ^ 2 ≤ c →
        a * transportLogDimBound q (roundedLogRadius Cr n) ≤ c₀ := by
  obtain ⟨c, hc, hbound⟩ := exists_pos_radius_smallness_threshold hq hc₀
  refine ⟨c, hc, ?_⟩
  filter_upwards [eventually_one_le_roundedLogRadius hCr] with n hn
  exact hbound (roundedLogRadius Cr n) hn

-- Zero rate and zero threshold are allowed by the pointwise conversion.
example {q r : ℕ} (hq : 1 ≤ q) (hr : 1 ≤ r) :
    (0 : ℝ) * transportLogDimBound q r ≤ 0 := by
  exact mul_transportLogDimBound_le_of_radius_small hq hr (by norm_num) (by norm_num)

-- Radius zero would make the radius premise vacuous for arbitrary positive rates.
example : (2 : ℝ) * (0 : ℝ) ^ 2 ≤ 1 / (1 + 9 * Real.log (1 : ℕ)) ∧
    ¬ (2 : ℝ) * transportLogDimBound 1 0 ≤ 1 := by
  norm_num [transportLogDimBound]

-- A negative rate reverses the dimension comparison, even at q = 1.
example : (-1 : ℝ) * (2 : ℝ) ^ 2 ≤ (-2) / (1 + 9 * Real.log (1 : ℕ)) ∧
    ¬ (-1 : ℝ) * transportLogDimBound 1 2 ≤ -2 := by
  norm_num [transportLogDimBound]

-- Cr = 0 does not eventually yield a positive radius.
example (n : ℕ) : roundedLogRadius 0 n = 0 := by simp [roundedLogRadius]

end TNLeanTest.ActualSubsystemDimension
