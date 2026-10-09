/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualHistory

/-!
# Unconditional lead of the actual scanner

Every assigned site of the chosen color lies at most `D + r₀` ahead of its
nominal front, for every finite history. Charges use the actual selected
candidate list; fills use the actual padded row schedule. No goodness event or
split certificate enters the invariant. The restriction to the chosen color
is essential because its exterior starts on the far side.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 234–242, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

omit [Fintype V] in
private theorem assign_some (σ : PhysicalPartition V) (side old : Bool)
    (move : Finset V) (x : V) (hx : assign σ side move x = some old) :
    σ x = some old ∨ (old = side ∧ x ∈ move) := by
  simp only [assign] at hx
  split_ifs at hx with h
  · exact Or.inr ⟨(Option.some.inj hx).symm, h.1⟩
  · exact Or.inl hx

/-- A nonblank fill slot is located at precisely its deterministic oriented row. -/
theorem fillSlot_depth {A : Finset V} {depth : V → ℤ} {n : ℕ}
    {lo hi : ℤ} {side : Bool} {t : ℕ} {x : V}
    (hx : fillSlot A depth n lo hi side t = some x) :
    orientedDepth depth side x = initialFront lo hi side + (t / n : ℕ) := by
  simp only [fillSlot, Option.filter_eq_some_iff] at hx
  exact (mem_orientedRow _ _ _ _).mp (List.mem_iff_getElem?.mpr ⟨_, hx.1⟩)

namespace CollarScan

variable (S : CollarScan V I)

omit [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I] in
/-- Nominal fronts never move backwards when a scheduled fill is consumed. -/
theorem front_mono_succ (g r k : ℕ) (side : Bool) :
    S.front g r k side ≤ S.front g r (k + 1) side := by
  have hcount : fillCount k side ≤ fillCount (k + 1) side := by
    rw [fillCount_succ]
    exact Nat.le_add_right _ _
  have hd := Nat.div_le_div_right (c := S.n) hcount
  simp only [front, nominalFront]
  have hcast : ((fillCount k side / S.n : ℕ) : ℤ) ≤
      ((fillCount (k + 1) side / S.n : ℕ) : ℤ) := by exact_mod_cast hd
  omega

omit [Fintype V] [DecidableEq V] in
/-- Selection from the actual padded list forces the anchor into its charge interval. -/
theorem selected_anchor_bounds (g r k : ℕ) (c : Bool × Fin S.M) (i : I)
    (hi : S.selected g r k c = some i) :
    S.front g r k c.1 - S.r₀ ≤ orientedDepth S.depth c.1 (S.anchor i) ∧
      orientedDepth S.depth c.1 (S.anchor i) ≤ S.front g r k c.1 + S.D := by
  have hm := mem_of_paddedChargeSlot_eq_some hi
  simpa only [candidates, orderedChargeCandidates, Finset.mem_sort, chargeCandidates,
    Finset.mem_filter, Finset.mem_univ, true_and] using hm

omit [Fintype I] [LinearOrder I] in
private theorem fill_lead (g r k : ℕ) (σ : PhysicalPartition V)
    (hσ : ∀ (side : Bool) (x : V), x ∈ S.A → σ x = some side →
      orientedDepth S.depth side x ≤ S.front g r k side + S.D + S.r₀) :
    ∀ (side : Bool) (x : V), x ∈ S.A →
      fill S.A S.depth S.n (S.lower g r) (S.upper g r) k σ x = some side →
      orientedDepth S.depth side x ≤ S.front g r (k + 1) side + S.D + S.r₀ := by
  intro side x hxA hx
  have hfront := S.front_mono_succ g r k side
  cases he : fillSlot S.A S.depth S.n (S.lower g r) (S.upper g r)
      (fillSide k) (fillCount k (fillSide k)) with
  | none =>
    have hold : σ x = some side := by simpa only [fill, he] using hx
    have := hσ side x hxA hold
    omega
  | some y =>
    have hass : assign σ (fillSide k) {y} x = some side := by
      simpa only [fill, he] using hx
    rcases assign_some σ (fillSide k) side {y} x hass with hold | ⟨hs, hxy⟩
    · have := hσ side x hxA hold
      omega
    · have hxy' : x = y := Finset.mem_singleton.mp hxy
      subst x
      have hd := fillSlot_depth he
      rw [← hs] at hd
      change orientedDepth S.depth side y = S.front g r k side at hd
      omega

private theorem charge_lead (g r k : ℕ) (c : Bool × Fin S.M)
    (σ : PhysicalPartition V)
    (hdepth : ∀ i x, x ∈ S.ball i → |S.depth x - S.depth (S.anchor i)| ≤ S.r₀)
    (hσ : ∀ (side : Bool) (x : V), x ∈ S.A → σ x = some side →
      orientedDepth S.depth side x ≤ S.front g r k side + S.D + S.r₀) :
    ∀ (side : Bool) (x : V), x ∈ S.A → S.chargeStep g r k c σ x = some side →
      orientedDepth S.depth side x ≤ S.front g r k side + S.D + S.r₀ := by
  intro side x hxA hx
  cases he : S.selected g r k c with
  | none => exact hσ side x hxA (by simpa only [chargeStep, he] using hx)
  | some i =>
    by_cases hsplit : (S.ball i ∩ receiving σ c.1).Nonempty ∧ (S.ball i ∩ middle σ).Nonempty
    · have hass : assign σ c.1 (S.ball i) x = some side := by
        simpa only [chargeStep, he, charge, ite_eq_left hsplit] using hx
      rcases assign_some σ c.1 side (S.ball i) x hass with hold | ⟨hs, hball⟩
      · exact hσ side x hxA hold
      · have hanchor := (S.selected_anchor_bounds g r k c i he).2
        have hv : |orientedDepth S.depth side x -
            orientedDepth S.depth side (S.anchor i)| ≤ S.r₀ := by
          cases side <;>
            simpa only [orientedDepth, Bool.false_eq_true, ↓reduceIte, neg_sub_neg,
              abs_sub_comm] using hdepth i x hball
        rw [← hs] at hanchor
        have := (abs_le.mp hv).2
        omega
    · exact hσ side x hxA (by simpa only [chargeStep, he, charge, ite_eq_right hsplit] using hx)

/-- Every assigned site of the chosen color satisfies the unconditional lead bound
in the actual completed history, without a good-history assumption. -/
theorem bandState_assigned_lead (g r k : ℕ) (choices : Fin k → Bool × Fin S.M)
    (hdepth : ∀ i x, x ∈ S.ball i → |S.depth x - S.depth (S.anchor i)| ≤ S.r₀)
    (side : Bool) (x : V) (hxA : x ∈ S.A)
    (hx : S.bandState g r k choices x = some side) :
    orientedDepth S.depth side x ≤ S.front g r k side + S.D + S.r₀ := by
  induction k generalizing side x with
  | zero =>
    simp only [bandState, initialPartition, hxA] at hx
    cases side <;>
      simp only [orientedDepth, front, nominalFront, initialFront, fillCount,
        Bool.false_eq_true, ↓reduceIte] <;> split_ifs at hx <;> simp_all <;> omega
  | succ k ih =>
    exact S.charge_lead g r (k + 1) (choices (Fin.last k)) _ hdepth
      (S.fill_lead g r k _ (fun s y hyA hy ↦ ih (fun i ↦ choices i.castSucc) s y hyA hy))
      side x hxA hx

/-- The same invariant holds just after the next scheduled fill, before its charge. -/
theorem oldChargeState_assigned_lead {k : ℕ} (h : History S.K S.m S.M k)
    (g : Fin S.K)
    (hdepth : ∀ i x, x ∈ S.ball i → |S.depth x - S.depth (S.anchor i)| ≤ S.r₀)
    (side : Bool) (x : V) (hxA : x ∈ S.A)
    (hx : S.oldChargeState h g x = some side) :
    orientedDepth S.depth side x ≤ S.front g (h.1 g) (k + 1) side + S.D + S.r₀ :=
  S.fill_lead g (h.1 g) k _
    (fun s y hyA hy ↦ S.bandState_assigned_lead g (h.1 g) k
      (fun t ↦ h.2 t g) hdepth s y hyA hy) side x hxA hx

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
