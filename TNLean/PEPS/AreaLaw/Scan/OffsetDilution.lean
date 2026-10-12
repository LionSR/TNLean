/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualHistory
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith

/-!
# Uniform-offset dilution for actual scanner fronts

At a fixed band, side, and fill count, the nominal front is an affine function
of the initial offset, with slope one or minus one. Consequently at most
`a + b + 1` offsets place a fixed integer depth in the interval from
`front - a` to `front + b`. The exact uniform marginal of the initial offset then bounds every
history event contained in that interval event. The contained event may depend
on the entire physical history; no independence of that event is required.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 83–154, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

/-- A weighted sum over completed histories equals the sum over old histories
and their next charge choices, with the product of the two classical weights. -/
theorem sum_historyWeight_mul_eq_sum_extendHistory {K m M k : ℕ}
    (f : History K m M (k + 1) → ℝ) :
    ∑ h : History K m M (k + 1), historyWeight h * f h =
      ∑ h : History K m M k, ∑ c : ChargeChoices K M,
        historyWeight h * chargeWeight c * f (extendHistory h c) := by
  let e : History K m M k × ChargeChoices K M ≃ History K m M (k + 1) :=
    (Equiv.prodAssoc (Fin K → Fin m) (Fin k → ChargeChoices K M)
      (ChargeChoices K M)).trans
      (Equiv.prodCongr (Equiv.refl _) ((Equiv.prodComm _ _).trans
        (Fin.snocEquiv fun _ : Fin (k + 1) ↦ ChargeChoices K M)))
  calc
    _ = ∑ x : History K m M k × ChargeChoices K M,
        historyWeight (e x) * f (e x) := (e.sum_comp _).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro c _
      change historyWeight (extendHistory h c) * f (extendHistory h c) = _
      rw [historyWeight_extendHistory]

/-- Summing any set of initial offsets gives its cardinality divided by the
number of possible offsets, independently of the number of completed charges. -/
theorem sum_historyWeight_offset_mem {K m M k : ℕ} (hm : 0 < m) (hM : 0 < M)
    (g : Fin K) (s : Finset (Fin m)) :
    ∑ h : History K m M k, (if h.1 g ∈ s then historyWeight h else 0) =
      (s.card : ℝ) / m := by
  classical
  calc
    _ = ∑ h : History K m M k, ∑ a ∈ s,
        if h.1 g = a then historyWeight h else 0 := by
      apply Finset.sum_congr rfl
      intro h _
      simp [eq_comm]
    _ = ∑ a ∈ s, ∑ h : History K m M k,
        if h.1 g = a then historyWeight h else 0 := Finset.sum_comm
    _ = (s.card : ℝ) / m := by
      simp [sum_historyWeight_offset hm hM g, div_eq_mul_inv]

namespace CollarScan

variable {V I : Type*} (S : CollarScan V I)

/-- The nominal front is injective in the initial offset on either side. -/
theorem front_injective_offset (g k : ℕ) (side : Bool) :
    Function.Injective (fun r : Fin S.m ↦ S.front g r k side) := by
  intro r t h
  apply Fin.ext
  cases side <;>
    simp only [front, nominalFront, initialFront, lower, upper, Bool.false_eq_true,
      ↓reduceIte, Nat.cast_add] at h <;> omega

/-- A fixed integer depth lies in an interval about the nominal front for at most
`a + b + 1` initial offsets. No band-separation or physical-history assumption
is needed for this counting statement. -/
theorem card_front_interval_le (g k : ℕ) (side : Bool) (z : ℤ) (a b : ℕ) :
    (Finset.univ.filter fun r : Fin S.m ↦
      S.front g r k side - a ≤ z ∧ z ≤ S.front g r k side + b).card ≤ a + b + 1 := by
  classical
  calc
    _ ≤ (Finset.Icc (z - b) (z + a)).card := by
      apply Finset.card_le_card_of_injOn (fun r : Fin S.m ↦ S.front g r k side)
      · intro r hr
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hr
        simp only [Finset.mem_coe, Finset.mem_Icc]
        omega
      · exact (S.front_injective_offset g k side).injOn
    _ = a + b + 1 := by rw [Int.card_Icc]; omega

/-- Every history event contained in a fixed nominal-front interval has weight
at most the interval length divided by the number of offsets. The front's fill
count is independent of the number of completed charges recorded in the history. -/
theorem sum_historyWeight_event_le {k : ℕ} (hm : 0 < S.m) (hM : 0 < S.M)
    (g : Fin S.K) (t : ℕ) (side : Bool) (z : ℤ) (a b : ℕ)
    (E : History S.K S.m S.M k → Prop) [DecidablePred E]
    (hE : ∀ h, E h → S.front g (h.1 g) t side - a ≤ z ∧
      z ≤ S.front g (h.1 g) t side + b) :
    ∑ h : History S.K S.m S.M k, (if E h then historyWeight h else 0) ≤
      ((a : ℝ) + b + 1) / S.m := by
  classical
  let s := Finset.univ.filter fun r : Fin S.m ↦
    S.front g r t side - a ≤ z ∧ z ≤ S.front g r t side + b
  calc
    _ ≤ ∑ h : History S.K S.m S.M k,
        (if h.1 g ∈ s then historyWeight h else 0) := by
      apply Finset.sum_le_sum
      intro h _
      by_cases he : E h
      · have hs : h.1 g ∈ s := by simpa [s] using hE h he
        simp [he, hs]
      · simp only [he, ↓reduceIte]
        split_ifs <;> simp [historyWeight_nonneg]
    _ = (s.card : ℝ) / S.m := sum_historyWeight_offset_mem hm hM g s
    _ ≤ ((a : ℝ) + b + 1) / S.m := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast S.card_front_interval_le g t side z a b

/-- Summing over both sides costs a factor of two when each side has at most
one band whose front interval can contain the fixed depth. The event inside
that interval may depend on every random choice in the history. -/
theorem sum_historyWeight_exists_band_side_le {k : ℕ}
    (hm : 0 < S.m) (hM : 0 < S.M) (t : ℕ) (z : Bool → ℤ) (a b : ℕ)
    (E : History S.K S.m S.M k → Fin S.K → Bool → Prop)
    [∀ h g side, Decidable (E h g side)]
    (hE : ∀ h g side, E h g side →
      S.front g (h.1 g) t side - a ≤ z side ∧
      z side ≤ S.front g (h.1 g) t side + b)
    (huniq : ∀ (side : Bool) (g g' : Fin S.K) (r r' : Fin S.m),
      S.front g r t side - a ≤ z side ∧ z side ≤ S.front g r t side + b →
      S.front g' r' t side - a ≤ z side ∧ z side ≤ S.front g' r' t side + b →
      g = g') :
    ∑ h : History S.K S.m S.M k,
      (if ∃ g side, E h g side then historyWeight h else 0) ≤
      2 * (((a : ℝ) + b + 1) / S.m) := by
  classical
  have hside (side : Bool) :
      (∑ h : History S.K S.m S.M k,
        if ∃ g, E h g side then historyWeight h else 0) ≤
        ((a : ℝ) + b + 1) / S.m := by
    by_cases hex : ∃ (g : Fin S.K) (r : Fin S.m),
        S.front g r t side - a ≤ z side ∧ z side ≤ S.front g r t side + b
    · obtain ⟨g₀, r₀, h₀⟩ := hex
      apply S.sum_historyWeight_event_le hm hM g₀ t side (z side) a b
      rintro h ⟨g, hg⟩
      have hgg := huniq side g g₀ (h.1 g) r₀ (hE h g side hg) h₀
      subst g
      exact hE h g₀ side hg
    · have hnone (h : History S.K S.m S.M k) : ¬∃ g, E h g side := by
        rintro ⟨g, hg⟩
        exact hex ⟨g, h.1 g, hE h g side hg⟩
      simp only [hnone, ↓reduceIte, Finset.sum_const_zero]
      positivity
  calc
    _ ≤ ∑ h : History S.K S.m S.M k, ∑ side : Bool,
        if ∃ g, E h g side then historyWeight h else 0 := by
      refine Finset.sum_le_sum fun h _ ↦ ?_
      have hw := historyWeight_nonneg h
      rw [Fintype.sum_bool]
      split_ifs with he <;> try linarith
      obtain ⟨g, side, hg⟩ := he
      cases side <;> simp_all
    _ = ∑ side : Bool, ∑ h : History S.K S.m S.M k,
        if ∃ g, E h g side then historyWeight h else 0 := Finset.sum_comm
    _ ≤ ∑ _side : Bool, (((a : ℝ) + b + 1) / S.m) :=
      Finset.sum_le_sum fun side _ ↦ hside side
    _ = 2 * (((a : ℝ) + b + 1) / S.m) := by simp

/-- A common convex mixture of old- and new-history event weights satisfies the
same interval-dilution bound when each event is contained in that interval.
The events may depend on all old and new choices, respectively. -/
theorem historyWeight_mixture_event_le {k : ℕ} (hm : 0 < S.m) (hM : 0 < S.M)
    (g : Fin S.K) (t : ℕ) (side : Bool) (z : ℤ) (a b : ℕ)
    (E : History S.K S.m S.M k → Prop) [DecidablePred E]
    (F : History S.K S.m S.M (k + 1) → Prop) [DecidablePred F]
    (hE : ∀ h, E h → S.front g (h.1 g) t side - a ≤ z ∧
      z ≤ S.front g (h.1 g) t side + b)
    (hF : ∀ h, F h → S.front g (h.1 g) t side - a ≤ z ∧
      z ≤ S.front g (h.1 g) t side + b)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * (∑ h : History S.K S.m S.M k, if E h then historyWeight h else 0) +
      p * (∑ h : History S.K S.m S.M (k + 1), if F h then historyWeight h else 0) ≤
      ((a : ℝ) + b + 1) / S.m := by
  have he := S.sum_historyWeight_event_le hm hM g t side z a b E hE
  have hf := S.sum_historyWeight_event_le hm hM g t side z a b F hF
  have hpe := mul_le_mul_of_nonneg_left he (sub_nonneg.mpr hp1)
  have hpf := mul_le_mul_of_nonneg_left hf hp0
  nlinarith

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
