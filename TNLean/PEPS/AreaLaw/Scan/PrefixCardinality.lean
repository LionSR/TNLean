/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.PrefixComparison
import Mathlib.Data.Finset.SymmDiff

/-!
# Row-count bounds for actual scan prefixes

Whole-row deterministic prefixes approximate both entropy regions within
`3nD` sites. The bound includes the incomplete nominal row and holds without
a good-history hypothesis. Both completed and pre-charge states are covered.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, Lemma 9.1(2), lines 243–260, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open scoped symmDiff

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

/-- A set between full depth prefixes differs from either endpoint by at most
the number of intervening rows times the row bound. Filtering both sets by
any fixed predicate cannot increase this estimate. -/
theorem card_filter_symmDiff_prefix_le (A R : Finset V) (depth : V → ℤ)
    (a b c : ℤ) (n : ℕ) (p : V → Prop) [DecidablePred p]
    (hlo : depthPrefix A depth a ⊆ R) (hhi : R ⊆ depthPrefix A depth b)
    (hc : c = a ∨ c = b)
    (hrow : ∀ d ∈ Finset.Icc (a + 1) b,
      (Finset.univ.filter fun x ↦ depth x = d).card ≤ n) :
    ((R.filter p) ∆ ((depthPrefix A depth c).filter p)).card ≤ (b - a).toNat * n := by
  classical
  have hsub : (R.filter p) ∆ ((depthPrefix A depth c).filter p) ⊆
      chargeCandidates depth (id : V → V) (a + 1) b := by
    intro x hx
    have hrange (hxR : x ∈ R) : x ∈ A ∧ depth x ≤ b := Finset.mem_filter.mp (hhi hxR)
    simp only [Finset.mem_symmDiff, Finset.mem_filter, depthPrefix] at hx
    rw [mem_chargeCandidates]
    change a + 1 ≤ depth x ∧ depth x ≤ b
    rcases hc with hc | hc
    all_goals subst c
    · rcases hx with ⟨⟨hxR, hxp⟩, hxnot⟩ | ⟨⟨⟨hxA, hxa⟩, hxp⟩, hxnot⟩
      · obtain ⟨hxA, hxb⟩ := hrange hxR
        have hna : ¬ depth x ≤ a := fun h ↦ hxnot ⟨⟨hxA, h⟩, hxp⟩
        exact ⟨by omega, hxb⟩
      · exact (hxnot ⟨hlo (Finset.mem_filter.mpr ⟨hxA, hxa⟩), hxp⟩).elim
    · rcases hx with ⟨⟨hxR, hxp⟩, hxnot⟩ | ⟨⟨⟨hxA, hxb⟩, hxp⟩, hxnot⟩
      · exact (hxnot ⟨hrange hxR, hxp⟩).elim
      · have hna : ¬ depth x ≤ a := fun h ↦
          hxnot ⟨hlo (Finset.mem_filter.mpr ⟨hxA, h⟩), hxp⟩
        exact ⟨by omega, hxb⟩
  have hb := card_chargeCandidates_le depth (id : V → V) (a + 1) b n 1 hrow
    (fun v ↦ by
      have he : (Finset.univ.filter fun x : V ↦ id x = v) = {v} := by ext x; simp
      rw [he, Finset.card_singleton])
  have he : (b - (a + 1) + 1).toNat = (b - a).toNat := by congr 1; omega
  simpa only [he, Nat.mul_one] using (Finset.card_le_card hsub).trans hb

/-- Four consequences of a full-prefix sandwich: distances before and after
removing the fixed target, for the near side and the near side with middle. -/
theorem prefix_sandwich_card_bounds (A : Finset V) (depth : V → ℤ)
    (σ : PhysicalPartition V) (jN jF : ℤ) (n D r₀ : ℕ)
    (hr : r₀ ≤ D) (hD : 1 ≤ D)
    (hs : depthPrefix A depth (jN - 1) ⊆ receiving σ false ∧
      receiving σ false ⊆ depthPrefix A depth (jN + (D + r₀ : ℕ)) ∧
      depthPrefix A depth (-jF - (D + r₀ : ℕ) - 1) ⊆ receiving σ false ∪ middle σ ∧
      receiving σ false ∪ middle σ ⊆ depthPrefix A depth (-jF))
    (hrowN : ∀ d ∈ Finset.Icc jN (jN + (D + r₀ : ℕ)),
      (Finset.univ.filter fun x ↦ depth x = d).card ≤ n)
    (hrowF : ∀ d ∈ Finset.Icc (-jF - (D + r₀ : ℕ)) (-jF),
      (Finset.univ.filter fun x ↦ depth x = d).card ≤ n) :
    positiveDepthPrefix A depth (jN - 1) ⊆ positiveNear depth σ ∧
    positiveNearMiddle depth σ ⊆ positiveDepthPrefix A depth (-jF) ∧
    ((receiving σ false) ∆ depthPrefix A depth (jN - 1)).card ≤ 3 * n * D ∧
    ((receiving σ false ∪ middle σ) ∆ depthPrefix A depth (-jF)).card ≤ 3 * n * D ∧
    ((positiveNear depth σ) ∆ positiveDepthPrefix A depth (jN - 1)).card ≤ 3 * n * D ∧
    ((positiveNearMiddle depth σ) ∆ positiveDepthPrefix A depth (-jF)).card ≤ 3 * n * D := by
  have hw : D + r₀ + 1 ≤ 3 * D := by omega
  have hN (p : V → Prop) [DecidablePred p] :
      (((receiving σ false).filter p) ∆ ((depthPrefix A depth (jN - 1)).filter p)).card ≤
        3 * n * D := by
    have hb := card_filter_symmDiff_prefix_le A (receiving σ false) depth
      (jN - 1) (jN + (D + r₀ : ℕ)) (jN - 1) n p hs.1 hs.2.1 (Or.inl rfl)
      (by simpa only [sub_add_cancel] using hrowN)
    have he : (jN + (D + r₀ : ℕ) - (jN - 1)).toNat = D + r₀ + 1 := by omega
    rw [he] at hb
    exact hb.trans (by nlinarith)
  have hF (p : V → Prop) [DecidablePred p] :
      (((receiving σ false ∪ middle σ).filter p) ∆
        ((depthPrefix A depth (-jF)).filter p)).card ≤ 3 * n * D := by
    have hb := card_filter_symmDiff_prefix_le A (receiving σ false ∪ middle σ) depth
      (-jF - (D + r₀ : ℕ) - 1) (-jF) (-jF) n p hs.2.2.1 hs.2.2.2 (Or.inr rfl)
      (by simpa only [sub_add_cancel] using hrowF)
    have he : (-jF - (-jF - (D + r₀ : ℕ) - 1)).toNat = D + r₀ + 1 := by omega
    rw [he] at hb
    exact hb.trans (by nlinarith)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxA, hx0, hxj⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hs.1 (Finset.mem_filter.mpr ⟨hxA, hxj⟩), hx0⟩
  · intro x hx
    obtain ⟨hxR, hx0⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxA, hxj⟩ := Finset.mem_filter.mp (hs.2.2.2 hxR)
    exact Finset.mem_filter.mpr ⟨hxA, hx0, hxj⟩
  · simpa using hN (fun _ ↦ True)
  · simpa using hF (fun _ ↦ True)
  · simpa [positiveNear, depthPrefix, positiveDepthPrefix, Finset.filter_filter,
      and_comm, and_left_comm] using hN (fun x ↦ 0 < depth x)
  · simpa [positiveNearMiddle, depthPrefix, positiveDepthPrefix, Finset.filter_filter,
      and_comm, and_left_comm] using hF (fun x ↦ 0 < depth x)

namespace CollarScan

variable (S : CollarScan V I)

omit [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I] in
/-- Both actual uncertainty intervals lie entirely within the positive physical
rows. Their width is `D+r₀+1`, including the partially consumed front row. -/
theorem prefix_uncertainty_rows {k L : ℕ} (offset : Fin S.K → Fin S.m)
    (g : Fin S.K) (hn : 0 < S.n) (hk : k ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hL : 8 * S.K * S.m ≤ L) :
    (1 ≤ S.front g (offset g) k false ∧
      S.front g (offset g) k false + (S.D + S.r₀ : ℕ) ≤ L) ∧
    (1 ≤ -S.front g (offset g) k true - (S.D + S.r₀ : ℕ) ∧
      -S.front g (offset g) k true ≤ L) := by
  have hns := fillCount_div_le_window hn hk false
  have hfs := fillCount_div_le_window hn hk true
  have hn0 : (0 : ℤ) ≤ (fillCount k false / S.n : ℕ) := by positivity
  have hf0 : (0 : ℤ) ≤ (fillCount k true / S.n : ℕ) := by positivity
  have hn1 : ((fillCount k false / S.n : ℕ) : ℤ) ≤ S.m := by exact_mod_cast hns
  have hf1 : ((fillCount k true / S.n : ℕ) : ℤ) ≤ S.m := by exact_mod_cast hfs
  have hband : 8 * g.val * S.m + 8 * S.m ≤ L := by
    calc
      _ = 8 * (g.val + 1) * S.m := by ring
      _ ≤ 8 * S.K * S.m := Nat.mul_le_mul_right S.m (Nat.mul_le_mul_left 8 g.isLt)
      _ ≤ L := hL
  have hb : (8 : ℤ) * g.val * S.m + 8 * S.m ≤ L := by exact_mod_cast hband
  have hbase : 0 ≤ (8 : ℤ) * g.val * S.m := by positivity
  have hr' : (S.r₀ : ℤ) ≤ S.D := by exact_mod_cast hr
  have hd' : 4 * (S.D : ℤ) ≤ S.m := by exact_mod_cast hD
  have hp' : (1 : ℤ) ≤ S.D := by exact_mod_cast hDpos
  have ho : ((offset g).val : ℤ) < S.m := by exact_mod_cast (offset g).isLt
  have ho0 : (0 : ℤ) ≤ (offset g).val := by positivity
  simp only [front, nominalFront, initialFront, lower, upper, Bool.false_eq_true,
    ↓reduceIte, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  omega

end CollarScan
end TNLean.PEPS.AreaLaw.Scan
