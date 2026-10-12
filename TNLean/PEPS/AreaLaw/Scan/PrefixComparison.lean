/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SplitIntervals
import TNLean.PEPS.AreaLaw.Scan.BandNesting
import TNLean.PEPS.AreaLaw.Scan.BandMargins

/-!
# Deterministic prefixes for actual scan statuses

The comparison prefixes contain whole depth rows. This makes them nested even
across unrelated histories and bands, without changing the fixed within-row
fill order. The one partially consumed row is included in the error interval.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, Lemma 9.1(2), lines 243–260, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

/-- A full depth prefix, including the fixed target. -/
def depthPrefix (A : Finset V) (depth : V → ℤ) (j : ℤ) : Finset V :=
  A.filter fun x ↦ depth x ≤ j

/-- A full positive-depth prefix, excluding the fixed target. -/
def positiveDepthPrefix (A : Finset V) (depth : V → ℤ) (j : ℤ) : Finset V :=
  A.filter fun x ↦ 0 < depth x ∧ depth x ≤ j

omit [Fintype V] [DecidableEq V] in
/-- All comparison prefixes belong to the same nested family. -/
theorem positiveDepthPrefix_mono (A : Finset V) (depth : V → ℤ) :
    Monotone (positiveDepthPrefix A depth) := by
  intro i j hij x hx
  obtain ⟨hxA, hx0, hxi⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hxA, hx0, hxi.trans hij⟩

omit [Fintype V] [DecidableEq V] in
/-- Full prefixes are nested before removing the fixed target too. -/
theorem depthPrefix_mono (A : Finset V) (depth : V → ℤ) :
    Monotone (depthPrefix A depth) := by
  intro i j hij x hx
  obtain ⟨hxA, hxi⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hxA, hxi.trans hij⟩

/-- The physical entropy region U removes the fixed zero-depth target. -/
def positiveNear (depth : V → ℤ) (σ : PhysicalPartition V) : Finset V :=
  (receiving σ false).filter fun x ↦ 0 < depth x

/-- The physical entropy region UY also removes the fixed zero-depth target. -/
def positiveNearMiddle (depth : V → ℤ) (σ : PhysicalPartition V) : Finset V :=
  (receiving σ false ∪ middle σ).filter fun x ↦ 0 < depth x

private theorem partition_prefix_sandwich (A : Finset V) (depth : V → ℤ)
    (σ : PhysicalPartition V) (jN jF w : ℤ) (hw : 0 ≤ w)
    (hout : ∀ x, x ∉ A → σ x = some true)
    (hmid : ∀ x, σ x = none → jN ≤ depth x ∧ jF ≤ -depth x)
    (hlead : ∀ side x, x ∈ A → σ x = some side →
      orientedDepth depth side x ≤ (if side then jF else jN) + w)
    (hsep : jN + w < -(jF + w)) :
    depthPrefix A depth (jN - 1) ⊆ receiving σ false ∧
    receiving σ false ⊆ depthPrefix A depth (jN + w) ∧
    depthPrefix A depth (-jF - w - 1) ⊆ receiving σ false ∪ middle σ ∧
    receiving σ false ∪ middle σ ⊆ depthPrefix A depth (-jF) := by
  have hA (x : V) (hx : σ x ≠ some true) : x ∈ A := by
    by_contra hn
    exact hx (hout x hn)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxA, hxd⟩ := Finset.mem_filter.mp hx
    cases he : σ x with
    | none => have := (hmid x he).1; omega
    | some side =>
      cases side
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
      · have := hlead true x hxA he
        simp only [orientedDepth, ↓reduceIte] at this
        omega
  · intro x hx
    have he := (Finset.mem_filter.mp hx).2
    have hxA := hA x (by simp [he])
    exact Finset.mem_filter.mpr ⟨hxA, by simpa [orientedDepth] using hlead false x hxA he⟩
  · intro x hx
    obtain ⟨hxA, hxd⟩ := Finset.mem_filter.mp hx
    cases he : σ x with
    | none => exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
    | some side =>
      cases side
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
      · have := hlead true x hxA he
        simp only [orientedDepth, ↓reduceIte] at this
        omega
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · have he := (Finset.mem_filter.mp hx).2
      have hxA := hA x (by simp [he])
      have hd := hlead false x hxA he
      simp only [orientedDepth, Bool.false_eq_true, ↓reduceIte] at hd
      exact Finset.mem_filter.mpr ⟨hxA, by omega⟩
    · have he := (Finset.mem_filter.mp hx).2
      exact Finset.mem_filter.mpr ⟨hA x (by simp [he]), by have := (hmid x he).2; omega⟩

namespace CollarScan

variable (S : CollarScan V I)

omit [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I] in
/-- The unconditional lead regions of the two sides remain strictly separated
throughout the source horizon. -/
theorem front_leads_separated {g r k : ℕ} (hn : 0 < S.n)
    (hk : k ≤ S.n * S.m) (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D)
    (hD : 4 * S.D ≤ S.m) :
    S.front g r k false + (S.D + S.r₀ : ℕ) <
      -(S.front g r k true + (S.D + S.r₀ : ℕ)) := by
  have hnshift := fillCount_div_le_window hn hk false
  have hfshift := fillCount_div_le_window hn hk true
  have hn' : ((fillCount k false / S.n : ℕ) : ℤ) ≤ S.m := by exact_mod_cast hnshift
  have hf' : ((fillCount k true / S.n : ℕ) : ℤ) ≤ S.m := by exact_mod_cast hfshift
  have hr' : (S.r₀ : ℤ) ≤ S.D := by exact_mod_cast hr
  have hD' : 4 * (S.D : ℤ) ≤ S.m := by exact_mod_cast hD
  have hp' : (1 : ℤ) ≤ S.D := by exact_mod_cast hDpos
  simp only [front, nominalFront, initialFront, lower, upper, Bool.false_eq_true,
    ↓reduceIte, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  omega

/-- Whole-row prefixes sandwich both physical near regions of a completed
history. The prefixes are computed from its deterministic nominal fronts. -/
theorem state_prefix_sandwich {k : ℕ} (h : History S.K S.m S.M k)
    (g : Fin S.K) (hn : 0 < S.n) (hk : k ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hrow : ∀ x, S.state h g x = none → (depthRow S.depth (S.depth x)).length ≤ S.n)
    (hdepth : ∀ i x, x ∈ S.ball i → |S.depth x - S.depth (S.anchor i)| ≤ S.r₀) :
    depthPrefix S.A S.depth (S.front g (h.1 g) k false - 1) ⊆ receiving (S.state h g) false ∧
    receiving (S.state h g) false ⊆
      depthPrefix S.A S.depth (S.front g (h.1 g) k false + (S.D + S.r₀ : ℕ)) ∧
    depthPrefix S.A S.depth (-S.front g (h.1 g) k true - (S.D + S.r₀ : ℕ) - 1) ⊆
      receiving (S.state h g) false ∪ middle (S.state h g) ∧
    receiving (S.state h g) false ∪ middle (S.state h g) ⊆
      depthPrefix S.A S.depth (-S.front g (h.1 g) k true) := by
  apply partition_prefix_sandwich _ _ _ _ _ _ (by positivity)
  · intro x hx
    exact S.bandState_of_initial_assigned _ _ _ _ _ _ (by simp [initialPartition, hx])
  · intro x hx
    have hf (side : Bool) := S.bandState_front_le g (h.1 g) k (fun t ↦ h.2 t g) side x hn
      (by cases side <;> simpa [orientedRow, orientedDepth] using hrow x hx) hx
    exact ⟨by simpa [orientedDepth] using hf false, by simpa [orientedDepth] using hf true⟩
  · intro side x hxA hx
    simpa only [show (if side then S.front g (h.1 g) k true else S.front g (h.1 g) k false) =
      S.front g (h.1 g) k side by cases side <;> rfl, Nat.cast_add, add_assoc]
      using S.bandState_assigned_lead g (h.1 g) k (fun t ↦ h.2 t g) hdepth side x hxA hx
  · exact S.front_leads_separated hn hk hr hDpos hD

/-- The same deterministic sandwich holds immediately after the next fill and
before its charge; this status requires `k+1 ≤ nm`. -/
theorem oldChargeState_prefix_sandwich {k : ℕ} (h : History S.K S.m S.M k)
    (g : Fin S.K) (hn : 0 < S.n) (hk : k + 1 ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hrow : ∀ x, S.oldChargeState h g x = none → (depthRow S.depth (S.depth x)).length ≤ S.n)
    (hdepth : ∀ i x, x ∈ S.ball i → |S.depth x - S.depth (S.anchor i)| ≤ S.r₀) :
    depthPrefix S.A S.depth (S.front g (h.1 g) (k + 1) false - 1) ⊆
      receiving (S.oldChargeState h g) false ∧
    receiving (S.oldChargeState h g) false ⊆
      depthPrefix S.A S.depth (S.front g (h.1 g) (k + 1) false + (S.D + S.r₀ : ℕ)) ∧
    depthPrefix S.A S.depth (-S.front g (h.1 g) (k + 1) true - (S.D + S.r₀ : ℕ) - 1) ⊆
      receiving (S.oldChargeState h g) false ∪ middle (S.oldChargeState h g) ∧
    receiving (S.oldChargeState h g) false ∪ middle (S.oldChargeState h g) ⊆
      depthPrefix S.A S.depth (-S.front g (h.1 g) (k + 1) true) := by
  apply partition_prefix_sandwich _ _ _ _ _ _ (by positivity)
  · intro x hx
    exact S.oldChargeState_of_initial_assigned h g (by simp [initialPartition, hx])
  · intro x hx
    have hf (side : Bool) := S.oldChargeState_front_le h g side x hn
      (by cases side <;> simpa [orientedRow, orientedDepth] using hrow x hx) hx
    exact ⟨by simpa [orientedDepth] using hf false, by simpa [orientedDepth] using hf true⟩
  · intro side x hxA hx
    simpa only [show (if side then S.front g (h.1 g) (k + 1) true else
      S.front g (h.1 g) (k + 1) false) = S.front g (h.1 g) (k + 1) side by cases side <;> rfl,
      Nat.cast_add, add_assoc] using S.oldChargeState_assigned_lead h g hdepth side x hxA hx
  · exact S.front_leads_separated hn hk hr hDpos hD

end CollarScan
end TNLean.PEPS.AreaLaw.Scan
