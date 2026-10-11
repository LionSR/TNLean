/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.Approximation.EffectCircuitDensity
import TNLean.PEPS.Approximation.EffectCircuitLocations
import TNLean.PEPS.Approximation.PhysicalReadout

/-! # Source-only reduction of a distributed physical density

For the original circuit, choose the gate budget from the prescribed physical
error and the original nonprivate gate count. The actual replacement density
then differs by at most half the prescribed error, including zero-gate circuits.
The input may be an arbitrary normalized whole-party product vector.

Source: polynomial-PEPS, `04-compression.tex`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-effect-circuit-error; Theorem 5.2, lines 137–151 and 199–251.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/

noncomputable section
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect
variable {P : Type}

/-- A positive gate budget, with the zero-nonprivate-gate case included.
For positive gate count it equals the manuscript's `ε / (8 M)`.
Source: polynomial-PEPS 04-compression.tex, lines 201–217. -/
def sourceGateBudget (ε : ℝ) (M : ℕ) : ℝ := ε / (8 * (max 1 M : ℕ))

/-- The chosen gate budget is positive for positive requested error. -/
theorem sourceGateBudget_pos {ε : ℝ} (hε : 0 < ε) (M : ℕ) :
    0 < sourceGateBudget ε M := by
  have hM : (0 : ℝ) < (max 1 M : ℕ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 M)
  exact div_pos hε (mul_pos (by norm_num) hM)

/-- Summing the physical gate errors consumes at most half the requested error. -/
theorem sourceGateBudget_spec {ε : ℝ} (hε : 0 ≤ ε) (M : ℕ) :
    4 * sourceGateBudget ε M * M ≤ ε / 2 := by
  have hM : (0 : ℝ) < (max 1 M : ℕ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 M)
  have hle : (M : ℝ) ≤ (max 1 M : ℕ) := by exact_mod_cast Nat.le_max_right 1 M
  change 4 * (ε / (8 * (max 1 M : ℕ))) * M ≤ ε / 2
  calc
    _ = (ε / 2) * ((M : ℝ) / (max 1 M : ℕ)) := by field_simp; ring
    _ ≤ (ε / 2) * 1 := mul_le_mul_of_nonneg_left
      ((div_le_one hM).mpr hle) (div_nonneg hε (by norm_num))
    _ = ε / 2 := mul_one _

namespace OriginalCircuit
variable {Phys Env : Type*} [Fintype Phys] [Fintype Env]

/-- Physical density error for the manuscript's original nonprivate gate count.
The readout identifies the original physical and discarded registers, while the
replacement readout additionally discards the explicitly retained auxiliary memory.
Source: polynomial-PEPS 04-compression.tex, lines 199–229. -/
theorem rectangularTraceNorm_sourceOnly_density_sub_le [DecidableEq Phys]
    {r : ℕ} {S δ : ℝ} (hδ : 0 < δ) {a b : Layout P} (w : OriginalCircuit a b)
    (hb : w.IsExpansionBounded r S)
    (K : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Phys × Env))
    (x : Mem a) (hx : ‖x‖ ≤ 1) :
    Matrix.rectangularTraceNorm
      (w.produce.replacementPhysicalDensity hδ w.isAllowed_produce
          ((w.isExpansionBounded_produce_iff r S).mpr hb) (isoL K) x -
        Matrix.partialTraceRight (Matrix.euclideanOuterProduct (K (w.eval x)) (K (w.eval x)))) ≤
      4 * δ * w.nonprivateCount := by
  have he := w.produce.rectangularTraceNorm_replacement_density_sub_le hδ
    w.isAllowed_produce ((w.isExpansionBounded_produce_iff r S).mpr hb) (isoL K)
      (LinearIsometry.norm_toContinuousLinearMap_le K.toLinearIsometry) x hx
  simpa only [EffectCircuit.originalPhysicalDensity, eval_produce,
    expandedGateCount_produce, isoL_apply] using he

/-- The actual source-only replacement uses at most half the requested physical
trace-norm error. This includes circuits with no nonprivate gates.
Source: polynomial-PEPS 04-compression.tex, lines 199–229. -/
theorem rectangularTraceNorm_sourceOnly_density_sub_le_half [DecidableEq Phys]
    {r : ℕ} {S ε : ℝ} (hε : 0 < ε) {a b : Layout P} (w : OriginalCircuit a b)
    (hb : w.IsExpansionBounded r S)
    (K : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Phys × Env))
    (x : Mem a) (hx : ‖x‖ ≤ 1) :
    Matrix.rectangularTraceNorm
      (w.produce.replacementPhysicalDensity (sourceGateBudget_pos hε w.nonprivateCount)
          w.isAllowed_produce ((w.isExpansionBounded_produce_iff r S).mpr hb) (isoL K) x -
        Matrix.partialTraceRight (Matrix.euclideanOuterProduct (K (w.eval x)) (K (w.eval x)))) ≤
      ε / 2 :=
  (w.rectangularTraceNorm_sourceOnly_density_sub_le
    (sourceGateBudget_pos hε w.nonprivateCount) hb K x hx).trans
      (sourceGateBudget_spec hε.le w.nonprivateCount)

/-- The source-only reduction on the source's genuine whole-party product input.
Every party occurs once, with an arbitrary normalized vector in its entire private memory.
Source: polynomial-PEPS 04-compression.tex, lines 137–139 and 199–229. -/
theorem rectangularTraceNorm_sourceOnly_wholeParty_density_sub_le_half
    [Fintype P] [DecidableEq Phys] {r : ℕ} {S ε : ℝ} (hε : 0 < ε)
    (H : P → HSpace) (x : ∀ p, H p) (hx : ∀ p, ‖x p‖ = 1) {b : Layout P}
    (w : OriginalCircuit (ProductInput.wholePartyLayout H) b)
    (hb : w.IsExpansionBounded r S)
    (K : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Phys × Env)) :
    let ψ := (ProductInput.ofAllParties H x hx).vector
    Matrix.rectangularTraceNorm
      (w.produce.replacementPhysicalDensity (sourceGateBudget_pos hε w.nonprivateCount)
          w.isAllowed_produce ((w.isExpansionBounded_produce_iff r S).mpr hb) (isoL K) ψ -
        Matrix.partialTraceRight (Matrix.euclideanOuterProduct (K (w.eval ψ)) (K (w.eval ψ)))) ≤
      ε / 2 :=
  w.rectangularTraceNorm_sourceOnly_density_sub_le_half hε hb K _
    (ProductInput.norm_vector _).le
end OriginalCircuit
end TNLean.PEPS.PairEffect

namespace TNLean.PEPS.PairEffect
/-- At a positive upper bound on the number of nonprivate gates, the common
budget is exactly the manuscript's choice.
Source: polynomial-PEPS 04-compression.tex, lines 200–202. -/
theorem sourceGateBudget_eq_of_pos (ε : ℝ) {M : ℕ} (hM : 0 < M) :
    sourceGateBudget ε M = ε / (8 * (M : ℝ)) := by
  simp only [sourceGateBudget, max_eq_right (Nat.succ_le_of_lt hM)]

namespace OriginalCircuit
variable {P : Type} {Phys Env : Type*} [Fintype Phys] [Fintype Env]
/-- Any upper bound on the original nonprivate-gate count suffices for the
manuscript's source-only density budget, including the zero-gate case.
The density is obtained from the actual replacement and original readout.
Source: polynomial-PEPS 04-compression.tex, lines 199–227. -/
theorem rectangularTraceNorm_sourceOnly_density_sub_le_half_of_count_le
    [DecidableEq Phys] {r M : ℕ} {S ε : ℝ} (hε : 0 < ε)
    {a b : Layout P} (w : OriginalCircuit a b) (hb : w.IsExpansionBounded r S)
    (hcount : w.nonprivateCount ≤ M)
    (K : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Phys × Env))
    (x : Mem a) (hx : ‖x‖ ≤ 1) :
    Matrix.rectangularTraceNorm
      (w.produce.replacementPhysicalDensity (sourceGateBudget_pos hε M)
          w.isAllowed_produce ((w.isExpansionBounded_produce_iff r S).mpr hb) (isoL K) x -
        Matrix.partialTraceRight (Matrix.euclideanOuterProduct (K (w.eval x)) (K (w.eval x)))) ≤
      ε / 2 := by
  have he := w.rectangularTraceNorm_sourceOnly_density_sub_le
    (sourceGateBudget_pos hε M) hb K x hx
  have hc : (w.nonprivateCount : ℝ) ≤ (M : ℝ) := by exact_mod_cast hcount
  exact he.trans ((mul_le_mul_of_nonneg_left hc
    (mul_nonneg (by norm_num) (sourceGateBudget_pos hε M).le)).trans
      (sourceGateBudget_spec hε.le M))
end OriginalCircuit
end TNLean.PEPS.PairEffect

namespace TNLean.PEPS.PairEffect.OriginalCircuit
variable {P : Type} [Fintype P] [DecidableEq P]

/-- The source-only density reduction with the actual labelled regional readout.
There is one physical register of dimension `d` at each original party. All
exterior physical coordinates and the original private registers are discarded.
The private-memory dimension has no numerical bound.
Source: polynomial-PEPS 04-compression.tex, lines 137–151 and 199–251. -/
theorem rectangularTraceNorm_sourceOnly_regional_density_sub_le_half
    {r M d : ℕ} {S ε : ℝ} (hε : 0 < ε)
    (H : P → HSpace) (x : ∀ p, H p) (hx : ∀ p, ‖x p‖ = 1)
    (priv : Layout P) [FiniteDimensional ℂ (Mem priv).carrier]
    (w : OriginalCircuit (ProductInput.wholePartyLayout H)
      (physicalOutputLayout d Finset.univ.toList priv))
    (hb : w.IsExpansionBounded r S) (hcount : w.nonprivateCount ≤ M) (A : Finset P) :
    let ψ := (ProductInput.ofAllParties H x hx).vector
    let K := regionalPhysicalReadout d Finset.univ.toList (Finset.nodup_toList _)
      (fun p ↦ Finset.mem_toList.mpr (Finset.mem_univ p)) priv A
    Matrix.rectangularTraceNorm
      (w.produce.replacementPhysicalDensity (sourceGateBudget_pos hε M)
          w.isAllowed_produce ((w.isExpansionBounded_produce_iff r S).mpr hb) (isoL K) ψ -
        Matrix.partialTraceRight (Matrix.euclideanOuterProduct (K (w.eval ψ)) (K (w.eval ψ)))) ≤
      ε / 2 :=
  w.rectangularTraceNorm_sourceOnly_density_sub_le_half_of_count_le hε hb hcount
    (regionalPhysicalReadout d Finset.univ.toList (Finset.nodup_toList _)
      (fun p ↦ Finset.mem_toList.mpr (Finset.mem_univ p)) priv A) _
    (ProductInput.norm_vector _).le
end TNLean.PEPS.PairEffect.OriginalCircuit
