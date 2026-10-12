import TNLean.PEPS.AreaLaw.Scan.RoundedClearance
import Lean.Util.CollectAxioms

/-!
# Rounded safe-rectangle clearance regressions

The threshold is uniform over positive safety parameters. Selected cells
include cap zero and negative coordinates; empty cuts impose no extra premise.
-/

open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Geometry TNLean.PEPS.AreaLaw.Scan

-- Zero truncation constant is included, with a fixed nonintegral row multiplier.
example : ∃ S : ℕ, 1 ≤ S ∧ ∀ s : ℕ, S ≤ s →
    let n := ⌈(3 / 2 : ℝ) * s⌉₊
    let L := ⌊(n : ℝ) ^ (1 - (1 / 2 : ℝ))⌋₊
    1 ≤ L ∧ L ≤ s ∧ ∀ D₀ : ℕ, 1 ≤ D₀ →
      (D₀ + 1) * L ≤ D₀ * s ∧ 2 * L ≤ D₀ * s := by
  simpa using exists_rounded_clearance_threshold
    (C₂ := (3 / 2 : ℝ)) (Cr := 0) (ell := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private def thinNegativeRect : IntRect := ⟨-10, -9, 0, 0, by decide, by decide⟩

-- A width-two, height-one rectangle has enough budget for side-one shell cells.
example {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)}
    (hsafe : IsSafe Λ A 1 thinNegativeRect) :
    IsSafe Λ A 1 (latticeDyadicRect 0 (-11, 0)) := by
  classical
  apply hsafe.cappedDyadicPartition_shell (j := 1) (L := 1) (Kcap := 0)
    (by decide) (by decide) (by decide)
  rw [mem_cappedDyadicPartition]
  refine ⟨by decide, ?_, by simp⟩
  simp [latticeDyadicCell_zero, thinNegativeRect, IntRect.toFinset, IntRect.dilate]

-- No cell can be selected from the zero-thickness shell, at any dyadic cap.
example (Q : IntRect) (Kcap : ℕ) :
    cappedDyadicPartition ((Q.dilate 0).toFinset \ Q.toFinset) Kcap = ∅ := by
  simp

run_cmd do
  for name in [``TNLean.PEPS.AreaLaw.Scan.exists_rounded_clearance_threshold,
      ``TNLean.PEPS.AreaLaw.Scan.ScannerExponents.exists_rounded_clearance_threshold,
      ``TNLean.PEPS.AreaLaw.IsSafe.cappedDyadicPartition_shell,
      ``TNLean.PEPS.AreaLaw.Scan.exists_safe_shell_cells_of_rounded_scales] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name} uses unexpected axiom {ax}"
