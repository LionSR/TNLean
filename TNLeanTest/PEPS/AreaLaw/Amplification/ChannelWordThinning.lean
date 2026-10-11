/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.ChannelWordThinning

/-! Retention, chronology, multiplicity and operator-norm Bochner consumers. -/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit Matrix MeasureTheory TNLean.PEPS.AreaLaw
open scoped NNReal Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace ChannelWordThinningTest

variable {q : ℕ} {ι κ Aux : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype Aux] [DecidableEq Aux]

-- Retaining everything preserves the actual full chronological composition.
theorem allRetained
    (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ) (w : PoissonWord.Word κ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    spectatorRootChannelWord (fun i : {_i : κ // True} => k i)
        (List.ofFn (PoissonWord.partitionWords (fun _ : κ => True) w).1.2) B =
      spectatorRootChannelWord k (List.ofFn w.2) B := by
  rw [← spectatorRootChannelWord_filter]
  simp

-- Retaining nothing leaves the arbitrary complex matrix unchanged.
theorem noneRetained
    (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ) (w : PoissonWord.Word κ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    spectatorRootChannelWord (fun i : {_i : κ // False} => k i)
        (List.ofFn (PoissonWord.partitionWords (fun _ : κ => False) w).1.2) B = B := by
  rw [← spectatorRootChannelWord_filter]
  simp

private def word : PoissonWord.Word (Fin 3) := ⟨4, ![0, 2, 1, 0]⟩

-- This retained word is ordered and contains the same event twice.
theorem retainedLetters :
    (List.ofFn (PoissonWord.partitionWords (fun i : Fin 3 => i ≠ 2) word).1.2).map
      Subtype.val = [0, 1, 0] := by
  rw [PoissonWord.ofFn_partitionWords_fst]
  decide

-- The duplicate acts again, after the intervening retained event. No
-- commutativity or idempotence of the physical channels is assumed.
theorem retainedChronology
    (k : Fin 3 → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    spectatorRootChannelWord (fun i : {i : Fin 3 // i ≠ 2} => k i)
        (List.ofFn (PoissonWord.partitionWords (fun i : Fin 3 => i ≠ 2) word).1.2) B =
      spectatorRootChannel (k 0)
        (spectatorRootChannel (k 1) (spectatorRootChannel (k 0) B)) := by
  rw [← spectatorRootChannelWord_filter]
  rfl

variable [Fintype κ]

-- The Bochner equality specializes to the actual matrix, in operator norm.
theorem allRetainedExpectation
    (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) (t : ℝ≥0) :
    (∫ w : PoissonWord.Word κ,
        spectatorRootChannelWord k (List.ofFn w.2) B ∂PoissonWord.measure κ t) =
      ∫ u : PoissonWord.Word {_i : κ // True},
        spectatorRootChannelWord (fun i : {_i : κ // True} => k i) (List.ofFn u.2) B
          ∂PoissonWord.measure {_i : κ // True} t := by
  simpa using integral_spectatorRootChannelWord_filter (fun _ : κ => True) k B id t

-- The empty retained alphabet gives the initial matrix at every time.
theorem noneRetainedExpectation
    (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) (t : ℝ≥0) :
    (∫ u : PoissonWord.Word {_i : κ // False},
        spectatorRootChannelWord (fun i : {_i : κ // False} => k i) (List.ofFn u.2) B
          ∂PoissonWord.measure {_i : κ // False} t) = B := by
  simpa using
    (integral_spectatorRootChannelWord_filter (fun _ : κ => False) k B id t).symm

-- Positivity and contraction give a genuine integrable matrix observation,
-- rather than relying only on the convention for nonintegrable integrals.
theorem integrableFilteredMatrix
    (P : κ → Prop) [DecidablePred P]
    (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) (t : ℝ≥0) :
    Integrable (fun w : PoissonWord.Word κ => spectatorRootChannelWord k
        ((List.ofFn w.2).filter (fun i => decide (P i))) B)
      (PoissonWord.measure κ t) := by
  apply (integrable_spectatorRootChannelWord_filter_iff P k B id t).2
  refine (integrable_const ‖B‖).mono' AEStronglyMeasurable.of_discrete ?_
  exact Filter.Eventually.of_forall fun u =>
    norm_spectatorRootChannelWord_le (fun i : {i // P i} => k i)
      (fun i => hk₀ i) (fun i => hk₁ i) (List.ofFn u.2) B

end ChannelWordThinningTest

/--
info: 'TNLean.PEPS.AreaLaw.spectatorRootChannelWord_filter'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms spectatorRootChannelWord_filter

/--
info: 'TNLean.PEPS.AreaLaw.integrable_spectatorRootChannelWord_filter_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms integrable_spectatorRootChannelWord_filter_iff

/--
info: 'TNLean.PEPS.AreaLaw.integral_spectatorRootChannelWord_filter'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms integral_spectatorRootChannelWord_filter

/--
info: 'TNLean.PEPS.AreaLaw.integrable_and_integral_siteOscillation_filter_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms integrable_and_integral_siteOscillation_filter_le
