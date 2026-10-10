/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.ChannelWordObservables

/-! Boundary and chronology consumers for actual physical channel words. -/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit Matrix TNLean.PEPS.AreaLaw
open scoped BigOperators Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace ChannelWordObservablesTest

variable {q : ℕ} {ι κ Aux : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype Aux] [DecidableEq Aux]

-- Empty words use the existing support indicator, with no assumptions on k.
theorem initialSupport [NeZero q]
    (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ) (K : Finset ι) (y : ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ)
    (hB : ∀ a b : Aux, (Matrix.of fun σ τ => B (σ, a) (τ, b)) ∈
      supportedOperators q (K : Set ι)) :
    siteOscillation q y (spectatorRootChannelWord k [] B) ≤
      2 * ‖B‖ * (K : Set ι).indicator (fun _ => (1 : ℝ)) y :=
  siteOscillation_le_support_indicator K B hB y

-- Two labels are applied in chronological order, without commuting.
theorem chronologicalPair (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ) (i j : κ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    spectatorRootChannelWord k [i, j] B =
      spectatorRootChannel (k j) (spectatorRootChannel (k i) B) := rfl

-- Appending to an arbitrary prefix applies the new channel on the outside.
example (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ) (w : List κ) (i j : κ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    spectatorRootChannelWord k ((w ++ [i]) ++ [j]) B =
      spectatorRootChannel (k j) (spectatorRootChannel (k i)
        (spectatorRootChannelWord k w B)) := by
  simp only [spectatorRootChannelWord_append_singleton]

-- Empty event types have only the empty word and zero summed increments.
theorem emptyEvents (G : SimpleGraph ι) (a : Empty → ι)
    (k : Empty → Matrix (ι → Fin q) (ι → Fin q) ℂ) (w : List Empty) (y : ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) (D b α : ℝ) (N : ℕ) :
    spectatorRootChannelWord k w B = B ∧
      (∑ i, (siteOscillation q y (spectatorRootChannelWord k (w ++ [i]) B) -
        siteOscillation q y (spectatorRootChannelWord k w B))) =
      ∑ z, graphChannelEventKernel G a D b α N y z *
        siteOscillation q z (spectatorRootChannelWord k w B) := by
  cases w with
  | nil => simp [graphChannelEventKernel]
  | cons i w => exact isEmptyElim i

-- The physical bounds require no inhabited spectator space.
example (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1) (w : List κ) (y : ι)
    (B : Matrix ((ι → Fin q) × Empty) ((ι → Fin q) × Empty) ℂ) :
    ‖spectatorRootChannelWord k w B‖ ≤ ‖B‖ ∧
      0 ≤ siteOscillation q y (spectatorRootChannelWord k w B) ∧
      siteOscillation q y (spectatorRootChannelWord k w B) ≤ 2 * ‖B‖ :=
  ⟨norm_spectatorRootChannelWord_le k hk₀ hk₁ w B,
    siteOscillation_spectatorRootChannelWord_bounds k hk₀ hk₁ w y B⟩

-- The generic foldl fixed-point lemma gives fixedness for any spectator matrix.
theorem fixesSpectator (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1)
    (w : List κ) (S : Matrix Aux Aux ℂ) :
    spectatorRootChannelWord k w ((1 : Matrix (ι → Fin q) (ι → Fin q) ℂ) ⊗ₖ S) =
      1 ⊗ₖ S := by
  apply List.foldl_fixed'
  intro i
  simp only [spectatorRootChannel, rootChannel, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul, ← Matrix.add_kronecker,
    sqrt_one_sub_mul_add_sqrt_mul (hk₀ i) (hk₁ i)]

private noncomputable def raisingObservable :
    Matrix ((Unit → Fin 2) × Fin 2) ((Unit → Fin 2) × Fin 2) ℂ :=
  (1 : Matrix (Unit → Fin 2) (Unit → Fin 2) ℂ) ⊗ₖ Matrix.single 0 1 1

-- This concrete full-system observable is non-Hermitian, and every word fixes it.
theorem nonHermitianSpectator
    (k : κ → Matrix (Unit → Fin 2) (Unit → Fin 2) ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1) (w : List κ) :
    ¬raisingObservable.IsHermitian ∧
      spectatorRootChannelWord k w raisingObservable = raisingObservable := by
  refine ⟨?_, fixesSpectator k hk₀ hk₁ w _⟩
  intro h
  have hentry := congrArg (fun M => M ((fun _ => 0), 0) ((fun _ => 0), 1)) h.eq
  simp [raisingObservable, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply] at hentry

-- A common cutoff exists by a finite supremum even for disconnected graphs.
example [Fintype κ] (G : SimpleGraph ι) (a : κ → ι) (i : κ) :
    Finset.univ.sup (G.dist (a i)) ≤
      Finset.univ.sup (fun j => Finset.univ.sup (G.dist (a j))) :=
  Finset.le_sup (f := fun j => Finset.univ.sup (G.dist (a j))) (Finset.mem_univ i)

-- The recurrence consumes the actual evolved matrix, at every prefix.
example [Fintype κ] [NeZero q]
    (G : SimpleGraph ι) (a : κ → ι) (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1)
    (hk : ∀ i, k i ∈ supportedOperators q {x | G.Reachable (a i) x})
    {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (N : ℕ) (hN : ∀ i, Finset.univ.sup (G.dist (a i)) ≤ N)
    (hε : ∀ i l, l ≤ N → ‖k i - siteExpectation q (graphBall G (a i) l) (k i)‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ α)))
    (w : List κ) (y : ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    (∑ i, (siteOscillation q y (spectatorRootChannelWord k (w ++ [i]) B) -
      siteOscillation q y (spectatorRootChannelWord k w B))) ≤
      ∑ z, graphChannelEventKernel G a (2 * (2 + 8 * Real.sqrt C * Real.exp (c / 2)))
        (c / 2) α N y z * siteOscillation q z (spectatorRootChannelWord k w B) :=
  sum_siteOscillation_spectatorRootChannelWord_append_sub_le_graphChannelEventKernel
    G a k hk₀ hk₁ hk hC hc hα hα₁ N hN hε w y B

end ChannelWordObservablesTest

/--
info: 'TNLean.PEPS.AreaLaw.spectatorRootChannelWord'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms spectatorRootChannelWord

/--
info: 'TNLean.PEPS.AreaLaw.spectatorRootChannelWord_nil'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms spectatorRootChannelWord_nil

/--
info: 'TNLean.PEPS.AreaLaw.spectatorRootChannelWord_append_singleton'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms spectatorRootChannelWord_append_singleton

/--
info: 'TNLean.PEPS.AreaLaw.norm_spectatorRootChannelWord_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms norm_spectatorRootChannelWord_le

/--
info: 'TNLean.PEPS.AreaLaw.siteOscillation_spectatorRootChannelWord_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms siteOscillation_spectatorRootChannelWord_bounds

/--
info: 'TNLean.PEPS.AreaLaw.sum_siteOscillation_spectatorRootChannelWord_append_sub_le_graphChannelEventKernel'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms sum_siteOscillation_spectatorRootChannelWord_append_sub_le_graphChannelEventKernel
