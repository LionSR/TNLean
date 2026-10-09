/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.GraphChannelEventError

/-!
Boundary regressions for actual one-event errors. Exact localization at radius
zero leaves coefficient two; disconnected components contribute only their own
sites. Empty spectators and explicit non-Hermitian observables are included.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit Matrix TNLean.PEPS.AreaLaw
open scoped BigOperators Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace GraphChannelEventErrorTest

variable {q : ℕ} {ι Aux : Type*} [Fintype ι] [DecidableEq ι] [NeZero q]
  [Fintype Aux] [DecidableEq Aux]

-- The localization hypotheses are proved from support, not assumed. At n = 0
-- and C = 0 the actual event error has coefficient two, not four or zero.
theorem exactSupportZeroRadius (K : Finset ι)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (hK : k ∈ supportedOperators q (K : Set ι))
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    ‖spectatorRootChannel k B - B‖ ≤ 2 * ∑ z ∈ K, siteOscillation q z B := by
  have hlocal : siteExpectation q K k = k :=
    siteExpectation_of_mem_supportedOperators K hK
  have hε : ∀ l ≤ (0 : ℕ), ‖k - siteExpectation q K k‖ ≤
      (0 : ℝ) * Real.exp (-(2 * (l : ℝ) ^ (1 : ℝ))) := by
    intro l _
    simp [hlocal]
  simpa [localRootChannel, hlocal] using
    norm_localRootChannel_sub_self_le_exp_sum_siteOscillation
      (fun _ => K) monotone_const hk₀ hk₁ (C := 0) (c := 2) (α := 1)
      le_rfl (by norm_num) (by norm_num) le_rfl 0 hε B

-- Retaining every site gives exact localization for every positive contraction.
-- There is no separate support, decay, connectedness, or Hermiticity hypothesis.
theorem exactFullSupport
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    ‖spectatorRootChannel k B - B‖ ≤ 2 * ∑ z, siteOscillation q z B := by
  apply exactSupportZeroRadius Finset.univ hk₀ hk₁
  simpa using mem_supportedOperators_univ k

-- The two isolated sites have natural-distance cutoff zero, but the graph ball
-- contains only the anchor. In particular the other site's oscillation is absent.
theorem disconnectedZeroRadius
    {k : Matrix (Fin 2 → Fin q) (Fin 2 → Fin q) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (hk : k ∈ supportedOperators q ({0} : Set (Fin 2)))
    (B : Matrix ((Fin 2 → Fin q) × Aux) ((Fin 2 → Fin q) × Aux) ℂ) :
    ‖spectatorRootChannel k B - B‖ ≤ 2 * siteOscillation q 0 B := by
  have hcomponent : {x : Fin 2 | (⊥ : SimpleGraph (Fin 2)).Reachable 0 x} = {0} := by
    ext x
    simp [eq_comm]
  have hball : graphBall (⊥ : SimpleGraph (Fin 2)) 0 0 = {0} := by
    ext x
    rw [mem_graphBall, Finset.mem_singleton]
    change ((⊥ : SimpleGraph (Fin 2)).edist 0 x ≤ ⊥) ↔ x = 0
    rw [le_bot_iff, (bot_eq_zero : (⊥ : ENat) = 0), SimpleGraph.edist_eq_zero_iff]
    exact eq_comm
  have hcutoff : Finset.univ.sup ((⊥ : SimpleGraph (Fin 2)).dist 0) ≤ 0 := by
    simp [SimpleGraph.dist, SimpleGraph.edist_bot]
  have hε : ∀ l ≤ (0 : ℕ),
      ‖k - siteExpectation q (graphBall (⊥ : SimpleGraph (Fin 2)) 0 l) k‖ ≤
        (0 : ℝ) * Real.exp (-(2 * (l : ℝ) ^ (1 : ℝ))) := by
    intro l hl
    have hl₀ : l = 0 := Nat.eq_zero_of_le_zero hl
    subst l
    rw [hball, siteExpectation_of_mem_supportedOperators {0} (by simpa using hk)]
    simp
  simpa [hball] using
    norm_spectatorRootChannel_sub_self_le_exp_of_component_support
      (⊥ : SimpleGraph (Fin 2)) 0 hk₀ hk₁ (by rwa [hcomponent])
      (C := 0) (c := 2) (α := 1) le_rfl (by norm_num) (by norm_num) le_rfl
      0 hcutoff hε B

-- An empty spectator has actual error zero, even before any effect assumptions.
omit [NeZero q] in
theorem emptySpectatorError (k : Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (B : Matrix ((ι → Fin q) × Empty) ((ι → Fin q) × Empty) ℂ) :
    ‖spectatorRootChannel k B - B‖ = 0 := by
  rw [Subsingleton.elim (spectatorRootChannel k B) B, sub_self, norm_zero]

-- The entire proposed shell majorant is also exactly zero in that case.
omit [NeZero q] in
theorem emptySpectatorShellSum (regions : ℕ → Finset ι) (C c α : ℝ) (n : ℕ)
    (B : Matrix ((ι → Fin q) × Empty) ((ι → Fin q) × Empty) ℂ) :
    (∑ l ∈ Finset.range (n + 1),
      ((2 + 8 * Real.sqrt C * Real.exp (c / 2)) *
        Real.exp (-(c / 2 * (l : ℝ) ^ α))) *
          ∑ z ∈ regions l, siteOscillation q z B) = 0 := by
  have hB : B = 0 := Subsingleton.elim _ _
  simp [hB]

private def nonHermitianObservable :
    Matrix ((Unit → Fin 2) × Fin 2) ((Unit → Fin 2) × Fin 2) ℂ :=
  (1 : Matrix (Unit → Fin 2) (Unit → Fin 2) ℂ) ⊗ₖ !![(0 : ℂ), 1; 0, 0]

-- This is a non-Hermitian observable on the full physical-spectator space.
theorem observable_not_isHermitian : ¬nonHermitianObservable.IsHermitian := by
  intro h
  have h01 := congrFun (congrFun h.eq ((fun _ => 0), 0)) ((fun _ => 0), 1)
  norm_num [nonHermitianObservable, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply] at h01

-- The new event estimate forces exact vanishing for this explicit observable.
theorem nonHermitianEventError
    {k : Matrix (Unit → Fin 2) (Unit → Fin 2) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1) :
    ‖spectatorRootChannel k nonHermitianObservable - nonHermitianObservable‖ = 0 := by
  apply le_antisymm _ (norm_nonneg _)
  simpa [nonHermitianObservable] using exactFullSupport hk₀ hk₁ nonHermitianObservable

end GraphChannelEventErrorTest
