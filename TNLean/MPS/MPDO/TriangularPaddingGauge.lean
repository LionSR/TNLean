/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.TriangularPhysicalPadding

/-!
# Scalar-gauge separation under triangular physical padding

A scalar-gauge relation between two padded operators or two padded states
restricts to the original tensors. The two kinds of padded tensors have
disjoint physical supports and cannot be scalar-gauge equivalent when the
target tensor is injective with positive virtual dimension.

These elementary restrictions supply the separation condition for the
auxiliary operator family used with the fusion and action tensors of
Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `rawrels` and `coupledpent`.
-/

namespace MPOTensor

variable {d D : ℕ}

/-- Restriction to the retained physical corner recovers a scalar-gauge
relation between the original operator tensors. -/
theorem gaugePhaseEquiv_of_operatorPhysicalPadding {O P : MPOTensor d D}
    (h : MPSTensor.GaugePhaseEquiv (operatorPhysicalPadding O).toMPSTensor
      (operatorPhysicalPadding P).toMPSTensor) :
    MPSTensor.GaugePhaseEquiv O.toMPSTensor P.toMPSTensor := by
  obtain ⟨X, ζ, hζ, hrel⟩ := h
  refine ⟨X, ζ, hζ, fun q ↦ ?_⟩
  simpa [toMPSTensor] using
    hrel (finProdFinEquiv (q.divNat.castSucc, q.modNat.castSucc))

/-- Restriction to the retained physical column recovers a scalar-gauge
relation between the original state tensors. -/
theorem gaugePhaseEquiv_of_statePhysicalPadding {A B : MPSTensor d D}
    (h : MPSTensor.GaugePhaseEquiv (statePhysicalPadding A).toMPSTensor
      (statePhysicalPadding B).toMPSTensor) : MPSTensor.GaugePhaseEquiv A B := by
  obtain ⟨X, ζ, hζ, hrel⟩ := h
  refine ⟨X, ζ, hζ, fun i ↦ ?_⟩
  simpa [toMPSTensor] using hrel (finProdFinEquiv (i.castSucc, Fin.last d))

private theorem not_isInjective_of_forall_eq_zero {A : MPSTensor d D}
    (hD : 0 < D) (hA : ∀ i, A i = 0) : ¬ Kraus.IsInjective A := by
  intro hInj
  have hle : Submodule.span ℂ (Set.range A) ≤
      (⊥ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ)) := by
    apply Submodule.span_le.mpr
    rintro M ⟨i, rfl⟩
    exact (Submodule.mem_bot ℂ).2 (hA i)
  have hmem : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ Submodule.span ℂ (Set.range A) := by
    rw [hInj.span_eq_top]
    exact Submodule.mem_top
  have hone : (1 : Matrix (Fin D) (Fin D) ℂ) = 0 := (Submodule.mem_bot ℂ).1 (hle hmem)
  let z : Fin D := ⟨0, hD⟩
  have hentry := congrArg (fun M : Matrix (Fin D) (Fin D) ℂ ↦ M z z) hone
  simp at hentry

/-- A padded operator cannot be scalar-gauge equivalent to a padded
injective state of positive virtual dimension: its last column is zero. -/
theorem not_gaugePhaseEquiv_operatorPhysicalPadding_statePhysicalPadding
    (O : MPOTensor d D) {A : MPSTensor d D} (hD : 0 < D)
    (hA : Kraus.IsInjective A) :
    ¬ MPSTensor.GaugePhaseEquiv (operatorPhysicalPadding O).toMPSTensor
      (statePhysicalPadding A).toMPSTensor := by
  rintro ⟨X, ζ, _, hrel⟩
  apply not_isInjective_of_forall_eq_zero hD ?_ hA
  intro i
  simpa [toMPSTensor] using hrel (finProdFinEquiv (i.castSucc, Fin.last d))

/-- A padded state cannot be scalar-gauge equivalent to a padded
injective operator of positive virtual dimension: its retained corner is zero. -/
theorem not_gaugePhaseEquiv_statePhysicalPadding_operatorPhysicalPadding
    (A : MPSTensor d D) {O : MPOTensor d D} (hD : 0 < D)
    (hO : Kraus.IsInjective O.toMPSTensor) :
    ¬ MPSTensor.GaugePhaseEquiv (statePhysicalPadding A).toMPSTensor
      (operatorPhysicalPadding O).toMPSTensor := by
  rintro ⟨X, ζ, _, hrel⟩
  apply not_isInjective_of_forall_eq_zero hD ?_ hO
  intro q
  simpa [toMPSTensor] using
    hrel (finProdFinEquiv (q.divNat.castSucc, q.modNat.castSucc))

end MPOTensor
