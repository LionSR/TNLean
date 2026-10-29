/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PhysicalSectorKernelSupport

/-!
# Decomposing physical-sector ground vectors

A vector whose mixed-alphabet coefficients vanish is exactly the sum of the
extensions of its two actual coefficient restrictions. Applied to the periodic
complementary projector of two embedded local spaces, mixed-coefficient
vanishing is derived from the Hamiltonian equation. No state decomposition or
component-state supplier is assumed.

This supplies physical-sector assembly for the finite-prefix investigation of
SPWC10, arXiv:0909.5347, Theorem 5, lines 850--880. It does not identify the
component Hamiltonian kernels or assert a full source counterexample.
-/

namespace MPSTensor

variable {a b M : ℕ}

private theorem mem_castAdd_word_range_iff (σ : Cfg (a + b) M) :
    σ ∈ Set.range (Function.Embedding.piCongrRight
      (fun _ : Fin M ↦ (Fin.castAddEmb b : Fin a ↪ Fin (a + b)))) ↔
      ∀ i, (σ i).val < a := by
  constructor
  · rintro ⟨w, rfl⟩ i
    exact (w i).isLt
  · intro hσ
    refine ⟨fun i ↦ ⟨(σ i).val, hσ i⟩, ?_⟩
    funext i
    apply Fin.ext
    rfl

private theorem mem_natAdd_word_range_iff (σ : Cfg (a + b) M) :
    σ ∈ Set.range (Function.Embedding.piCongrRight
      (fun _ : Fin M ↦ (Fin.natAddEmb a : Fin b ↪ Fin (a + b)))) ↔
      ∀ i, a ≤ (σ i).val := by
  constructor
  · rintro ⟨w, rfl⟩ i
    change a ≤ a + (w i).val
    omega
  · intro hσ
    refine ⟨fun i ↦ ⟨(σ i).val - a, by have := (σ i).isLt; have := hσ i; omega⟩, ?_⟩
    funext i
    apply Fin.ext
    change a + ((σ i).val - a) = (σ i).val
    omega

/-- A vector supported on the two pure physical alphabets is the sum of the
extensions of its actual coefficient restrictions, without scalar or dimension
factors. The positive chain length makes the two word images disjoint.
Source: physical-sector assembly for SPWC10, Theorem 5, lines 850--880. -/
theorem physical_sum_state_decomposition (hM : 0 < M) (ψ : MPVSpace (a + b) M)
    (hψ : ∀ (σ : Cfg (a + b) M) (i j : Fin M),
      (σ i).val < a → a ≤ (σ j).val → ψ σ = 0) :
    ψ = (Function.Embedding.piCongrRight (fun _ : Fin M ↦ Fin.castAddEmb b))
        .euclideanExtendByZero (WithLp.toLp 2 fun w ↦ ψ (fun i ↦ Fin.castAdd b (w i))) +
      (Function.Embedding.piCongrRight (fun _ : Fin M ↦ Fin.natAddEmb a))
        .euclideanExtendByZero (WithLp.toLp 2 fun w ↦ ψ (fun i ↦ Fin.natAdd a (w i))) := by
  classical
  let E := Function.Embedding.piCongrRight
    (fun _ : Fin M ↦ (Fin.castAddEmb b : Fin a ↪ Fin (a + b)))
  let F := Function.Embedding.piCongrRight
    (fun _ : Fin M ↦ (Fin.natAddEmb a : Fin b ↪ Fin (a + b)))
  let x : MPVSpace a M := WithLp.toLp 2 fun w ↦ ψ (E w)
  let y : MPVSpace b M := WithLp.toLp 2 fun w ↦ ψ (F w)
  change ψ = E.euclideanExtendByZero x + F.euclideanExtendByZero y
  apply PiLp.ext
  intro σ
  change ψ σ = E.euclideanExtendByZero x σ + F.euclideanExtendByZero y σ
  by_cases hE : σ ∈ Set.range E
  · obtain ⟨w, rfl⟩ := hE
    have hF : E w ∉ Set.range F := by
      rintro ⟨v, hv⟩
      have hval := congrArg (fun z : Cfg (a + b) M ↦ (z ⟨0, hM⟩).val) hv
      change a + (v ⟨0, hM⟩).val = (w ⟨0, hM⟩).val at hval
      have hw := (w ⟨0, hM⟩).isLt
      omega
    calc
      ψ (E w) = x w := rfl
      _ = E.euclideanExtendByZero x (E w) + F.euclideanExtendByZero y (E w) := by
        rw [E.euclideanExtendByZero_apply_image,
          F.euclideanExtendByZero_apply_not_mem_range y _ hF, add_zero]
  · by_cases hF : σ ∈ Set.range F
    · obtain ⟨w, rfl⟩ := hF
      calc
        ψ (F w) = y w := rfl
        _ = E.euclideanExtendByZero x (F w) + F.euclideanExtendByZero y (F w) := by
          rw [E.euclideanExtendByZero_apply_not_mem_range x _ hE,
            F.euclideanExtendByZero_apply_image, zero_add]
    · have hnot_left : ¬ ∀ i, (σ i).val < a := by
        intro h
        exact hE ((mem_castAdd_word_range_iff σ).mpr h)
      have hnot_right : ¬ ∀ i, a ≤ (σ i).val := by
        intro h
        exact hF ((mem_natAdd_word_range_iff σ).mpr h)
      push_neg at hnot_left hnot_right
      obtain ⟨j, hj⟩ := hnot_left
      obtain ⟨i, hi⟩ := hnot_right
      rw [E.euclideanExtendByZero_apply_not_mem_range x _ hE,
        F.euclideanExtendByZero_apply_not_mem_range y _ hF, zero_add]
      exact hψ σ i j hi hj

/-- Every vector in the actual periodic two-sector projector kernel splits
into the extensions of its actual sector coefficient restrictions. Mixed
coefficients are derived from the Hamiltonian equation rather than supplied.
Source: physical-sector assembly for SPWC10, Theorem 5, lines 850--880. -/
theorem physical_sum_state_decomposition_of_projectorHamiltonian_eq_zero
    {R : ℕ} (S : Submodule ℂ (MPVSpace a R)) (T : Submodule ℂ (MPVSpace b R))
    (hR : 2 ≤ R) (hRM : R ≤ M) (ψ : MPVSpace (a + b) M)
    (hzero : periodicInteractionHamiltonianES
      ((S.map
          (Function.Embedding.piCongrRight
            (fun _ : Fin R ↦ Fin.castAddEmb b)).euclideanExtendByZero.toLinearMap ⊔
        T.map
          (Function.Embedding.piCongrRight
            (fun _ : Fin R ↦ Fin.natAddEmb a)).euclideanExtendByZero.toLinearMap)ᗮ
        .starProjection.toLinearMap) M ψ = 0) :
    ψ = (Function.Embedding.piCongrRight (fun _ : Fin M ↦ Fin.castAddEmb b))
        .euclideanExtendByZero (WithLp.toLp 2 fun w ↦ ψ (fun i ↦ Fin.castAdd b (w i))) +
      (Function.Embedding.piCongrRight (fun _ : Fin M ↦ Fin.natAddEmb a))
        .euclideanExtendByZero (WithLp.toLp 2 fun w ↦ ψ (fun i ↦ Fin.natAdd a (w i))) := by
  apply physical_sum_state_decomposition (by omega) ψ
  intro σ i j hi hj
  exact coeff_eq_zero_of_physical_sum_projectorHamiltonian S T hR hRM ψ hzero σ i j hi hj

end MPSTensor
