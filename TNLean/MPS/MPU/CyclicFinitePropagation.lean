/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.CyclicConjugation
import TNLean.MPS.MPU.FiniteWindowSupport
import TNLean.Algebra.FinCyclicInduction
import TNLean.Circuit.Geometry

/-!
# Uniform finite-ring propagation from a supplied standard form

The actual finite standard-form conjugation controls an arbitrary observable
on the complete central interval. Closed-trace cyclic covariance transports
that bound to every singleton, including those at the periodic seam. The
radius is independent of the ring length; no inverse or propagation bound
is supplied as a hypothesis.

Source: arXiv:1703.09188, StandardForm/SF and Appendix eq:appendix-1,
lines 603–622 and 2300–2306.

**Scope restriction (supplied standard form):** These results consume
actual MPU unitarity, a positive block length and supplied two-site
standard-form data, and their neighbourhoods are measured in that block
length. The standard-form construction from bare MPU data and the source
bond-dimension radius remain separate. See
`docs/paper-gaps/mpu_qca_complete_block_heisenberg_scope.tex`.
-/

open scoped Matrix
open Fin.CommRing

namespace MPOTensor

/-- A forward singleton bound at one site propagates cyclically to every
site for the actual periodic MPO. No unitarity or locality hypothesis at
other sites is required. Source context: arXiv:1703.09188, eq:appendix-1,
lines 2300–2306; cyclic covariance is the closed virtual trace identity. -/
theorem mpo_conjugation_singleton_propagation_of_one
    {d D N : ℕ} [NeZero N] (U : MPOTensor d D) (x₀ : Fin N) (r : ℕ)
    (h₀ : ∀ A ∈ QuantumCircuit.supportedOperators d ({x₀} : Set (Fin N)),
      mpo U N * A * (mpo U N)ᴴ ∈
        QuantumCircuit.supportedOperators d (QuantumCircuit.neighbourhood {x₀} r)) :
    ∀ x : Fin N, ∀ A ∈ QuantumCircuit.supportedOperators d ({x} : Set (Fin N)),
      mpo U N * A * (mpo U N)ᴴ ∈
        QuantumCircuit.supportedOperators d (QuantumCircuit.neighbourhood {x} r) := by
  classical
  have hbase : ∀ A ∈ QuantumCircuit.supportedOperators d ({x₀ + 0} : Set (Fin N)),
      mpo U N * A * (mpo U N)ᴴ ∈
        QuantumCircuit.supportedOperators d (QuantumCircuit.neighbourhood {x₀ + 0} r) := by
    simpa only [add_zero] using h₀
  have hstep (i : Fin N)
      (hi : ∀ A ∈ QuantumCircuit.supportedOperators d ({x₀ + i} : Set (Fin N)),
        mpo U N * A * (mpo U N)ᴴ ∈
          QuantumCircuit.supportedOperators d (QuantumCircuit.neighbourhood {x₀ + i} r)) :
      ∀ A ∈ QuantumCircuit.supportedOperators d ({x₀ + (i + 1)} : Set (Fin N)),
        mpo U N * A * (mpo U N)ᴴ ∈
          QuantumCircuit.supportedOperators d
            (QuantumCircuit.neighbourhood {x₀ + (i + 1)} r) := by
    intro A hA
    let A₀ := A.submatrix (fun σ => σ ∘ (finRotate N).symm)
      (fun σ => σ ∘ (finRotate N).symm)
    have hpred : (finRotate N).symm (x₀ + (i + 1)) = x₀ + i := by
      apply (finRotate N).injective
      simp only [Equiv.apply_symm_apply, finRotate_apply, add_assoc]
    have hA₀ : A₀ ∈ QuantumCircuit.supportedOperators d ({x₀ + i} : Set (Fin N)) := by
      have h := QuantumCircuit.supportedOperators_submatrix_siteEquiv (finRotate N).symm hA
      simpa only [Set.image_singleton, hpred] using h
    have hcancel : A₀.submatrix (rotateConfig N d) (rotateConfig N d) = A := by
      ext σ τ
      simp only [A₀, Matrix.submatrix_apply, rotateConfig_apply, Function.comp_def,
        Equiv.apply_symm_apply]
    have h := mpo_conjugation_mem_supportedOperators_rotate U (hi A₀ hA₀)
    rw [QuantumCircuit.neighbourhood_finRotate, Set.image_singleton] at h
    simpa only [hcancel, finRotate_apply, add_assoc] using h
  intro x
  have h := Fin.cyclic_induction hbase hstep (x - x₀)
  have hx : x₀ + (x - x₀) = x := by abel
  simpa only [hx] using h

/-- A supplied actual unitary two-site standard form gives a uniform
singleton propagation radius on every sufficiently long periodic ring,
including the seam. Source: arXiv:1703.09188, StandardForm/SF and
Appendix eq:appendix-1, lines 603–622 and 2300–2306. -/
theorem mpo_conjugation_mem_supportedOperators_singleton
    {d D ℓ r N : ℕ} [NeZero N] {U : MPOTensor d D} (hU : U.IsMPU)
    (k : ℕ) (hk : 0 < k) (hN : 3 * (2 * k) ≤ N)
    {u : Matrix (Fin ℓ × Fin r)
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ}
    {v : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData (blockTwo (blockTensor U k)) u v)
    (x : Fin N) {A : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    (hA : A ∈ QuantumCircuit.supportedOperators d ({x} : Set (Fin N))) :
    mpo U N * A * (mpo U N)ᴴ ∈ QuantumCircuit.supportedOperators d
      (QuantumCircuit.neighbourhood {x} (4 * k)) := by
  classical
  obtain ⟨s, rfl⟩ : ∃ s, N = 0 + (3 * (2 * k) + s) := ⟨N - 3 * (2 * k), by omega⟩
  let x₀ : Fin (0 + (3 * (2 * k) + s)) := ⟨2 * k, by omega⟩
  apply mpo_conjugation_singleton_propagation_of_one U x₀ (4 * k) ?_ x A hA
  intro B hB
  have hCentral : B ∈ QuantumCircuit.supportedOperators d
      {i : Fin (0 + (3 * (2 * k) + s)) | 0 + 2 * k ≤ i.val ∧ i.val < 0 + 2 * k + 2 * k} :=
    QuantumCircuit.supportedOperators_mono (by
      intro i hi
      obtain rfl := Set.mem_singleton_iff.mp hi
      change 0 + 2 * k ≤ 2 * k ∧ 2 * k < 0 + 2 * k + 2 * k
      omega) hB
  have hForward := mpo_conjugation_mem_supportedOperators_central hU k 0 s hk S hCentral
  apply QuantumCircuit.supportedOperators_mono ?_ hForward
  intro j hj
  have hj' : j.val < 0 + 3 * (2 * k) := hj.2
  refine ⟨x₀, Set.mem_singleton x₀, (j.val : ℤ) - x₀.val, ?_, ?_⟩
  · apply abs_le.mpr
    change -((4 * k : ℕ) : ℤ) ≤ (j.val : ℤ) - (2 * k : ℕ) ∧
      (j.val : ℤ) - (2 * k : ℕ) ≤ (4 * k : ℕ)
    constructor <;> omega
  · simp only [Int.cast_sub, Int.cast_natCast, Fin.cast_val_eq_self]
    abel

end MPOTensor
