/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.BlockedOrbitPeriod

/-!
# Absorbing phases of the actual blocked orbit tensors

The orbit tensors and their compression isometries are chosen once. Every
family of phases whose orders divide the orbit period can then be absorbed
into a trace-preserving one-site tensor. Thus the phase choice does not
require a new choice of orbit decomposition.

Source: arXiv:1708.00029, equations `eq:ZPA-is-cPA` and
`eq:Aprime-is-cPA`, lines 765--806.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- The same compressed periodic orbit tensors admit every phase choice
allowed by their period, realized by a trace-preserving one-site twist.
Source: arXiv:1708.00029, equations `eq:ZPA-is-cPA` and
`eq:Aprime-is-cPA`, lines 765--806. -/
theorem IsPeriodic.exists_phaseTwisted_orbit_decomposition
    {d D m : ℕ} [NeZero m] (A : MPSTensor d D)
    (hA : IsPeriodic m A) {p : ℕ} (hp : 0 < p) :
    ∃ (dim : Fin (Nat.gcd m p) → ℕ)
      (C : (j : Fin (Nat.gcd m p)) → MPSTensor (blockPhysDim d p) (dim j))
      (V : (j : Fin (Nat.gcd m p)) → Matrix (Fin D) (Fin (dim j)) ℂ),
      (∀ j, dim j ≠ 0) ∧
      (∀ j, IsPeriodic (m / Nat.gcd m p) (C j)) ∧
      (∀ j, (V j)ᴴ * V j = 1) ∧
      (∑ j, V j * (V j)ᴴ = 1) ∧
      (∀ I, blockTensor A p I = ∑ j, V j * C j I * (V j)ᴴ) ∧
      ∀ c : Fin (Nat.gcd m p) → Circle,
        (∀ j, c j ^ (m / Nat.gcd m p) = 1) →
        ∃ A' : MPSTensor d D, IsLeftCanonical A' ∧
          ∀ I, blockTensor A' p I = ∑ j, (c j : ℂ) • (V j * C j I * (V j)ᴴ) := by
  classical
  obtain ⟨dim, C, Q, V, α, P, hP, _, hPsum, hPorth, hshift, hα, _, hQorbit,
    hQproj, hQsum, _, hQcomm, hViso, hVrange, hdim, hcorner, hletter, hPer, _⟩ :=
    hA.exists_blockTensor_periodic_orbit_decomposition A hp
  have hVsum : ∑ j, V j * (V j)ᴴ = 1 := by
    simpa only [hVrange] using hQsum
  refine ⟨dim, C, V, hdim, hPer, hViso, hVsum, hletter, ?_⟩
  intro c hc
  obtain ⟨A', hA', hTP⟩ := exists_phaseTwistedTensor_blockTensor P A
    hP hPorth hPsum hshift p (fun u => c (α u))
    (fun u => congrArg c (hα u))
    (fun u => by simpa only [phase_residue_orbit_length] using hc (α u))
  refine ⟨A', hTP hA.leftCanonical, ?_⟩
  intro I
  rw [hA']
  have hsmall : ∀ u, P u * blockTensor A p I * P (u + p • (1 : Fin m)) =
      P u * blockTensor A p I := by
    intro u
    rw [cyclic_projection_blockTensor_shift P A hshift p u I,
      Matrix.mul_assoc, (hP (u + p • (1 : Fin m))).2]
  have hlarge : ∀ j, V j * C j I * (V j)ᴴ = Q j * blockTensor A p I := by
    intro j
    rw [hcorner, hQcomm, Matrix.mul_assoc, (hQproj j).2]
  simp_rw [hsmall, hlarge, ← Matrix.smul_mul]
  rw [← Matrix.sum_mul, ← Matrix.sum_mul]
  congr 1
  simp_rw [hQorbit, orbitProjection, Finset.smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  simp

end MPSTensor
