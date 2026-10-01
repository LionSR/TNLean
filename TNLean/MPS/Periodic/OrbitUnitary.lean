/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.EqualCaseGlobal.Basic
import TNLean.MPS.Periodic.PrescribedBlocking
import TNLean.MPS.Periodic.SectorPhaseBlocking
import TNLean.MPS.SharedInfra.BlockIsometryAssembly

/-!
# Unitary orbit coordinates and phase-weighted blocked roots

The isometries of the prescribed periodic decomposition assemble into a unitary
on the original bond space. Its columns keep the original step-orbit labels,
so the diagonal multiplicity phases can be transported to those orbit supports.
The cyclic phase construction then gives a left-canonical tensor whose blocking
is the phase-weighted direct sum in these same coordinates.

This supplies the bond-coordinate and phase-transport steps of
arXiv:1708.00029, Theorem 4.1. It does not yet identify the phases supplied by the
global equal-case theorem after grouping multiple original periodic blocks.

**Local fix (powered roots):** The period of each orbit block is `m / gcd(m,p)`.
The source's displayed peripheral root set omits the exponent `p`; see
`docs/paper-gaps/dccsp17_blocking_peripheral_roots.tex`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D m : ℕ} [NeZero m]

private theorem blockScalarMatrix_mul_blockInclusion {r : ℕ} {dim : Fin r → ℕ}
    (c : Fin r → ℂ) (a : Fin r) :
    blockScalarMatrix dim c * blockInclusion dim a = c a • blockInclusion dim a := by
  have h := toTensorFromBlocks_mul_blockInclusion (d := 1) (dim := dim) c
    (fun _ _ ↦ 1) a 0
  change blockScalarMatrix dim c * blockInclusion dim a =
    blockInclusion dim a * (c a • 1) at h
  simpa only [Matrix.mul_smul, Matrix.mul_one] using h

private theorem exists_root_of_orbit_phase (A : MPSTensor d D) (hA : IsLeftCanonical A)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hproj : ∀ u, IsOrthogonalProjection (P u)) (hsum : ∑ u, P u = 1)
    (hshift : ∀ u i, P u * A i = A i * P (u + 1)) (p : ℕ)
    (dim : Fin (m.gcd p) → ℕ)
    (B : (a : Fin (m.gcd p)) → MPSTensor (blockPhysDim d p) (dim a))
    (V : (a : Fin (m.gcd p)) → Matrix (Fin D) (Fin (dim a)) ℂ)
    (hrange : ∀ a, V a * (V a)ᴴ = stepOrbitProjection P p a)
    (U : Matrix (Fin D) (Fin (∑ a, dim a)) ℂ)
    (hiso : Uᴴ * U = 1)
    (hinc : ∀ a, U * blockInclusion dim a = V a)
    (hconj : ∀ i, blockTensor A p i = U * toTensorFromBlocks (fun _ ↦ 1) B i * Uᴴ)
    (c : Fin (m.gcd p) → ℂ) (hc : ∀ a, c a ^ (m / m.gcd p) = 1) :
    ∃ A' : MPSTensor d D, IsLeftCanonical A' ∧
      ∀ i, blockTensor A' p i = U * toTensorFromBlocks c B i * Uᴴ := by
  let Z := U * blockScalarMatrix dim c * Uᴴ
  have hZV (a) : Z * V a = c a • V a := by
    rw [← hinc]
    dsimp only [Z]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hiso, Matrix.one_mul, blockScalarMatrix_mul_blockInclusion,
      Matrix.mul_smul]
  have hZ (a i) : Z * (stepOrbitProjection P p a * blockTensor A p i) =
      c a • (stepOrbitProjection P p a * blockTensor A p i) := by
    rw [← hrange]
    simp only [← Matrix.mul_assoc]
    rw [hZV]
    simp only [Matrix.smul_mul]
  have hmul := orthogonalProjection_mul_eq_ite_of_sum_eq_one P hproj hsum
  obtain ⟨A', hA', hblock⟩ := exists_isLeftCanonical_blockTensor_eq_of_orbit_action
    A P hmul (fun u ↦ (hproj u).1.eq) hsum hshift hA p c hc Z hZ
  refine ⟨A', hA', fun i ↦ ?_⟩
  rw [hblock]
  change Z * blockTensor A p i = _
  rw [hconj]
  dsimp only [Z]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, hiso, Matrix.one_mul,
    ← Matrix.mul_assoc (blockScalarMatrix dim c), blockScalarMatrix_mul_toTensorFromBlocks]
  simp only [mul_one]

omit [NeZero m] in
/-- The prescribed periodic blocks assemble by one unitary, retaining their orbit
inclusions. Every family of root-of-unity phases on these same blocks lifts to a
left-canonical root with the original physical dimension and bond space.

Source: arXiv:1708.00029, `lem:blocking-arbitrary`, lines 432–456, and
`eq:ZPA-is-cPA` through `eq:Aprime-is-cPA`, lines 778–807. -/
theorem IsPeriodic.exists_unitary_stepOrbit_decomposition
    (A : MPSTensor d D) (hA : IsPeriodic m A) {p : ℕ} (hp : 0 < p) :
    let _ : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
    ∃ (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
      (dim : Fin (m.gcd p) → ℕ)
      (B : (a : Fin (m.gcd p)) → MPSTensor (blockPhysDim d p) (dim a))
      (V : (a : Fin (m.gcd p)) → Matrix (Fin D) (Fin (dim a)) ℂ)
      (U : Matrix (Fin D) (Fin (∑ a, dim a)) ℂ),
      (∀ u, IsOrthogonalProjection (P u)) ∧ (∑ u, P u = 1) ∧
      (∀ u i, P u * A i = A i * P (u + 1)) ∧
      (∑ a, dim a) = D ∧
      (∀ a, IsPeriodic (m / m.gcd p) (B a)) ∧
      (∀ a, V a * (V a)ᴴ = stepOrbitProjection P p a) ∧
      U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧
      (∀ a, U * blockInclusion dim a = V a) ∧
      (∀ i, blockTensor A p i = U * toTensorFromBlocks (fun _ ↦ 1) B i * Uᴴ) ∧
      ∀ c : Fin (m.gcd p) → ℂ, (∀ a, c a ^ (m / m.gcd p) = 1) →
        ∃ A' : MPSTensor d D, IsLeftCanonical A' ∧
          ∀ i, blockTensor A' p i = U * toTensorFromBlocks c B i * Uᴴ := by
  let : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
  obtain ⟨P, dim, B, V, hproj, hsum, _, hshift, _, hdim, _, _, hiso, hrange, hB, hper⟩ :=
    hA.exists_stepOrbit_blockDecomposition p
  have hinter (a) (i) : blockTensor A p i * V a = V a * B a i := by
    have hPV : stepOrbitProjection P p a * V a = V a := by
      rw [← hrange, Matrix.mul_assoc, hiso, Matrix.mul_one]
    rw [hB, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hrange,
      stepOrbitProjection_mul_blockTensor P A hshift, Matrix.mul_assoc, hPV]
  obtain ⟨U, hco, hU, hinc, hconj⟩ :=
    exists_unitary_toTensorFromBlocks_of_resolution (blockTensor A p) B V
      (by simp only [hrange, sum_stepOrbitProjection, hsum]) hdim hinter
  refine ⟨P, dim, B, V, U, hproj, hsum, hshift, hdim, hper hp, hrange,
    hco, hU, hinc, hconj, ?_⟩
  exact fun c hc ↦ exists_root_of_orbit_phase A hA.leftCanonical P hproj hsum hshift p
    dim B V hrange U hU hinc hconj c hc

end MPSTensor
