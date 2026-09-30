/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.BlockedOrbitDecomposition
import TNLean.MPS.Periodic.CompressedCyclicShift
import TNLean.MPS.Periodic.OrbitFixedPointBasis

/-!
# Cyclic microsectors inside a blocked orbit

Each original cyclic projection belongs to exactly one shift orbit. Its
compression to that orbit is nonzero, and the compressed adjoint transfer
map advances it by the blocking length.

Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 765--806.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- An original cyclic projection is supported on its orbit projection.
Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 765--806. -/
theorem orbitProjection_supports_cyclic_projection
    {D m r : ℕ} (α : Fin m → Fin r) (P : Fin m → MatrixAlg D)
    (hP : ∀ u, IsOrthogonalProjection (P u))
    (horth : ∀ u v, u ≠ v → P u * P v = 0)
    (u : Fin m) :
    orbitProjection α P (α u) * P u * orbitProjection α P (α u) = P u := by
  have hright := mul_orbitProjection_self α P hP horth u
  have hleft : orbitProjection α P (α u) * P u = P u := by
    have h := congrArg Matrix.conjTranspose hright
    rw [Matrix.conjTranspose_mul, (hP u).1,
      (orbitProjection_isOrthogonalProjection α P hP horth (α u)).1] at h
    exact h
  rw [hleft, hright]

/-- Compression of a nonzero cyclic projection to its orbit remains
nonzero. Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 765--806. -/
theorem compressed_cyclic_projection_ne_zero
    {D m r n : ℕ} (α : Fin m → Fin r) (P : Fin m → MatrixAlg D)
    (hP : ∀ u, IsOrthogonalProjection (P u))
    (hPne : ∀ u, P u ≠ 0)
    (horth : ∀ u v, u ≠ v → P u * P v = 0)
    (u : Fin m) (V : Matrix (Fin D) (Fin n) ℂ)
    (hVrange : V * Vᴴ = orbitProjection α P (α u)) :
    Vᴴ * P u * V ≠ 0 := by
  intro hzero
  have hsupport := orbitProjection_supports_cyclic_projection α P hP horth u
  have hzero' : P u = 0 := by
    calc
      P u = orbitProjection α P (α u) * P u *
          orbitProjection α P (α u) := hsupport.symm
      _ = V * (Vᴴ * P u * V) * Vᴴ := by
        rw [← hVrange]
        simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hzero, Matrix.mul_zero, Matrix.zero_mul]
  exact hPne u hzero'

/-- The compression of a cyclic projection to its orbit is again an
orthogonal projection. Source: arXiv:1708.00029, Lemma
`lem:blocking-arbitrary`, lines 765--806. -/
theorem compressed_cyclic_projection_isOrthogonalProjection
    {D m r n : ℕ} (α : Fin m → Fin r) (P : Fin m → MatrixAlg D)
    (hP : ∀ u, IsOrthogonalProjection (P u))
    (horth : ∀ u v, u ≠ v → P u * P v = 0)
    (u : Fin m) (V : Matrix (Fin D) (Fin n) ℂ)
    (hVrange : V * Vᴴ = orbitProjection α P (α u)) :
    IsOrthogonalProjection (Vᴴ * P u * V) := by
  constructor
  · change (Vᴴ * P u * V)ᴴ = Vᴴ * P u * V
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
    rw [(hP u).1]
  · have hPQ := mul_orbitProjection_self α P hP horth u
    calc
      (Vᴴ * P u * V) * (Vᴴ * P u * V) =
          Vᴴ * (P u * (V * Vᴴ) * P u) * V := by
            simp only [Matrix.mul_assoc]
      _ = Vᴴ * P u * V := by
        rw [hVrange, hPQ, (hP u).2]

/-- Distinct cyclic projections in one orbit remain orthogonal after
compression. Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 765--806. -/
theorem compressed_cyclic_projections_mul_eq_zero
    {D m r n : ℕ} (α : Fin m → Fin r) (P : Fin m → MatrixAlg D)
    (hP : ∀ u, IsOrthogonalProjection (P u))
    (horth : ∀ u v, u ≠ v → P u * P v = 0)
    (u v : Fin m) (huv : u ≠ v)
    (V : Matrix (Fin D) (Fin n) ℂ)
    (hVrange : V * Vᴴ = orbitProjection α P (α u)) :
    (Vᴴ * P u * V) * (Vᴴ * P v * V) = 0 := by
  have hPQ := mul_orbitProjection_self α P hP horth u
  calc
    (Vᴴ * P u * V) * (Vᴴ * P v * V) =
        Vᴴ * (P u * (V * Vᴴ) * P v) * V := by
          simp only [Matrix.mul_assoc]
    _ = Vᴴ * (P u * P v) * V := by rw [hVrange, hPQ]
    _ = 0 := by rw [horth u v huv]; simp

/-- Distinct original cyclic sectors lying in the same orbit give
independent compressed projection matrices. Source: arXiv:1708.00029,
Lemma `lem:blocking-arbitrary`, lines 765--806. -/
theorem linearIndependent_compressed_cyclic_projections
    {D m r n s : ℕ} (α : Fin m → Fin r)
    (P : Fin m → MatrixAlg D)
    (hP : ∀ u, IsOrthogonalProjection (P u))
    (hPne : ∀ u, P u ≠ 0)
    (horth : ∀ u v, u ≠ v → P u * P v = 0)
    (j : Fin r) (f : Fin s → Fin m)
    (hf : Function.Injective f) (hα : ∀ t, α (f t) = j)
    (V : Matrix (Fin D) (Fin n) ℂ)
    (hVrange : V * Vᴴ = orbitProjection α P j) :
    LinearIndependent ℂ (fun t => Vᴴ * P (f t) * V) := by
  let R : Fin s → MatrixAlg n := fun t => Vᴴ * P (f t) * V
  have hrange : ∀ t, V * Vᴴ = orbitProjection α P (α (f t)) := by
    intro t
    rw [hα t]
    exact hVrange
  have hRproj : ∀ t, IsOrthogonalProjection (R t) := by
    intro t
    exact compressed_cyclic_projection_isOrthogonalProjection α P hP horth
      (f t) V (hrange t)
  have hRne : ∀ t, R t ≠ 0 := by
    intro t
    exact compressed_cyclic_projection_ne_zero α P hP hPne horth
      (f t) V (hrange t)
  have hRorth : ∀ t u, t ≠ u → R t * R u = 0 := by
    intro t u htu
    exact compressed_cyclic_projections_mul_eq_zero α P hP horth
      (f t) (f u) (hf.ne htu) V (hrange t)
  exact linearIndependent_orthogonal_corners R R hRorth
    (fun t => by rw [(hRproj t).2, (hRproj t).2]) hRne

/-- The compressed adjoint transfer map advances each microsector by
the blocking length. Source: arXiv:1708.00029, Lemma
`lem:blocking-arbitrary`, lines 765--806. -/
theorem compressed_blockTensor_cyclic_projection_shift
    {d D m r n p : ℕ} [NeZero m] (A : MPSTensor d D)
    (C : MPSTensor (blockPhysDim d p) n)
    (α : Fin m → Fin r) (P : Fin m → MatrixAlg D)
    (hP : ∀ u, IsOrthogonalProjection (P u))
    (horth : ∀ u v, u ≠ v → P u * P v = 0)
    (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (hshift : ∀ u i, P u * A i = A i * P (u + 1))
    (u : Fin m) (V : Matrix (Fin D) (Fin n) ℂ)
    (hVrange : V * Vᴴ = orbitProjection α P (α u))
    (hC : ∀ I, C I = Vᴴ * blockTensor A p I * V) :
    Kraus.map (fun I => (C I)ᴴ) (Vᴴ * P u * V) =
      Vᴴ * P (u + p • (1 : Fin m)) * V := by
  apply compressed_adjointTransferMap_shift (blockTensor A p) C
    (orbitProjection α P (α u)) (P u)
    (P (u + p • (1 : Fin m))) V hVrange hC
  · exact orbitProjection_supports_cyclic_projection α P hP horth u
  · exact adjointTransferMap_blockTensor_cyclic_projection_shift
      P A hTP hshift p u

end MPSTensor
