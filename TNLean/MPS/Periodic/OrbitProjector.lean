/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.CyclicSectors.CommutingProj

/-!
# Projections onto unions of cyclic sectors

Summing mutually orthogonal sector projections over the fibres of an orbit
label gives complete orthogonal orbit projections. A tensor with no matrix
corners between distinct labels commutes with each orbit projection. These
finite-dimensional identities are used for the blocked decomposition in
arXiv:1708.00029, Section 4.1, lines 765--806.
-/
open scoped Matrix BigOperators
namespace MPSTensor
variable {ι : Type*} [DecidableEq ι] {m D d : ℕ}

/-- The sum of cyclic projections in one orbit. Source:
arXiv:1708.00029, Section 4.1, lines 765--806. -/
noncomputable def orbitProjection (α : Fin m → ι) (P : Fin m → MatrixAlg D)
    (a : ι) : MatrixAlg D :=
  ∑ u : Fin m, if α u = a then P u else 0

/-- The orbit projections partition the identity. Source:
arXiv:1708.00029, Section 4.1, lines 765--806. -/
theorem orbitProjection_sum [Fintype ι] (α : Fin m → ι) (P : Fin m → MatrixAlg D)
    (hsum : ∑ u : Fin m, P u = 1) :
    ∑ a : ι, orbitProjection α P a = 1 := by
  simp [orbitProjection, Finset.sum_comm, hsum]

/-- Each orbit projection is an orthogonal projection. Source:
arXiv:1708.00029, Section 4.1, lines 765--806. -/
theorem orbitProjection_isOrthogonalProjection (α : Fin m → ι)
    (P : Fin m → MatrixAlg D)
    (hP : ∀ u, IsOrthogonalProjection (P u))
    (horth : ∀ u v, u ≠ v → P u * P v = 0)
    (a : ι) : IsOrthogonalProjection (orbitProjection α P a) := by
  constructor
  · change (orbitProjection α P a)ᴴ = orbitProjection α P a
    simp only [orbitProjection, Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro u _
    split_ifs
    · exact (hP u).1
    · simp
  · let S : Finset (Fin m) := Finset.univ.filter (fun u => α u = a)
    have hQ : orbitProjection α P a = ∑ u ∈ S, P u := by
      simp [orbitProjection, S, Finset.sum_filter]
    rw [hQ]
    calc
      (∑ u ∈ S, P u) * (∑ v ∈ S, P v) =
          ∑ u ∈ S, ∑ v ∈ S, P u * P v := by
            rw [Finset.sum_mul]
            simp only [Finset.mul_sum]
      _ = ∑ u ∈ S, P u := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [Finset.sum_eq_single u]
        · exact (hP u).2
        · intro v hv hne
          exact horth u v hne.symm
        · intro hnot
          exact False.elim (hnot hu)

/-- A cyclic projection is contained in its orbit projection. Source:
arXiv:1708.00029, Section 4.1, lines 765--806. -/
theorem mul_orbitProjection_self (α : Fin m → ι)
    (P : Fin m → MatrixAlg D)
    (hP : ∀ u, IsOrthogonalProjection (P u))
    (horth : ∀ u v, u ≠ v → P u * P v = 0)
    (u : Fin m) : P u * orbitProjection α P (α u) = P u := by
  let S : Finset (Fin m) := Finset.univ.filter (fun v => α v = α u)
  have hQ : orbitProjection α P (α u) = ∑ v ∈ S, P v := by
    simp [orbitProjection, S, Finset.sum_filter]
  rw [hQ, Matrix.mul_sum]
  calc
    (∑ v ∈ S, P u * P v) = P u * P u := by
      apply Finset.sum_eq_single u
      · intro v _ hne
        exact horth u v hne.symm
      · simp [S]
    _ = P u := (hP u).2

/-- Each orbit projection is nonzero when every fibre contains a nonzero
cyclic projection. Source: arXiv:1708.00029, Section 4.1,
lines 765--806. -/
theorem orbitProjection_ne_zero (α : Fin m → ι)
    (P : Fin m → MatrixAlg D)
    (hP : ∀ u, IsOrthogonalProjection (P u))
    (horth : ∀ u v, u ≠ v → P u * P v = 0)
    (hPne : ∀ u, P u ≠ 0)
    (hsurj : Function.Surjective α)
    (a : ι) : orbitProjection α P a ≠ 0 := by
  obtain ⟨u, rfl⟩ := hsurj a
  intro hzero
  have h := mul_orbitProjection_self α P hP horth u
  rw [hzero, Matrix.mul_zero] at h
  exact hPne u h.symm

/-- Distinct orbit projections have no matrix corner across a tensor letter.
Source: arXiv:1708.00029, Section 4.1, lines 765--806. -/
theorem orbitProjection_offDiagonal (α : Fin m → ι) (P : Fin m → MatrixAlg D)
    (B : MPSTensor d D)
    (hcorner : ∀ u v, α u ≠ α v → ∀ i, P u * B i * P v = 0)
    (a b : ι) (hab : a ≠ b) (i : Fin d) :
    orbitProjection α P a * B i * orbitProjection α P b = 0 := by
  let Sa : Finset (Fin m) := Finset.univ.filter (fun u => α u = a)
  let Sb : Finset (Fin m) := Finset.univ.filter (fun v => α v = b)
  have hQa : orbitProjection α P a = ∑ u ∈ Sa, P u := by
    simp [orbitProjection, Sa, Finset.sum_filter]
  have hQb : orbitProjection α P b = ∑ v ∈ Sb, P v := by
    simp [orbitProjection, Sb, Finset.sum_filter]
  rw [hQa, hQb, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro u hu
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro v hv
  have hvb : α u = b := (Finset.mem_filter.mp hu).2
  have hva : α v = a := (Finset.mem_filter.mp hv).2
  exact hcorner v u (by rw [hva, hvb]; exact hab) i

/-- A tensor with no corners between distinct orbits commutes with each
orbit projection. Source: arXiv:1708.00029, Section 4.1,
lines 765--806. -/
theorem orbitProjection_commutes [Finite ι]
    (α : Fin m → ι) (P : Fin m → MatrixAlg D)
    (B : MPSTensor d D)
    (hsum : ∑ u : Fin m, P u = 1)
    (hcorner : ∀ u v, α u ≠ α v → ∀ i, P u * B i * P v = 0)
    (a : ι) (i : Fin d) :
    orbitProjection α P a * B i = B i * orbitProjection α P a := by
  have : Fintype ι := Fintype.ofFinite ι
  have hQsum : ∑ b : ι, orbitProjection α P b = 1 := orbitProjection_sum α P hsum
  have hleft : orbitProjection α P a * B i =
      orbitProjection α P a * B i * orbitProjection α P a := by
    calc
      orbitProjection α P a * B i = orbitProjection α P a * B i * 1 := by simp
      _ = ∑ b : ι, orbitProjection α P a * B i * orbitProjection α P b := by
        rw [← hQsum, Matrix.mul_sum]
      _ = orbitProjection α P a * B i * orbitProjection α P a := by
        apply Finset.sum_eq_single a
        · intro b _ hne
          exact orbitProjection_offDiagonal α P B hcorner a b hne.symm i
        · simp
  have hright : B i * orbitProjection α P a =
      orbitProjection α P a * B i * orbitProjection α P a := by
    calc
      B i * orbitProjection α P a = 1 * (B i * orbitProjection α P a) := by simp
      _ = ∑ b : ι, orbitProjection α P b * B i * orbitProjection α P a := by
        rw [← hQsum, Finset.sum_mul]
        simp only [Matrix.mul_assoc]
      _ = orbitProjection α P a * B i * orbitProjection α P a := by
        apply Finset.sum_eq_single a
        · intro b _ hne
          exact orbitProjection_offDiagonal α P B hcorner b a hne i
        · simp
  exact hleft.trans hright.symm
end MPSTensor
