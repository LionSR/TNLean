/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.BlockedOrbitCorners
import TNLean.MPS.Periodic.OrbitProjector

/-!
# Compression of the orbit blocks of a periodic tensor

Blocking a period-`m` tensor by `p` sites divides its cyclic sectors into
`gcd(m,p)` orbits. Summing the projectors in each orbit gives a commuting
projection for the blocked tensor. Compression onto these orthogonal ranges
gives a literal unit-weight direct-sum presentation of the blocked letters.

This is the decomposition part of arXiv:1708.00029, Section 4.1,
lines 765--806. Periodicity and irreducibility of the compressed tensors are
separate claims.
-/

open scoped Matrix BigOperators
namespace MPSTensor

/-- The `p`-blocked tensor of a period-`m` tensor is a unit-weight direct
sum over the `gcd(m,p)` shift orbits, with an explicit isometric embedding
of each compressed orbit block into the original bond space.

Source: arXiv:1708.00029, Section 4.1, lines 765--806. -/
theorem exists_blockTensor_orbit_compression {d D m : ℕ} [NeZero m]
    (A : MPSTensor d D) (hA : IsPeriodic m A) (p : ℕ) :
    ∃ (dim : Fin (Nat.gcd m p) → ℕ)
      (C : (j : Fin (Nat.gcd m p)) → MPSTensor (blockPhysDim d p) (dim j))
      (Q : Fin (Nat.gcd m p) → MatrixAlg D)
      (V : (j : Fin (Nat.gcd m p)) → Matrix (Fin D) (Fin (dim j)) ℂ)
      (α : Fin m → Fin (Nat.gcd m p))
      (P : Fin m → MatrixAlg D),
      (∀ u, IsOrthogonalProjection (P u)) ∧
      (∀ u, P u ≠ 0) ∧
      (∑ u, P u = 1) ∧
      (∀ u v, u ≠ v → P u * P v = 0) ∧
      (∀ u i, P u * A i = A i * P (u + 1)) ∧
      (∀ u, α (u + p • (1 : Fin m)) = α u) ∧
      Function.Surjective α ∧
      (∀ j, Q j = orbitProjection α P j) ∧
      (∀ j, IsOrthogonalProjection (Q j)) ∧
      (∑ j, Q j = 1) ∧
      (∀ j k, j ≠ k → Q j * Q k = 0) ∧
      (∀ j (I : Fin (blockPhysDim d p)), Q j * blockTensor A p I =
        blockTensor A p I * Q j) ∧
      (∀ j, (V j)ᴴ * V j = 1) ∧
      (∀ j, V j * (V j)ᴴ = Q j) ∧
      (∀ j, dim j ≠ 0) ∧
      (∀ j (I : Fin (blockPhysDim d p)),
        V j * C j I * (V j)ᴴ = Q j * blockTensor A p I * Q j) ∧
      (∀ I : Fin (blockPhysDim d p),
        blockTensor A p I = ∑ j, V j * C j I * (V j)ᴴ) ∧
      (∀ j, ∑ I : Fin (blockPhysDim d p), (C j I)ᴴ * C j I = 1) ∧
      SameMPV₂ (blockTensor A p) (toTensorFromBlocks (μ := fun _ => 1) C) := by
  classical
  obtain ⟨ι, α, _k, P, hP, hPne, hPsum, hPorth, hshift,
    hα, _hk, hsurj, _horbit, hcard, hcorner⟩ :=
    exists_blockTensor_offOrbit_corners A hA p
  have hgcd : Nat.gcd m p ≠ 0 :=
    (Nat.gcd_pos_of_pos_left p (NeZero.pos m)).ne'
  have : Finite ι := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hgcd)
  have : Fintype ι := Fintype.ofFinite ι
  let e : ι ≃ Fin (Nat.gcd m p) :=
    Fintype.equivFinOfCardEq (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let α' : Fin m → Fin (Nat.gcd m p) := e ∘ α
  let Q : Fin (Nat.gcd m p) → MatrixAlg D :=
    fun j => orbitProjection α P (e.symm j)
  have hQorbit : ∀ j, Q j = orbitProjection α' P j := by
    intro j
    simp only [Q, α', orbitProjection]
    apply Finset.sum_congr rfl
    intro u _
    split_ifs with h₁ h₂ <;> simp_all [Equiv.eq_symm_apply]
  have hα' : ∀ u, α' (u + p • (1 : Fin m)) = α' u :=
    fun u => congrArg e (hα u)
  have hsurj' : Function.Surjective α' := e.surjective.comp hsurj
  have hQproj : ∀ j, IsOrthogonalProjection (Q j) :=
    fun j => orbitProjection_isOrthogonalProjection α P hP hPorth (e.symm j)
  have hQne : ∀ j, Q j ≠ 0 :=
    fun j => orbitProjection_ne_zero α P hP hPorth hPne hsurj (e.symm j)
  have hQsum : ∑ j : Fin (Nat.gcd m p), Q j = 1 := by
    have h := Fintype.sum_equiv e (orbitProjection α P) Q (fun a => by simp [Q])
    exact h.symm.trans (orbitProjection_sum α P hPsum)
  have hQorth : ∀ j k, j ≠ k → Q j * Q k = 0 :=
    pairwise_mul_zero_of_orthogonalProjection_sum_one Q hQproj hQsum
  let B : MPSTensor (blockPhysDim d p) D := blockTensor A p
  have hcornerB : ∀ u v, α u ≠ α v →
      ∀ I : Fin (blockPhysDim d p), P u * B I * P v = 0 := hcorner
  have hQcomm : ∀ j (I : Fin (blockPhysDim d p)), Q j * B I = B I * Q j :=
    fun j I => orbitProjection_commutes α P B hPsum hcornerB (e.symm j) I
  have hBtp : ∑ I : Fin (blockPhysDim d p), (B I)ᴴ * B I = 1 :=
    leftCanonical_blockTensor A p hA.leftCanonical
  obtain ⟨dim, C, φ, V, hCtp, hMPV, _htrace, _hinter, _hmul, _hstar,
    hletter, hViso, hVrange, hEmbed⟩ :=
    exists_blockDecomp_of_commuting_projections_with_letter_and_isometry
      B Q hQproj hQsum hBtp hQcomm
  have hcornerLetter : ∀ j (I : Fin (blockPhysDim d p)),
      V j * C j I * (V j)ᴴ = Q j * B I * Q j := by
    intro j I
    exact (hEmbed j (C j I)).symm.trans (hletter j I)
  have hdimNe : ∀ j, dim j ≠ 0 := by
    intro j hzero
    have hVzero : V j = 0 := by
      ext x y
      exact Fin.elim0 (by simpa [hzero] using y)
    have hQzero := hVrange j
    rw [hVzero, Matrix.zero_mul] at hQzero
    exact hQne j hQzero.symm
  refine ⟨dim, C, Q, V, α', P, hP, hPne, hPsum, hPorth,
    hshift, hα', hsurj', hQorbit, hQproj, hQsum, hQorth, hQcomm,
    hViso, hVrange, hdimNe, hcornerLetter, ?_, hCtp, hMPV⟩
  intro I
  calc
    B I = (∑ j, Q j) * B I := by rw [hQsum, Matrix.one_mul]
    _ = ∑ j, Q j * B I := by rw [Finset.sum_mul]
    _ = ∑ j, Q j * B I * Q j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hQcomm j I, Matrix.mul_assoc, (hQproj j).2]
    _ = ∑ j, V j * C j I * (V j)ᴴ := by
      apply Finset.sum_congr rfl
      intro j _
      exact (hcornerLetter j I).symm

end MPSTensor
