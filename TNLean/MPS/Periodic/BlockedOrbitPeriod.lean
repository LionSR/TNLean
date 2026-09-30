/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.BlockedOrbitIrreducible
import TNLean.MPS.Periodic.BlockedOrbitRootSpectrum
import TNLean.MPS.Periodic.BlockedSpectrumOrbitBound
import TNLean.MPS.Periodic.CompressedSpectrumLift

/-!
# Period of the compressed blocked orbit tensors

Blocking a period-`m` tensor by `p>0` produces exactly `gcd(m,p)`
irreducible orbit tensors, each with period `m/gcd(m,p)` and unit weight.
The lower spectrum comes from the surviving cyclic microprojections;
the upper spectrum comes from spectral mapping for the blocked transfer
map and isometric lifting of the compressed transfer maps.

Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 765--806.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators

namespace MPSTensor

/-- A positive real block weight remains positive and real after a
positive blocking power. Source: arXiv:1708.00029, Section 4.1,
lines 765--806. -/
theorem positiveRealWeight_pow (μ : ℂ)
    (hμ : 0 < μ.re ∧ μ.im = 0) (p : ℕ) :
    0 < (μ ^ p).re ∧ (μ ^ p).im = 0 := by
  have heq : μ = (μ.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hμ.2
  rw [heq]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨pow_pos hμ.1 _, trivial⟩

/-- Positive blocking decomposes a periodic tensor into literal isometric
orbit corners, each with period `m / gcd(m,p)`. The cyclic projections and
orbit map are retained so that subsequent phase choices act on these same
corners. Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary` and
Theorem 4.1, lines 765--806. -/
theorem IsPeriodic.exists_blockTensor_periodic_orbit_decomposition
    {d D m : ℕ} [NeZero m] (A : MPSTensor d D)
    (hA : IsPeriodic m A) {p : ℕ} (hp : 0 < p) :
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
      (∀ j I, Q j * blockTensor A p I = blockTensor A p I * Q j) ∧
      (∀ j, (V j)ᴴ * V j = 1) ∧
      (∀ j, V j * (V j)ᴴ = Q j) ∧
      (∀ j, dim j ≠ 0) ∧
      (∀ j I, V j * C j I * (V j)ᴴ =
        Q j * blockTensor A p I * Q j) ∧
      (∀ I, blockTensor A p I = ∑ j, V j * C j I * (V j)ᴴ) ∧
      (∀ j, IsPeriodic (m / Nat.gcd m p) (C j)) ∧
      SameMPV₂ (blockTensor A p) (toTensorFromBlocks (μ := fun _ => 1) C) := by
  obtain ⟨dim, C, Q, V, α, P, ρ, hP, hPne, hPsum,
    hPorth, hshift, hα, hsurj, hQorbit, hQproj,
    hQsum, hQorth, hQcomm, hViso, hVrange, hdim,
    hcorner, hletter, hTP, hMPV, hρpd, hρfix, hspan⟩ :=
    hA.exists_blockTensor_orbit_fixed_basis A hp
  let N := addOrderOf (p : ZMod m)
  have hNpos : 0 < N := addOrderOf_pos (p : ZMod m)
  obtain ⟨s, hs⟩ : ∃ s, N = s + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hNpos)
  have hUpperB := hA.blockTensor_peripheral_pow_orbitLength A hp rfl
  refine ⟨dim, C, Q, V, α, P, hP, hPne, hPsum, hPorth, hshift,
    hα, hsurj, hQorbit, hQproj, hQsum, hQorth, hQcomm, hViso,
    hVrange, hdim, hcorner, hletter, ?_, hMPV⟩
  intro j
  have hIrr : Kraus.IsIrreducibleFamily (C j) :=
    irreducible_compression_of_orbit_fixed_basis
      (blockTensor A p) dim C Q V ρ hQorth hQcomm hViso hVrange
      hdim hcorner hTP hρpd hρfix hspan j
  have hC : ∀ I, C j I = (V j)ᴴ * blockTensor A p I * V j :=
    compressed_letter_eq_conj (blockTensor A p) (C j) (Q j)
      (V j) (hViso j) (hVrange j) (hcorner j)
  have hcomm : ∀ I, Commute (V j * (V j)ᴴ) (blockTensor A p I) := by
    intro I
    rw [hVrange j]
    exact hQcomm j I
  have hUpper : peripheralEigenvalues (Kraus.mapLM (C j)) ⊆
      {ζ : ℂ | ζ ^ N = 1} := by
    intro ζ hζ
    have hEigB := compressedTensorMap_hasEigenvalue_lift
      (blockTensor A p) (C j) (V j) (hViso j) hcomm hC ζ hζ.1
    exact hUpperB ⟨hEigB, hζ.2⟩
  have hLower : {ζ : ℂ | ζ ^ N = 1} ⊆
      peripheralEigenvalues (Kraus.mapLM (C j)) := by
    obtain ⟨u, hu⟩ := hsurj j
    have hVrange' : V j * (V j)ᴴ = orbitProjection α P (α u) := by
      rw [hu, ← hQorbit j]
      exact hVrange j
    intro ζ hζ
    change ζ ^ N = 1 at hζ
    have hroot : ζ ^ (s + 1) = 1 := by simpa only [← hs] using hζ
    exact compressed_blockTensor_roots_subset_peripheral A (C j) α P
      hP hPne hPorth hα hA.leftCanonical hshift u hs (V j)
      hVrange' hC hroot
  have hper : peripheralEigenvalues (Kraus.mapLM (C j)) =
      {ζ : ℂ | ζ ^ N = 1} := Set.Subset.antisymm hUpper hLower
  have hPeriodic : IsPeriodic N (C j) :=
    ⟨hIrr, hTP j, hNpos, hper⟩
  simpa only [N, phase_residue_orbit_length] using hPeriodic

/-- Arbitrary positive blocking of a periodic tensor gives precisely its
shift-orbit sectors, each with the translation-orbit period and unit
coefficient. Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 765--806. -/
theorem IsPeriodic.exists_blockTensor_periodic_orbit_compression
    {d D m : ℕ} [NeZero m] (A : MPSTensor d D)
    (hA : IsPeriodic m A) {p : ℕ} (hp : 0 < p) :
    ∃ (dim : Fin (Nat.gcd m p) → ℕ)
      (C : (j : Fin (Nat.gcd m p)) →
        MPSTensor (blockPhysDim d p) (dim j)),
      (∀ j, dim j ≠ 0) ∧
      (∀ j, IsPeriodic (m / Nat.gcd m p) (C j)) ∧
      SameMPV₂ (blockTensor A p)
        (toTensorFromBlocks (μ := fun _ => 1) C) := by
  obtain ⟨dim, C, Q, V, α, P, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hdim, _, _, hPeriodic, hSame⟩ := hA.exists_blockTensor_periodic_orbit_decomposition A hp
  exact ⟨dim, C, hdim, hPeriodic, hSame⟩

/-- The positive blocking of one periodic block has an irreducible-form
representation with unit weights, with no additional canonicalization
hypothesis. Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 765--806. -/
noncomputable def IsPeriodic.blockTensor_isIrreducibleForm
    {d D m : ℕ} [NeZero m] (A : MPSTensor d D)
    (hA : IsPeriodic m A) {p : ℕ} (hp : 0 < p) :
    IsIrreducibleForm (blockTensor A p) := by
  classical
  refine Classical.choice ?_
  obtain ⟨dim, C, _hdim, hPeriodic, hSame⟩ :=
    hA.exists_blockTensor_periodic_orbit_compression A hp
  exact ⟨
    { r := Nat.gcd m p
      dim := dim
      blocks := C
      μ := fun _ => 1
      period := fun _ => m / Nat.gcd m p
      periodic := hPeriodic
      weight_pos := by intro j; simp
      sameMPV := hSame }⟩

end MPSTensor
