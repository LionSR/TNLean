/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.BlockedOrbitDecomposition
import TNLean.MPS.Periodic.BlockedFixedDimension
import TNLean.MPS.Periodic.OrbitFixedPointBasis
import TNLean.MPS.Core.BlockingTransfer
import QICLean.Channel.Irreducible.Ergodicity

/-!
# Stationary basis for the blocked orbit decomposition

For a positive blocking length, the stationary matrices supported on the
`gcd(m,p)` orbit sectors span the full fixed space of the blocked transfer
map. This is the fixed-space argument needed to show that the compressed
orbit tensors are irreducible.

Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 765--806.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators

namespace MPSTensor

/-- The actual compressed orbit sectors of a periodic tensor support a basis
of stationary matrices for the blocked transfer map.
Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 765--806. -/
theorem IsPeriodic.exists_blockTensor_orbit_fixed_basis
    {d D m : ℕ} [NeZero m] (A : MPSTensor d D)
    (hA : IsPeriodic m A) {p : ℕ} (hp : 0 < p) :
    ∃ (dim : Fin (Nat.gcd m p) → ℕ)
      (C : (j : Fin (Nat.gcd m p)) → MPSTensor (blockPhysDim d p) (dim j))
      (Q : Fin (Nat.gcd m p) → MatrixAlg D)
      (V : (j : Fin (Nat.gcd m p)) → Matrix (Fin D) (Fin (dim j)) ℂ)
      (α : Fin m → Fin (Nat.gcd m p))
      (P : Fin m → MatrixAlg D)
      (ρ : MatrixAlg D),
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
      (∀ j, ∑ I : Fin (blockPhysDim d p), (C j I)ᴴ * C j I = 1) ∧
      SameMPV₂ (blockTensor A p) (toTensorFromBlocks (μ := fun _ => 1) C) ∧
      ρ.PosDef ∧
      Kraus.map (blockTensor A p) ρ = ρ ∧
      Submodule.span ℂ (Set.range fun j => Q j * ρ * Q j) =
        Module.End.eigenspace (Kraus.mapLM (blockTensor A p)) 1 := by
  have : NeZero D := ⟨hA.bondDim_ne_zero⟩
  obtain ⟨dim, C, Q, V, α, P, hP, hPne, hPsum, hPorth,
    hshift, hα, hsurj, hQorbit, hQproj, hQsum, hQorth, hQcomm,
    hViso, hVrange, hdim, hcorner, hletter, hTP, hMPV⟩ :=
    exists_blockTensor_orbit_compression A hA p
  let E := Kraus.mapLM A
  have hIrr : IsIrreducibleMap E :=
    Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hA.irreducible
  have hE : IsChannel E := Kraus.isChannel_mapLM A hA.leftCanonical
  obtain ⟨ρ, _, hρpd, hρfix, _⟩ :=
    hE.exists_unique_density_fixedPoint_of_irreducible E hIrr (NeZero.pos D)
  have hmap : Kraus.mapLM (blockTensor A p) = E ^ p :=
    transferMap_blockTensor A p
  have hpow : ∀ n : ℕ, (E ^ n) ρ = ρ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, ih, hρfix]
  have hρfixB : Kraus.map (blockTensor A p) ρ = ρ := by
    change Kraus.mapLM (blockTensor A p) ρ = ρ
    rw [hmap]
    exact hpow p
  have hfixedDim : Module.finrank ℂ
      (Module.End.eigenspace (Kraus.mapLM (blockTensor A p)) 1) ≤ Nat.gcd m p := by
    rw [hmap]
    exact hA.finrank_blocked_fixed_le_gcd A hp
  have hspan := orbit_stationary_corners_span_fixed (blockTensor A p)
    dim Q V hQproj hQorth
    (fun j I => show Commute (Q j) (blockTensor A p I) from hQcomm j I)
    hViso hVrange hdim ρ hρpd hρfixB hfixedDim
  exact ⟨dim, C, Q, V, α, P, ρ, hP, hPne, hPsum, hPorth,
    hshift, hα, hsurj, hQorbit, hQproj, hQsum, hQorth, hQcomm,
    hViso, hVrange, hdim, hcorner, hletter, hTP, hMPV, hρpd, hρfixB, hspan⟩

end MPSTensor
