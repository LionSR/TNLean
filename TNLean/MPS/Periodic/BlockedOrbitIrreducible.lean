/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.BlockedOrbitFixedBasis
import TNLean.MPS.Periodic.CompressedFixedPoint
import TNLean.MPS.Periodic.CompressedFixedLift
import QICLean.Channel.Irreducible.FromSpectral

/-!
# Irreducibility of the blocked orbit sectors

The stationary matrix in each compressed orbit is faithful. The stationary
orbit matrices form a basis of the ambient fixed space, so a stationary
positive matrix in one compressed orbit must be proportional to its faithful
stationary matrix. The fixed-point criterion for irreducible channels then
applies.

Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 765--806.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators

namespace MPSTensor

/-- A reducing compressed sector is irreducible when its stationary matrix
is the only positive stationary matrix up to scalar, as certified by an
ambient orbit-corner basis. Source: arXiv:1708.00029, Lemma
`lem:blocking-arbitrary`, lines 765--806. -/
theorem irreducible_compression_of_orbit_fixed_basis
    {d D r : ℕ} (B : MPSTensor d D)
    (dim : Fin r → ℕ) (C : (j : Fin r) → MPSTensor d (dim j))
    (Q : Fin r → MatrixAlg D)
    (V : (j : Fin r) → Matrix (Fin D) (Fin (dim j)) ℂ)
    (ρ : MatrixAlg D)
    (hQorth : ∀ j k, j ≠ k → Q j * Q k = 0)
    (hQcomm : ∀ j i, Q j * B i = B i * Q j)
    (hViso : ∀ j, (V j)ᴴ * V j = 1)
    (hVrange : ∀ j, V j * (V j)ᴴ = Q j)
    (hdim : ∀ j, dim j ≠ 0)
    (hcorner : ∀ j i, V j * C j i * (V j)ᴴ = Q j * B i * Q j)
    (hTP : ∀ j, ∑ i, (C j i)ᴴ * C j i = 1)
    (hρpd : ρ.PosDef)
    (hρfix : Kraus.map B ρ = ρ)
    (hspan : Submodule.span ℂ (Set.range fun j => Q j * ρ * Q j) =
      Module.End.eigenspace (Kraus.mapLM B) 1)
    (j : Fin r) : Kraus.IsIrreducibleFamily (C j) := by
  let : NeZero (dim j) := ⟨hdim j⟩
  have hC : ∀ i, C j i = (V j)ᴴ * B i * V j :=
    compressed_letter_eq_conj B (C j) (Q j) (V j)
      (hViso j) (hVrange j) (hcorner j)
  have hcomm : ∀ i, Commute (V j * (V j)ᴴ) (B i) := by
    intro i
    rw [hVrange j]
    exact hQcomm j i
  have hfaith := compressed_posDef_fixedPoint B (V j) (hViso j)
    hcomm ρ hρpd hρfix
  have hρjpd : ((V j)ᴴ * ρ * V j).PosDef := hfaith.1
  have hρjfix : Kraus.map (C j) ((V j)ᴴ * ρ * V j) =
      (V j)ᴴ * ρ * V j := by
    rw [funext hC]
    exact hfaith.2
  have hchannel : IsChannel (Kraus.mapLM (C j)) :=
    Kraus.isChannel_mapLM (C j) (hTP j)
  have hunique : ∀ σ : MatrixAlg (dim j), σ.PosSemidef →
      Kraus.mapLM (C j) σ = σ →
      ∃ c : ℂ, σ = c • ((V j)ᴴ * ρ * V j) := by
    intro σ _ hσfix
    have hlift : Kraus.map B (V j * σ * (V j)ᴴ) =
        V j * σ * (V j)ᴴ := by
      rw [compressedTensorMap_lift_of_commute B (C j) (V j)
        (hViso j) hcomm hC σ]
      exact congrArg (fun X => V j * X * (V j)ᴴ) hσfix
    have hmem : V j * σ * (V j)ᴴ ∈
        Submodule.span ℂ (Set.range fun k => Q k * ρ * Q k) := by
      rw [hspan, Module.End.mem_eigenspace_iff]
      simpa only [one_smul, Kraus.mapLM_apply] using hlift
    exact compressed_eq_smul_of_mem_orbit_stationary_span Q
      hQorth j (V j) (hViso j) (hVrange j) ρ σ hmem
  exact Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM (C j)
    (isIrreducibleMap_of_channel_posDef_fixedPoint_unique
      (Kraus.mapLM (C j)) hchannel _ hρjpd hρjfix hunique)

/-- Blocking an irreducible period-`m` tensor by `p>0` produces exactly
`gcd(m,p)` nonzero, trace-preserving, irreducible compressed orbit tensors.
Their unit-weight direct sum has the same matrix product vectors as the
blocked tensor. The precise periods are established separately.
Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 765--806. -/
theorem IsPeriodic.exists_blockTensor_irreducible_orbit_compression
    {d D m : ℕ} [NeZero m] (A : MPSTensor d D)
    (hA : IsPeriodic m A) {p : ℕ} (hp : 0 < p) :
    ∃ (dim : Fin (Nat.gcd m p) → ℕ)
      (C : (j : Fin (Nat.gcd m p)) →
        MPSTensor (blockPhysDim d p) (dim j)),
      (∀ j, dim j ≠ 0) ∧
      (∀ j, Kraus.IsIrreducibleFamily (C j)) ∧
      (∀ j, ∑ I, (C j I)ᴴ * C j I = 1) ∧
      SameMPV₂ (blockTensor A p) (toTensorFromBlocks (μ := fun _ => 1) C) := by
  obtain ⟨dim, C, Q, V, _α, _P, ρ, _hP, _hPne, _hPsum,
    _hPorth, _hshift, _hα, _hsurj, _hQorbit, _hQproj,
    _hQsum, hQorth, hQcomm, hViso, hVrange, hdim,
    hcorner, _hletter, hTP, hMPV, hρpd, hρfix, hspan⟩ :=
    hA.exists_blockTensor_orbit_fixed_basis A hp
  refine ⟨dim, C, hdim, ?_, hTP, hMPV⟩
  intro j
  exact irreducible_compression_of_orbit_fixed_basis
    (blockTensor A p) dim C Q V ρ hQorth hQcomm hViso hVrange
    hdim hcorner hTP hρpd hρfix hspan j

end MPSTensor
