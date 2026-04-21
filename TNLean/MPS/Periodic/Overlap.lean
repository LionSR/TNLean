/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Defs
import TNLean.MPS.Overlap.CastDecay
import TNLean.MPS.FundamentalTheorem.Basic
import TNLean.MPS.FundamentalTheorem.Full
import TNLean.MPS.Chain.OneSidedInverse
import TNLean.MPS.Core.Blocking
import TNLean.MPS.CanonicalForm.CyclicSectors
import TNLean.MPS.CanonicalForm.Assembly
import TNLean.MPS.CanonicalForm.SectorIrreducibility
import TNLean.MPS.Irreducible.Adjoint
import TNLean.MPS.SharedInfra.KrausAdjointSetup
import TNLean.Spectral.SpectralGapNT
import TNLean.Channel.Irreducible.PerronFrobenius
import TNLean.Channel.Schwarz.MultiplicativeDomainFull

import TNLean.Algebra.GramMatrixLI
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Periodic overlap dichotomy (Proposition 3.3, arXiv:1708.00029)

This file formalizes Proposition 3.3 of De las Cuevas–Cirac–Schuch–Perez-Garcia
(arXiv:1708.00029) and its proof from Appendix A: the "equal-or-orthogonal"
dichotomy for periodic MPS tensors.

## Main results

### Self-overlap
* `periodicSelfOverlap_tendsto` — for a periodic tensor `A` with period `m`,
  `⟨V_{mk}(A)|V_{mk}(A)⟩ → m` as `k → ∞`.

### Cross-overlap dichotomy
* `periodicOverlap_tendsto_zero_of_ne_period` — (Case 1) different periods
  imply orthogonality.
* `periodicOverlap_tendsto_zero_of_no_sector_match` — (Case 2) same period,
  same bond dimension, but no sector match implies orthogonality.
* `periodicOverlap_tendsto_zero_of_ne_dim` — different bond dimensions
  imply orthogonality (cross-transfer spectral gap).
* `periodicOverlap_gaugeEquiv_of_sector_match` — (Case 3) same period with
  a sector match forces gauge-phase equivalence `A^i = e^{iξ} U B^i U†`.

### Combined dichotomy
* `periodicOverlapDichotomy` — the full Proposition 3.3 statement.

## Proof structure (Appendix A)

**Case 1** (different periods): Block by `lcm(m_a, m_b)`. The blocked sectors
are non-repeated normal tensors by Lemma 2.4. If any sector pair matched,
translation invariance would force two non-repeated sectors of `B` to generate
equal states — contradiction.

**Case 2** (same period, no match): Block by `m`. All cross-sector overlaps
decay by the normal-tensor overlap dichotomy. The finite sum decays.

**Case 3** (same period, sector match): The hard case. From one matching pair,
propagate by translation to all sectors, define sector-restricted tensors,
establish blocked proportionality, use injectivity contraction via the
decomposition map to extract per-site proportionality, absorb phases, and
assemble the global gauge unitary.

## Status

The main theorems in this file are currently stated with `sorry` proofs.
The same-period sector statements (Case 2 and Case 3 helpers) are formulated
using **compressed sector tensors** on corner bond spaces, matching the output
of `exists_cyclic_sector_decomp_after_blocking_of_isPeriodic` and the cyclic-sector
decomposition results in `CanonicalForm/CyclicSectors.lean`.

This module records the intended mathematical statements and should not yet be
relied on as a completed formalization of Proposition 3.3.

## References

* De las Cuevas, Cirac, Schuch, Perez-Garcia, *Irreducible forms of Matrix
  Product States: Theory and Applications*, arXiv:1708.00029, Proposition 3.3
  and Appendix A.
-/

open scoped Matrix BigOperators ComplexOrder InnerProductSpace
open Filter Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- The blocks form a **cyclic sector decomposition** of `blockTensor A m`, witnessed by
orthogonal projections `P` that are fixed by the blocked adjoint transfer map and
therefore commute with every blocked letter at the **same** index:
`P k * (blockTensor A m) i = (blockTensor A m) i * P k`.

The projections arise from the peripheral spectrum of the original (unblocked)
transfer map, where they satisfy the *shifted* relation `E†(P (k+1)) = P k`.
After blocking by the period `m`, the blocked transfer map `E^m` fixes every
`P k`, so `commutes_letters_of_adjoint_fixed_projection` gives same-index
commutation with the blocked letters.

The per-sector trace relation ties each compressed block `blocks k` back to the
projection `P k` via `mpv (blocks k) σ = tr(P k · evalWord(blockTensor A m)(σ))`,
which is the defining property of `exists_compressedTensor_of_supported_projection`.

Also carries per-sector compression `∗`-algebra isomorphisms
`φ k : M_{dim k}(ℂ) ≃ₗ[ℂ] cornerSubmodule (P k)` that are multiplicative and
`∗`-preserving, together with the intertwining identity relating the compressed
adjoint transfer map to the sector adjoint transfer map on the corner of `P k`.
Exposing `φ k` as a `LinearEquiv` with mul/star compatibility lets downstream
consumers (see `compressedTensor_adjointTransferMap_cornerBridge`) transport
corner-level irreducibility / primitivity results back to the compressed matrix
algebra via conjugation.  The underlying linear map is an isometry for the
canonical inner products; that property is witnessed separately where needed. -/
def IsCyclicSectorDecomp [NeZero D] [NeZero m] (A : MPSTensor d D)
    {dim : Fin m → ℕ}
    (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k)) : Prop :=
  ∃ (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (φ : (k : Fin m) →
      Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k)),
    (∀ k, IsOrthogonalProjection (P k)) ∧
    (∑ k : Fin m, P k = 1) ∧
    (∀ k, transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k) ∧
    (∀ k (i : Fin (blockPhysDim d m)),
      P k * (blockTensor A m) i = (blockTensor A m) i * P k) ∧
    (∀ k (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)),
      mpv (blocks k) σ = (P k * evalWord (blockTensor A m) (List.ofFn σ)).trace) ∧
    (∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k (transferMap (d := blockPhysDim d m) (D := dim k)
          (fun i => (blocks k i)ᴴ) X)).1 =
        transferMap (d := blockPhysDim d m) (D := D)
          (fun i => (P k * blockTensor A m i)ᴴ) ((φ k X).1)) ∧
    (∀ k (X Y : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k (X * Y)).1 = (φ k X).1 * (φ k Y).1) ∧
    (∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k Xᴴ).1 = ((φ k X).1)ᴴ)

private theorem exists_cyclic_sector_decomp_after_blocking_of_isPeriodic
    [NeZero D] (A : MPSTensor d D) {m : ℕ} [NeZero m]
    (hP : IsPeriodic m A) :
    ∃ (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k)),
      (∀ k, ∑ i : Fin (blockPhysDim d m), (blocks k i)ᴴ * blocks k i = 1) ∧
      SameMPV₂ (blockTensor A m) (toTensorFromBlocks (μ := fun _ => 1) blocks) ∧
      IsCyclicSectorDecomp A blocks ∧
      (∀ k, dim k ≠ 0) := by
  obtain ⟨K, h_unitalK, hIrrK, ρ, hρ_pd, h_adjfix, rfl⟩ :=
    conjTranspose_kraus_setup A hP.leftCanonical hP.irreducible
  obtain ⟨ω, hωprim⟩ := hP.primitiveRoot
  have hM : (1 : Matrix (Fin D) (Fin D) ℂ).PosDef := by
    classical
    simpa using (Matrix.PosDef.one (n := Fin D) (R := ℂ))
  letI : NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixNormedAddCommGroup (n := Fin D) (𝕜 := ℂ) 1 hM
  letI : SeminormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixSeminormedAddCommGroup (n := Fin D) (𝕜 := ℂ) 1 hM.posSemidef
  letI : InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixInnerProductSpace (n := Fin D) (𝕜 := ℂ) 1 hM.posSemidef
  have hAdj :
      transferMap (d := d) (D := D) (fun i => (A i)ᴴ) =
        (transferMap (d := d) (D := D) A).adjoint := by
    simpa using transferMap_conjTranspose_eq_adjoint (d := d) (D := D) (A := A)
  have hperiph_roots :
      peripheralEigenvalues (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) =
        {μ : ℂ | μ ^ m = 1} := by
    ext μ
    constructor
    · intro hμ
      have hEigAdj :
          Module.End.HasEigenvalue ((transferMap (d := d) (D := D) A).adjoint) μ := by
        simpa [hAdj] using hμ.1
      have hEig :
          Module.End.HasEigenvalue (transferMap (d := d) (D := D) A) (star μ) :=
        (Module.End.hasEigenvalue_adjoint_iff
          (E := transferMap (d := d) (D := D) A) (μ := star μ)).2 <| by
            simpa [star_star] using hEigAdj
      have hNorm : ‖star μ‖ = 1 := by
        simpa [norm_star] using hμ.2
      have hStarMem :
          star μ ∈ peripheralEigenvalues (transferMap (d := d) (D := D) A) :=
        ⟨hEig, hNorm⟩
      have hpowStar : (star μ) ^ m = 1 := by
        simpa [hP.peripheral_eq] using hStarMem
      have hpow : μ ^ m = 1 := by
        have := congrArg star hpowStar
        simpa using this
      exact hpow
    · intro hμ
      have hpowStar : (star μ) ^ m = 1 := by
        have := congrArg star hμ
        simpa using this
      have hStarMem :
          star μ ∈ peripheralEigenvalues (transferMap (d := d) (D := D) A) := by
        simpa [hP.peripheral_eq] using hpowStar
      have hEigAdj :
          Module.End.HasEigenvalue ((transferMap (d := d) (D := D) A).adjoint) μ := by
          simpa [star_star] using
            (Module.End.hasEigenvalue_adjoint_iff
              (E := transferMap (d := d) (D := D) A) (μ := star μ)).1 hStarMem.1
      have hNorm : ‖μ‖ = 1 := by
        simpa [norm_star] using hStarMem.2
      exact ⟨by simpa [hAdj] using hEigAdj, hNorm⟩
  have hperiph_range :
      peripheralEigenvalues (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) =
        Set.range (fun j : Fin m => ω ^ (j : ℕ)) := by
    ext μ
    constructor
    · intro hμ
      have hpow : μ ^ m = 1 := by
        simpa [hperiph_roots] using hμ
      obtain ⟨i, hi, hωi⟩ := hωprim.eq_pow_of_pow_eq_one hpow
      exact ⟨⟨i, hi⟩, by simpa using hωi⟩
    · rintro ⟨j, rfl⟩
      have hpow : (ω ^ (j : ℕ)) ^ m = 1 := by
        calc
          (ω ^ (j : ℕ)) ^ m = ω ^ ((j : ℕ) * m) := by rw [pow_mul]
          _ = ω ^ (m * (j : ℕ)) := by rw [Nat.mul_comm]
          _ = (ω ^ m) ^ (j : ℕ) := by rw [pow_mul]
          _ = 1 := by simp [hωprim.pow_eq_one]
      simpa [hperiph_roots] using hpow
  obtain ⟨dim, blocks, P, φ, hLC, hMPV, hPproj, hPsum, hCyclic, hComm, hTraceNondeg⟩ :=
    exists_cyclic_sector_decomp_after_blocking
      A hP.leftCanonical hP.irreducible ρ hρ_pd h_adjfix hIrrK hωprim hperiph_range
  obtain ⟨hTrace, hIntertwine, hMul, hStar, hNondeg⟩ := hTraceNondeg
  exact ⟨dim, blocks, hLC, hMPV,
    ⟨P, φ, hPproj, hPsum, hCyclic, hComm, hTrace, hIntertwine, hMul, hStar⟩, hNondeg⟩


private lemma hLift_cyclicDecomp_mps_of_fixUpgrade_missingBridge
    [NeZero D] (A : MPSTensor d D) {m : ℕ} [NeZero m]
    (hP : IsPeriodic m A)
    {P : Fin m → MatrixAlg D}
    (hPproj : ∀ k, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hCyclic :
      ∀ k, transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k) :
    ∀ k : Fin m, ∀ Q : MatrixAlg D,
      IsOrthogonalProjection Q →
      Q * P k = Q →
      P k * Q = Q →
      PreservesCorner Q ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) →
      ∃ R : MatrixAlg D,
        IsOrthogonalProjection R ∧
        PreservesCorner R (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ∧
        (Q = 0 ↔ R = 0) ∧
        (Q = P k ↔ R = 1) := by
  sorry

private lemma cyclic_projection_ne_zero_of_sum_one
    {m D : ℕ} [NeZero m] [NeZero D]
    {T : MatrixEnd D} {P : Fin m → MatrixAlg D}
    (hPsum : ∑ k : Fin m, P k = 1)
    (hCyclic : ∀ k, T (P (k + 1)) = P k) :
    ∀ k, P k ≠ 0 := by
  by_contra! hzero
  obtain ⟨k₀, hk₀⟩ := hzero
  have hback : ∀ j : Fin m, P (j + 1) = 0 → P j = 0 := by
    intro j hj
    rw [← hCyclic j, hj, map_zero]
  have hall : ∀ j : Fin m, P j = 0 := by
    suffices hs : ∀ n : ℕ, n < m → ∀ j : Fin m,
        (k₀ - j).val = n → P j = 0 by
      intro j
      exact hs _ (k₀ - j).isLt j rfl
    intro n
    induction n with
    | zero =>
        intro _ j hj
        have : k₀ - j = 0 := by
          ext
          simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.val_eq_zero_iff] at hj ⊢
          exact hj
        have : k₀ = j := sub_eq_zero.mp this
        subst this
        exact hk₀
    | succ n ih =>
        intro hd j hj
        apply hback j
        apply ih (by omega) (j + 1)
        have h_eq : k₀ - (j + 1) = (k₀ - j) - 1 := by abel
        rw [h_eq, Fin.val_sub_one_of_ne_zero (by intro h; simp [h] at hj)]
        omega
  exact absurd
    (show (∑ k : Fin m, P k) = 0 from Finset.sum_eq_zero (fun k _ => hall k))
    (by rw [hPsum]; exact one_ne_zero)

/-- Missing compressed-sector bridge.

This is the precise remaining interface needed by
`primitive_and_irreducible_sectorBlocks_of_cyclicDecomp`: the compressed sector
tensor produced from a cyclic projection must have adjoint transfer map
conjugate to the corner restriction of `(E_A†)^m`. Once that identification is
available, corner primitivity and corner irreducibility give the two conclusions
below, and the target lemma only has to convert from the adjoint map back to the
ordinary transfer map/tensor statement. -/
private lemma cornerRestriction_primitive_and_irreducible_of_cyclicDecomp
    [NeZero D] (A : MPSTensor d D) {m : ℕ} [NeZero m]
    (hP : IsPeriodic m A)
    {dim : Fin m → ℕ}
    (blocks :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (_hBlocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocks k i)ᴴ * blocks k i = 1)
    (_hBlocks_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocks))
    {P : Fin m → MatrixAlg D}
    (hPproj : ∀ k, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hCyclic :
      ∀ k, transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (_hComm :
      ∀ k (i : Fin (blockPhysDim d m)),
        P k * (blockTensor A m) i = (blockTensor A m) i * P k)
    (_hTrace :
      ∀ k (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)),
        mpv (blocks k) σ = (P k * evalWord (blockTensor A m) (List.ofFn σ)).trace)
    (u : Fin m) (_hNonzero : dim u ≠ 0) :
    ∃ hInv :
        PreservesCorner (P u)
          ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m),
      _root_.IsPrimitive
        (cornerRestriction (P u)
          ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) hInv) ∧
      IsIrreducibleOnCorner (P u)
        ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) := by
  let T : MatrixEnd D := transferMap (d := d) (D := D) (fun i => (A i)ᴴ)
  let K : Fin d → MatrixAlg D := fun i => (A i)ᴴ
  have hUnital : KadisonSchwarz.IsUnitalKraus (d := d) (D := D) K := by
    simpa [KadisonSchwarz.IsUnitalKraus, K] using hP.leftCanonical
  have hK_apply : ∀ X : MatrixAlg D, T X = KadisonSchwarz.krausMap K X := by
    intro X
    simp [T, K, MPSTensor.transferMap_apply, KadisonSchwarz.krausMap]
  have hMulDomain : ∀ k : Fin m, P k ∈ KadisonSchwarz.multiplicativeDomain K := by
    intro k
    have hPk_star : (P k)ᴴ = P k := (hPproj k).1.eq
    have hTPk_eq : T (P k) = P (k - 1) := by
      change transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) = P (k - 1)
      simpa [show k - 1 + 1 = k by abel] using hCyclic (k - 1)
    have hTPk_proj : IsOrthogonalProjection (T (P k)) := by
      simpa [hTPk_eq] using hPproj (k - 1)
    have hRight :
        KadisonSchwarz.krausMap K (P k * (P k)ᴴ) =
          KadisonSchwarz.krausMap K (P k) * (KadisonSchwarz.krausMap K (P k))ᴴ := by
      calc
        KadisonSchwarz.krausMap K (P k * (P k)ᴴ)
            = T (P k * (P k)ᴴ) := by rw [hK_apply]
        _ = T (P k) := by rw [hPk_star, (hPproj k).2]
        _ = T (P k) * (T (P k))ᴴ := by
              rw [hTPk_proj.1.eq, hTPk_proj.2]
        _ = KadisonSchwarz.krausMap K (P k) *
              (KadisonSchwarz.krausMap K (P k))ᴴ := by rw [hK_apply]
    have hLeft :
        KadisonSchwarz.krausMap K ((P k)ᴴ * P k) =
          (KadisonSchwarz.krausMap K (P k))ᴴ * KadisonSchwarz.krausMap K (P k) := by
      calc
        KadisonSchwarz.krausMap K ((P k)ᴴ * P k)
            = T ((P k)ᴴ * P k) := by rw [hK_apply]
        _ = T (P k) := by rw [hPk_star, (hPproj k).2]
        _ = (T (P k))ᴴ * T (P k) := by
              rw [hTPk_proj.1.eq, hTPk_proj.2]
        _ = (KadisonSchwarz.krausMap K (P k))ᴴ *
              KadisonSchwarz.krausMap K (P k) := by rw [hK_apply]
    exact ⟨
      (KadisonSchwarz.mem_rightMultiplicativeDomain_iff K hUnital (P k)).2 hRight,
      (KadisonSchwarz.mem_leftMultiplicativeDomain_iff K hUnital (P k)).2 hLeft⟩
  have hMulLeft : ∀ k : Fin m, ∀ X : MatrixAlg D, T (P k * X) = T (P k) * T X := by
    intro k X
    simpa [T, K, MPSTensor.transferMap_apply, KadisonSchwarz.krausMap] using
      KadisonSchwarz.krausMap_mul_right_of_mem_multiplicativeDomain
        (K := K) (hMulDomain k) X
  have hMulRight : ∀ k : Fin m, ∀ X : MatrixAlg D, T (X * P k) = T X * T (P k) := by
    intro k X
    simpa [T, K, MPSTensor.transferMap_apply, KadisonSchwarz.krausMap] using
      KadisonSchwarz.krausMap_mul_left_of_mem_multiplicativeDomain
        (K := K) (hMulDomain k) X
  obtain ⟨ω, hωprim⟩ := hP.primitiveRoot
  have hM : (1 : MatrixAlg D).PosDef := by
    classical
    simpa using (Matrix.PosDef.one (n := Fin D) (R := ℂ))
  letI : NormedAddCommGroup (MatrixAlg D) :=
    Matrix.toMatrixNormedAddCommGroup (n := Fin D) (𝕜 := ℂ) 1 hM
  letI : SeminormedAddCommGroup (MatrixAlg D) :=
    Matrix.toMatrixSeminormedAddCommGroup (n := Fin D) (𝕜 := ℂ) 1 hM.posSemidef
  letI : InnerProductSpace ℂ (MatrixAlg D) :=
    Matrix.toMatrixInnerProductSpace (n := Fin D) (𝕜 := ℂ) 1 hM.posSemidef
  have hAdj :
      T = (transferMap (d := d) (D := D) A).adjoint := by
    simpa [T] using transferMap_conjTranspose_eq_adjoint (d := d) (D := D) (A := A)
  have hperiph_roots : peripheralEigenvalues T = {μ : ℂ | μ ^ m = 1} := by
    ext μ
    constructor
    · intro hμ
      have hEigAdj :
          Module.End.HasEigenvalue ((transferMap (d := d) (D := D) A).adjoint) μ := by
        simpa [hAdj] using hμ.1
      have hEig :
          Module.End.HasEigenvalue (transferMap (d := d) (D := D) A) (star μ) :=
        (Module.End.hasEigenvalue_adjoint_iff
          (E := transferMap (d := d) (D := D) A) (μ := star μ)).2 <| by
            simpa [star_star] using hEigAdj
      have hNorm : ‖star μ‖ = 1 := by
        simpa [norm_star] using hμ.2
      have hStarMem :
          star μ ∈ peripheralEigenvalues (transferMap (d := d) (D := D) A) :=
        ⟨hEig, hNorm⟩
      have hpowStar : (star μ) ^ m = 1 := by
        simpa [hP.peripheral_eq] using hStarMem
      have hpow : μ ^ m = 1 := by
        have := congrArg star hpowStar
        simpa using this
      exact hpow
    · intro hμ
      have hpowStar : (star μ) ^ m = 1 := by
        have := congrArg star hμ
        simpa using this
      have hStarMem :
          star μ ∈ peripheralEigenvalues (transferMap (d := d) (D := D) A) := by
        simpa [hP.peripheral_eq] using hpowStar
      have hEigAdj :
          Module.End.HasEigenvalue ((transferMap (d := d) (D := D) A).adjoint) μ := by
        simpa [star_star] using
          (Module.End.hasEigenvalue_adjoint_iff
            (E := transferMap (d := d) (D := D) A) (μ := star μ)).1 hStarMem.1
      have hNorm : ‖μ‖ = 1 := by
        simpa [norm_star] using hStarMem.2
      exact ⟨by simpa [hAdj] using hEigAdj, hNorm⟩
  have hperiph_range : peripheralEigenvalues T = Set.range (fun j : Fin m => ω ^ (j : ℕ)) := by
    ext μ
    constructor
    · intro hμ
      have hpow : μ ^ m = 1 := by
        simpa [hperiph_roots] using hμ
      obtain ⟨i, hi, hωi⟩ := hωprim.eq_pow_of_pow_eq_one hpow
      exact ⟨⟨i, hi⟩, by simpa using hωi⟩
    · rintro ⟨j, rfl⟩
      have hpow : (ω ^ (j : ℕ)) ^ m = 1 := by
        calc
          (ω ^ (j : ℕ)) ^ m = ω ^ ((j : ℕ) * m) := by rw [pow_mul]
          _ = ω ^ (m * (j : ℕ)) := by rw [Nat.mul_comm]
          _ = (ω ^ m) ^ (j : ℕ) := by rw [pow_mul]
          _ = 1 := by simp [hωprim.pow_eq_one]
      simpa [hperiph_roots] using hpow
  have hPne : ∀ k, P k ≠ 0 :=
    cyclic_projection_ne_zero_of_sum_one (T := T) hPsum (by simpa [T] using hCyclic)
  let hInv : PreservesCorner (P u) (T ^ m) :=
    preserves_corner_pow_of_cyclic_decomp (T := T) P hPproj hPsum
      (by simpa [T] using hCyclic) hMulLeft hMulRight u
  have hCornerPrim :
      _root_.IsPrimitive (cornerRestriction (P u) (T ^ m) hInv) :=
    isPrimitive_restriction_of_cyclic_decomp (T := T)
      hωprim hperiph_range P hPproj hPsum (by simpa [T] using hCyclic)
      hMulLeft hMulRight hPne u
  have hIrr : IsIrreducibleMap T := by
    simpa [T] using
      isIrreducibleCP_transferMap_conjTranspose_of_isIrreducibleTensor
        (A := A) hP.irreducible
  have hLift :=
    hLift_cyclicDecomp_mps_of_fixUpgrade_missingBridge
      A hP hPproj hPsum hCyclic
  have hCornerIrr : IsIrreducibleOnCorner (P u) (T ^ m) :=
    isIrreducible_restriction_of_cyclic_decomp (T := T)
      hIrr P hPproj hPsum (by simpa [T] using hCyclic) (by simpa [T] using hLift) u
  exact ⟨hInv, by simpa [T] using hCornerPrim, by simpa [T] using hCornerIrr⟩

/-- **Compression-transfer bridge.**

Given a `∗`-algebra compression equivalence `φ : M_n(ℂ) ≃ₗ[ℂ] cornerSubmodule P`
intertwining the compressed adjoint transfer map (of `C`) with the
`P·B`-adjoint transfer map on the corner (`hIntertwine`), and preserving both
multiplication (`hMul`) and the adjoint (`hStar`), primitivity and
irreducibility of the corner restriction of the ambient `T = transferMap Bᴴ`
transport to primitivity and irreducibility of `transferMap Cᴴ`.

The proof uses `hMul` / `hStar` to lift orthogonal projections on
`M_n(ℂ)` to corner projections `Q = (φ Q').1 ≤ P`, transports
`PreservesCorner` across `φ` via the intertwining identity, and applies
`IsPrimitive.conj_iff_cross` to move primitivity across the cross-space
conjugation `cornerRestriction P T = φ.conj (transferMap Cᴴ)`.
-/
private lemma compressedTensor_adjointTransferMap_cornerBridge
    {r D n : ℕ} [NeZero n]
    (B : MPSTensor r D) (C : MPSTensor r n) (P : MatrixAlg D)
    (T : MatrixEnd D)
    (φ : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] cornerSubmodule P)
    (hT :
      transferMap (d := r) (D := D) (fun i => (B i)ᴴ) = T)
    (hPproj : IsOrthogonalProjection P)
    (hIntertwine : ∀ X : Matrix (Fin n) (Fin n) ℂ,
      (φ (transferMap (d := r) (D := n) (fun i => (C i)ᴴ) X)).1 =
        transferMap (d := r) (D := D) (fun i => (P * B i)ᴴ) ((φ X).1))
    (hMul : ∀ X Y : Matrix (Fin n) (Fin n) ℂ,
      (φ (X * Y)).1 = (φ X).1 * (φ Y).1)
    (hStar : ∀ X : Matrix (Fin n) (Fin n) ℂ,
      (φ Xᴴ).1 = ((φ X).1)ᴴ)
    (hInv : PreservesCorner P T)
    (hCornerPrim :
      _root_.IsPrimitive (cornerRestriction P T hInv))
    (hCornerIrr : IsIrreducibleOnCorner P T) :
    _root_.IsPrimitive
      (transferMap (d := r) (D := n) (fun i => (C i)ᴴ)) ∧
      IsIrreducibleMap
        (transferMap (d := r) (D := n) (fun i => (C i)ᴴ)) := by
  classical
  set F_C : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    transferMap (d := r) (D := n) (fun i => (C i)ᴴ) with hF_C_def
  have hPherm : Pᴴ = P := hPproj.1.eq
  -- On the corner, the ambient `T` and the `P*B`-adjoint transfer map agree.
  have hTeq :
      ∀ Y : MatrixAlg D, P * Y * P = Y →
        transferMap (d := r) (D := D) (fun i => (P * B i)ᴴ) Y = T Y := by
    intro Y hY
    have hstep :
        transferMap (d := r) (D := D) (fun i => (P * B i)ᴴ) Y =
          transferMap (d := r) (D := D) (fun i => (B i)ᴴ) Y := by
      simp only [transferMap_apply]
      refine Finset.sum_congr rfl ?_
      intro i _
      have hPBi : ((P * B i)ᴴ) = (B i)ᴴ * P := by
        rw [Matrix.conjTranspose_mul, hPherm]
      simp only [Matrix.conjTranspose_conjTranspose]
      rw [hPBi]
      calc
        (B i)ᴴ * P * Y * (P * B i)
            = (B i)ᴴ * (P * Y * P) * B i := by
              simp [Matrix.mul_assoc]
        _ = (B i)ᴴ * Y * B i := by rw [hY]
    rw [hstep, hT]
  -- `cornerRestriction P T hInv = φ.conj F_C`.
  have hConj :
      cornerRestriction P T hInv = φ.conj F_C := by
    refine LinearMap.ext ?_
    intro Y
    refine Subtype.ext ?_
    change T Y.1 = (φ.conj F_C Y).1
    rw [LinearEquiv.conj_apply_apply]
    have hkey := hIntertwine (φ.symm Y)
    have hφsy : (φ (φ.symm Y)).1 = Y.1 :=
      congrArg Subtype.val (LinearEquiv.apply_symm_apply φ Y)
    rw [hφsy] at hkey
    rw [hkey]
    exact (hTeq Y.1 Y.2).symm
  -- Primitivity: transport from the corner via cross-space conjugation.
  have hPrim_F_C : _root_.IsPrimitive F_C :=
    (IsPrimitive.conj_iff_cross (e := φ) (f := F_C)).mp (hConj ▸ hCornerPrim)
  -- Irreducibility: map orthogonal projections `Q'` in `M_n(ℂ)` to corner projections.
  -- `(φ 1).1 = P` since `(φ 1).1` is the identity of `cornerSubmodule P`.
  have hφ1_eq_P : (φ 1).1 = P := by
    have hPcorn : P * P * P = P := by rw [hPproj.2, hPproj.2]
    set Yinv : Matrix (Fin n) (Fin n) ℂ := φ.symm ⟨P, hPcorn⟩
    have hφYinv : (φ Yinv).1 = P :=
      congrArg Subtype.val (LinearEquiv.apply_symm_apply φ ⟨P, hPcorn⟩)
    have hPleft : (φ 1).1 * P = P := by
      have hmul := hMul 1 Yinv
      rw [one_mul, hφYinv] at hmul
      exact hmul.symm
    calc
      (φ 1).1 = P * (φ 1).1 * P := ((φ 1).2).symm
      _ = P * ((φ 1).1 * P) := by simp [Matrix.mul_assoc]
      _ = P * P := by rw [hPleft]
      _ = P := hPproj.2
  have hIrr : IsIrreducibleMap F_C := by
    intro Q' hQ'proj hQ'preserves
    set Q : MatrixAlg D := (φ Q').1 with hQ_def
    have hQ_corner : P * Q * P = Q := (φ Q').2
    have hQherm : Qᴴ = Q := by
      have hstar := hStar Q'
      rw [hQ'proj.1.eq] at hstar
      exact hstar.symm
    have hQidem : Q * Q = Q := by
      have h1 := hMul Q' Q'
      rw [hQ'proj.2] at h1
      exact h1.symm
    have hQP : Q * P = Q := by
      calc Q * P = P * Q * P * P := by rw [hQ_corner]
        _ = P * Q * (P * P) := by simp [Matrix.mul_assoc]
        _ = P * Q * P := by rw [hPproj.2]
        _ = Q := hQ_corner
    have hPQ : P * Q = Q := by
      calc P * Q = P * (P * Q * P) := by rw [hQ_corner]
        _ = (P * P) * Q * P := by simp [Matrix.mul_assoc]
        _ = P * Q * P := by rw [hPproj.2]
        _ = Q := hQ_corner
    have hQproj : IsOrthogonalProjection Q := ⟨hQherm, hQidem⟩
    -- PreservesCorner Q T: use `hIntertwine`, `hMul`, and Q'-invariance of F_C.
    have hQinv : PreservesCorner Q T := by
      intro Y
      set W : MatrixAlg D := P * Y * P with hW_def
      have hW_corner : P * W * P = W := by
        change P * (P * Y * P) * P = P * Y * P
        calc
          P * (P * Y * P) * P = (P * P) * Y * (P * P) := by simp [Matrix.mul_assoc]
          _ = P * Y * P := by rw [hPproj.2]
      have hQYQ_eq : Q * Y * Q = Q * W * Q := by
        calc Q * Y * Q
            = (Q * P) * Y * (P * Q) := by rw [hQP, hPQ]
          _ = Q * (P * Y * P) * Q := by simp [Matrix.mul_assoc]
          _ = Q * W * Q := rfl
      set W' : Matrix (Fin n) (Fin n) ℂ := φ.symm ⟨W, hW_corner⟩
      have hφW' : (φ W').1 = W :=
        congrArg Subtype.val (LinearEquiv.apply_symm_apply φ ⟨W, hW_corner⟩)
      set Z' : Matrix (Fin n) (Fin n) ℂ := Q' * W' * Q' with hZ'_def
      have hQWQ_φZ' : Q * W * Q = (φ Z').1 := by
        have hZ'assoc : Z' = Q' * (W' * Q') := by
          simp [hZ'_def, Matrix.mul_assoc]
        calc
          Q * W * Q = (φ Q').1 * W * (φ Q').1 := rfl
          _ = (φ Q').1 * (φ W').1 * (φ Q').1 := by rw [hφW']
          _ = (φ Q').1 * ((φ W').1 * (φ Q').1) := by simp [Matrix.mul_assoc]
          _ = (φ Q').1 * (φ (W' * Q')).1 := by rw [hMul W' Q']
          _ = (φ (Q' * (W' * Q'))).1 := by rw [hMul Q' (W' * Q')]
          _ = (φ Z').1 := by rw [← hZ'assoc]
      have hQYQ_φZ' : Q * Y * Q = (φ Z').1 := hQYQ_eq.trans hQWQ_φZ'
      -- F_C Z' ∈ corner(Q') by Q'-invariance of F_C.
      have hF_C_fix : Q' * F_C Z' * Q' = F_C Z' := by
        have := hQ'preserves W'
        simpa [hZ'_def, hF_C_def] using this
      -- Transport Q'-invariance of F_C via φ.
      have hφF_C_fix : (φ (F_C Z')).1 = Q * (φ (F_C Z')).1 * Q := by
        have key : (φ (Q' * F_C Z' * Q')).1 = Q * (φ (F_C Z')).1 * Q := by
          calc
            (φ (Q' * F_C Z' * Q')).1
                = (φ (Q' * (F_C Z' * Q'))).1 := by rw [Matrix.mul_assoc]
              _ = (φ Q').1 * (φ (F_C Z' * Q')).1 := hMul _ _
              _ = (φ Q').1 * ((φ (F_C Z')).1 * (φ Q').1) := by rw [hMul (F_C Z') Q']
              _ = Q * (φ (F_C Z')).1 * Q := by simp [hQ_def, Matrix.mul_assoc]
        rw [hF_C_fix] at key
        exact key
      -- `T ((φ Z').1) = (φ (F_C Z')).1`.
      have hTφZ' : T ((φ Z').1) = (φ (F_C Z')).1 := by
        have hZ'corner : P * (φ Z').1 * P = (φ Z').1 := (φ Z').2
        have hIw := (hIntertwine Z').symm
        rw [hTeq _ hZ'corner] at hIw
        exact hIw
      rw [hQYQ_φZ', hTφZ']
      exact hφF_C_fix.symm
    rcases hCornerIrr Q hQproj hQP hPQ hQinv with hQ0 | hQP_eq
    · left
      apply φ.injective
      apply Subtype.ext
      simp only [map_zero, Submodule.coe_zero]
      exact hQ0
    · right
      apply φ.injective
      apply Subtype.ext
      rw [hφ1_eq_P]
      exact hQP_eq
  exact ⟨hPrim_F_C, hIrr⟩

/-- **Per-sector compressed-block bridge.**

For a cyclic sector decomposition with per-sector `∗`-algebra compression
equivalences `φ k : M_{dim k}(ℂ) ≃ₗ[ℂ] cornerSubmodule (P k)` that are
multiplicative (`hMul`), `∗`-preserving (`hStar`), and intertwine the
compressed adjoint transfer map with the `P k · blockTensor`-adjoint transfer
map on the corner (`hIntertwine`): primitivity and irreducibility on the
corner of `P u` (for the ambient `m`-step adjoint transfer map
`(transferMap Aᴴ) ^ m`) transport along `φ u` to primitivity and
irreducibility of the compressed block `blocks u`. -/
private lemma compressedSector_adjointTransferMap_cornerBridge_of_cyclicDecomp
    [NeZero D] (A : MPSTensor d D) {m : ℕ} [NeZero m]
    {dim : Fin m → ℕ}
    (blocks :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    {P : Fin m → MatrixAlg D}
    {φ : (k : Fin m) →
      Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k)}
    (hPproj : ∀ k, IsOrthogonalProjection (P k))
    (hIntertwine :
      ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k (transferMap (d := blockPhysDim d m) (D := dim k)
            (fun i => (blocks k i)ᴴ) X)).1 =
          transferMap (d := blockPhysDim d m) (D := D)
            (fun i => (P k * blockTensor A m i)ᴴ) ((φ k X).1))
    (hMul :
      ∀ k (X Y : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k (X * Y)).1 = (φ k X).1 * (φ k Y).1)
    (hStar :
      ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k Xᴴ).1 = ((φ k X).1)ᴴ)
    (u : Fin m) (hNonzero : dim u ≠ 0)
    (hInv :
      PreservesCorner (P u)
        ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m))
    (hCornerPrim :
      _root_.IsPrimitive
        (cornerRestriction (P u)
          ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) hInv))
    (hCornerIrr :
      IsIrreducibleOnCorner (P u)
        ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m)) :
    _root_.IsPrimitive
      (transferMap (d := blockPhysDim d m) (D := dim u)
        (fun i => (blocks u i)ᴴ)) ∧
      IsIrreducibleMap
        (transferMap (d := blockPhysDim d m) (D := dim u)
          (fun i => (blocks u i)ᴴ)) := by
  haveI : NeZero (dim u) := ⟨hNonzero⟩
  let T : MatrixEnd D :=
    (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m
  have hT :
      transferMap (d := blockPhysDim d m) (D := D)
          (fun i => (blockTensor A m i)ᴴ) =
        T := by
    ext X : 1
    exact transferMap_adjoint_blocked_eq_pow A m X
  exact
    compressedTensor_adjointTransferMap_cornerBridge
      (B := blockTensor A m) (C := blocks u) (P := P u) (T := T) (φ := φ u)
      hT (hPproj u) (hIntertwine u) (hMul u) (hStar u)
      hInv hCornerPrim hCornerIrr

private lemma adjointTransferMap_primitive_and_irreducible_sectorBlock_of_cyclicDecomp
    [NeZero D] (A : MPSTensor d D) {m : ℕ} [NeZero m]
    (hP : IsPeriodic m A)
    {dim : Fin m → ℕ}
    (blocks :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (hBlocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocks k i)ᴴ * blocks k i = 1)
    (hBlocks_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocks))
    (hCyclic : IsCyclicSectorDecomp A blocks)
    (u : Fin m) (hNonzero : dim u ≠ 0) :
    _root_.IsPrimitive
        (transferMap (d := blockPhysDim d m) (D := dim u)
          (fun i => (blocks u i)ᴴ))
      ∧ IsIrreducibleMap
        (transferMap (d := blockPhysDim d m) (D := dim u)
          (fun i => (blocks u i)ᴴ)) := by
  obtain ⟨P, φ, hPproj, hPsum, hCyclicP, hComm, hTrace, hIntertwine, hMul, hStar⟩ := hCyclic
  obtain ⟨hInv, hCornerPrim, hCornerIrr⟩ :=
    cornerRestriction_primitive_and_irreducible_of_cyclicDecomp
      A hP blocks hBlocks_lc hBlocks_mpv hPproj hPsum hCyclicP hComm hTrace u hNonzero
  exact
    compressedSector_adjointTransferMap_cornerBridge_of_cyclicDecomp
      A blocks (φ := φ) hPproj hIntertwine hMul hStar u hNonzero
      hInv hCornerPrim hCornerIrr

/-- **Structural bridge** for Case 3 of Proposition 3.3 (arXiv:1708.00029):
each nonzero compressed sector block `blocks u` arising from a cyclic sector
decomposition of a periodic irreducible tensor has both a primitive transfer
map and is tensor-irreducible.

This is the still-missing identification

  `transferMap (blocks u) ≃ cornerRestriction (P u) ((transferMap Aᴴ)^m)`

threaded through the compression spectral isometry produced by
`exists_compressedTensor_of_supported_projection` in
`TNLean/MPS/CanonicalForm/CyclicSectors.lean`. Once that identification is in
place, primitivity follows from `isPrimitive_restriction_of_cyclic_decomp` in
`TNLean/Channel/Peripheral/CyclicDecomposition.lean` (which is unconditional),
and corner irreducibility transports to `IsIrreducibleTensor (blocks u)` via
the adjoint-side identification together with
`MPS/Irreducible/Adjoint.lean`.

See issue #450 for the recommended split: (i) close the MPS-level `hLift`
in `SectorIrreducibility.lean` to expose corner irreducibility of `(E†)^m`,
(ii) prove `compressedTensor_transferMap_conj` (the compressed ↔ cornerRestriction
identification), (iii) combine with this helper to discharge
`sectorBlocked_isNormal_of_isPeriodic`.

Kept as an explicit named sublemma so downstream consumers (`Case 2`,
`Case 3`) and subsequent PRs can target its statement directly — the
declaration is intentionally non-`private` so that follow-up modules
(e.g. a dedicated `SectorIrreducibility` bridge) can reference it. -/
lemma primitive_and_irreducible_sectorBlocks_of_cyclicDecomp
    [NeZero D] (A : MPSTensor d D) {m : ℕ} [NeZero m]
    (hP : IsPeriodic m A)
    {dim : Fin m → ℕ}
    (blocks :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (hBlocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocks k i)ᴴ * blocks k i = 1)
    (hBlocks_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocks))
    (hCyclic : IsCyclicSectorDecomp A blocks)
    (u : Fin m) (hNonzero : dim u ≠ 0) :
    _root_.IsPrimitive
        (transferMap (d := blockPhysDim d m) (D := dim u) (blocks u))
      ∧ IsIrreducibleTensor (blocks u) := by
  obtain ⟨hPrimAdj, hIrrAdj⟩ :=
    adjointTransferMap_primitive_and_irreducible_sectorBlock_of_cyclicDecomp
      A hP blocks hBlocks_lc hBlocks_mpv hCyclic u hNonzero
  haveI : NeZero (dim u) := ⟨hNonzero⟩
  have hM : (1 : Matrix (Fin (dim u)) (Fin (dim u)) ℂ).PosDef := by
    classical
    simpa only using (Matrix.PosDef.one (n := Fin (dim u)) (R := ℂ))
  letI : NormedAddCommGroup (Matrix (Fin (dim u)) (Fin (dim u)) ℂ) :=
    Matrix.toMatrixNormedAddCommGroup (n := Fin (dim u)) (𝕜 := ℂ) 1 hM
  letI : SeminormedAddCommGroup (Matrix (Fin (dim u)) (Fin (dim u)) ℂ) :=
    Matrix.toMatrixSeminormedAddCommGroup (n := Fin (dim u)) (𝕜 := ℂ) 1 hM.posSemidef
  letI : InnerProductSpace ℂ (Matrix (Fin (dim u)) (Fin (dim u)) ℂ) :=
    Matrix.toMatrixInnerProductSpace (n := Fin (dim u)) (𝕜 := ℂ) 1 hM.posSemidef
  have hAdj :
      transferMap (d := blockPhysDim d m) (D := dim u) (fun i => (blocks u i)ᴴ) =
        (transferMap (d := blockPhysDim d m) (D := dim u) (blocks u)).adjoint := by
    simpa only using
      (transferMap_conjTranspose_eq_adjoint
        (d := blockPhysDim d m) (D := dim u) (A := blocks u))
  have hPrimAdj' :
      _root_.IsPrimitive
        ((transferMap (d := blockPhysDim d m) (D := dim u) (blocks u)).adjoint) := by
    simpa only [hAdj] using hPrimAdj
  refine ⟨(IsPrimitive.adjoint_iff
    (E := transferMap (d := blockPhysDim d m) (D := dim u) (blocks u))).1 hPrimAdj', ?_⟩
  exact isIrreducibleTensor_of_isIrreducibleMap_conjTranspose (blocks u) hIrrAdj

/-! ## Self-overlap (first paragraph of Appendix A) -/

private theorem mpvOverlap_blockTensor_self_eq
    [NeZero D] (A : MPSTensor d D) (L N : ℕ) :
    mpvOverlap (d := blockPhysDim d L) (blockTensor (d := d) (D := D) A L)
        (blockTensor (d := d) (D := D) A L) N =
      mpvOverlap (d := d) A A (N * L) := by
  rw [← trace_mixedTransferMap_pow_eq_mpvOverlap
      (A := blockTensor (d := d) (D := D) A L)
      (B := blockTensor (d := d) (D := D) A L) N]
  rw [← trace_mixedTransferMap_pow_eq_mpvOverlap (A := A) (B := A) (N * L)]
  simp [mixedTransferMap_self, transferMap_blockTensor, pow_mul, Nat.mul_comm]

/-- Orthogonal-corner rigidity for compressed cyclic sectors.

This is the missing linear-algebra bridge behind the sector separation statement:
if two compressed sectors come from orthogonal projections in the same cyclic
decomposition, their trace functionals cannot be related by a nonzero
gauge-phase transform.  The proof should use the trace identities
`mpv(blocks k) = tr(P k · -)`, the cyclic corner structure, and
`P u * P v = 0`.

Keeping this as a narrow helper lets the main sector-separation lemma expose all
currently available API facts instead of hiding the projection argument behind a
top-level `sorry`. -/
private lemma not_gaugePhaseEquiv_of_orthogonal_cyclicSector_traces
    [NeZero D] (A : MPSTensor d D) {m : ℕ} [NeZero m]
    {dim : Fin m → ℕ}
    (blocks :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    {P : Fin m → MatrixAlg D}
    (hPproj : ∀ k, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hCyclic :
      ∀ k, transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (hComm :
      ∀ k (i : Fin (blockPhysDim d m)),
        P k * (blockTensor A m) i = (blockTensor A m) i * P k)
    (hTrace :
      ∀ k (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)),
        mpv (blocks k) σ = (P k * evalWord (blockTensor A m) (List.ofFn σ)).trace)
    (hNondeg : ∀ k, dim k ≠ 0)
    {u v : Fin m} (huv : u ≠ v) (hdim : dim u = dim v)
    (hOrth : P u * P v = 0) :
    ¬ GaugePhaseEquiv
      (cast (congr_arg (MPSTensor (blockPhysDim d m)) hdim) (blocks u))
      (blocks v) := by
  sorry

/-- Distinct compressed sectors of a cyclic sector decomposition are not gauge-phase
equivalent.

Mathematically, a gauge-phase equivalence would identify the two compressed MPV traces.
Through `IsCyclicSectorDecomp`, those traces are
`tr(P u · evalWord(blockTensor A m) w)` and
`tr(P v · evalWord(blockTensor A m) w)`.  The projections in a cyclic
decomposition are orthogonal corners, so for `u ≠ v` these corner states cannot
be related by an invertible gauge and nonzero scalar.

The current cyclic-sector API exposes the trace formula and projection data but
does not yet package this orthogonal-corner rigidity in a reusable theorem, so
we isolate exactly that missing bridge here. -/
private lemma sectorBlocks_not_gaugePhaseEquiv_of_ne
    [NeZero D] (A : MPSTensor d D) {m : ℕ} [NeZero m]
    (_hP : IsPeriodic m A)
    {dim : Fin m → ℕ}
    (blocks :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (_hBlocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocks k i)ᴴ * blocks k i = 1)
    (_hBlocks_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocks))
    (hCyclic : IsCyclicSectorDecomp A blocks)
    (hNondeg : ∀ k, dim k ≠ 0)
    {u v : Fin m} (huv : u ≠ v) (hdim : dim u = dim v) :
    ¬ GaugePhaseEquiv
      (cast (congr_arg (MPSTensor (blockPhysDim d m)) hdim) (blocks u))
      (blocks v) := by
  obtain ⟨P, _φ, hPproj, hPsum, hCyclicP, hComm, hTrace, _hIntertwine, _hMul, _hStar⟩ :=
    hCyclic
  have hPairwise : Pairwise fun i j : Fin m => P i * P j = 0 :=
    pairwise_mul_zero_of_orthogonalProjection_sum_one P hPproj hPsum
  have hOrth : P u * P v = 0 := hPairwise huv
  exact
    not_gaugePhaseEquiv_of_orthogonal_cyclicSector_traces
      A blocks hPproj hPsum hCyclicP hComm hTrace hNondeg huv hdim hOrth

/-- Sector-asymptotic bridge for the self-overlap proof.

After blocking by the period, the cyclic sector decomposition should make each
compressed sector a primitive normalized tensor, while distinct sectors are
asymptotically orthogonal.

This is the remaining bridge from the cyclic-sector decomposition API to the
overlap-asymptotic API. -/
private theorem sectorOverlap_tendsto_delta_of_cyclicSectorDecomp
    [NeZero D] (A : MPSTensor d D) {m : ℕ} [NeZero m]
    (hP : IsPeriodic m A)
    {dim : Fin m → ℕ}
    (blocks :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (hBlocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocks k i)ᴴ * blocks k i = 1)
    (hBlocks_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocks))
    (hCyclic : IsCyclicSectorDecomp A blocks)
    (hNondeg : ∀ k, dim k ≠ 0)
    (u v : Fin m) :
    Tendsto
      (fun k => mpvOverlap (d := blockPhysDim d m) (blocks u) (blocks v) k)
      atTop (nhds (if u = v then (1 : ℂ) else 0)) := by
  classical
  by_cases huv : u = v
  · subst v
    haveI : NeZero (dim u) := ⟨hNondeg u⟩
    obtain ⟨hPrim, hIrr⟩ :=
      primitive_and_irreducible_sectorBlocks_of_cyclicDecomp
        A hP blocks hBlocks_lc hBlocks_mpv hCyclic u (hNondeg u)
    obtain ⟨ρ, hρ_psd, hρ_ne, hρ_fix, htr, hgap⟩ :=
      spectralRadius_compl_lt_one_of_peripheralPrimitive_of_irreducible
        (A := blocks u) hIrr (hBlocks_lc u) hPrim
    have hSelf :
        Tendsto
          (fun k =>
            mpvOverlap (d := blockPhysDim d m) (blocks u) (blocks u) k)
          atTop (nhds (1 : ℂ)) :=
      mpvOverlap_tendsto_one_of_transfer_spectralRadius_compl_lt_one
        (blocks u) (hBlocks_lc u) ρ hρ_fix hρ_ne hρ_psd (by
          simpa using hgap)
    simpa using hSelf
  · have hIrr_u : IsIrreducibleTensor (blocks u) :=
      (primitive_and_irreducible_sectorBlocks_of_cyclicDecomp
        A hP blocks hBlocks_lc hBlocks_mpv hCyclic u (hNondeg u)).2
    have hIrr_v : IsIrreducibleTensor (blocks v) :=
      (primitive_and_irreducible_sectorBlocks_of_cyclicDecomp
        A hP blocks hBlocks_lc hBlocks_mpv hCyclic v (hNondeg v)).2
    haveI : NeZero (dim u) := ⟨hNondeg u⟩
    haveI : NeZero (dim v) := ⟨hNondeg v⟩
    by_cases hdim : dim u = dim v
    · have hNot :
          ¬ GaugePhaseEquiv
            (cast (congr_arg (MPSTensor (blockPhysDim d m)) hdim) (blocks u))
            (blocks v) :=
        sectorBlocks_not_gaugePhaseEquiv_of_ne
          A hP blocks hBlocks_lc hBlocks_mpv hCyclic hNondeg huv hdim
      have hZero :
          Tendsto
            (fun k =>
              mpvOverlap (d := blockPhysDim d m) (blocks u) (blocks v) k)
            atTop (nhds (0 : ℂ)) :=
        mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP
          hdim (blocks u) (blocks v) hIrr_u hIrr_v
          (hBlocks_lc u) (hBlocks_lc v) hNot
      simpa [huv] using hZero
    · have hZero :
          Tendsto
            (fun k =>
              mpvOverlap (d := blockPhysDim d m) (blocks u) (blocks v) k)
            atTop (nhds (0 : ℂ)) :=
        mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP
          (blocks u) (blocks v) hIrr_u hIrr_v
          (hBlocks_lc u) (hBlocks_lc v) hdim
      simpa [huv] using hZero

/-- Self-overlap limit for a blocked tensor from a cyclic sector decomposition.

If `blockTensor A m` splits as the sum of compressed cyclic sector tensors
`blocks u`, each sector is normalized to have self-overlap tending to `1`, and
distinct sectors are asymptotically orthogonal. Expanding the blocked
self-overlap as the finite double sum over sector overlaps therefore gives the
limit `m`, one contribution from each sector. -/
private theorem blockTensor_selfOverlap_tendsto_of_cyclicSectorDecomp
    [NeZero D] (A : MPSTensor d D) {m : ℕ} [NeZero m]
    (hP : IsPeriodic m A)
    {dim : Fin m → ℕ}
    (blocks :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (hBlocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocks k i)ᴴ * blocks k i = 1)
    (hBlocks_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocks))
    (hCyclic : IsCyclicSectorDecomp A blocks)
    (hNondeg : ∀ k, dim k ≠ 0) :
    Tendsto
      (fun k => mpvOverlap (d := blockPhysDim d m)
        (blockTensor (d := d) (D := D) A m)
        (blockTensor (d := d) (D := D) A m) k)
      atTop (nhds (m : ℂ)) := by
  classical
  have hDecomp : ∀ N (σ : Fin N → Fin (blockPhysDim d m)),
      mpv (blockTensor (d := d) (D := D) A m) σ =
        ∑ u : Fin m, mpv (blocks u) σ := by
    intro N σ
    calc
      mpv (blockTensor (d := d) (D := D) A m) σ =
          mpv (toTensorFromBlocks (d := blockPhysDim d m)
            (μ := fun _ : Fin m => (1 : ℂ)) blocks) σ := hBlocks_mpv N σ
      _ = ∑ u : Fin m, ((1 : ℂ) ^ N) • mpv (blocks u) σ := by
            rw [mpv_toTensorFromBlocks_eq_sum]
      _ = ∑ u : Fin m, mpv (blocks u) σ := by simp
  have hOverlap_eq : ∀ N,
      mpvOverlap (d := blockPhysDim d m)
          (blockTensor (d := d) (D := D) A m)
          (blockTensor (d := d) (D := D) A m) N =
        ∑ u : Fin m, ∑ v : Fin m,
          mpvOverlap (d := blockPhysDim d m) (blocks u) (blocks v) N := by
    intro N
    calc
      mpvOverlap (d := blockPhysDim d m)
          (blockTensor (d := d) (D := D) A m)
          (blockTensor (d := d) (D := D) A m) N
        = ∑ σ : Cfg (blockPhysDim d m) N,
          mpv (blockTensor (d := d) (D := D) A m) σ *
            star (mpv (blockTensor (d := d) (D := D) A m) σ) := rfl
      _ = ∑ σ : Cfg (blockPhysDim d m) N,
            (∑ u : Fin m, mpv (blocks u) σ) *
              star (∑ v : Fin m, mpv (blocks v) σ) := by
              refine Finset.sum_congr rfl ?_
              intro σ _
              rw [hDecomp N σ]
      _ = ∑ σ : Cfg (blockPhysDim d m) N,
            ∑ u : Fin m, ∑ v : Fin m,
              mpv (blocks u) σ * star (mpv (blocks v) σ) := by
              refine Finset.sum_congr rfl ?_
              intro σ _
              rw [star_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl ?_
              intro u _
              rw [Finset.mul_sum]
      _ = ∑ u : Fin m, ∑ σ : Cfg (blockPhysDim d m) N,
            ∑ v : Fin m, mpv (blocks u) σ * star (mpv (blocks v) σ) := by
              rw [Finset.sum_comm]
      _ = ∑ u : Fin m, ∑ v : Fin m, ∑ σ : Cfg (blockPhysDim d m) N,
            mpv (blocks u) σ * star (mpv (blocks v) σ) := by
              refine Finset.sum_congr rfl ?_
              intro u _
              rw [Finset.sum_comm]
      _ = ∑ u : Fin m, ∑ v : Fin m,
            mpvOverlap (d := blockPhysDim d m) (blocks u) (blocks v) N := by
              simp [mpvOverlap]
  have hInner : ∀ u : Fin m,
      Tendsto
        (fun N => ∑ v : Fin m,
          mpvOverlap (d := blockPhysDim d m) (blocks u) (blocks v) N)
        atTop (nhds (∑ v : Fin m, if u = v then (1 : ℂ) else 0)) := by
    intro u
    exact tendsto_finset_sum (s := Finset.univ) fun v _ =>
      sectorOverlap_tendsto_delta_of_cyclicSectorDecomp
        A hP blocks hBlocks_lc hBlocks_mpv hCyclic hNondeg u v
  have hSum :
      Tendsto
        (fun N => ∑ u : Fin m, ∑ v : Fin m,
          mpvOverlap (d := blockPhysDim d m) (blocks u) (blocks v) N)
        atTop (nhds (∑ u : Fin m, ∑ v : Fin m, if u = v then (1 : ℂ) else 0)) := by
    exact tendsto_finset_sum (s := Finset.univ) fun u _ => hInner u
  have hLimit :
      (∑ u : Fin m, ∑ v : Fin m, if u = v then (1 : ℂ) else 0) = (m : ℂ) := by
    simp
  simpa [hLimit] using Filter.Tendsto.congr (fun N => (hOverlap_eq N).symm) hSum

/-- Self-overlap of a periodic tensor: `⟨V_N(A)|V_N(A)⟩ = tr(E_A^N)`, and
since the peripheral eigenvalues are `m`-th roots of unity, each contributing 1
at multiples of `m`, the limit along `m·ℕ` equals `m`.

This is the first displayed equation of Appendix A. -/
theorem periodicSelfOverlap_tendsto
    [NeZero D] (A : MPSTensor d D) {m : ℕ}
    (hP : IsPeriodic m A) :
    Tendsto (fun k => mpvOverlap A A (m * k)) atTop (nhds (m : ℂ)) := by
  -- PROOF STRUCTURE: see bridge lemma
  -- `blockTensor_selfOverlap_tendsto_of_cyclicSectorDecomp` for the planned
  -- proof route.
  -- Currently sorry-backed pending discharge of
  -- `primitive_and_irreducible_sectorBlocks_of_cyclicDecomp`.
  sorry

/-! ## Case 1: Different periods → orthogonal (Appendix A, first case) -/

/-- Cancellation: `X⁻¹ * (X * Y * Xᴴ) * (X⁻¹)ᴴ = Y`. -/
private theorem gl_conj_cancel (X : GL (Fin D) ℂ)
    (Y : Matrix (Fin D) (Fin D) ℂ) :
    X⁻¹.val * (X.val * Y * X.valᴴ) * X⁻¹.valᴴ = Y := by
  have h1 : X⁻¹.val * X.val = 1 := Units.inv_mul X
  have h2 : X.valᴴ * X⁻¹.valᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Units.inv_mul]; simp
  calc _ = X⁻¹.val * X.val * Y * (X.valᴴ * X⁻¹.valᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = 1 * Y * 1 := by rw [h1, h2]
      _ = Y := by simp

/-- The conjugation `Y ↦ X Y Xᴴ` as a linear equivalence on matrices. -/
private noncomputable def glConjEquiv (X : GL (Fin D) ℂ) :
    Matrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  LinearEquiv.ofLinear
    ((LinearMap.mulLeft ℂ X.val).comp (LinearMap.mulRight ℂ X.valᴴ))
    ((LinearMap.mulLeft ℂ X⁻¹.val).comp (LinearMap.mulRight ℂ X⁻¹.valᴴ))
    (LinearMap.ext fun Y => by
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply,
        LinearMap.mulRight_apply, LinearMap.id_apply, ← Matrix.mul_assoc]
      rw [Units.mul_inv, one_mul, Matrix.mul_assoc Y,
        show X⁻¹.valᴴ * X.valᴴ = 1 from by
          rw [← Matrix.conjTranspose_mul, Units.mul_inv]; simp,
        mul_one])
    (LinearMap.ext fun Y => by
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply,
        LinearMap.mulRight_apply, LinearMap.id_apply, ← Matrix.mul_assoc]
      rw [Units.inv_mul, one_mul, Matrix.mul_assoc Y,
        show X.valᴴ * X⁻¹.valᴴ = 1 from by
          rw [← Matrix.conjTranspose_mul, Units.inv_mul]; simp,
        mul_one])

/-- **GaugePhaseEquiv preserves periods.**

If two periodic tensors (same bond dimension) are gauge-phase equivalent,
they must have the same period.

arXiv:0909.5347, via eigenvalue uniqueness (Wolf Thm 6.3). -/
private theorem period_eq_of_gaugePhaseEquiv_of_isPeriodic
    [NeZero D] {A B : MPSTensor d D}
    {m_a m_b : ℕ} (hA : IsPeriodic m_a A) (hB : IsPeriodic m_b B)
    (hGPE : GaugePhaseEquiv A B) : m_a = m_b := by
  obtain ⟨X, ζ, hζ_ne, hBi⟩ := hGPE
  -- PSD fixed points
  obtain ⟨ρ, hρ_psd, hρ_ne, hρ_fix⟩ :=
    exists_posSemidef_fixedPoint A hA.leftCanonical (NeZero.pos D)
  obtain ⟨τ, hτ_psd, hτ_ne, hτ_fix⟩ :=
    exists_posSemidef_fixedPoint B hB.leftCanonical (NeZero.pos D)
  -- E_B is irreducible CP
  have hB_irrMap : IsIrreducibleMap (transferMap (d := d) (D := D) B) :=
    isIrreducibleCP_transferMap_of_isIrreducibleTensor B hB.irreducible
  have hB_cp : IsCPMap (transferMap (d := d) (D := D) B) := transferMap_isCPMap B
  -- Transfer map scaling: B = ζ • (X A X⁻¹) implies E_B = |ζ|² E_{XAX⁻¹}
  have hEB_eq : ∀ Y, transferMap (d := d) (D := D) B Y =
      (ζ * starRingEnd ℂ ζ) •
        (X.val * transferMap (d := d) (D := D) A
          (X⁻¹.val * Y * X⁻¹.valᴴ) * X.valᴴ) := by
    intro Y
    simp only [transferMap_apply]
    simp_rw [hBi]
    simp only [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm,
      smul_smul, ← Finset.smul_sum, Matrix.conjTranspose_mul,
      Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc]
    congr 1; exact mul_comm _ _
  -- σ = X ρ Xᴴ is a PSD eigenvector of E_B with eigenvalue |ζ|²
  set σ := X.val * ρ * X.valᴴ
  have hσ_psd : σ.PosSemidef :=
    hρ_psd.mul_mul_conjTranspose_same X.val
  have hσ_ne : σ ≠ 0 := by
    intro h
    apply hρ_ne
    have h1 := congr_arg (X⁻¹.val * · * X⁻¹.valᴴ) h
    simp only [Matrix.mul_zero, Matrix.zero_mul] at h1
    rwa [gl_conj_cancel] at h1
  have hEB_σ : transferMap (d := d) (D := D) B σ = (ζ * starRingEnd ℂ ζ) • σ := by
    simp only [σ, hEB_eq, gl_conj_cancel, hρ_fix]
  -- ζ * star ζ = ‖ζ‖²
  have hζζ_real : ζ * starRingEnd ℂ ζ = (↑(‖ζ‖ ^ 2) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hζζ_pos : (0 : ℝ) < ‖ζ‖ ^ 2 := by positivity
  -- By eigenvalue uniqueness (Wolf 6.3): ‖ζ‖² = 1
  have h_eig_eq : ‖ζ‖ ^ 2 = 1 :=
    (eigenvalue_unique_of_irreducible_cp
      (transferMap (d := d) (D := D) B) hB_cp hB_irrMap
      τ σ 1 (‖ζ‖ ^ 2) hτ_psd hτ_ne one_pos hσ_psd hσ_ne hζζ_pos
      (by simp [hτ_fix]) (by rw [hEB_σ, hζζ_real])).symm
  have hζ_norm : ‖ζ‖ = 1 := by nlinarith [norm_nonneg ζ]
  -- RepeatedBlocks A B with phase ζ⁻¹
  have hRepeated : RepeatedBlocks A B := by
    refine ⟨ζ⁻¹, X⁻¹, by rw [norm_inv, hζ_norm, inv_one], ?_⟩
    intro i
    -- Goal: A i = ζ⁻¹ • (↑(X⁻¹) * B i * ↑((X⁻¹)⁻¹))
    -- Simplify (X⁻¹)⁻¹ = X
    simp only [inv_inv]
    -- Goal: A i = ζ⁻¹ • (X⁻¹.val * B i * X.val)
    -- Show X⁻¹ * B i * X = ζ • A i
    have hconj : X⁻¹.val * B i * X.val = ζ • A i := by
      rw [hBi i, mul_smul_comm, smul_mul_assoc]
      congr 1
      calc X⁻¹.val * (X.val * A i * X⁻¹.val) * X.val
          = X⁻¹.val * X.val * A i * (X⁻¹.val * X.val) := by
            simp only [Matrix.mul_assoc]
        _ = 1 * A i * 1 := by rw [Units.inv_mul]
        _ = A i := by simp
    rw [hconj, smul_smul, inv_mul_cancel₀ hζ_ne, one_smul]
  -- Peripheral eigenvalue equality via conjugation
  have hSpec : peripheralEigenvalues (transferMap (d := d) (D := D) A) =
      peripheralEigenvalues (transferMap (d := d) (D := D) B) := by
    have hEB_is_conj : transferMap (d := d) (D := D) B =
        (glConjEquiv X).conj (transferMap (d := d) (D := D) A) := by
      apply LinearMap.ext; intro Y
      rw [hEB_eq, hζζ_real, show (↑(‖ζ‖ ^ 2) : ℂ) = (1 : ℂ) from by simp [h_eig_eq],
        one_smul,
        show (glConjEquiv X).conj (transferMap (d := d) (D := D) A) Y =
          X.val * (transferMap (d := d) (D := D) A
            (X⁻¹.val * (Y * X⁻¹.valᴴ)) * X.valᴴ) from rfl]
      simp only [Matrix.mul_assoc]
    rw [hEB_is_conj]
    exact (peripheralEigenvalues_conj (glConjEquiv X)
      (transferMap (d := d) (D := D) A)).symm
  exact IsPeriodic.period_eq_of_repeatedBlocks hA hB hRepeated hSpec

/-- If two periodic tensors have different periods `m_a ≠ m_b`, their overlap
decays to zero.

*Proof*: split on whether `D₁ = D₂`. If not, use dimension mismatch
(`periodicOverlap_tendsto_zero_of_ne_dim`). If `D₁ = D₂`, assume for
contradiction that `GaugePhaseEquiv A B`; then
`period_eq_of_gaugePhaseEquiv_of_isPeriodic` gives `m_a = m_b`, contradicting
`hne`. So `¬ GaugePhaseEquiv`, and `mpvOverlap_tendsto_zero_of_irreducible_TP`
gives the result.

This is the first substantial argument in Appendix A of arXiv:1708.00029. -/
theorem periodicOverlap_tendsto_zero_of_ne_period
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    {m_a m_b : ℕ}
    (hA : IsPeriodic m_a A) (hB : IsPeriodic m_b B)
    (hne : m_a ≠ m_b) :
    Tendsto (fun N => mpvOverlap A B N) atTop (nhds 0) := by
  by_cases hD : D₁ = D₂
  · subst hD
    exact mpvOverlap_tendsto_zero_of_irreducible_TP A B
      hA.irreducible hB.irreducible hA.leftCanonical hB.leftCanonical
      (fun hGPE => hne (period_eq_of_gaugePhaseEquiv_of_isPeriodic hA hB hGPE))
  · exact mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP A B
      hA.irreducible hB.irreducible hA.leftCanonical hB.leftCanonical hD

/-! ## Case 2: Same period, no sector match → orthogonal (Appendix A, second case) -/

/-- Case-2 helper for the compressed blocked sector tensors.

The intended mathematical content is Lemma 2.4: after blocking by the period,
each cyclic sector is a normal tensor. The statement uses the compressed sector
tensor on the corner bond space, as produced by
`exists_cyclic_sector_decomp_after_blocking_of_isPeriodic`.

The nontriviality hypothesis `dim u ≠ 0` excludes the degenerate
zero-dimensional "missing sector" case. With the current definitions, an
`MPSTensor _ 0` may satisfy block-injectivity/normality vacuously, so this
assumption is used to focus on genuine nonempty sectors.

The `hBlocks_mpv` hypothesis ties the compressed block decomposition back to
the original blocked tensor, and `hCyclic` ensures the block indexing
follows the cyclic orbit structure of the transfer map's peripheral
spectrum (see `IsCyclicSectorDecomp`). -/
lemma sectorBlocked_isNormal_of_isPeriodic
    [NeZero D] (A : MPSTensor d D) {m : ℕ} [NeZero m]
    (hP : IsPeriodic m A)
    {dim : Fin m → ℕ}
    (blocks :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (hBlocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocks k i)ᴴ * blocks k i = 1)
    (hBlocks_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocks))
    (hCyclic : IsCyclicSectorDecomp A blocks)
    (u : Fin m) (hNonzero : dim u ≠ 0) :
    IsNormal (blocks u) := by
  haveI : NeZero (dim u) := ⟨hNonzero⟩
  obtain ⟨hPrim, hIrr⟩ :=
    primitive_and_irreducible_sectorBlocks_of_cyclicDecomp
      A hP blocks hBlocks_lc hBlocks_mpv hCyclic u hNonzero
  exact isNormal_of_tp_primitive_irreducible (blocks u) (hBlocks_lc u) hPrim hIrr

/-- Gauge-phase equivalence is preserved by physical blocking.

If `B i = ζ · X A i X⁻¹`, then every blocked letter is a word of length `L`,
so `blockTensor B L` is related to `blockTensor A L` by the same gauge and
phase `ζ ^ L`. -/
private theorem gaugePhaseEquiv_blockTensor
    (A B : MPSTensor d D) (L : ℕ)
    (hGPE : GaugePhaseEquiv A B) :
    GaugePhaseEquiv (blockTensor (d := d) (D := D) A L)
      (blockTensor (d := d) (D := D) B L) := by
  rcases hGPE with ⟨X, ζ, hζ, hX⟩
  refine ⟨X, ζ ^ L, pow_ne_zero L hζ, ?_⟩
  intro i
  let C : MPSTensor d D := fun j =>
    (X : Matrix (Fin D) (Fin D) ℂ) * A j *
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  have hB : B = fun j => ζ • C j := by
    funext j
    simpa [C] using hX j
  have hGauge :
      evalWord C (wordOfBlock d L i) =
        (X : Matrix (Fin D) (Fin D) ℂ) *
          evalWord A (wordOfBlock d L i) *
          ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
    simpa [C] using
      (evalWord_gauge (A := A) (B := C) X (by intro j; rfl)
        (wordOfBlock d L i))
  calc
    blockTensor (d := d) (D := D) B L i
        = evalWord B (wordOfBlock d L i) := rfl
    _ = evalWord (fun j => ζ • C j) (wordOfBlock d L i) := by simp [hB]
    _ = (ζ ^ (wordOfBlock d L i).length) •
          evalWord C (wordOfBlock d L i) := by
          simpa using
            (evalWord_smul (ζ := ζ) (A := C) (wordOfBlock d L i))
    _ = (ζ ^ L) •
          ((X : Matrix (Fin D) (Fin D) ℂ) *
            blockTensor (d := d) (D := D) A L i *
            ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
          simp [hGauge, blockTensor]

/-- Missing mixed-overlap bridge after blocking.

If two blocked tensors are globally gauge-phase equivalent and both are decomposed
into cyclic compressed sectors, then some sector of the `A` decomposition has a
non-decaying overlap with some sector of the `B` decomposition.

This is the analytic core of the Wedderburn uniqueness step needed below.  The
intended proof expands the total blocked overlap using `hA_mpv` and `hB_mpv` as a
finite double sum of sector overlaps.  Global gauge-phase equivalence keeps the
total blocked overlap nonzero asymptotically (after the usual unit-modulus
normalization of the global phase), so not every mixed sector overlap can tend
to zero. -/
private lemma exists_nondecaying_sectorOverlap_of_blockedGaugePhaseEquiv_cyclicDecomp
    [NeZero D] (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA : IsPeriodic m A) (hB : IsPeriodic m B)
    {dimA dimB : Fin m → ℕ}
    (blocksA :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (hA_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksA k i)ᴴ * blocksA k i = 1)
    (hB_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksB k i)ᴴ * blocksB k i = 1)
    (hA_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksA))
    (hB_mpv :
      SameMPV₂ (blockTensor B m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksB))
    (hA_cyclic : IsCyclicSectorDecomp A blocksA)
    (hB_cyclic : IsCyclicSectorDecomp B blocksB)
    (hNondegA : ∀ u, dimA u ≠ 0)
    (hNondegB : ∀ v, dimB v ≠ 0)
    (hGPE_block :
      GaugePhaseEquiv (blockTensor (d := d) (D := D) A m)
        (blockTensor (d := d) (D := D) B m)) :
    ∃ u v : Fin m,
      ¬ Tendsto
        (fun N => mpvOverlap (d := blockPhysDim d m)
          (blocksA u) (blocksB v) N)
        atTop (nhds (0 : ℂ)) := by
  -- Missing bridge: expand the globally non-decaying blocked overlap as a
  -- finite sum of mixed sector overlaps and use finite-sum convergence.
  sorry

/-- Missing compressed-sector uniqueness bridge after blocking.

Once global gauge-phase equivalence has been transported to the blocked
tensors, the cyclic sector decompositions of the two blocked tensors should be
unique up to relabeling of nonzero Wedderburn/cyclic sectors. This bridge is
the precise remaining API needed for `exists_sector_match_of_gaugePhaseEquiv`:
it extracts one nonzero compressed sector of `A` and a gauge-phase-equivalent
compressed sector of `B`. -/
private lemma exists_sector_match_of_blockedGaugePhaseEquiv_cyclicDecomp
    [NeZero D] (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA : IsPeriodic m A) (hB : IsPeriodic m B)
    {dimA dimB : Fin m → ℕ}
    (blocksA :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (hA_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksA k i)ᴴ * blocksA k i = 1)
    (hB_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksB k i)ᴴ * blocksB k i = 1)
    (hA_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksA))
    (hB_mpv :
      SameMPV₂ (blockTensor B m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksB))
    (hA_cyclic : IsCyclicSectorDecomp A blocksA)
    (hB_cyclic : IsCyclicSectorDecomp B blocksB)
    (hNondegA : ∀ u, dimA u ≠ 0)
    (hNondegB : ∀ v, dimB v ≠ 0)
    (hGPE_block :
      GaugePhaseEquiv (blockTensor (d := d) (D := D) A m)
        (blockTensor (d := d) (D := D) B m)) :
    ∃ (u v : Fin m) (hdim : dimA u = dimB v),
      dimA u ≠ 0 ∧
      GaugePhaseEquiv
        (cast (congr_arg
          (MPSTensor (blockPhysDim d m)) hdim)
          (blocksA u))
        (blocksB v) := by
  obtain ⟨u, v, hNondecay⟩ :=
    exists_nondecaying_sectorOverlap_of_blockedGaugePhaseEquiv_cyclicDecomp
      A B hA hB blocksA blocksB hA_blocks_lc hB_blocks_lc
      hA_mpv hB_mpv hA_cyclic hB_cyclic hNondegA hNondegB hGPE_block
  haveI : NeZero (dimA u) := ⟨hNondegA u⟩
  haveI : NeZero (dimB v) := ⟨hNondegB v⟩
  have hA_irr : IsIrreducibleTensor (blocksA u) :=
    (primitive_and_irreducible_sectorBlocks_of_cyclicDecomp
      A hA blocksA hA_blocks_lc hA_mpv hA_cyclic u (hNondegA u)).2
  have hB_irr : IsIrreducibleTensor (blocksB v) :=
    (primitive_and_irreducible_sectorBlocks_of_cyclicDecomp
      B hB blocksB hB_blocks_lc hB_mpv hB_cyclic v (hNondegB v)).2
  have hdim : dimA u = dimB v := by
    by_contra hne
    exact hNondecay
      (mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP
        (blocksA u) (blocksB v) hA_irr hB_irr
        (hA_blocks_lc u) (hB_blocks_lc v) hne)
  refine ⟨u, v, hdim, hNondegA u, ?_⟩
  by_contra hNot
  exact hNondecay
    (mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP
      hdim (blocksA u) (blocksB v) hA_irr hB_irr
      (hA_blocks_lc u) (hB_blocks_lc v) hNot)

/-- A global gauge-phase equivalence between two periodic tensors forces at
least one compatible nonzero pair of compressed cyclic sectors to be
gauge-phase equivalent.

This is the structural bridge used by the no-sector-match case: the cyclic
sector decomposition is unique up to relabeling, and a global gauge-phase
equivalence carries a nonzero sector of `A` to a sector of `B`. The hypothesis
`hNondegA` supplies the nonzero-sector bookkeeping for the returned `A` sector, while
`hNondegB` provides the typeclass needed to apply the mixed-sector overlap dichotomy.
Both come from the periodic sector decomposition constructed by
`exists_cyclic_sector_decomp_after_blocking_of_isPeriodic`.
The current API does not yet expose that uniqueness theorem in this
compressed-sector form, so the bridge is isolated here as the only missing
ingredient. -/
lemma exists_sector_match_of_gaugePhaseEquiv
    [NeZero D] (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA : IsPeriodic m A) (hB : IsPeriodic m B)
    {dimA dimB : Fin m → ℕ}
    (blocksA :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (hA_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksA k i)ᴴ * blocksA k i = 1)
    (hB_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksB k i)ᴴ * blocksB k i = 1)
    (hA_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksA))
    (hB_mpv :
      SameMPV₂ (blockTensor B m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksB))
    (hA_cyclic : IsCyclicSectorDecomp A blocksA)
    (hB_cyclic : IsCyclicSectorDecomp B blocksB)
    (hNondegA : ∀ u, dimA u ≠ 0)
    (hNondegB : ∀ v, dimB v ≠ 0)
    (hGPE : GaugePhaseEquiv A B) :
    ∃ (u v : Fin m) (hdim : dimA u = dimB v),
      dimA u ≠ 0 ∧
      GaugePhaseEquiv
        (cast (congr_arg
          (MPSTensor (blockPhysDim d m)) hdim)
          (blocksA u))
        (blocksB v) := by
  -- PROOF STRUCTURE: see bridge lemma
  -- `exists_sector_match_of_blockedGaugePhaseEquiv_cyclicDecomp` for the
  -- planned proof route.
  -- Currently sorry-backed pending discharge of
  -- `exists_nondecaying_sectorOverlap_of_blockedGaugePhaseEquiv_cyclicDecomp`
  -- and `primitive_and_irreducible_sectorBlocks_of_cyclicDecomp`.
  sorry

/-- If no nonzero compressed sector pair matches, then the original periodic
tensors cannot be globally gauge-phase equivalent. -/
lemma not_gaugePhaseEquiv_of_no_sector_match
    [NeZero D] (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA : IsPeriodic m A) (hB : IsPeriodic m B)
    {dimA dimB : Fin m → ℕ}
    (blocksA :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (hA_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksA k i)ᴴ * blocksA k i = 1)
    (hB_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksB k i)ᴴ * blocksB k i = 1)
    (hA_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksA))
    (hB_mpv :
      SameMPV₂ (blockTensor B m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksB))
    (hA_cyclic : IsCyclicSectorDecomp A blocksA)
    (hB_cyclic : IsCyclicSectorDecomp B blocksB)
    (hNondegA : ∀ u, dimA u ≠ 0)
    (hNondegB : ∀ v, dimB v ≠ 0)
    (hNoMatch : ∀ u v (hdim : dimA u = dimB v),
      dimA u ≠ 0 →
      ¬ GaugePhaseEquiv
        (cast (congr_arg
          (MPSTensor (blockPhysDim d m)) hdim)
          (blocksA u))
        (blocksB v)) :
    ¬ GaugePhaseEquiv A B := by
  -- PROOF STRUCTURE: see bridge lemma
  -- `exists_sector_match_of_gaugePhaseEquiv` for the planned proof route.
  -- Currently sorry-backed pending discharge of
  -- `exists_nondecaying_sectorOverlap_of_blockedGaugePhaseEquiv_cyclicDecomp`
  -- and `primitive_and_irreducible_sectorBlocks_of_cyclicDecomp`.
  sorry

/-- Same-period / no-match statement using compressed sector tensors.

If two periodic tensors have the same period `m` but no compressed sector
pair matches (up to dimension cast and gauge-phase equivalence), their
overlap decays to zero.

The `hNoMatch` hypothesis quantifies over nondegenerate dimension
equalities: for each sector pair `(u, v)` with `dimA u ≠ 0` and any
proof that `dimA u = dimB v`, the compressed blocks are not gauge-phase
equivalent. The nondegeneracy guard `dimA u ≠ 0` is essential: when
`dimA u = 0`, `GaugePhaseEquiv` may hold vacuously for
`MPSTensor _ 0`, and without this guard `hNoMatch` would be
unsatisfiable whenever a zero-dimensional sector pair exists. With
this guard and the separate nondegeneracy hypotheses
`hNondegA : ∀ u, dimA u ≠ 0` and `hNondegB : ∀ v, dimB v ≠ 0`
coming from the periodic sector decompositions, `hNoMatch` is exactly
the negation of `hSomeMatch` in `periodicOverlap_gaugeEquiv_of_sector_match`,
making the two conditions complementary for the dichotomy proof.  The
`hNondegB` hypothesis is also needed by the mixed-sector overlap dichotomy
used to extract a sector match from global gauge-phase equivalence.

This is the "first case" of the same-period argument in Appendix A:
block by `m`, decompose into normal sectors, and observe that all
cross-sector overlaps decay by the normal-tensor overlap dichotomy. -/
theorem periodicOverlap_tendsto_zero_of_no_sector_match
    [NeZero D] (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA : IsPeriodic m A) (hB : IsPeriodic m B)
    {dimA dimB : Fin m → ℕ}
    (blocksA :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (hA_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksA k i)ᴴ * blocksA k i = 1)
    (hB_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksB k i)ᴴ * blocksB k i = 1)
    (hA_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksA))
    (hB_mpv :
      SameMPV₂ (blockTensor B m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksB))
    (hA_cyclic : IsCyclicSectorDecomp A blocksA)
    (hB_cyclic : IsCyclicSectorDecomp B blocksB)
    (hNondegA : ∀ u, dimA u ≠ 0)
    (hNondegB : ∀ v, dimB v ≠ 0)
    (hNoMatch : ∀ u v (hdim : dimA u = dimB v),
      dimA u ≠ 0 →
      ¬ GaugePhaseEquiv
        (cast (congr_arg
          (MPSTensor (blockPhysDim d m)) hdim)
          (blocksA u))
        (blocksB v)) :
    Tendsto (fun N => mpvOverlap A B N) atTop (nhds 0) := by
  -- PROOF STRUCTURE: see bridge lemma
  -- `not_gaugePhaseEquiv_of_no_sector_match` for the planned proof route.
  -- Currently sorry-backed pending discharge of
  -- `exists_sector_match_of_gaugePhaseEquiv`.
  sorry

/-! ## Case 3: Same period, sector match → gauge-equivalent (Appendix A, main case) -/

/-- Nonzero sector dimensions propagate one step around a cyclic sector decomposition.

This part uses only the currently exposed cyclic-sector API: if `dim u ≠ 0` then the
projection `P u` is nonzero by the `N = 0` trace identity. If `P (u + 1)` were zero,
the cyclic relation `E†(P (u + 1)) = P u` would force `P u = 0`, contradiction. -/
private lemma sectorDim_ne_zero_succ_of_cyclicSectorDecomp
    [NeZero D] (A : MPSTensor d D)
    {m : ℕ} [NeZero m]
    {dim : Fin m → ℕ}
    (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (hCyclic : IsCyclicSectorDecomp A blocks)
    {u : Fin m} (hNondeg : dim u ≠ 0) :
    dim (u + 1) ≠ 0 := by
  classical
  obtain ⟨P, _φ, hPproj, _hPsum, hShift, _hComm, hTrace, _hIntertwine, _hMul, _hStar⟩ :=
    hCyclic
  intro hzero
  have htrace_succ :
      Matrix.trace (P (u + 1)) = 0 := by
    have h0 := hTrace (u + 1) 0 Fin.elim0
    simp only [mpv, coeff, List.ofFn_zero, evalWord_nil, Matrix.mul_one] at h0
    rw [← h0, Matrix.trace_one, Fintype.card_fin, hzero, Nat.cast_zero]
  have hPsucc_zero : P (u + 1) = 0 :=
    (isOrthogonalProjection_posSemidef (hPproj (u + 1))).trace_eq_zero_iff.mp htrace_succ
  have hPu_zero : P u = 0 := by
    rw [← hShift u, hPsucc_zero, map_zero]
  have htrace_u : Matrix.trace (P u) = 0 := by
    rw [hPu_zero, Matrix.trace_zero]
  have hdim_zero : dim u = 0 := by
    have h0 := hTrace u 0 Fin.elim0
    simp only [mpv, coeff, List.ofFn_zero, evalWord_nil, Matrix.mul_one] at h0
    have hcast : (dim u : ℂ) = 0 := by
      have htrace_one_zero :
          Matrix.trace (1 : Matrix (Fin (dim u)) (Fin (dim u)) ℂ) = 0 := by
        exact h0.trans htrace_u
      simpa [Matrix.trace_one, Fintype.card_fin] using htrace_one_zero
    exact Nat.cast_eq_zero.mp hcast
  exact hNondeg hdim_zero

/-- Missing cyclic gauge-transport bridge.

This is the precise API still needed for Eq. A.8 of arXiv:1708.00029. From the
current `IsCyclicSectorDecomp` data one knows the projection shift
`E†(P (k+1)) = P k` and the blocked trace realization of each compressed sector.
To prove this bridge, the cyclic-sector construction must additionally expose
one-site corner transition tensors, for example the compressions of
`P k * A i * P (k+1)` and `Q l * B i * Q (l+1)`, together with an identification
of their `m`-fold cyclic products with the supplied `blocksA k` and `blocksB l`.
Then a gauge-phase equivalence at `(u, v)` transports along those one-site
transition tensors to a gauge-phase equivalence at `(u + 1, v + 1)`. -/
private lemma sectorGaugePhaseEquiv_succ_of_cyclicTransport
    [NeZero D]
    (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA_lc : IsLeftCanonical A) (hB_lc : IsLeftCanonical B)
    {dimA dimB : Fin m → ℕ}
    (blocksA :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (hA_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksA k i)ᴴ * blocksA k i = 1)
    (hB_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksB k i)ᴴ * blocksB k i = 1)
    (hA_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksA))
    (hB_mpv :
      SameMPV₂ (blockTensor B m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksB))
    (hA_cyclic : IsCyclicSectorDecomp A blocksA)
    (hB_cyclic : IsCyclicSectorDecomp B blocksB)
    {u : Fin m} {v : Fin m}
    (hdim : dimA u = dimB v)
    (hNondeg : dimA u ≠ 0)
    (hMatch : GaugePhaseEquiv
      (cast (congr_arg
        (MPSTensor (blockPhysDim d m)) hdim)
        (blocksA u))
      (blocksB v)) :
    ∃ (hdim' : dimA (u + 1) = dimB (v + 1)),
      GaugePhaseEquiv
        (cast (congr_arg
          (MPSTensor (blockPhysDim d m)) hdim')
          (blocksA (u + 1)))
        (blocksB (v + 1)) := by
  -- Missing bridge: one-site cyclic transition tensors and their identification
  -- with the compressed blocked sector tensors produced by
  -- `exists_compressedTensor_of_supported_projection`.
  sorry

/-- Missing one-step cyclic transport bridge for sector matches.

This is the formal one-step version of Eq. A.8 in arXiv:1708.00029. The cyclic
projection relation `E†(P (k+1)) = P k`, together with the compressed-sector
realization, should transport a gauge-phase equivalence between sector pair
`(u, v)` to one between `(u + 1, v + 1)`. The conclusion also propagates
nondegeneracy so the step can be iterated around the cycle. -/
private lemma sectorMatch_succ_of_cyclicSectorDecomp
    [NeZero D]
    (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA_lc : IsLeftCanonical A) (hB_lc : IsLeftCanonical B)
    {dimA dimB : Fin m → ℕ}
    (blocksA :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (hA_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksA k i)ᴴ * blocksA k i = 1)
    (hB_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksB k i)ᴴ * blocksB k i = 1)
    (hA_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksA))
    (hB_mpv :
      SameMPV₂ (blockTensor B m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksB))
    (hA_cyclic : IsCyclicSectorDecomp A blocksA)
    (hB_cyclic : IsCyclicSectorDecomp B blocksB)
    {u : Fin m} {v : Fin m}
    (hdim : dimA u = dimB v)
    (hNondeg : dimA u ≠ 0)
    (hMatch : GaugePhaseEquiv
      (cast (congr_arg
        (MPSTensor (blockPhysDim d m)) hdim)
        (blocksA u))
      (blocksB v)) :
    ∃ (hdim' : dimA (u + 1) = dimB (v + 1)),
      dimA (u + 1) ≠ 0 ∧
      GaugePhaseEquiv
        (cast (congr_arg
          (MPSTensor (blockPhysDim d m)) hdim')
          (blocksA (u + 1)))
        (blocksB (v + 1)) := by
  obtain ⟨hdim', hMatch'⟩ :=
    sectorGaugePhaseEquiv_succ_of_cyclicTransport A B hA_lc hB_lc
      blocksA blocksB hA_blocks_lc hB_blocks_lc hA_mpv hB_mpv
      hA_cyclic hB_cyclic hdim hNondeg hMatch
  exact ⟨hdim',
    sectorDim_ne_zero_succ_of_cyclicSectorDecomp A blocksA hA_cyclic hNondeg,
    hMatch'⟩

/-- Transport a sector `GaugePhaseEquiv` across equalities of both sector indices. -/
private lemma gaugePhaseEquiv_cast_indices {d gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    {i₁ i₂ : Fin gA} {j₁ j₂ : Fin gB}
    (hi : i₁ = i₂) (hj : j₁ = j₂)
    (hdim : dimA i₁ = dimB j₁)
    (hg : GaugePhaseEquiv
      (cast (congr_arg (MPSTensor d) hdim) (A i₁)) (B j₁)) :
    GaugePhaseEquiv
      (cast (congr_arg (MPSTensor d) (show dimA i₂ = dimB j₂ from hi ▸ hj ▸ hdim))
        (A i₂)) (B j₂) := by
  subst hi
  subst hj
  exact hg

/-- **Translation propagation** (Eq. A.8 / blockedABprop of arXiv:1708.00029):
Given one matching compressed sector pair at `(u₀, v₀)`, applying the
translation operator `T^l` for `l = 1, …, m-1` yields matching for all
sector pairs `(u₀ + l, v₀ + l)`. Each offset `l` gets its own gauge
(the paper's Eq. blockedABprop produces a different unitary at each
sector, not a single transported gauge).

The `hA_cyclic`/`hB_cyclic` hypotheses (see `IsCyclicSectorDecomp`)
tie the `Fin m` block indexing to the cyclic orbit structure of the
transfer map, which is essential: without them, `SameMPV₂` alone is
permutation-invariant over blocks and would not justify the shifted
conclusion `(u₀ + l, v₀ + l)`.

The nondegeneracy hypothesis `dimA u₀ ≠ 0` ensures the initial match
is substantive: for `MPSTensor _ 0`, `GaugePhaseEquiv` holds vacuously
and propagation would produce only vacuous matches.

The left-canonical hypotheses (`hA_lc`, `hB_lc`) ensure the propagated
phases are unit-modulus: the transfer operator preserves the
trace-preserving condition, so the scaling factor remains on the unit
circle at each step. -/
lemma sectorMatch_propagation
    [NeZero D]
    (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA_lc : IsLeftCanonical A) (hB_lc : IsLeftCanonical B)
    {dimA dimB : Fin m → ℕ}
    (blocksA :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (hA_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksA k i)ᴴ * blocksA k i = 1)
    (hB_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksB k i)ᴴ * blocksB k i = 1)
    (hA_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksA))
    (hB_mpv :
      SameMPV₂ (blockTensor B m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksB))
    (hA_cyclic : IsCyclicSectorDecomp A blocksA)
    (hB_cyclic : IsCyclicSectorDecomp B blocksB)
    {u₀ : Fin m} {v₀ : Fin m}
    (hdim₀ : dimA u₀ = dimB v₀)
    (hNondeg : dimA u₀ ≠ 0)
    (hMatch : GaugePhaseEquiv
      (cast (congr_arg
        (MPSTensor (blockPhysDim d m)) hdim₀)
        (blocksA u₀))
      (blocksB v₀)) :
    ∀ l : Fin m,
      ∃ (hdim : dimA (u₀ + l) = dimB (v₀ + l)),
        GaugePhaseEquiv
          (cast (congr_arg
            (MPSTensor (blockPhysDim d m)) hdim)
            (blocksA (u₀ + l)))
          (blocksB (v₀ + l)) := by
  -- PROOF STRUCTURE: see bridge lemma
  -- `sectorMatch_succ_of_cyclicSectorDecomp` for the planned proof route.
  -- Currently sorry-backed pending discharge of
  -- `sectorGaugePhaseEquiv_succ_of_cyclicTransport`.
  sorry

/-- Missing full-cycle contraction step for periodic-overlap Case 3.

At this point the sector transport has already been abstracted into
`hBlockMatch`, so the remaining gap is no longer the Eq. A.8 staircase
identification.  What is still needed from Eqs. A.14-A.18 of
arXiv:1708.00029 is the contraction argument around the whole cycle:
for each sector `u`, normality gives a repetition length after which
`blocksA u` is injective, and one should use a right inverse from
`decompositionMap` to contract the repeated blocked products and recover
per-site proportionality with a single telescoped phase.

The current chain library provides `decompositionMap` /
`exists_rightInverse` in `MPS/Chain/OneSidedInverse.lean` and the two-site
proportionality theorem `tensor_proportional` in
`MPS/Chain/TensorEquality.lean`, but it does not yet provide the `m`-factor
cyclic contraction theorem needed to pass from `hBlockMatch` to a global
`RepeatedBlocks` witness. -/
private lemma repeatedBlocks_of_blockedSectorGaugePhase
    [NeZero D] (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA_lc : IsLeftCanonical A) (hB_lc : IsLeftCanonical B)
    {dimA dimB : Fin m → ℕ}
    (blocksA :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (hA_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksA k i)ᴴ * blocksA k i = 1)
    (hB_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksB k i)ᴴ * blocksB k i = 1)
    (hA_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksA))
    (hB_mpv :
      SameMPV₂ (blockTensor B m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksB))
    (hA_cyclic : IsCyclicSectorDecomp A blocksA)
    (hB_cyclic : IsCyclicSectorDecomp B blocksB)
    (q : Fin m)
    (hBlockMatch : ∀ u : Fin m,
      ∃ (hdim : dimA u = dimB (u + q)),
        GaugePhaseEquiv
          (cast (congr_arg
            (MPSTensor (blockPhysDim d m)) hdim)
            (blocksA u))
          (blocksB (u + q)))
    (hNondeg : ∀ u, dimA u ≠ 0)
    (hNormal : ∀ u, IsNormal (blocksA u)) :
    RepeatedBlocks A B := by
  -- Missing ingredient: a reusable `m`-factor cyclic contraction theorem,
  -- built from `decompositionMap`, that upgrades the per-sector blocked
  -- gauge data in `hBlockMatch` to one global phase and one global gauge.
  -- The current library only provides the two-site theorem
  -- `tensor_proportional`, so the full-cycle step from Eqs. A.14-A.18 of
  -- arXiv:1708.00029 still has to be formalized separately.
  sorry

/-- **Per-site proportionality** (Eq. A.14 of arXiv:1708.00029):
After injectivity contraction, the sector-restricted tensors satisfy
`A_u^i = κ_v · e^{iη/m} · B_v^i` with `∏ κ_v = 1` and `|κ_v| = 1`.

The offset `q` accounts for the cyclic shift between sector labelings of
`A` and `B`: propagation from a match at `(u₀, v₀)` yields pairs
`(u, u + q)` where `q = v₀ - u₀`.

The `hBlockMatch` hypothesis says that for every sector `u`, the
compressed blocks `blocksA u` and `blocksB (u + q)` are gauge-phase
equivalent (after dimension cast). The injectivity contraction argument
shows these per-sector gauges combine into a single global gauge for
`RepeatedBlocks`.

The nondegeneracy hypothesis `hNondeg` ensures every sector has
positive bond dimension. Without this, zero-dimensional sectors
satisfy `IsNormal`, `GaugePhaseEquiv`, and `hBlockMatch` vacuously,
which would make the conclusion `RepeatedBlocks A B` too strong.

The left-canonical hypotheses (`hA_lc`, `hB_lc`) are essential: they
force the gauge-proportionality phases to have unit modulus, which is
required by `RepeatedBlocks`. -/
lemma sectorTensor_proportional_of_blockedMatch
    [NeZero D] (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA_lc : IsLeftCanonical A) (hB_lc : IsLeftCanonical B)
    {dimA dimB : Fin m → ℕ}
    (blocksA :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (hA_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksA k i)ᴴ * blocksA k i = 1)
    (hB_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksB k i)ᴴ * blocksB k i = 1)
    (hA_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksA))
    (hB_mpv :
      SameMPV₂ (blockTensor B m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksB))
    (hA_cyclic : IsCyclicSectorDecomp A blocksA)
    (hB_cyclic : IsCyclicSectorDecomp B blocksB)
    (q : Fin m)
    (hBlockMatch : ∀ u : Fin m,
      ∃ (hdim : dimA u = dimB (u + q)),
        GaugePhaseEquiv
          (cast (congr_arg
            (MPSTensor (blockPhysDim d m)) hdim)
            (blocksA u))
          (blocksB (u + q)))
    (hNondeg : ∀ u, dimA u ≠ 0)
    (hNormal : ∀ u, IsNormal (blocksA u)) :
    RepeatedBlocks A B := by
  -- PROOF STRUCTURE: see bridge lemma
  -- `repeatedBlocks_of_blockedSectorGaugePhase` for the planned proof route.
  -- Currently sorry-backed pending discharge of
  -- `repeatedBlocks_of_blockedSectorGaugePhase`.
  sorry

/-- **Case 3: a matching sector implies gauge equivalence**. If two periodic tensors have
the same period and a compressed sector match exists, then they are related by a gauge
transformation with a unit-modulus phase: `A^i = e^{iξ} U B^i U†`.

The hypotheses describe compressed sector decompositions: `blocksA`/`blocksB` are
the cyclic-sector tensors on corner bond spaces, tied back to the
original blocked tensors via `SameMPV₂` and to the cyclic orbit
structure via `IsCyclicSectorDecomp`. Global nondegeneracy
(`hNondegA : ∀ u, dimA u ≠ 0`) ensures every sector of `A` has
positive bond dimension, which is needed for normality of each sector
tensor. The `hSomeMatch` witness provides a single matching sector pair
`(u₀, v₀)` with compatible dimensions (the nondegeneracy of `dimA u₀`
follows from `hNondegA`), from which translation propagation extends the
match to all sectors.

This is Eq. (A.17)–(A.18) of arXiv:1708.00029. -/
theorem periodicOverlap_gaugeEquiv_of_sector_match
    [NeZero D] (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA : IsPeriodic m A) (hB : IsPeriodic m B)
    {dimA dimB : Fin m → ℕ}
    (blocksA :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (hA_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksA k i)ᴴ * blocksA k i = 1)
    (hB_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksB k i)ᴴ * blocksB k i = 1)
    (hA_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksA))
    (hB_mpv :
      SameMPV₂ (blockTensor B m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksB))
    (hA_cyclic : IsCyclicSectorDecomp A blocksA)
    (hB_cyclic : IsCyclicSectorDecomp B blocksB)
    (hNondegA : ∀ u, dimA u ≠ 0)
    (hSomeMatch : ∃ (u₀ v₀ : Fin m) (hdim : dimA u₀ = dimB v₀),
      GaugePhaseEquiv
        (cast (congr_arg
          (MPSTensor (blockPhysDim d m)) hdim)
          (blocksA u₀))
        (blocksB v₀)) :
    RepeatedBlocks A B := by
  -- PROOF STRUCTURE: see bridge lemmas `sectorMatch_propagation`,
  -- `sectorBlocked_isNormal_of_isPeriodic`, and
  -- `sectorTensor_proportional_of_blockedMatch` for the planned proof route.
  -- Currently sorry-backed pending discharge of
  -- `sectorGaugePhaseEquiv_succ_of_cyclicTransport`,
  -- `compressedTensor_adjointTransferMap_cornerBridge`, and
  -- `repeatedBlocks_of_blockedSectorGaugePhase`.
  sorry

/-- When `D₁ ≠ D₂`, no `RepeatedBlocks` relation can hold (the types don't
match), so the overlap must decay. This covers the `D₁ ≠ D₂` subcase of
the main dichotomy regardless of period matching. -/
theorem periodicOverlap_tendsto_zero_of_ne_dim
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    {m_a m_b : ℕ}
    (hA : IsPeriodic m_a A) (hB : IsPeriodic m_b B)
    (hdim : D₁ ≠ D₂) :
    Tendsto (fun N => mpvOverlap A B N) atTop (nhds 0) :=
  mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP A B
    hA.irreducible hB.irreducible hA.leftCanonical hB.leftCanonical hdim

/-! ## Main dichotomy (Proposition 3.3) -/

/-- **Periodic overlap dichotomy** (Proposition 3.3 of arXiv:1708.00029).

For two periodic tensors `A` and `B` with periods `m_a` and `m_b` in
irreducible form II, either their overlap decays to zero, or `D_a = D_b` and
they are related by a gauge transformation up to a unit-modulus phase (which
forces `m_a = m_b`).

This is the core technical result of the paper: all subsequent theorems
(proportional FT, equal FT with Z-gauge, symmetry corollary) depend on it. -/
theorem periodicOverlapDichotomy
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    {m_a m_b : ℕ}
    (hA : IsPeriodic m_a A) (hB : IsPeriodic m_b B) :
    Tendsto (fun N => mpvOverlap A B N) atTop (nhds 0)
      ∨ ∃ (hdim : D₁ = D₂),
          RepeatedBlocks (cast (congr_arg (MPSTensor d) hdim) A) B := by
  -- PROOF STRUCTURE: see bridge theorems
  -- `periodicOverlap_tendsto_zero_of_no_sector_match` and
  -- `periodicOverlap_gaugeEquiv_of_sector_match` for the same-period branches.
  -- Currently sorry-backed pending discharge of
  -- `exists_sector_match_of_gaugePhaseEquiv`,
  -- `sectorGaugePhaseEquiv_succ_of_cyclicTransport`, and
  -- `compressedTensor_adjointTransferMap_cornerBridge`.
  sorry

/-- **Eventual linear independence** (Corollary of Proposition 3.3):
Given a family of periodic tensors `{A_j}` whose periods all divide a common
period `p`, there exists `N₀` such that for all `N ≥ N₀` that are multiples
of `p`, the vectors `{|V_N(A_j)⟩}` are linearly independent.

The common-period restriction ensures all `mpvState (A k) N` are nonzero
simultaneously (a zero vector would prevent `LinearIndependent` from holding).

This is the "consequence" stated at the end of Proposition 3.3. -/
theorem periodicBasis_eventuallyLinearlyIndependent
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (period : Fin r → ℕ)
    (hPer : ∀ k, IsPeriodic (period k) (A k))
    (p : ℕ) [NeZero p]
    (hDiv : ∀ k, period k ∣ p)
    (hNonrep : ∀ i j, i ≠ j →
      ∀ (hdim : dim i = dim j),
        ¬ RepeatedBlocks (cast (congr_arg (MPSTensor d) hdim) (A i)) (A j)) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      LinearIndependent ℂ (fun k => mpvState (A k) (p * N)) := by
  -- PROOF STRUCTURE: see bridge theorems
  -- `periodicSelfOverlap_tendsto` and `periodicOverlapDichotomy` for the
  -- Gram-matrix argument.
  -- Currently sorry-backed pending discharge of
  -- `primitive_and_irreducible_sectorBlocks_of_cyclicDecomp`,
  -- `exists_sector_match_of_gaugePhaseEquiv`, and
  -- `sectorGaugePhaseEquiv_succ_of_cyclicTransport`.
  sorry

end MPSTensor
