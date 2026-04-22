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
# Periodic overlap dichotomy: setup and self-overlap

This module contains the cyclic-sector setup used throughout the periodic
overlap argument together with the self-overlap results from the first
paragraph of Appendix A of arXiv:1708.00029.

## Main declarations

* `IsCyclicSectorDecomp`
* `primitive_and_irreducible_sectorBlocks_of_cyclicDecomp`
* `periodicSelfOverlap_tendsto`

## References

* De las Cuevas, Cirac, Schuch, Perez-Garcia,
  *Irreducible forms of Matrix Product States: Theory and Applications*,
  arXiv:1708.00029, Appendix A.
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

/-- Missing compressed-sector statement.

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

/-- **Compression-transfer comparison theorem.**

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

/-- **Per-sector compressed-block comparison theorem.**

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

/-- **Structural step** for Case 3 of Proposition 3.3 (arXiv:1708.00029):
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
(e.g. a dedicated `SectorIrreducibility` lemma) can reference it. -/
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

This is the missing linear-algebra step behind the sector separation statement:
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
does not yet state this orthogonal-corner rigidity as a reusable theorem, so
we isolate exactly that missing step here. -/
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

/-- Sector-asymptotic step for the self-overlap proof.

After blocking by the period, the cyclic sector decomposition should make each
compressed sector a primitive normalized tensor, while distinct sectors are
asymptotically orthogonal.

This is the remaining step from the cyclic-sector decomposition API to the
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
  -- PROOF STRUCTURE: see lemma
  -- `blockTensor_selfOverlap_tendsto_of_cyclicSectorDecomp` for the planned
  -- proof route.
  -- Currently sorry-backed pending discharge of
  -- `primitive_and_irreducible_sectorBlocks_of_cyclicDecomp`.
  sorry


end MPSTensor
