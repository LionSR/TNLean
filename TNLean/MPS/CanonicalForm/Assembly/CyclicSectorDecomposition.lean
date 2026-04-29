/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Assembly.PrimitiveBlocks
import TNLean.Channel.Peripheral.Conjugation
import TNLean.Channel.Schwarz.MultiplicativeDomainFull
import TNLean.MPS.CanonicalForm.SectorIrreducibility
import TNLean.MPS.CanonicalForm.CyclicSectors.CornerBridge

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Filter

/-!
# Cyclic sector decomposition after blocking

This file contains the cyclic-sector part of the canonical-form reduction. It
relates powers of the adjoint transfer map to blocked transfer maps, applies the
channel-level cyclic decomposition to a blocked periodic tensor, and then derives
its MPS-formulation for irreducible TP tensors.

## Main statements

* `adjointTransferMap_pow_fixes_cyclic_projection` — iterating the cyclic
  relation for the adjoint transfer map fixes each cyclic projection after one
  period.
* `transferMap_adjoint_blocked_eq_pow` — the blocked adjoint transfer map agrees
  with the corresponding power of the adjoint transfer map.
* `exists_cyclic_sector_decomp_after_blocking` — channel-level cyclic
  decomposition for a blocked periodic tensor.
* `exists_cyclic_sector_decomp_of_TP_of_isIrreducibleTensor` — MPS-level cyclic
  sector decomposition for irreducible TP tensors.
* `primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking_of_projStep`
  — under the remaining one-step orbit-lift hypothesis `hProjStep`, each
  compressed cyclic sector has primitive transfer map and is tensor-irreducible.
* `primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking_of_fixedAlgebraRigidity`
  — the same conclusion under the structured fixed-point-algebra rigidity
  hypothesis from `SectorIrreducibility/HLift.lean`.
* `sectorFixedPointAlgebraRigidity_of_cyclic_decomp_after_blocking_of_scalarBlockedFixedPoints`
  — a scalar blocked fixed-point algebra hypothesis implies the sector
  rigidity needed by the orbit-sum argument.
* The scalar blocked fixed-point variant of the sector-block theorem — the same
  blocked fixed-point algebra hypothesis yields primitive, tensor-irreducible
  compressed sectors.
* `primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking`
  — the unconditional conclusion using
  `isIrreducibleOnCorner_of_cyclic_decomp_mps`.

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Appendix A]
* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:2011.12127, §IV]

## Tags

matrix product states, cyclic sectors, peripheral spectrum, blocking
-/

namespace MPSTensor

variable {d D : ℕ}

/-!
## Cyclic sector decomposition from cyclic-sector data

### Mathematical overview

For an irreducible TP block `A` of period `m`, the adjoint transfer map
`E† = transferMap (fun i => (A i)ᴴ)` has peripheral spectrum `{γ^k | k ∈ Fin m}`.
The cyclic decomposition from `CyclicDecomposition.lean` produces projections `P_k` with:
- `∀ k, IsOrthogonalProjection (P k)` and `∑ k, P k = 1`
- `E†(P(k+1)) = P k` (cyclic), hence `(E†)^m (P k) = P k`

The key connection: `(E†)^m = transferMap (fun j => (blockTensor A m j)ᴴ)` because the
adjoint of the blocked transfer map equals the m-th iterate of the adjoint transfer map.
This is proved by a tuple-reversal bijection: summing `A_w†·X·A_w` over all length-`m`
words `w` gives the same result regardless of whether `A_w` or `A_{rev(w)}` is used.

### Reduction

1. Get cyclic projections from `CyclicDecomposition.lean` applied to `K = (A·)ᴴ`
2. Show `(transferMap K)^m` fixes each projection (iterate cycling `m` times)
3. Use `transferMap_blockTensor` to identify `(transferMap K)^m = transferMap(blockTensor K m)`
4. Show `transferMap(blockTensor K m) = transferMap(fun j => (blockTensor A m j)ᴴ)` by reversal
5. Apply `exists_blockDecomp_of_adjoint_fixed_projections` from `CyclicSectors.lean`
-/

section CyclicSectorRelation


open KadisonSchwarz

/-- Cyclic shift: `(k + n) % m` as a `Fin m`. -/
private def cyclicShift {m : ℕ} [NeZero m] (k : Fin m) (n : ℕ) : Fin m :=
  ⟨((k : ℕ) + n) % m, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))⟩

@[simp] private lemma cyclicShift_zero {m : ℕ} [NeZero m] (k : Fin m) :
    cyclicShift k 0 = k := by
  ext; simp [cyclicShift, Nat.mod_eq_of_lt k.is_lt]

private lemma cyclicShift_succ {m : ℕ} [NeZero m] (k : Fin m) (n : ℕ) :
    cyclicShift k (n + 1) = cyclicShift k n + 1 := by
  ext
  change ((↑k + n) + 1) % m = (((↑k + n) % m) + 1 % m) % m
  exact Nat.add_mod (↑k + n) 1 m

private lemma cyclicShift_succ_left {m : ℕ} [NeZero m] (k : Fin m) (n : ℕ) :
    cyclicShift k (n + 1) = cyclicShift (k + 1) n := by
  ext
  simp [cyclicShift, Fin.val_add]
  congr 1
  omega

@[simp] private lemma cyclicShift_self {m : ℕ} [NeZero m] (k : Fin m) :
    cyclicShift k m = k := by
  ext
  change (↑k + m) % m = ↑k
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt k.is_lt]

/-- Iterating the cyclic relation `E†(P(k+1)) = P_k` exactly `m` times gives
`(E†)^m (P_k) = P_k`. -/
theorem adjointTransferMap_pow_fixes_cyclic_projection
    {d D m : ℕ} [NeZero m]
    (K : Fin d → MatrixAlg D)
    (P : Fin m → MatrixAlg D)
    (hcyclic : ∀ k : Fin m, transferMap (d := d) (D := D) K (P (k + 1)) = P k) :
    ∀ k : Fin m, ((transferMap (d := d) (D := D) K) ^ m) (P k) = P k := by
  intro k
  have hiter :
      ∀ n : ℕ, ∀ k : Fin m,
        ((transferMap (d := d) (D := D) K) ^ n) (P (cyclicShift k n)) = P k := by
    intro n
    induction n with
    | zero =>
        intro k
        simp
    | succ n ih =>
        intro k
        rw [pow_succ', cyclicShift_succ_left]
        change
          transferMap (d := d) (D := D) K
            (((transferMap (d := d) (D := D) K) ^ n) (P (cyclicShift (k + 1) n))) = P k
        rw [ih (k + 1)]
        exact hcyclic k
  simpa using hiter m k

/-- The adjoint of the blocked transfer map equals the `m`-th iterate of the
adjoint transfer map:
`transferMap (fun j => (blockTensor A m j)ᴴ) X = ((transferMap (fun i => (A i)ᴴ))^m) X`

This is proved by passing to Frobenius adjoints. First,
`transferMap (fun i => (A i)ᴴ) = (transferMap A).adjoint`, and likewise for the blocked
family `blockTensor A m`. Second, `transferMap (blockTensor A m) = (transferMap A)^m` by
`transferMap_blockTensor`. Finally, adjoint commutes with powers, so
`((transferMap A)^m).adjoint = ((transferMap A).adjoint)^m`. -/
theorem transferMap_adjoint_blocked_eq_pow
    {d D : ℕ} (A : MPSTensor d D) (m : ℕ) (X : MatrixAlg D) :
    transferMap (d := blockPhysDim d m) (D := D) (fun j => (blockTensor A m j)ᴴ) X =
      ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) X := by
  classical
  have hM : (1 : Matrix (Fin D) (Fin D) ℂ).PosDef := by
    simpa using (Matrix.PosDef.one (n := Fin D) (R := ℂ))
  letI : NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixNormedAddCommGroup (n := Fin D) (𝕜 := ℂ) 1 hM
  letI : SeminormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixSeminormedAddCommGroup (n := Fin D) (𝕜 := ℂ) 1 hM.posSemidef
  letI : InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixInnerProductSpace (n := Fin D) (𝕜 := ℂ) 1 hM.posSemidef
  have hBlockedAdj :
      transferMap (d := blockPhysDim d m) (D := D) (fun j => (blockTensor A m j)ᴴ) =
        (transferMap (d := blockPhysDim d m) (D := D) (blockTensor A m)).adjoint := by
    simpa using
      (transferMap_conjTranspose_eq_adjoint
        (d := blockPhysDim d m) (D := D) (A := blockTensor A m))
  have hAdj :
      transferMap (d := d) (D := D) (fun i => (A i)ᴴ) =
        (transferMap (d := d) (D := D) A).adjoint := by
    simpa using
      (transferMap_conjTranspose_eq_adjoint (d := d) (D := D) (A := A))
  have hPowAdj :
      ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) =
        (((transferMap (d := d) (D := D) A) ^ m).adjoint) := by
    rw [hAdj]
    have hpow : (((transferMap (d := d) (D := D) A) ^ m).adjoint) =
        ((transferMap (d := d) (D := D) A).adjoint) ^ m := by
      simpa only [LinearMap.star_eq_adjoint] using
        (star_pow (x := transferMap (d := d) (D := D) A) (n := m))
    simpa using hpow.symm
  calc
    transferMap (d := blockPhysDim d m) (D := D) (fun j => (blockTensor A m j)ᴴ) X
        = ((transferMap (d := blockPhysDim d m) (D := D) (blockTensor A m)).adjoint) X := by
            rw [hBlockedAdj]
    _ = (((transferMap (d := d) (D := D) A) ^ m).adjoint) X := by
          rw [transferMap_blockTensor]
    _ = ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) X := by
          rw [← hPowAdj]

/-- **Cyclic sector decomposition for a blocked periodic tensor.**

For an irreducible TP tensor `A` of period `m`, after blocking by `m`, the blocked tensor
`blockTensor A m` admits a sector decomposition into `m` TP blocks via the cyclic
spectral projections. Returns:
- `blocks k`: TP sector tensors (each left-canonical),
- `P k`: orthogonal projections forming a partition of unity (`∑ P k = 1`),
- compression linear equivalences `φ k : M_{dim k}(ℂ) ≃ₗ[ℂ] cornerSubmodule (P k)` together
  with the intertwining identity connecting the compressed adjoint transfer map and the
  sector adjoint transfer map,
- cyclic shift: `transferMap (fun i => (A i)ᴴ) (P (k+1)) = P k`,
- commutation: each `P k` commutes with every blocked letter,
- trace relation: `mpv (blocks k) σ = (P k * evalWord (blockTensor A m) σ).trace`,
- MPV equivalence: the direct-sum tensor is `SameMPV₂`-equivalent to the blocked tensor,
- nondegeneracy: every sector dimension is positive (`∀ k, dim k ≠ 0`). -/
theorem exists_cyclic_sector_decomp_after_blocking
    {d D m : ℕ} [NeZero D] [NeZero m]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (_hIrr : IsIrreducibleTensor A)
    (ρ : MatrixAlg D) (hρ : ρ.PosDef)
    (hρfix : Kraus.adjointMap (fun i : Fin d => (A i)ᴴ) ρ = ρ)
    (hIrrMap : IsIrreducibleMap (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)))
    {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (hperiph : peripheralEigenvalues (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) =
      Set.range (fun j : Fin m => γ ^ (j : ℕ))) :
    ∃ (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
      (P : Fin m → MatrixAlg D)
      (φ : (k : Fin m) →
        Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k)),
      (∀ k, ∑ i : Fin (blockPhysDim d m), (blocks k i)ᴴ * blocks k i = 1) ∧
      SameMPV₂ (blockTensor A m) (toTensorFromBlocks (μ := fun _ => 1) blocks) ∧
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
        (φ k Xᴴ).1 = ((φ k X).1)ᴴ) ∧
      (∀ k, dim k ≠ 0) := by
  -- Step 1: Get cyclic decomposition data
  let K : Fin d → MatrixAlg D := fun i => (A i)ᴴ
  have hUnital : IsUnitalKraus (d := d) (D := D) K := by
    simpa [IsUnitalKraus, K] using hTP
  obtain ⟨U, P, hU, hPow, hUm, hPproj, hPsum, hUspec, hcyclic⟩ :=
    MPSTensor.exists_cyclic_decomposition_of_irreducible_schwarz
      (K := K) hUnital ρ hρ hρfix hIrrMap hγprim hperiph
  -- Step 2: (E†)^m fixes each P_k
  have hPow_fix : ∀ k : Fin m,
      ((transferMap (d := d) (D := D) K) ^ m) (P k) = P k :=
    adjointTransferMap_pow_fixes_cyclic_projection K P hcyclic
  -- Step 3: Adjoint blocked transfer map fixes P_k
  have hFix : ∀ k : Fin m,
      transferMap (d := blockPhysDim d m) (D := D)
        (fun i => (blockTensor A m i)ᴴ) (P k) = P k := by
    intro k
    rw [transferMap_adjoint_blocked_eq_pow A m (P k)]
    exact hPow_fix k
  -- Step 4: Blocked tensor is TP
  have hTP_blocked : ∑ i : Fin (blockPhysDim d m),
      (blockTensor A m i)ᴴ * blockTensor A m i = 1 :=
    leftCanonical_blockTensor (d := d) (D := D) (A := A) (L := m) hTP
  -- Step 5: Apply the CyclicSectors decomposition
  obtain ⟨dim, blocks, φ, hLC, hMPV_hTrace⟩ := exists_blockDecomp_of_adjoint_fixed_projections
    (blockTensor A m) P hPproj hPsum hTP_blocked hFix
  obtain ⟨hMPV, hTrace, hIntertwine, hMul, hStar⟩ := hMPV_hTrace
  -- Step 6: Derive commutation from the adjoint fix property
  have hComm : ∀ k (i : Fin (blockPhysDim d m)),
      P k * (blockTensor A m) i = (blockTensor A m) i * P k := by
    intro k i
    exact commutes_letters_of_adjoint_fixed_projection
      (blockTensor A m) hTP_blocked (hP := hPproj k) (hFix := hFix k) i
  -- Step 7: Nondegeneracy — all projections are nonzero, hence all sector dimensions > 0
  have hNondeg : ∀ k, dim k ≠ 0 := by
    -- First: all projections are nonzero (cyclic propagation from hcyclic + hPsum)
    have hPne : ∀ k, P k ≠ 0 := by
      by_contra! h
      obtain ⟨k₀, hk₀⟩ := h
      -- If P(j+1) = 0 then P(j) = E†(P(j+1)) = E†(0) = 0
      have hback : ∀ j : Fin m, P (j + 1) = 0 → P j = 0 := fun j hj => by
        simpa [hj] using (hcyclic j).symm
      -- Every j is zero: induct on backward distance (k₀ - j).val
      have hall : ∀ j : Fin m, P j = 0 := by
        suffices hs : ∀ n : ℕ, n < m → ∀ j : Fin m,
            (k₀ - j).val = n → P j = 0 by
          intro j; exact hs _ (k₀ - j).isLt j rfl
        intro n
        induction n with
        | zero =>
          intro _ j hj
          have : k₀ - j = 0 := by
            ext; simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod,
              Fin.val_eq_zero_iff] at hj ⊢; exact hj
          have : k₀ = j := sub_eq_zero.mp this
          subst this; exact hk₀
        | succ n ih =>
          intro hd j hj
          apply hback j
          apply ih (by omega) (j + 1)
          have h_eq : k₀ - (j + 1) = (k₀ - j) - 1 := by abel
          rw [h_eq, Fin.val_sub_one_of_ne_zero (by intro h; simp [h] at hj)]
          omega
      -- Contradiction: ∑ P_k = 0 ≠ 1
      have hsum_zero : ∑ k, P k = 0 := Finset.sum_eq_zero fun k _ => hall k
      exact absurd hsum_zero (by rw [hPsum]; exact one_ne_zero)
    -- Second: dim k ≠ 0 follows from P k ≠ 0 via the trace relation
    intro k hk
    apply hPne k
    have h0 := hTrace k 0 Fin.elim0
    simp only [mpv, coeff, List.ofFn_zero, evalWord_nil, Matrix.mul_one] at h0
    have htrace_zero : (P k).trace = 0 := by
      rw [← h0, Matrix.trace_one, Fintype.card_fin, hk, Nat.cast_zero]
    exact (isOrthogonalProjection_posSemidef (hPproj k)).trace_eq_zero_iff.mp htrace_zero
  exact ⟨dim, blocks, P, φ, hLC, hMPV, hPproj, hPsum, hcyclic, hComm, hTrace, hIntertwine,
    hMul, hStar, hNondeg⟩

end CyclicSectorRelation

/-!
## Derivation from MPS hypotheses

For an irreducible TP tensor, all channel-level hypotheses needed by
`exists_cyclic_sector_decomp_after_blocking` can be derived automatically:

1. `IsIrreducibleTensor A` → `IsIrreducibleMap (transferMap (fun i => (A i)ᴴ))`
2. TP + irreducible → ∃ ρ.PosDef fixed by `transferMap A` = `Kraus.adjointMap K`
3. `peripheral_eigenvalues_cyclic_structure` → `(m, γ, IsPrimitiveRoot γ m, periph = {γ^k})`
4. Feed all into `exists_cyclic_sector_decomp_after_blocking`
-/

section CyclicSectorFromMPS

open KadisonSchwarz

/-- **Derivation of cyclic sector decomposition from an irreducible TP tensor.**

For an irreducible TP tensor `A` with `0 < D`, there exists a period `m > 0`
such that after blocking by `m`, the blocked tensor admits a decomposition
into `m` left-canonical (TP) blocks via cyclic spectral projections.

This establishes the connection from the MPS-level hypotheses
(`IsIrreducibleTensor` + TP) to the channel-level cyclic decomposition,
deriving all intermediate hypotheses (`ρ.PosDef`, `Kraus.adjointMap` fixed
point, `IsIrreducibleMap`, peripheral spectrum structure) automatically via
`conjTranspose_kraus_setup`. -/
theorem exists_cyclic_sector_decomp_of_TP_of_isIrreducibleTensor
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : IsIrreducibleTensor A) :
    ∃ (m : ℕ) (_ : 0 < m)
      (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k)),
      (∀ k, ∑ i : Fin (blockPhysDim d m), (blocks k i)ᴴ * blocks k i = 1) ∧
      SameMPV₂ (blockTensor A m) (toTensorFromBlocks (μ := fun _ => 1) blocks) := by
  -- Use shared setup to get conjugate Kraus family and PosDef fixed point.
  obtain ⟨K, h_unitalK, hIrrK, ρ, hρ_pd, h_adjfix, rfl⟩ :=
    conjTranspose_kraus_setup A hTP hIrr
  -- Extract cyclic peripheral structure via
  -- `peripheral_eigenvalues_cyclic_structure` from `GroupStructure.lean`.
  obtain ⟨m, γ, hm_pos, hγ_prim, hperiph_set⟩ :=
    PeripheralSpectrum.peripheral_eigenvalues_cyclic_structure _ h_unitalK ρ hρ_pd h_adjfix hIrrK
  -- Convert set representation to range form.
  have hperiph_range :
      peripheralEigenvalues (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) =
        Set.range (fun j : Fin m => γ ^ (j : ℕ)) := by
    rw [hperiph_set]; ext x; simp [Set.mem_range, eq_comm]
  -- Apply exists_cyclic_sector_decomp_after_blocking.
  haveI : NeZero m := ⟨Nat.ne_of_gt hm_pos⟩
  obtain ⟨dim, blocks, _, _, hTP_blocks, hSame, _, _, _, _, _, _, _⟩ :=
    exists_cyclic_sector_decomp_after_blocking A hTP hIrr ρ hρ_pd h_adjfix hIrrK hγ_prim
      hperiph_range
  exact ⟨m, hm_pos, dim, blocks, hTP_blocks, hSame⟩

end CyclicSectorFromMPS

section SectorOrbitLift

open KadisonSchwarz

/-- If cyclic projections sum to `1`, then none of the summands can vanish. -/
private theorem cyclic_projection_nonzero_of_sum_one
    {m D : ℕ} [NeZero m] [NeZero D]
    {T : MatrixEnd D} {P : Fin m → MatrixAlg D}
    (hPsum : ∑ k : Fin m, P k = 1)
    (hCyclic : ∀ k : Fin m, T (P (k + 1)) = P k) :
    ∀ k, P k ≠ 0 :=
  cyclic_projection_ne_zero_of_sum_one hPsum hCyclic

/-- Each cyclic projection lies in the multiplicative domain of the one-step
adjoint transfer map. -/
theorem cyclic_projection_mem_multiplicativeDomain
    {d D m : ℕ} [NeZero D] [NeZero m]
    {A : MPSTensor d D}
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hcyclic :
      ∀ k : Fin m,
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k) :
    ∀ k : Fin m, P k ∈ KadisonSchwarz.multiplicativeDomain (fun i : Fin d => (A i)ᴴ) := by
  let K : Fin d → MatrixAlg D := fun i => (A i)ᴴ
  have hUnital : KadisonSchwarz.IsUnitalKraus (d := d) (D := D) K := by
    simpa [KadisonSchwarz.IsUnitalKraus, K] using hTP
  have hK_apply :
      ∀ X : MatrixAlg D,
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X = KadisonSchwarz.krausMap K X := by
    intro X
    simp [K, MPSTensor.transferMap_apply, KadisonSchwarz.krausMap]
  intro k
  have hPk_star : (P k)ᴴ = P k := (hPproj k).1.eq
  have hTPk_eq : transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) = P (k - 1) := by
    change transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) = P (k - 1)
    simpa [show k - 1 + 1 = k by abel] using hcyclic (k - 1)
  have hTPk_proj :
      IsOrthogonalProjection (transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k)) := by
    simpa [hTPk_eq] using hPproj (k - 1)
  have hRight :
      KadisonSchwarz.krausMap K (P k * (P k)ᴴ) =
        KadisonSchwarz.krausMap K (P k) * (KadisonSchwarz.krausMap K (P k))ᴴ := by
    calc
      KadisonSchwarz.krausMap K (P k * (P k)ᴴ)
          = transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k * (P k)ᴴ) := by
              rw [hK_apply]
      _ = transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) := by
            rw [hPk_star, (hPproj k).2]
      _ = transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) *
            (transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k))ᴴ := by
              rw [hTPk_proj.1.eq, hTPk_proj.2]
      _ = KadisonSchwarz.krausMap K (P k) * (KadisonSchwarz.krausMap K (P k))ᴴ := by
            rw [hK_apply]
  have hLeft :
      KadisonSchwarz.krausMap K ((P k)ᴴ * P k) =
        (KadisonSchwarz.krausMap K (P k))ᴴ * KadisonSchwarz.krausMap K (P k) := by
    calc
      KadisonSchwarz.krausMap K ((P k)ᴴ * P k)
          = transferMap (d := d) (D := D) (fun i => (A i)ᴴ) ((P k)ᴴ * P k) := by
              rw [hK_apply]
      _ = transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) := by
            rw [hPk_star, (hPproj k).2]
      _ = (transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k))ᴴ *
            transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) := by
              rw [hTPk_proj.1.eq, hTPk_proj.2]
      _ = (KadisonSchwarz.krausMap K (P k))ᴴ * KadisonSchwarz.krausMap K (P k) := by
            rw [hK_apply]
  exact ⟨
    (KadisonSchwarz.mem_rightMultiplicativeDomain_iff K hUnital (P k)).2 hRight,
    (KadisonSchwarz.mem_leftMultiplicativeDomain_iff K hUnital (P k)).2 hLeft⟩

/-- The adjoint transfer map is multiplicative on the left of a cyclic
projection. -/
theorem cyclic_projection_mul_left
    {d D m : ℕ} [NeZero D] [NeZero m]
    {A : MPSTensor d D}
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hcyclic :
      ∀ k : Fin m,
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k) :
    ∀ k : Fin m, ∀ X : MatrixAlg D,
      transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k * X) =
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) *
          transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X := by
  let K : Fin d → MatrixAlg D := fun i => (A i)ᴴ
  have hMulDomain := cyclic_projection_mem_multiplicativeDomain (A := A) hTP P hPproj hcyclic
  intro k X
  simpa [K, MPSTensor.transferMap_apply, KadisonSchwarz.krausMap] using
    KadisonSchwarz.krausMap_mul_right_of_mem_multiplicativeDomain (K := K) (hMulDomain k) X

/-- The adjoint transfer map is multiplicative on the right of a cyclic
projection. -/
theorem cyclic_projection_mul_right
    {d D m : ℕ} [NeZero D] [NeZero m]
    {A : MPSTensor d D}
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hcyclic :
      ∀ k : Fin m,
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k) :
    ∀ k : Fin m, ∀ X : MatrixAlg D,
      transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (X * P k) =
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X *
          transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) := by
  let K : Fin d → MatrixAlg D := fun i => (A i)ᴴ
  have hMulDomain := cyclic_projection_mem_multiplicativeDomain (A := A) hTP P hPproj hcyclic
  intro k X
  simpa [K, MPSTensor.transferMap_apply, KadisonSchwarz.krausMap] using
    KadisonSchwarz.krausMap_mul_left_of_mem_multiplicativeDomain (K := K) (hMulDomain k) X

private theorem compressedTensor_adjointTransferMap_primitive_and_irreducible_of_corner
    {r D n : ℕ} [NeZero n]
    (B : MPSTensor r D) (C : MPSTensor r n) (P : MatrixAlg D)
    (T : MatrixEnd D)
    (φ : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] cornerSubmodule P)
    (hT : transferMap (d := r) (D := D) (fun i => (B i)ᴴ) = T)
    (hPproj : IsOrthogonalProjection P)
    (hIntertwine :
      ∀ X : Matrix (Fin n) (Fin n) ℂ,
        (φ (transferMap (d := r) (D := n) (fun i => (C i)ᴴ) X)).1 =
          transferMap (d := r) (D := D) (fun i => (P * B i)ᴴ) ((φ X).1))
    (hMul : ∀ X Y : Matrix (Fin n) (Fin n) ℂ, (φ (X * Y)).1 = (φ X).1 * (φ Y).1)
    (hStar : ∀ X : Matrix (Fin n) (Fin n) ℂ, (φ Xᴴ).1 = ((φ X).1)ᴴ)
    (hInv : PreservesCorner P T)
    (hCornerPrim : _root_.IsPrimitive (cornerRestriction P T hInv))
    (hCornerIrr : IsIrreducibleOnCorner P T) :
    _root_.IsPrimitive (transferMap (d := r) (D := n) (fun i => (C i)ᴴ)) ∧
      IsIrreducibleMap (transferMap (d := r) (D := n) (fun i => (C i)ᴴ)) :=
  compressedTensor_adjointTransferMap_cornerBridge
    (B := B) (C := C) (P := P) (T := T) (φ := φ)
    hT hPproj hIntertwine hMul hStar hInv hCornerPrim hCornerIrr

/-- Transport corner primitivity and corner irreducibility of the blocked adjoint
transfer map to the compressed cyclic-sector tensors.

The only remaining input beyond the cyclic-sector decomposition data is the
corner irreducibility theorem for `((transferMap A†)^m)` on each projection
`P k`. In particular, this theorem isolates the orbit-sum / `hProjStep` part of
the non-periodic Gap §1 proof chain from the downstream compression-transport
step. -/
theorem primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking_of_cornerIrreducible
    {d D m : ℕ} [NeZero D] [NeZero m]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    {γ : ℂ}
    (hγprim : IsPrimitiveRoot γ m)
    (hperiph :
      peripheralEigenvalues (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) =
        Set.range (fun j : Fin m => γ ^ (j : ℕ)))
    {dim : Fin m → ℕ}
    (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (P : Fin m → MatrixAlg D)
    (φ : (k : Fin m) →
      Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k))
    (hPproj : ∀ k, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic :
      ∀ k : Fin m,
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
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
    (hNondeg : ∀ k, dim k ≠ 0)
    (hCornerIrr :
      ∀ k : Fin m,
        IsIrreducibleOnCorner
          (P k)
          ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m)) :
    ∀ u : Fin m,
      _root_.IsPrimitive (transferMap (d := blockPhysDim d m) (D := dim u) (blocks u)) ∧
        IsIrreducibleTensor (blocks u) := by
  let T : MatrixEnd D := transferMap (d := d) (D := D) (fun i => (A i)ᴴ)
  have hMulLeft := cyclic_projection_mul_left (A := A) (m := m) hTP P hPproj hcyclic
  have hMulRight := cyclic_projection_mul_right (A := A) (m := m) hTP P hPproj hcyclic
  have hPne : ∀ k : Fin m, P k ≠ 0 := cyclic_projection_nonzero_of_sum_one hPsum hcyclic
  intro u
  haveI : NeZero (dim u) := ⟨hNondeg u⟩
  let hInv : PreservesCorner (P u) (T ^ m) :=
    preserves_corner_pow_of_cyclic_decomp (T := T) P hPproj hPsum hcyclic hMulLeft hMulRight u
  have hCornerPrim : _root_.IsPrimitive (cornerRestriction (P u) (T ^ m) hInv) :=
    isPrimitive_restriction_of_cyclic_decomp (T := T)
      hγprim hperiph P hPproj hPsum hcyclic hMulLeft hMulRight hPne u
  have hTpow :
      transferMap (d := blockPhysDim d m) (D := D) (fun i => (blockTensor A m i)ᴴ) = T ^ m := by
    ext X : 1
    exact transferMap_adjoint_blocked_eq_pow A m X
  obtain ⟨hPrimAdj, hIrrAdj⟩ :=
    compressedTensor_adjointTransferMap_primitive_and_irreducible_of_corner
      (B := blockTensor A m) (C := blocks u) (P := P u) (T := T ^ m) (φ := φ u)
      hTpow (hPproj u) (hIntertwine u) (hMul u) (hStar u) hInv hCornerPrim (hCornerIrr u)
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

/-- Under the one-step projection-preservation hypothesis `hProjStep`, the cyclic
sector blocks produced after blocking are primitive and tensor-irreducible.

This combines the orbit-sum part of the argument via
`isIrreducibleOnCorner_of_cyclic_decomp_mps_of_projStep` and then applies the
compression transport theorem above. The residual non-periodic Gap §1 blocker is
therefore isolated exactly to the one-step `hProjStep` input. -/
theorem primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking_of_projStep
    {d D m : ℕ} [NeZero D] [NeZero m]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : IsIrreducibleTensor A)
    {γ : ℂ}
    (hγprim : IsPrimitiveRoot γ m)
    (hperiph :
      peripheralEigenvalues (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) =
        Set.range (fun j : Fin m => γ ^ (j : ℕ)))
    {dim : Fin m → ℕ}
    (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (P : Fin m → MatrixAlg D)
    (φ : (k : Fin m) →
      Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k))
    (hPproj : ∀ k, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic :
      ∀ k : Fin m,
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
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
    (hNondeg : ∀ k, dim k ≠ 0)
    (hProjStep :
      ∀ k : Fin m, ∀ X : MatrixAlg D,
        IsOrthogonalProjection X →
        X * P k = X →
        P k * X = X →
        IsOrthogonalProjection
          (transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X)) :
    ∀ u : Fin m,
      _root_.IsPrimitive (transferMap (d := blockPhysDim d m) (D := dim u) (blocks u)) ∧
        IsIrreducibleTensor (blocks u) := by
  let T : MatrixEnd D := transferMap (d := d) (D := D) (fun i => (A i)ᴴ)
  have hIrrAdj : IsIrreducibleMap T := by
    simpa [T] using
      isIrreducibleCP_transferMap_conjTranspose_of_isIrreducibleTensor (A := A) hIrr
  have hMulLeft := cyclic_projection_mul_left (A := A) (m := m) hTP P hPproj hcyclic
  have hMulRight := cyclic_projection_mul_right (A := A) (m := m) hTP P hPproj hcyclic
  have hCornerIrr :
      ∀ k : Fin m, IsIrreducibleOnCorner (P k) (T ^ m) := by
    intro k
    exact isIrreducibleOnCorner_of_cyclic_decomp_mps_of_projStep
      (A := A) (m := m) hIrrAdj hTP P hPproj hPsum hcyclic hMulLeft hMulRight hProjStep k
  exact primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking_of_cornerIrreducible
    A hTP hγprim hperiph blocks P φ hPproj hPsum hcyclic hIntertwine hMul hStar hNondeg
    hCornerIrr

/-- Under the structured fixed-point-algebra rigidity hypothesis
`SectorFixedPointAlgebraRigidity`, the cyclic sector blocks produced after
blocking are primitive and tensor-irreducible.

This reformulates the remaining orbit-sum obstruction as a single named
hypothesis, uses
`isIrreducibleOnCorner_of_cyclic_decomp_mps_of_sectorFixedPointAlgebraRigidity`
to obtain corner irreducibility of `((transferMap A†)^m)|_{P_k}`, and then
applies the compression transport theorem above. -/
theorem primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking_of_fixedAlgebraRigidity
    {d D m : ℕ} [NeZero D] [NeZero m]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : IsIrreducibleTensor A)
    {γ : ℂ}
    (hγprim : IsPrimitiveRoot γ m)
    (hperiph :
      peripheralEigenvalues (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) =
        Set.range (fun j : Fin m => γ ^ (j : ℕ)))
    {dim : Fin m → ℕ}
    (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (P : Fin m → MatrixAlg D)
    (φ : (k : Fin m) →
      Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k))
    (hPproj : ∀ k, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic :
      ∀ k : Fin m,
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
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
    (hNondeg : ∀ k, dim k ≠ 0)
    (hRigidity :
      SectorFixedPointAlgebraRigidity
        (D := D) (m := m)
        (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) P) :
    ∀ u : Fin m,
      _root_.IsPrimitive (transferMap (d := blockPhysDim d m) (D := dim u) (blocks u)) ∧
        IsIrreducibleTensor (blocks u) := by
  let T : MatrixEnd D := transferMap (d := d) (D := D) (fun i => (A i)ᴴ)
  have hIrrAdj : IsIrreducibleMap T := by
    simpa [T] using
      isIrreducibleCP_transferMap_conjTranspose_of_isIrreducibleTensor (A := A) hIrr
  have hMulLeft := cyclic_projection_mul_left (A := A) (m := m) hTP P hPproj hcyclic
  have hMulRight := cyclic_projection_mul_right (A := A) (m := m) hTP P hPproj hcyclic
  have hCornerIrr :
      ∀ k : Fin m, IsIrreducibleOnCorner (P k) (T ^ m) := by
    intro k
    exact isIrreducibleOnCorner_of_cyclic_decomp_mps_of_sectorFixedPointAlgebraRigidity
      (A := A) (m := m) hIrrAdj hTP P hPproj hPsum hcyclic hMulLeft hMulRight hRigidity k
  exact primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking_of_cornerIrreducible
    A hTP hγprim hperiph blocks P φ hPproj hPsum hcyclic hIntertwine hMul hStar hNondeg
    hCornerIrr

/-- If a blocked sector channel has only scalar adjoint fixed points, then any
`((transferMap A†)^m)`-fixed element supported on the corresponding cyclic
sector is already a scalar multiple of that sector projection. -/
private theorem sector_supported_pow_fixed_eq_smul_projection_of_scalarFixedPoints
    {d D m : ℕ} [NeZero D] [NeZero m]
    {A : MPSTensor d D}
    {dim : Fin m → ℕ}
    (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (P : Fin m → MatrixAlg D)
    (φ : (k : Fin m) →
      Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k))
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
    (hScalarFixed :
      ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        transferMap (d := blockPhysDim d m) (D := dim k)
            (fun i => (blocks k i)ᴴ) X = X →
          ∃ c : ℂ, X = c • 1)
    {k : Fin m} {X : MatrixAlg D}
    (hXP : X * P k = X)
    (hPX : P k * X = X)
    (hXfix :
      ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) X = X) :
    ∃ c : ℂ, X = c • P k := by
  let T : MatrixEnd D := transferMap (d := d) (D := D) (fun i => (A i)ᴴ)
  have hXcorner : P k * X * P k = X := by
    calc
      P k * X * P k = P k * (X * P k) := by simp [Matrix.mul_assoc]
      _ = P k * X := by rw [hXP]
      _ = X := hPX
  let Xcorner : cornerSubmodule (P k) := ⟨X, hXcorner⟩
  let X' : Matrix (Fin (dim k)) (Fin (dim k)) ℂ := (φ k).symm Xcorner
  have hφX' : (φ k X').1 = X := by
    exact congrArg Subtype.val (LinearEquiv.apply_symm_apply (φ k) Xcorner)
  have hPherm : (P k)ᴴ = P k := (hPproj k).1.eq
  have hCornerTransfer :
      transferMap (d := blockPhysDim d m) (D := D)
        (fun i => (P k * blockTensor A m i)ᴴ) X =
      (T ^ m) X := by
    calc
      transferMap (d := blockPhysDim d m) (D := D)
          (fun i => (P k * blockTensor A m i)ᴴ) X
          = transferMap (d := blockPhysDim d m) (D := D)
              (fun i => (blockTensor A m i)ᴴ) X := by
              simp only [transferMap_apply]
              refine Finset.sum_congr rfl ?_
              intro i _
              have hPBi : ((P k * blockTensor A m i)ᴴ) = (blockTensor A m i)ᴴ * P k := by
                rw [Matrix.conjTranspose_mul, hPherm]
              rw [hPBi]
              calc
                (blockTensor A m i)ᴴ * P k * X * ((blockTensor A m i)ᴴ * P k)ᴴ
                    = (blockTensor A m i)ᴴ * P k * X * (P k * blockTensor A m i) := by
                        simp [Matrix.conjTranspose_mul, hPherm]
                _ = (blockTensor A m i)ᴴ * (P k * X * P k) * blockTensor A m i := by
                        simp [Matrix.mul_assoc]
                -- keep the ᴴᴴ so the summand matches `transferMap K` with `K = (blockTensor …)ᴴ`
                _ = (blockTensor A m i)ᴴ * X * (blockTensor A m i)ᴴᴴ := by
                        simpa using congrArg
                          (fun Z => (blockTensor A m i)ᴴ * Z * (blockTensor A m i)ᴴᴴ) hXcorner
      _ = (T ^ m) X := by
            simpa [T] using transferMap_adjoint_blocked_eq_pow A m X
  have hX'fix :
      transferMap (d := blockPhysDim d m) (D := dim k)
        (fun i => (blocks k i)ᴴ) X' = X' := by
    apply (φ k).injective
    apply Subtype.ext
    change
      (φ k
          (transferMap (d := blockPhysDim d m) (D := dim k)
            (fun i => (blocks k i)ᴴ) X')).1 =
        (φ k X').1
    rw [hIntertwine k X', hφX']
    exact hCornerTransfer.trans hXfix
  obtain ⟨c, hc⟩ := hScalarFixed k X' hX'fix
  have hφ1_eq_P : (φ k 1).1 = P k := by
    have hPcorner : P k * P k * P k = P k := by
      rw [(hPproj k).2, (hPproj k).2]
    let Yinv : Matrix (Fin (dim k)) (Fin (dim k)) ℂ := (φ k).symm ⟨P k, hPcorner⟩
    have hφYinv : (φ k Yinv).1 = P k := by
      exact congrArg Subtype.val (LinearEquiv.apply_symm_apply (φ k) ⟨P k, hPcorner⟩)
    have hleft : (φ k 1).1 * P k = P k := by
      have hmul := hMul k 1 Yinv
      rw [one_mul, hφYinv] at hmul
      exact hmul.symm
    calc
      (φ k 1).1 = P k * (φ k 1).1 * P k := ((φ k 1).2).symm
      _ = P k * ((φ k 1).1 * P k) := by simp [Matrix.mul_assoc]
      _ = P k * P k := by rw [hleft]
      _ = P k := (hPproj k).2
  refine ⟨c, ?_⟩
  calc
    X = (φ k X').1 := hφX'.symm
    _ = (φ k (c • 1)).1 := by rw [hc]
    _ = c • (φ k 1).1 := by simp
    _ = c • P k := by rw [hφ1_eq_P]

/-- If each blocked sector channel has only scalar adjoint fixed points, then
its cyclic projections satisfy `SectorFixedPointAlgebraRigidity`.

This is the strongest currently available general route in the direction of
the scalar blocked fixed-point algebra result (see CPGSV21, Appendix A): once
the blocked fixed-point algebra is known to be scalar on all compressed sectors,
every `((transferMap A†)^m)`-fixed corner element is a scalar multiple of the
corresponding sector projection, so the one-step adjoint transition is
automatically multiplicative on the sector fixed-point algebra. -/
theorem sectorFixedPointAlgebraRigidity_of_cyclic_decomp_after_blocking_of_scalarBlockedFixedPoints
    {d D m : ℕ} [NeZero D] [NeZero m]
    (A : MPSTensor d D)
    {dim : Fin m → ℕ}
    (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (P : Fin m → MatrixAlg D)
    (φ : (k : Fin m) →
      Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k))
    (hPproj : ∀ k, IsOrthogonalProjection (P k))
    (hcyclic :
      ∀ k : Fin m,
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (hIntertwine :
      ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k (transferMap (d := blockPhysDim d m) (D := dim k)
            (fun i => (blocks k i)ᴴ) X)).1 =
          transferMap (d := blockPhysDim d m) (D := D)
            (fun i => (P k * blockTensor A m i)ᴴ) ((φ k X).1))
    (hMul :
      ∀ k (X Y : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k (X * Y)).1 = (φ k X).1 * (φ k Y).1)
    (hScalarFixed :
      ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        transferMap (d := blockPhysDim d m) (D := dim k)
            (fun i => (blocks k i)ᴴ) X = X →
          ∃ c : ℂ, X = c • 1) :
    SectorFixedPointAlgebraRigidity
      (D := D) (m := m)
      (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) P := by
  let T : MatrixEnd D := transferMap (d := d) (D := D) (fun i => (A i)ᴴ)
  change SectorFixedPointAlgebraRigidity (D := D) (m := m) T P
  intro k X Y hXP hPX hYP hPY hXfix hYfix
  obtain ⟨cX, hcX⟩ :=
    sector_supported_pow_fixed_eq_smul_projection_of_scalarFixedPoints
      (A := A) (blocks := blocks) (P := P) (φ := φ) hPproj hIntertwine hMul hScalarFixed
      hXP hPX (by simpa [T] using hXfix)
  obtain ⟨cY, hcY⟩ :=
    sector_supported_pow_fixed_eq_smul_projection_of_scalarFixedPoints
      (A := A) (blocks := blocks) (P := P) (φ := φ) hPproj hIntertwine hMul hScalarFixed
      hYP hPY (by simpa [T] using hYfix)
  have hTPk : T (P k) = P (k - 1) := by
    simpa [T, show k - 1 + 1 = k by abel] using hcyclic (k - 1)
  rw [hcX, hcY]
  calc
    T ((cX • P k) * (cY • P k)) = T ((cY * cX) • P k) := by
          simp [smul_smul, (hPproj k).2]
    _ = (cY * cX) • P (k - 1) := by rw [map_smul, hTPk]
    _ = (cX • P (k - 1)) * (cY • P (k - 1)) := by
          simp [smul_smul, (hPproj (k - 1)).2]
    _ = T (cX • P k) * T (cY • P k) := by
          simp only [map_smul, hTPk]

/-- Under the scalar blocked fixed-point-algebra hypothesis, the blocked cyclic
sectors are primitive and tensor-irreducible.

This combines the scalar blocked fixed-point algebra hypothesis with the
orbit-sum / corner-compression reduction: the paper-level remaining gap is now
concentrated in proving that the blocked sector adjoint fixed-point algebra is
scalar. Once that input is available, the present theorem derives
`SectorFixedPointAlgebraRigidity` and applies the orbit-sum / corner-compression
reduction from the fixed-algebra-rigidity sector-block theorem. -/
theorem primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking_of_scalarBlockedFixedPoints
    {d D m : ℕ} [NeZero D] [NeZero m]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : IsIrreducibleTensor A)
    {γ : ℂ}
    (hγprim : IsPrimitiveRoot γ m)
    (hperiph :
      peripheralEigenvalues (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) =
        Set.range (fun j : Fin m => γ ^ (j : ℕ)))
    {dim : Fin m → ℕ}
    (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (P : Fin m → MatrixAlg D)
    (φ : (k : Fin m) →
      Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k))
    (hPproj : ∀ k, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic :
      ∀ k : Fin m,
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
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
    (hNondeg : ∀ k, dim k ≠ 0)
    (hScalarFixed :
      ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        transferMap (d := blockPhysDim d m) (D := dim k)
            (fun i => (blocks k i)ᴴ) X = X →
          ∃ c : ℂ, X = c • 1) :
    ∀ u : Fin m,
      _root_.IsPrimitive (transferMap (d := blockPhysDim d m) (D := dim u) (blocks u)) ∧
        IsIrreducibleTensor (blocks u) := by
  have hRigidity :=
    sectorFixedPointAlgebraRigidity_of_cyclic_decomp_after_blocking_of_scalarBlockedFixedPoints
      (A := A) (blocks := blocks) (P := P) (φ := φ) hPproj hcyclic hIntertwine hMul
      hScalarFixed
  exact
    primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking_of_fixedAlgebraRigidity
      A hTP hIrr hγprim hperiph blocks P φ hPproj hPsum hcyclic hIntertwine hMul hStar
      hNondeg hRigidity

/-- Unconditional cyclic-sector block primitivity and irreducibility after blocking.

This uses `isIrreducibleOnCorner_of_cyclic_decomp_mps`, so the older
projection-step and fixed-point-algebra rigidity assumptions are no longer needed
once the ambient tensor is irreducible and trace-preserving. -/
theorem primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking
    {d D m : ℕ} [NeZero D] [NeZero m]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : IsIrreducibleTensor A)
    {γ : ℂ}
    (hγprim : IsPrimitiveRoot γ m)
    (hperiph :
      peripheralEigenvalues (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) =
        Set.range (fun j : Fin m => γ ^ (j : ℕ)))
    {dim : Fin m → ℕ}
    (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (P : Fin m → MatrixAlg D)
    (φ : (k : Fin m) →
      Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k))
    (hPproj : ∀ k, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic :
      ∀ k : Fin m,
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
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
    (hNondeg : ∀ k, dim k ≠ 0) :
    ∀ u : Fin m,
      _root_.IsPrimitive (transferMap (d := blockPhysDim d m) (D := dim u) (blocks u)) ∧
        IsIrreducibleTensor (blocks u) := by
  let T : MatrixEnd D := transferMap (d := d) (D := D) (fun i => (A i)ᴴ)
  have hIrrAdj : IsIrreducibleMap T := by
    simpa [T] using
      isIrreducibleCP_transferMap_conjTranspose_of_isIrreducibleTensor (A := A) hIrr
  have hMulLeft := cyclic_projection_mul_left (A := A) (m := m) hTP P hPproj hcyclic
  have hMulRight := cyclic_projection_mul_right (A := A) (m := m) hTP P hPproj hcyclic
  have hCornerIrr :
      ∀ k : Fin m, IsIrreducibleOnCorner (P k) (T ^ m) := by
    intro k
    exact isIrreducibleOnCorner_of_cyclic_decomp_mps
      (A := A) (m := m) hIrrAdj hTP P hPproj hPsum hcyclic hMulLeft hMulRight k
  exact primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking_of_cornerIrreducible
    A hTP hγprim hperiph blocks P φ hPproj hPsum hcyclic hIntertwine hMul hStar hNondeg
    hCornerIrr

/-- Cyclic sector decomposition with primitive and tensor-irreducible sector blocks.

This strengthens `exists_cyclic_sector_decomp_of_TP_of_isIrreducibleTensor` by
exposing the primitive and irreducible conclusions already available from the
unconditional sector-orbit lift. It is the one-block result used in the later
multi-block construction before the sectors of all live blocks are flattened to
a common period. -/
theorem exists_primitive_irreducible_cyclic_sector_decomp_of_TP_of_isIrreducibleTensor
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : IsIrreducibleTensor A) :
    ∃ (m : ℕ) (_ : 0 < m)
      (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k)),
      (∀ k, ∑ i : Fin (blockPhysDim d m), (blocks k i)ᴴ * blocks k i = 1) ∧
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (d := blockPhysDim d m) (μ := fun _ : Fin m => (1 : ℂ)) blocks) ∧
      (∀ k, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d m) (D := dim k) (blocks k))) ∧
      (∀ k, IsIrreducibleTensor (blocks k)) ∧
      (∀ k, 0 < dim k) := by
  -- Use shared setup to get conjugate Kraus data and the cyclic peripheral structure.
  obtain ⟨K, h_unitalK, hIrrK, ρ, hρ_pd, h_adjfix, rfl⟩ :=
    conjTranspose_kraus_setup A hTP hIrr
  obtain ⟨m, γ, hm_pos, hγ_prim, hperiph_set⟩ :=
    PeripheralSpectrum.peripheral_eigenvalues_cyclic_structure _ h_unitalK ρ hρ_pd h_adjfix hIrrK
  have hperiph_range :
      peripheralEigenvalues (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) =
        Set.range (fun j : Fin m => γ ^ (j : ℕ)) := by
    rw [hperiph_set]
    ext x
    simp [Set.mem_range, eq_comm]
  haveI : NeZero m := ⟨Nat.ne_of_gt hm_pos⟩
  obtain ⟨dim, blocks, P, φ, hTP_blocks, hSame, hPproj, hPsum, hcyclic, _hComm,
      _hTrace, hIntertwine, hMul, hStar, hNondeg⟩ :=
    exists_cyclic_sector_decomp_after_blocking A hTP hIrr ρ hρ_pd h_adjfix hIrrK hγ_prim
      hperiph_range
  have hPrimIrr : ∀ u : Fin m,
      _root_.IsPrimitive (transferMap (d := blockPhysDim d m) (D := dim u) (blocks u)) ∧
        IsIrreducibleTensor (blocks u) :=
    primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking
      A hTP hIrr hγ_prim hperiph_range blocks P φ hPproj hPsum hcyclic hIntertwine hMul hStar
      hNondeg
  refine ⟨m, hm_pos, dim, blocks, hTP_blocks, hSame, ?_, ?_, ?_⟩
  · intro k
    exact (hPrimIrr k).1
  · intro k
    exact (hPrimIrr k).2
  · intro k
    exact Nat.pos_of_ne_zero (hNondeg k)

/-- A one-block period-removal package with primitive irreducible sectors.

`HasPrimitiveIrreducibleCyclicSectors A` means that some positive period `m`
removes the cyclic peripheral structure of `A`: the blocked tensor `A^[m]` is
represented by unit-weight sector blocks, each of which is trace-preserving, has
primitive transfer map, is tensor-irreducible, and has positive bond dimension.
The later common-refinement or Wielandt/injectivity blocking length is deliberately
not part of this predicate. -/
def HasPrimitiveIrreducibleCyclicSectors {d D : ℕ} (A : MPSTensor d D) : Prop :=
  ∃ (m : ℕ), 0 < m ∧
  ∃ (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k)),
    (∀ k, ∑ i : Fin (blockPhysDim d m), (blocks k i)ᴴ * blocks k i = 1) ∧
    SameMPV₂ (blockTensor (d := d) (D := D) A m)
      (toTensorFromBlocks (d := blockPhysDim d m) (μ := fun _ : Fin m => (1 : ℂ)) blocks) ∧
    (∀ k, _root_.IsPrimitive
      (transferMap (d := blockPhysDim d m) (D := dim k) (blocks k))) ∧
    (∀ k, IsIrreducibleTensor (blocks k)) ∧
    (∀ k, 0 < dim k)

/-- Trace-preserving irreducible tensors admit primitive irreducible cyclic sectors. -/
theorem hasPrimitiveIrreducibleCyclicSectors_of_TP_of_isIrreducibleTensor
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : IsIrreducibleTensor A) :
    HasPrimitiveIrreducibleCyclicSectors A := by
  simpa [HasPrimitiveIrreducibleCyclicSectors] using
    exists_primitive_irreducible_cyclic_sector_decomp_of_TP_of_isIrreducibleTensor
      (d := d) (D := D) A hTP hIrr

/-- Common reblocking data for the cyclic sectors of a finite live-block family.

For each original live block, `period k` is the period-removal length produced by
cyclic-sector decomposition, while `extra k` is the later positive blocking length
that moves all sectors to the single physical alphabet `blockPhysDim d p`.  The
flattened family `flatBlocks` is indexed by the finite type
`Fin (∑ k, period k)`, using `finSigmaFinEquiv` to identify an index with an
original live block and one of its cyclic sectors.

The field `nested_same` records the checked MPV compatibility condition available
at this stage: the iterated blocked live block is MPV-equivalent to the corresponding
unit-weight reblocked cyclic sectors, all at the common physical dimension.  The
remaining work for issue #969 is the one-shot iterated-blocking identification
and the weighted direct-sum flattening across the original live-block weights. -/
structure CommonBlockedCyclicSectorFamily {d r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k)) where
  /-- The common physical blocking length. -/
  p : ℕ
  /-- The common physical blocking length is positive. -/
  p_pos : 0 < p
  /-- The period-removal length of each original live block. -/
  period : Fin r → ℕ
  /-- Every period-removal length is positive. -/
  period_pos : ∀ k, 0 < period k
  /-- The later reblocking length applied after period removal. -/
  extra : Fin r → ℕ
  /-- Every later reblocking length is positive. -/
  extra_pos : ∀ k, 0 < extra k
  /-- The common length factors as period removal followed by later reblocking. -/
  p_eq_period_mul_extra : ∀ k, p = period k * extra k
  /-- Bond dimensions of the cyclic sector blocks before later reblocking. -/
  sectorDim : (k : Fin r) → Fin (period k) → ℕ
  /-- Cyclic sector blocks before later reblocking. -/
  sectorBlocks : (k : Fin r) → (s : Fin (period k)) →
    MPSTensor (blockPhysDim d (period k)) (sectorDim k s)
  /-- The sector blocks are trace-preserving before later reblocking. -/
  sector_tp : ∀ k s,
    ∑ i : Fin (blockPhysDim d (period k)), (sectorBlocks k s i)ᴴ * sectorBlocks k s i = 1
  /-- Each period-blocked live block is represented by its unit-weight cyclic sectors. -/
  sector_same : ∀ k,
    SameMPV₂ (blockTensor (d := d) (D := dim k) (blocks k) (period k))
      (toTensorFromBlocks (d := blockPhysDim d (period k))
        (μ := fun _ : Fin (period k) => (1 : ℂ)) (sectorBlocks k))
  /-- The sector transfer maps are primitive before later reblocking. -/
  sector_primitive : ∀ k s,
    _root_.IsPrimitive
      (transferMap (d := blockPhysDim d (period k)) (D := sectorDim k s)
        (sectorBlocks k s))
  /-- The sector blocks are tensor-irreducible before later reblocking. -/
  sector_irreducible : ∀ k s, IsIrreducibleTensor (sectorBlocks k s)
  /-- The sector bond dimensions are positive before later reblocking. -/
  sector_dim_pos : ∀ k s, 0 < sectorDim k s
  /-- The iterated blocked physical alphabet is propositionally the common alphabet. -/
  blockPhysDim_nested_eq : ∀ k,
    blockPhysDim (blockPhysDim d (period k)) (extra k) = blockPhysDim d p
  /-- Bond dimensions of the flattened common-alphabet sector family. -/
  flatDim : Fin (∑ k : Fin r, period k) → ℕ
  /-- The flattened common-alphabet sector family. -/
  flatBlocks : (x : Fin (∑ k : Fin r, period k)) → MPSTensor (blockPhysDim d p) (flatDim x)
  /-- Flattened common-alphabet sectors are trace-preserving. -/
  flat_tp : ∀ x,
    ∑ i : Fin (blockPhysDim d p), (flatBlocks x i)ᴴ * flatBlocks x i = 1
  /-- Flattened common-alphabet sectors have primitive transfer maps. -/
  flat_primitive : ∀ x,
    _root_.IsPrimitive (transferMap (d := blockPhysDim d p) (D := flatDim x) (flatBlocks x))
  /-- Flattened common-alphabet sectors are tensor-irreducible. -/
  flat_irreducible : ∀ x, IsIrreducibleTensor (flatBlocks x)
  /-- Flattened common-alphabet sectors have positive bond dimensions. -/
  flat_dim_pos : ∀ x, 0 < flatDim x
  /-- The checked MPV compatibility condition for each original live block
  after later reblocking. -/
  nested_same : ∀ k,
    SameMPV₂
      (cast (congr_arg (fun d' => MPSTensor d' (dim k)) (blockPhysDim_nested_eq k))
        (blockTensor (d := blockPhysDim d (period k)) (D := dim k)
          (blockTensor (d := d) (D := dim k) (blocks k) (period k)) (extra k)))
      (toTensorFromBlocks (d := blockPhysDim d p)
        (μ := fun _ : Fin (period k) => (1 : ℂ))
        (fun s => cast
          (congr_arg (fun d' => MPSTensor d' (sectorDim k s)) (blockPhysDim_nested_eq k))
          (blockTensor (d := blockPhysDim d (period k)) (D := sectorDim k s)
            (sectorBlocks k s) (extra k))))

namespace CommonBlockedCyclicSectorFamily

variable {d r : ℕ} {dim : Fin r → ℕ}
variable {blocks : (k : Fin r) → MPSTensor d (dim k)}

/-- Decode a flattened common-sector index as an original live block and a cyclic sector. -/
noncomputable def flatKey (F : CommonBlockedCyclicSectorFamily blocks)
    (x : Fin (∑ k : Fin r, F.period k)) : (k : Fin r) × Fin (F.period k) :=
  finSigmaFinEquiv.symm x

/-- The flattened sectors produced by `CommonBlockedCyclicSectorFamily` carry unit weights. -/
def flatWeight (F : CommonBlockedCyclicSectorFamily blocks) :
    Fin (∑ k : Fin r, F.period k) → ℂ :=
  fun _ => 1

/-- The unit weights of the flattened common-alphabet sectors are nonzero. -/
theorem flatWeight_ne_zero (F : CommonBlockedCyclicSectorFamily blocks)
    (x : Fin (∑ k : Fin r, F.period k)) : F.flatWeight x ≠ 0 := by
  simp [flatWeight]

/-- The common-alphabet sector obtained by later reblocking one cyclic sector. -/
noncomputable def commonSectorBlock (F : CommonBlockedCyclicSectorFamily blocks)
    (k : Fin r) (s : Fin (F.period k)) :
    MPSTensor (blockPhysDim d F.p) (F.sectorDim k s) :=
  cast (congr_arg (fun d' => MPSTensor d' (F.sectorDim k s))
      (F.blockPhysDim_nested_eq k))
    (blockTensor (d := blockPhysDim d (F.period k)) (D := F.sectorDim k s)
      (F.sectorBlocks k s) (F.extra k))

/-- Bond dimensions of the derived flattened common-sector family. -/
noncomputable def commonFlatDim (F : CommonBlockedCyclicSectorFamily blocks) :
    Fin (∑ k : Fin r, F.period k) → ℕ :=
  fun x =>
    let y := F.flatKey x
    F.sectorDim y.1 y.2

/-- The derived flattened common-sector family, indexed by `Fin (∑ k, F.period k)`. -/
noncomputable def commonFlatBlocks (F : CommonBlockedCyclicSectorFamily blocks)
    (x : Fin (∑ k : Fin r, F.period k)) :
    MPSTensor (blockPhysDim d F.p) (F.commonFlatDim x) :=
  let y := F.flatKey x
  show MPSTensor (blockPhysDim d F.p) (F.sectorDim y.1 y.2) from
    F.commonSectorBlock y.1 y.2

/-- The common-alphabet sector tensor for one original live block. -/
noncomputable def commonSectorTensor (F : CommonBlockedCyclicSectorFamily blocks)
    (k : Fin r) : MPSTensor (blockPhysDim d F.p) (∑ s : Fin (F.period k), F.sectorDim k s) :=
  toTensorFromBlocks (d := blockPhysDim d F.p)
    (μ := fun _ : Fin (F.period k) => (1 : ℂ)) (F.commonSectorBlock k)

/-- A one-shot common-blocked live block with the explicit physical-label relabeling
from iterated blocking to the one-shot blocked alphabet. -/
noncomputable def oneShotReindexedBlock (F : CommonBlockedCyclicSectorFamily blocks)
    (k : Fin r) : MPSTensor (blockPhysDim d F.p) (dim k) :=
  cast (congr_arg (fun d' => MPSTensor d' (dim k)) (F.blockPhysDim_nested_eq k))
    (reindexPhysical (iteratedBlockIndex d (F.period k) (F.extra k))
      (blockTensor (d := d) (D := dim k) (blocks k) (F.period k * F.extra k)))

/-- The derived flattened sector weights obtained from the original live weights after
blocking by the common length. -/
noncomputable def commonFlatWeight (F : CommonBlockedCyclicSectorFamily blocks)
    (μ : Fin r → ℂ) : Fin (∑ k : Fin r, F.period k) → ℂ :=
  fun x => (μ (F.flatKey x).1) ^ F.p

/-- Transported live weights remain nonzero after common blocking.

This named form records the per-live-block weight transport used before flattening;
`commonFlatWeight_ne_zero` is the corresponding statement after passing to flattened
sector indices. -/
theorem commonBlockWeight_ne_zero (F : CommonBlockedCyclicSectorFamily blocks)
    (μ : Fin r → ℂ) (hμ : ∀ k, μ k ≠ 0) (k : Fin r) :
    (μ k) ^ F.p ≠ 0 :=
  pow_ne_zero F.p (hμ k)

/-- Flattened sector weights remain nonzero after common blocking. -/
theorem commonFlatWeight_ne_zero (F : CommonBlockedCyclicSectorFamily blocks)
    (μ : Fin r → ℂ) (hμ : ∀ k, μ k ≠ 0)
    (x : Fin (∑ k : Fin r, F.period k)) : F.commonFlatWeight μ x ≠ 0 :=
  pow_ne_zero F.p (hμ (F.flatKey x).1)

private theorem commonSectorBlock_structural (F : CommonBlockedCyclicSectorFamily blocks)
    (k : Fin r) (s : Fin (F.period k)) :
    (∑ i : Fin (blockPhysDim d F.p),
      (F.commonSectorBlock k s i)ᴴ * F.commonSectorBlock k s i = 1) ∧
    _root_.IsPrimitive
      (transferMap (d := blockPhysDim d F.p) (D := F.sectorDim k s)
        (F.commonSectorBlock k s)) ∧
    IsIrreducibleTensor (F.commonSectorBlock k s) := by
  haveI : NeZero (F.sectorDim k s) := ⟨Nat.ne_of_gt (F.sector_dim_pos k s)⟩
  have hExtra := tp_primitive_irreducible_extra_blocking
    (d := blockPhysDim d (F.period k)) (D := F.sectorDim k s)
    (A := F.sectorBlocks k s) (F.sector_tp k s) (F.sector_primitive k s)
    (F.sector_irreducible k s) (hk := F.extra_pos k)
  refine ⟨?_, ?_, ?_⟩
  · have hcast := (leftCanonical_cast_physDim (F.blockPhysDim_nested_eq k)
      (A := blockTensor (d := blockPhysDim d (F.period k)) (D := F.sectorDim k s)
        (F.sectorBlocks k s) (F.extra k))).2 hExtra.1
    simpa [commonSectorBlock] using hcast
  · have hcast := (isPrimitive_transferMap_cast_physDim (F.blockPhysDim_nested_eq k)
      (A := blockTensor (d := blockPhysDim d (F.period k)) (D := F.sectorDim k s)
        (F.sectorBlocks k s) (F.extra k))).2 hExtra.2.1
    simpa [commonSectorBlock] using hcast
  · have hcast := (isIrreducibleTensor_cast_physDim (F.blockPhysDim_nested_eq k)
      (A := blockTensor (d := blockPhysDim d (F.period k)) (D := F.sectorDim k s)
        (F.sectorBlocks k s) (F.extra k))).2 hExtra.2.2
    simpa [commonSectorBlock] using hcast

/-- Derived common-alphabet sectors are trace-preserving. -/
theorem commonSectorBlock_tp (F : CommonBlockedCyclicSectorFamily blocks)
    (k : Fin r) (s : Fin (F.period k)) :
    ∑ i : Fin (blockPhysDim d F.p),
      (F.commonSectorBlock k s i)ᴴ * F.commonSectorBlock k s i = 1 :=
  (commonSectorBlock_structural F k s).1

/-- Derived common-alphabet sectors have primitive transfer maps. -/
theorem commonSectorBlock_primitive (F : CommonBlockedCyclicSectorFamily blocks)
    (k : Fin r) (s : Fin (F.period k)) :
    _root_.IsPrimitive
      (transferMap (d := blockPhysDim d F.p) (D := F.sectorDim k s)
        (F.commonSectorBlock k s)) :=
  (commonSectorBlock_structural F k s).2.1

/-- Derived common-alphabet sectors are tensor-irreducible. -/
theorem commonSectorBlock_irreducible (F : CommonBlockedCyclicSectorFamily blocks)
    (k : Fin r) (s : Fin (F.period k)) : IsIrreducibleTensor (F.commonSectorBlock k s) :=
  (commonSectorBlock_structural F k s).2.2

/-- Derived common-alphabet sectors have positive bond dimensions. -/
theorem commonSectorBlock_dim_pos (F : CommonBlockedCyclicSectorFamily blocks)
    (k : Fin r) (s : Fin (F.period k)) : 0 < F.sectorDim k s :=
  F.sector_dim_pos k s

/-- The derived flattened common-sector family is trace-preserving. -/
theorem commonFlatBlocks_tp (F : CommonBlockedCyclicSectorFamily blocks)
    (x : Fin (∑ k : Fin r, F.period k)) :
    ∑ i : Fin (blockPhysDim d F.p),
      (F.commonFlatBlocks x i)ᴴ * F.commonFlatBlocks x i = 1 := by
  let y := F.flatKey x
  simpa [commonFlatBlocks, commonFlatDim, y] using F.commonSectorBlock_tp y.1 y.2

/-- The derived flattened common-sector family has primitive transfer maps. -/
theorem commonFlatBlocks_primitive (F : CommonBlockedCyclicSectorFamily blocks)
    (x : Fin (∑ k : Fin r, F.period k)) :
    _root_.IsPrimitive
      (transferMap (d := blockPhysDim d F.p) (D := F.commonFlatDim x)
        (F.commonFlatBlocks x)) := by
  let y := F.flatKey x
  simpa [commonFlatBlocks, commonFlatDim, y] using F.commonSectorBlock_primitive y.1 y.2

/-- The derived flattened common-sector family is tensor-irreducible. -/
theorem commonFlatBlocks_irreducible (F : CommonBlockedCyclicSectorFamily blocks)
    (x : Fin (∑ k : Fin r, F.period k)) : IsIrreducibleTensor (F.commonFlatBlocks x) := by
  let y := F.flatKey x
  simpa [commonFlatBlocks, commonFlatDim, y] using F.commonSectorBlock_irreducible y.1 y.2

/-- The derived flattened common-sector family has positive bond dimensions. -/
theorem commonFlatDim_pos (F : CommonBlockedCyclicSectorFamily blocks)
    (x : Fin (∑ k : Fin r, F.period k)) : 0 < F.commonFlatDim x := by
  let y := F.flatKey x
  simpa [commonFlatDim, y] using F.commonSectorBlock_dim_pos y.1 y.2

/-- Iterated blocking of a live block is the relabeled one-shot common block. -/
theorem nestedBlock_sameMPV₂_oneShotReindexedBlock
    (F : CommonBlockedCyclicSectorFamily blocks) (k : Fin r) :
    SameMPV₂
      (cast (congr_arg (fun d' => MPSTensor d' (dim k)) (F.blockPhysDim_nested_eq k))
        (blockTensor (d := blockPhysDim d (F.period k)) (D := dim k)
          (blockTensor (d := d) (D := dim k) (blocks k) (F.period k)) (F.extra k)))
      (F.oneShotReindexedBlock k) := by
  have h := sameMPV₂_blockTensor_blockTensor_mul_reindex
    (d := d) (D := dim k) (A := blocks k) (m := F.period k) (n := F.extra k)
  exact (sameMPV₂_cast_physDim (F.blockPhysDim_nested_eq k)
    (A := blockTensor (d := blockPhysDim d (F.period k)) (D := dim k)
      (blockTensor (d := d) (D := dim k) (blocks k) (F.period k)) (F.extra k))
    (B := reindexPhysical (iteratedBlockIndex d (F.period k) (F.extra k))
      (blockTensor (d := d) (D := dim k) (blocks k) (F.period k * F.extra k)))).2 h

/-- A one-shot relabeled live block is represented by its common-alphabet cyclic sectors. -/
theorem oneShotReindexedBlock_sameMPV₂_commonSectorTensor
    (F : CommonBlockedCyclicSectorFamily blocks) (k : Fin r) :
    SameMPV₂ (F.oneShotReindexedBlock k) (F.commonSectorTensor k) := by
  intro N σ
  calc
    mpv (F.oneShotReindexedBlock k) σ =
        mpv (cast (congr_arg (fun d' => MPSTensor d' (dim k)) (F.blockPhysDim_nested_eq k))
          (blockTensor (d := blockPhysDim d (F.period k)) (D := dim k)
            (blockTensor (d := d) (D := dim k) (blocks k) (F.period k)) (F.extra k))) σ :=
      ((F.nestedBlock_sameMPV₂_oneShotReindexedBlock k) N σ).symm
    _ = mpv (F.commonSectorTensor k) σ := by
      simpa [commonSectorTensor, commonSectorBlock] using F.nested_same k N σ

/-- Weighted live blocks with explicit one-shot relabelings flatten to the common-sector family. -/
theorem sameMPV₂_weightedOneShotReindexedBlock_commonFlat
    (F : CommonBlockedCyclicSectorFamily blocks) (μ : Fin r → ℂ) :
    SameMPV₂
      (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := fun k : Fin r => (μ k) ^ F.p) (F.oneShotReindexedBlock))
      (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := F.commonFlatWeight μ) (F.commonFlatBlocks)) := by
  intro N σ
  let gSigma : ((k : Fin r) × Fin (F.period k)) → ℂ := fun y =>
    ((μ y.1) ^ F.p) ^ N * mpv (F.commonSectorBlock y.1 y.2) σ
  calc
    mpv (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := fun k : Fin r => (μ k) ^ F.p) (F.oneShotReindexedBlock)) σ
        = ∑ k : Fin r, ((μ k) ^ F.p) ^ N •
            mpv (F.oneShotReindexedBlock k) σ :=
          mpv_toTensorFromBlocks_eq_sum (fun k : Fin r => (μ k) ^ F.p)
            (F.oneShotReindexedBlock) σ
    _ = ∑ k : Fin r, ((μ k) ^ F.p) ^ N • mpv (F.commonSectorTensor k) σ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [F.oneShotReindexedBlock_sameMPV₂_commonSectorTensor k N σ]
    _ = ∑ k : Fin r, ∑ s : Fin (F.period k),
          ((μ k) ^ F.p) ^ N • mpv (F.commonSectorBlock k s) σ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          change ((μ k) ^ F.p) ^ N •
              mpv (toTensorFromBlocks (d := blockPhysDim d F.p)
                (fun _ : Fin (F.period k) => (1 : ℂ)) (F.commonSectorBlock k)) σ =
            ∑ s : Fin (F.period k),
              ((μ k) ^ F.p) ^ N • mpv (F.commonSectorBlock k s) σ
          rw [mpv_toTensorFromBlocks_eq_sum
            (fun _ : Fin (F.period k) => (1 : ℂ)) (F.commonSectorBlock k) σ]
          simp [smul_eq_mul, Finset.mul_sum]
    _ = ∑ y : ((k : Fin r) × Fin (F.period k)),
          ((μ y.1) ^ F.p) ^ N • mpv (F.commonSectorBlock y.1 y.2) σ := by
          exact (Fintype.sum_sigma'
            (fun k s => ((μ k) ^ F.p) ^ N • mpv (F.commonSectorBlock k s) σ)).symm
    _ = ∑ x : Fin (∑ k : Fin r, F.period k),
          (F.commonFlatWeight μ x) ^ N • mpv (F.commonFlatBlocks x) σ := by
          have h := (Equiv.sum_comp
            (finSigmaFinEquiv.symm :
              Fin (∑ k : Fin r, F.period k) ≃ ((k : Fin r) × Fin (F.period k)))
            gSigma).symm
          simpa [gSigma, commonFlatWeight, commonFlatBlocks, commonFlatDim, flatKey,
            smul_eq_mul] using h
    _ = mpv (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := F.commonFlatWeight μ) (F.commonFlatBlocks)) σ := by
          exact (mpv_toTensorFromBlocks_eq_sum (F.commonFlatWeight μ) (F.commonFlatBlocks) σ).symm

/-- If the canonical one-shot blocked live blocks agree with the explicitly relabeled
blocks, then the weighted live tensor agrees with the derived common-sector family.

The hypothesis isolates the remaining physical-label compatibility step: `oneShotReindexedBlock`
uses the iterated-blocking relabeling supplied by `iteratedBlockIndex`, while the canonical
blocked live tensor uses the ambient blocked alphabet directly. -/
theorem sameMPV₂_weightedCanonicalBlock_commonFlat_of_oneShot
    (F : CommonBlockedCyclicSectorFamily blocks) (μ : Fin r → ℂ)
    (hLabel : SameMPV₂
      (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := fun k : Fin r => (μ k) ^ F.p)
        (fun k => blockTensor (d := d) (D := dim k) (blocks k) F.p))
      (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := fun k : Fin r => (μ k) ^ F.p) F.oneShotReindexedBlock)) :
    SameMPV₂
      (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := fun k : Fin r => (μ k) ^ F.p)
        (fun k => blockTensor (d := d) (D := dim k) (blocks k) F.p))
      (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := F.commonFlatWeight μ) F.commonFlatBlocks) := by
  intro N σ
  calc
    mpv (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := fun k : Fin r => (μ k) ^ F.p)
        (fun k => blockTensor (d := d) (D := dim k) (blocks k) F.p)) σ
        = mpv (toTensorFromBlocks (d := blockPhysDim d F.p)
          (μ := fun k : Fin r => (μ k) ^ F.p) F.oneShotReindexedBlock) σ :=
            hLabel N σ
    _ = mpv (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := F.commonFlatWeight μ) F.commonFlatBlocks) σ :=
          F.sameMPV₂_weightedOneShotReindexedBlock_commonFlat μ N σ

end CommonBlockedCyclicSectorFamily

/-- A finite family of live blocks with per-block primitive irreducible cyclic sectors
admits a prescribed common physical blocking length, provided that the prescribed
length is a positive multiple of every period-removal length.

This variant is used for two-sided endpoints: one first chooses a common multiple
of the period-removal lengths on both sides, then builds each one-sided cyclic
sector family at that same physical length. -/
theorem exists_commonBlockedCyclicSectorFamily_of_commonMultiple
    {d r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hcyc : ∀ k, HasPrimitiveIrreducibleCyclicSectors (blocks k))
    (p : ℕ) (hp : 0 < p)
    (hperiod_dvd : ∀ k, (hcyc k).choose ∣ p) :
    Nonempty { F : CommonBlockedCyclicSectorFamily blocks // F.p = p } := by
  classical
  let period : Fin r → ℕ := fun k => (hcyc k).choose
  have period_pos : ∀ k, 0 < period k := fun k => (hcyc k).choose_spec.1
  let sectorDim : (k : Fin r) → Fin (period k) → ℕ :=
    fun k => (hcyc k).choose_spec.2.choose
  let sectorBlocks : (k : Fin r) → (s : Fin (period k)) →
      MPSTensor (blockPhysDim d (period k)) (sectorDim k s) :=
    fun k => (hcyc k).choose_spec.2.choose_spec.choose
  have hSector : ∀ k,
      (∀ s, ∑ i : Fin (blockPhysDim d (period k)),
        (sectorBlocks k s i)ᴴ * sectorBlocks k s i = 1) ∧
      SameMPV₂ (blockTensor (d := d) (D := dim k) (blocks k) (period k))
        (toTensorFromBlocks (d := blockPhysDim d (period k))
          (μ := fun _ : Fin (period k) => (1 : ℂ)) (sectorBlocks k)) ∧
      (∀ s, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d (period k)) (D := sectorDim k s)
          (sectorBlocks k s))) ∧
      (∀ s, IsIrreducibleTensor (sectorBlocks k s)) ∧
      (∀ s, 0 < sectorDim k s) := by
    intro k
    exact (hcyc k).choose_spec.2.choose_spec.choose_spec
  have sector_tp : ∀ k s,
      ∑ i : Fin (blockPhysDim d (period k)),
        (sectorBlocks k s i)ᴴ * sectorBlocks k s i = 1 := fun k => (hSector k).1
  have sector_same : ∀ k,
      SameMPV₂ (blockTensor (d := d) (D := dim k) (blocks k) (period k))
        (toTensorFromBlocks (d := blockPhysDim d (period k))
          (μ := fun _ : Fin (period k) => (1 : ℂ)) (sectorBlocks k)) :=
    fun k => (hSector k).2.1
  have sector_primitive : ∀ k s,
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim d (period k)) (D := sectorDim k s)
          (sectorBlocks k s)) := fun k => (hSector k).2.2.1
  have sector_irreducible : ∀ k s, IsIrreducibleTensor (sectorBlocks k s) :=
    fun k => (hSector k).2.2.2.1
  have sector_dim_pos : ∀ k s, 0 < sectorDim k s :=
    fun k => (hSector k).2.2.2.2
  have p_pos : 0 < p := hp
  let extra : Fin r → ℕ := fun k => (hperiod_dvd k).choose
  have p_eq_period_mul_extra : ∀ k, p = period k * extra k :=
    fun k => (hperiod_dvd k).choose_spec
  have extra_pos : ∀ k, 0 < extra k := by
    intro k
    have hmul_pos : 0 < period k * extra k := by
      simpa [p_eq_period_mul_extra k] using p_pos
    exact Nat.pos_of_mul_pos_left hmul_pos
  have hPhys : ∀ k,
      blockPhysDim (blockPhysDim d (period k)) (extra k) = blockPhysDim d p := by
    intro k
    simpa [p_eq_period_mul_extra k] using
      (blockPhysDim_blockPhysDim d (period k) (extra k))
  let flatKey : Fin (∑ k : Fin r, period k) → ((k : Fin r) × Fin (period k)) :=
    fun x => finSigmaFinEquiv.symm x
  let flatDim : Fin (∑ k : Fin r, period k) → ℕ :=
    fun x => sectorDim (flatKey x).1 (flatKey x).2
  let flatBlocks : (x : Fin (∑ k : Fin r, period k)) →
      MPSTensor (blockPhysDim d p) (flatDim x) := fun x =>
    let y := flatKey x
    show MPSTensor (blockPhysDim d p) (sectorDim y.1 y.2) from
      cast (congr_arg (fun d' => MPSTensor d' (sectorDim y.1 y.2)) (hPhys y.1))
        (blockTensor (d := blockPhysDim d (period y.1)) (D := sectorDim y.1 y.2)
          (sectorBlocks y.1 y.2) (extra y.1))
  have hExtra : ∀ k s,
      (∑ i : Fin (blockPhysDim (blockPhysDim d (period k)) (extra k)),
        (blockTensor (d := blockPhysDim d (period k)) (D := sectorDim k s)
          (sectorBlocks k s) (extra k) i)ᴴ *
          blockTensor (d := blockPhysDim d (period k)) (D := sectorDim k s)
            (sectorBlocks k s) (extra k) i = 1) ∧
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim (blockPhysDim d (period k)) (extra k))
          (D := sectorDim k s)
          (blockTensor (d := blockPhysDim d (period k)) (D := sectorDim k s)
            (sectorBlocks k s) (extra k))) ∧
      IsIrreducibleTensor
        (blockTensor (d := blockPhysDim d (period k)) (D := sectorDim k s)
          (sectorBlocks k s) (extra k)) := by
    intro k s
    haveI : NeZero (sectorDim k s) := ⟨Nat.ne_of_gt (sector_dim_pos k s)⟩
    exact tp_primitive_irreducible_extra_blocking
      (d := blockPhysDim d (period k)) (D := sectorDim k s)
      (A := sectorBlocks k s) (sector_tp k s) (sector_primitive k s)
      (sector_irreducible k s) (hk := extra_pos k)
  have flat_tp : ∀ x,
      ∑ i : Fin (blockPhysDim d p), (flatBlocks x i)ᴴ * flatBlocks x i = 1 := by
    intro x
    let y := flatKey x
    have hcast := (leftCanonical_cast_physDim (hPhys y.1)
      (A := blockTensor (d := blockPhysDim d (period y.1)) (D := sectorDim y.1 y.2)
        (sectorBlocks y.1 y.2) (extra y.1))).2 (hExtra y.1 y.2).1
    simpa [flatBlocks, y] using hcast
  have flat_primitive : ∀ x,
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := flatDim x) (flatBlocks x)) := by
    intro x
    let y := flatKey x
    have hcast := (isPrimitive_transferMap_cast_physDim (hPhys y.1)
      (A := blockTensor (d := blockPhysDim d (period y.1)) (D := sectorDim y.1 y.2)
        (sectorBlocks y.1 y.2) (extra y.1))).2 (hExtra y.1 y.2).2.1
    simpa [flatBlocks, flatDim, y] using hcast
  have flat_irreducible : ∀ x, IsIrreducibleTensor (flatBlocks x) := by
    intro x
    let y := flatKey x
    have hcast := (isIrreducibleTensor_cast_physDim (hPhys y.1)
      (A := blockTensor (d := blockPhysDim d (period y.1)) (D := sectorDim y.1 y.2)
        (sectorBlocks y.1 y.2) (extra y.1))).2 (hExtra y.1 y.2).2.2
    simpa [flatBlocks, y] using hcast
  have flat_dim_pos : ∀ x, 0 < flatDim x := by
    intro x
    let y := flatKey x
    simpa [flatDim, y] using sector_dim_pos y.1 y.2
  have nested_same : ∀ k,
      SameMPV₂
        (cast (congr_arg (fun d' => MPSTensor d' (dim k)) (hPhys k))
          (blockTensor (d := blockPhysDim d (period k)) (D := dim k)
            (blockTensor (d := d) (D := dim k) (blocks k) (period k)) (extra k)))
        (toTensorFromBlocks (d := blockPhysDim d p)
          (μ := fun _ : Fin (period k) => (1 : ℂ))
          (fun s => cast
            (congr_arg (fun d' => MPSTensor d' (sectorDim k s)) (hPhys k))
            (blockTensor (d := blockPhysDim d (period k)) (D := sectorDim k s)
              (sectorBlocks k s) (extra k)))) := by
    intro k
    have hNested : SameMPV₂
        (blockTensor (d := blockPhysDim d (period k)) (D := dim k)
          (blockTensor (d := d) (D := dim k) (blocks k) (period k)) (extra k))
        (toTensorFromBlocks (d := blockPhysDim (blockPhysDim d (period k)) (extra k))
          (μ := fun _ : Fin (period k) => (1 : ℂ))
          (fun s => blockTensor (d := blockPhysDim d (period k)) (D := sectorDim k s)
            (sectorBlocks k s) (extra k))) := by
      simpa using
        (sameMPV₂_blockTensor_of_sameMPV₂_toTensorFromBlocks
          (d := blockPhysDim d (period k)) (D := dim k)
          (A := blockTensor (d := d) (D := dim k) (blocks k) (period k))
          (μ := fun _ : Fin (period k) => (1 : ℂ))
          (blocks := sectorBlocks k) (hSame := sector_same k) (p := extra k))
    have hCast := (sameMPV₂_cast_physDim (hPhys k)
      (A := blockTensor (d := blockPhysDim d (period k)) (D := dim k)
        (blockTensor (d := d) (D := dim k) (blocks k) (period k)) (extra k))
      (B := toTensorFromBlocks (d := blockPhysDim (blockPhysDim d (period k)) (extra k))
        (μ := fun _ : Fin (period k) => (1 : ℂ))
        (fun s => blockTensor (d := blockPhysDim d (period k)) (D := sectorDim k s)
          (sectorBlocks k s) (extra k)))).2 hNested
    rw [toTensorFromBlocks_cast_physDim (h := hPhys k)] at hCast
    simpa using hCast
  exact ⟨⟨{
    p := p
    p_pos := p_pos
    period := period
    period_pos := period_pos
    extra := extra
    extra_pos := extra_pos
    p_eq_period_mul_extra := p_eq_period_mul_extra
    sectorDim := sectorDim
    sectorBlocks := sectorBlocks
    sector_tp := sector_tp
    sector_same := sector_same
    sector_primitive := sector_primitive
    sector_irreducible := sector_irreducible
    sector_dim_pos := sector_dim_pos
    blockPhysDim_nested_eq := hPhys
    flatDim := flatDim
    flatBlocks := flatBlocks
    flat_tp := flat_tp
    flat_primitive := flat_primitive
    flat_irreducible := flat_irreducible
    flat_dim_pos := flat_dim_pos
    nested_same := nested_same }, rfl⟩⟩

/-- A finite family of live blocks with per-block primitive irreducible cyclic sectors
admits one common physical blocking length for all those sectors.

This theorem chooses the least common multiple of the per-live-block period-removal
lengths.  Each cyclic sector is then blocked by the corresponding quotient,
identified with the common physical alphabet, and collected into one finite
flattened family.  Trace preservation, primitive transfer maps, tensor
irreducibility, positive bond dimensions, nonzero unit weights, and the per-block
iterated-blocking MPV compatibility conditions are all retained. -/
theorem exists_commonBlockedCyclicSectorFamily_of_hasPrimitiveIrreducibleCyclicSectors
    {d r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hcyc : ∀ k, HasPrimitiveIrreducibleCyclicSectors (blocks k)) :
    Nonempty (CommonBlockedCyclicSectorFamily blocks) := by
  classical
  let period : Fin r → ℕ := fun k => (hcyc k).choose
  have period_pos : ∀ k, 0 < period k := fun k => (hcyc k).choose_spec.1
  obtain ⟨F, _hFp⟩ :=
    exists_commonBlockedCyclicSectorFamily_of_commonMultiple
      blocks hcyc (lcmPeriod period) (lcmPeriod_pos period_pos) (by
        intro k
        simpa [period] using (dvd_lcmPeriod period k))
  exact ⟨F⟩

end SectorOrbitLift

end MPSTensor
