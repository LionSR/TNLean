/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.CyclicSectors
import TNLean.MPS.CanonicalForm.CyclicSectorAssembly
import TNLean.MPS.Core.BlockingTransfer
import TNLean.MPS.SharedInfra.KrausAdjointSetup
import TNLean.Channel.Peripheral.CyclicDecomposition
import TNLean.Channel.Peripheral.GroupStructure

/-!
# Assembly — Cyclic sector bridge

This companion file contains the bridge between the abstract cyclic decomposition
(`CyclicDecomposition.lean`) and the MPS-specific cyclic sector decomposition:

* `adjointTransferMap_pow_fixes_cyclic_projection` — iterating the cyclic relation
  `m` times shows each projection is fixed by the `m`-th iterate.
* `transferMap_adjoint_blocked_eq_pow` — the adjoint of the blocked transfer map
  equals the `m`-th power of the adjoint transfer map.
* `exists_cyclic_sector_decomp_after_blocking` — irreducible TP block → cyclic sector
  decomposition after blocking.
* `exists_cyclic_sector_decomp_of_TP_of_isIrreducibleTensor` — bridge from MPS-level
  hypotheses to automatic cyclic sector decomposition.

The main reduction theorem and structural assembly are in `Assembly.lean`.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Filter

namespace MPSTensor

variable {d D : ℕ}

/-!
## Cyclic sector decomposition via the CyclicSectors API

### Mathematical overview

For an irreducible TP block `A` of period `m`, the adjoint transfer map
`E† = transferMap (fun i => (A i)ᴴ)` has peripheral spectrum `{γ^k | k ∈ Fin m}`.
The cyclic decomposition from `CyclicDecomposition.lean` produces projections `P_k` with:
- `∀ k, IsOrthogonalProjection (P k)` and `∑ k, P k = 1`
- `E†(P(k+1)) = P k` (cyclic), hence `(E†)^m (P k) = P k`

The key bridge: `(E†)^m = transferMap (fun j => (blockTensor A m j)ᴴ)` because the
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

section CyclicSectorBridge


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
  -- Strategy: prove (E†)^n (P (k + n)) = P k for Fin m addition, by induction on n.
  -- For n = m, k + m = k in Fin m, so (E†)^m (P k) = P k.
  -- The key is: (E†)^(n+1) (P (k + (n+1))) = E†((E†)^n (P (k + (n+1))))
  -- = E†((E†)^n (P ((k+1) + n)))     [since k + (n+1) = (k+1) + n in Fin m]
  -- = E†(P (k+1))                     [by IH with k' = k+1]
  -- = P k                              [by hcyclic]
  -- Prove: ∀ n, ∀ k, (E†)^n (P (k + n)) = P k  where n is a Fin m literal.
  -- We use Nat.rec on n, carrying a proof that the Fin m literal n is (n % m).
  -- But this is cleaner using hcyclic directly in a simple induction.
  -- Base: (E†)^0 (P (k + 0)) = P k  ✓
  -- Step: (E†)^(n+1) (P (k + (n+1)))
  --     = E†((E†)^n (P (k + (n+1))))     [pow decomp]
  --     = E†((E†)^n (P ((k+1) + n)))     [Fin m add assoc]
  --     = E†(P (k+1))                    [IH with k' = k+1]
  --     = P k                             [hcyclic]
  -- At n = m: k + m = k in Fin m, so (E†)^m (P k) = P k.
  intro k
  -- Direct approach: iterate hcyclic m times
  suffices ∀ n : ℕ, n ≤ m →
      ∀ (k : Fin m), ((transferMap (d := d) (D := D) K) ^ n)
        (P ⟨((k : ℕ) + n) % m, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))⟩) = P k by
    have h := this m le_rfl k
    simpa [Nat.add_mod_right, Nat.mod_eq_of_lt k.is_lt] using h
  intro n
  induction n with
  | zero =>
    intro _ k
    simp [Nat.mod_eq_of_lt k.is_lt]
  | succ n ih =>
    intro hn k
    have hn' : n ≤ m := Nat.le_of_succ_le hn
    have hlt : ((k : ℕ) + (n + 1)) % m < m :=
      Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))
    -- Decompose the power
    have hpow : ((transferMap (d := d) (D := D) K) ^ (n + 1))
        (P ⟨((k : ℕ) + (n + 1)) % m, hlt⟩) =
        (transferMap (d := d) (D := D) K)
          (((transferMap (d := d) (D := D) K) ^ n)
            (P ⟨((k : ℕ) + (n + 1)) % m, hlt⟩)) := by
      rw [pow_succ']; rfl
    rw [hpow]
    -- (k + (n+1)) % m = ((k+1) + n) % m
    have hmod : ((k : ℕ) + (n + 1)) % m = (((k : ℕ) + 1) + n) % m := by
      congr 1; omega
    -- Create the Fin m index for (k+1)
    set k1 : Fin m := k + 1
    -- Apply IH with k' = k+1
    have := ih hn' k1
    -- ih says: (E†)^n (P ⟨(↑k1 + n) % m, _⟩) = P k1
    -- We need: (E†)^n (P ⟨((↑k + n + 1)) % m, _⟩) = P k1
    -- Since (↑k + (n+1)) % m = (↑k1 + n) % m
    have hval_eq : ((k : ℕ) + (n + 1)) % m = ((k1 : ℕ) + n) % m := by
      simp [k1, Fin.val_add]; omega
    have hfin_eq :
        (⟨((k : ℕ) + (n + 1)) % m, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))⟩ : Fin m) =
          ⟨((k1 : ℕ) + n) % m, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))⟩ := by
      ext; exact hval_eq
    rw [hfin_eq, this]
    exact hcyclic k

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
- commutation: each `P k` commutes with every blocked letter,
- trace relation: `mpv (blocks k) σ = (P k * evalWord (blockTensor A m) σ).trace`,
- MPV equivalence: the direct-sum tensor is `SameMPV₂`-equivalent to the blocked tensor. -/
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
      (P : Fin m → MatrixAlg D),
      (∀ k, ∑ i : Fin (blockPhysDim d m), (blocks k i)ᴴ * blocks k i = 1) ∧
      SameMPV₂ (blockTensor A m) (toTensorFromBlocks (μ := fun _ => 1) blocks) ∧
      (∀ k, IsOrthogonalProjection (P k)) ∧
      (∑ k : Fin m, P k = 1) ∧
      (∀ k (i : Fin (blockPhysDim d m)),
        P k * (blockTensor A m) i = (blockTensor A m) i * P k) ∧
      (∀ k (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)),
        mpv (blocks k) σ = (P k * evalWord (blockTensor A m) (List.ofFn σ)).trace) := by
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
  obtain ⟨dim, blocks, hLC, hMPV_hTrace⟩ := exists_blockDecomp_of_adjoint_fixed_projections
    (blockTensor A m) P hPproj hPsum hTP_blocked hFix
  obtain ⟨hMPV, hTrace⟩ := hMPV_hTrace
  -- Step 6: Derive commutation from the adjoint fix property
  have hComm : ∀ k (i : Fin (blockPhysDim d m)),
      P k * (blockTensor A m) i = (blockTensor A m) i * P k := by
    intro k i
    exact commutes_letters_of_adjoint_fixed_projection
      (blockTensor A m) hTP_blocked (hP := hPproj k) (hFix := hFix k) i
  exact ⟨dim, blocks, P, hLC, hMPV, hPproj, hPsum, hComm, hTrace⟩

end CyclicSectorBridge

/-!
## Bridge: MPS hypotheses → cyclic sector decomposition

For an irreducible TP tensor, all channel-level hypotheses needed by
`exists_cyclic_sector_decomp_after_blocking` can be derived automatically:

1. `IsIrreducibleTensor A` → `IsIrreducibleMap (transferMap (fun i => (A i)ᴴ))`
2. TP + irreducible → ∃ ρ.PosDef fixed by `transferMap A` = `Kraus.adjointMap K`
3. `peripheral_eigenvalues_cyclic_structure` → `(m, γ, IsPrimitiveRoot γ m, periph = {γ^k})`
4. Feed all into `exists_cyclic_sector_decomp_after_blocking`
-/

section CyclicSectorFromMPS

open KadisonSchwarz

/-- **Bridge: irreducible TP tensor → cyclic sector decomposition.**

For an irreducible TP tensor `A` with `0 < D`, there exists a period `m > 0`
such that after blocking by `m`, the blocked tensor admits a decomposition
into `m` left-canonical (TP) blocks via cyclic spectral projections.

This bridges the MPS-level hypotheses (`IsIrreducibleTensor` + TP) to the
channel-level cyclic decomposition, deriving all intermediate hypotheses
(`ρ.PosDef`, `Kraus.adjointMap` fixed point, `IsIrreducibleMap`, peripheral
spectrum structure) automatically via `conjTranspose_kraus_setup`. -/
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
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨dim, blocks, _, hTP_blocks, hSame, _, _, _, _⟩ :=
    exists_cyclic_sector_decomp_after_blocking A hTP hIrr ρ hρ_pd h_adjfix hIrrK hγ_prim
      hperiph_range
  exact ⟨m, hm_pos, dim, blocks, hTP_blocks, hSame⟩

end CyclicSectorFromMPS

end MPSTensor
