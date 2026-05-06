/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.CyclicSectors.FixedAdjoint

open scoped Matrix BigOperators ComplexOrder MatrixOrder

/-!
# Cyclic-sector relations for blocked tensors

A cyclic decomposition of the adjoint transfer map determines a sector
decomposition for the tensor obtained by blocking over one full period.  The
connection is made by comparing the blocked adjoint transfer map with the
corresponding power of the original adjoint transfer map.

The mathematical source is the cyclic projection structure for irreducible
quantum channels from Wolf Chapter 6, together with the off-diagonal form and
period-blocking lemmas for periodic MPS blocks in arXiv:1708.00029.  The formulas
formalized here are
$$
  \mathcal E_A^*(P_{u+1}) = P_u,\qquad
  A^i = \sum_u P_u A^i P_{u+1},\qquad
  C_u = P_u A^{[m]} P_u.
$$

## References

* [Wolf, *Quantum Channels & Operations*, Chapter 6]
* [De las Cuevas et al., arXiv:1708.00029, periodic-block decomposition]

## Tags

matrix product states, cyclic sectors, peripheral spectrum, blocking
-/

namespace MPSTensor

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

end MPSTensor
