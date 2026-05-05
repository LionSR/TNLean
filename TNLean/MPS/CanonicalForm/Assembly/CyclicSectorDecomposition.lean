/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Assembly.CyclicSectorRelation
import TNLean.MPS.CanonicalForm.Assembly.CommonBlockedCyclicSectorFamily
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
* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:2011.12127, Section IV]

## Tags

matrix product states, cyclic sectors, peripheral spectrum, blocking
-/

namespace MPSTensor

variable {d D : ℕ}


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

The only remaining hypothesis beyond the cyclic-sector decomposition data is the
corner irreducibility theorem for `((transferMap A†)^m)` on each projection
`P k`. In particular, this theorem isolates the orbit-sum / `hProjStep` part of
the non-periodic proof chain from the subsequent compression-transport
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
compression transport theorem above. The residual blocker is
therefore isolated exactly to the one-step `hProjStep` hypothesis. -/
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
theorem
  primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking_of_fixedAlgebraRigidity
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
                -- Keep the ᴴᴴ so the summand matches `transferMap K`
                -- with `K = (blockTensor …)ᴴ`.
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

This is the strongest currently available general route in the direction of the scalar
blocked fixed-point algebra result
(see Cirac--Perez-Garcia--Schuch--Verstraete 2021, Appendix A): once the blocked
fixed-point algebra is known to be scalar on all compressed sectors,
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
scalar. Once that hypothesis is available, the present theorem derives
`SectorFixedPointAlgebraRigidity` and applies the orbit-sum / corner-compression
reduction from the fixed-algebra-rigidity sector-block theorem. -/
theorem
  primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking_of_scalarBlockedFixedPoints
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
multi-block construction before the sectors of all nonzero-weight blocks are flattened to
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

end SectorOrbitLift

end MPSTensor
