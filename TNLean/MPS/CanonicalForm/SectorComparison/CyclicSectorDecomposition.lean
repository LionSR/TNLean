/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.SectorComparison.CyclicSectorRelation
import TNLean.MPS.CanonicalForm.SectorComparison.CommonBlockedCyclicSectorFamily
import TNLean.Channel.Peripheral.Conjugation
import TNLean.Channel.Schwarz.MultiplicativeDomainFull
import TNLean.MPS.Periodic.SectorIrreducibility
import TNLean.MPS.CanonicalForm.CyclicSectors.CornerBridge

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Filter

/-!
# Period removal (cyclic-sector decomposition) after blocking

This file performs the **period-removal step** of the canonical-form
reduction.  In arXiv:1606.00608 the only required input is that after
blocking by the least common multiple of the per-block periods, the
resulting tensor has no nontrivial $p$-periodic vectors (1606.00608,
§2.3).  The non-periodic route then proceeds to the normal/BNT
comparison; there is no standalone ``cyclic-sector theory'' in
1606.00608.

The file therefore
1. derives the channel-level cyclic decomposition from the adjoint
   transfer map (Wolf 2012, Theorem 6.6);
2. feeds it into the blocked-sector infrastructure to obtain the
   MPS-level period-removal decomposition for an irreducible
   trace-preserving tensor;
3. proves that the resulting sector blocks are primitive and
   tensor-irreducible.

The bulk of the projection-multiplicativity and orbit-lift
arguments are internal to the period-removal step; they are not
exposed as independent results of CPSV.

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, §2.3/App.A]
* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:2011.12127, §IV]
* [Wolf, Quantum Channels & Operations (2012), §6.5–6.6]
-/

namespace MPSTensor

variable {d D : ℕ}


section SectorOrbitLift

/-!
## Sector primitivity and irreducibility after period removal

The remaining theorems in this section prove that the cyclic-sector
blocks produced by period removal are primitive and tensor-irreducible.
These are internal lemmas that close the orbit-sum / corner-compression
argument; they are not independent results of CPSV.

The sequence of theorems proceeds through progressively weaker
hypotheses (corner-irreducible → proj-step → fixed-algebra-rigidity
→ scalar-blocked-fixed-points) until the unconditional form
`primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking`
is reached.  Only the unconditional form and the top-level existence theorem
`exists_primitive_irreducible_cyclic_sector_decomp_of_TP_of_isIrreducibleTensor`
are consumed by the downstream canonical-form proof chain.
-/

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

/-- Unconditional: cyclic-sector blocks after period removal are primitive and
tensor-irreducible.

This is the internal lemma that closes the orbit-sum / corner-compression
argument.  It uses `isIrreducibleOnCorner_of_cyclic_decomp_mps` so that no
extra projection-step or fixed-point-algebra hypotheses are needed when the
ambient tensor is irreducible and trace-preserving. -/
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

/-- **Period removal with primitive, irreducible sectors.**

For an irreducible TP tensor `A`, after blocking by the least common
multiple of its periods the blocked tensor is a unit-weight sum of
primitive, tensor-irreducible, trace-preserving sector blocks with
positive bond dimensions.

This encodes the unconditional sector-orbit lift into the single
result consumed by the downstream common-blocking construction.  It is
the period-removal step of arXiv:1606.00608, §2.3, strengthened with
primitivity and irreducibility of the sector blocks. -/
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
