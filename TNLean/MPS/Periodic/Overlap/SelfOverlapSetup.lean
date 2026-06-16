/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Defs
import TNLean.MPS.Overlap.CastDecay
import TNLean.MPS.FundamentalTheorem.Basic
import TNLean.MPS.Chain.OneSidedInverse
import TNLean.MPS.Core.Blocking
import TNLean.MPS.CanonicalForm.CyclicSectors
import TNLean.MPS.CanonicalForm.CyclicSectors.CornerBridge
import TNLean.MPS.CanonicalForm.SectorComparison.CommonSectorData
import TNLean.MPS.CanonicalForm.SectorComparison.CyclicSectorRelation
import TNLean.MPS.Periodic.SectorIrreducibility
import TNLean.MPS.Periodic.Overlap.GaugePhase
import TNLean.MPS.Irreducible.Adjoint
import TNLean.MPS.SharedInfra.KrausAdjointSetup
import TNLean.MPS.SharedInfra.BlockAssembly
import TNLean.Spectral.TransferOperatorGapNT
import TNLean.Channel.Irreducible.PerronFrobenius
import TNLean.Channel.Schwarz.MultiplicativeDomainFull

import TNLean.Algebra.GramMatrixLI
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Periodic overlap dichotomy: cyclic-sector setup

This module contains the cyclic-sector setup used throughout the periodic
overlap argument, together with the non-repetition input from Lemma bdcf
of arXiv:1708.00029.

## Main declarations

* `IsCyclicSectorDecomp`
* `exists_cyclic_sector_decomp_with_letter_and_isometry_after_blocking_of_isPeriodic`
* `primitive_and_irreducible_sectorBlocks_of_cyclicDecomp`
* `exists_offDiag_eigenvector_of_gaugePhase_cast_left`

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
transfer map, with the shifted relation E†(P(k + 1)) = P k.  In the
off-diagonal convention of arXiv:1708.00029, Appendix A, the displayed blocks
satisfy A^i = ∑ u, P_u A^i P_{u+1} and the same adjoint transfer map is
written E^*, with source labels satisfying E^*(P_u) = P_{u+1}.  The two
conventions agree after inverse cyclic reindexing: `P k` corresponds to the
source projection with index `-k` modulo the period.  After blocking by the
period `m`, the blocked transfer map E^m fixes every `P k`, so
\(P_k (A^{(m)})^i = (A^{(m)})^i P_k\) for every blocked letter.

The per-sector trace relation
\(V^{(N)}(C_k)_\sigma =
  \operatorname{tr}(P_k (A^{(m)})^\sigma)\)
ties each compressed block `blocks k` back to the projection `P k`.

Also carries per-sector compression `∗`-algebra isomorphisms
`φ k : M_{dim k}(ℂ) ≃ₗ[ℂ] cornerSubmodule (P k)` that are multiplicative and
`∗`-preserving, together with the intertwining identity relating the compressed
adjoint transfer map to the sector adjoint transfer map on the corner of `P k`.
These isomorphisms identify the corner dynamics with the compressed matrix
algebras, so irreducibility and primitivity may be transferred through the
corner representation.  The underlying linear maps are isometries for the
canonical inner products; the support isometries record this property where
needed. -/
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

/-- The single-site off-diagonal grading carried by a cyclic sector decomposition:
each unblocked Kraus operator carries the cyclic projection index `k` to `k + 1`,
P_{k+1} · A^i = A^i · P_k.  This is the single-site shift of arXiv:1708.00029,
eq:Auprop, obtained from the cyclic relation 𝓔^*(P_{k+1}) = P_k stored in
`IsCyclicSectorDecomp`. -/
theorem IsCyclicSectorDecomp.offDiag_shift [NeZero D] [NeZero m]
    {A : MPSTensor d D} (hP : IsPeriodic m A) {dim : Fin m → ℕ}
    {blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k)}
    (hCyclic : IsCyclicSectorDecomp A blocks)
    (k : Fin m) (i : Fin d) :
    ∃ P : Fin m → Matrix (Fin D) (Fin D) ℂ,
      (∀ l, IsOrthogonalProjection (P l)) ∧ (∑ l : Fin m, P l = 1) ∧
        P (k + 1) * A i = A i * P k := by
  obtain ⟨P, _φ, hPproj, hPsum, hShift, _⟩ := hCyclic
  exact ⟨P, hPproj, hPsum,
    offDiag_shift_of_adjoint_cyclic_shift A hP.leftCanonical hPproj hShift k i⟩

/-- The off-diagonal reconstruction A^i = ∑_u P_{u+1} · A^i · P_u carried by a
cyclic sector decomposition (arXiv:1708.00029, eq:Aoffdiag), graded by the cyclic
projections stored in `IsCyclicSectorDecomp`. -/
theorem IsCyclicSectorDecomp.eq_sum_offDiag [NeZero D] [NeZero m]
    {A : MPSTensor d D} (hP : IsPeriodic m A) {dim : Fin m → ℕ}
    {blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k)}
    (hCyclic : IsCyclicSectorDecomp A blocks)
    (i : Fin d) :
    ∃ P : Fin m → Matrix (Fin D) (Fin D) ℂ,
      (∀ l, IsOrthogonalProjection (P l)) ∧ (∑ l : Fin m, P l = 1) ∧
        A i = ∑ u : Fin m, P (u + 1) * A i * P u := by
  obtain ⟨P, _φ, hPproj, hPsum, hShift, _⟩ := hCyclic
  exact ⟨P, hPproj, hPsum,
    eq_sum_offDiag_of_adjoint_cyclic_shift A hP.leftCanonical hPproj hPsum hShift i⟩

/-- The next cyclic index modulo a positive period. -/
def cyclicNextOfPos {m : ℕ} (hm : 0 < m) (k : Fin m) : Fin m :=
  ⟨(k.1 + 1) % m, Nat.mod_lt _ hm⟩

/-- A periodic tensor of period `m`, after blocking by `m`, admits a cyclic-sector
decomposition with support isometries, whose compression maps send each sector
letter to the corresponding ambient corner.

Source: arXiv:1708.00029, Lemma bdcf, lines 404--423, and eq. Cu. This theorem
records the existence of the cyclic projectors and corner blocks
C_u = P_u A^{(m)}. The blocks are left-canonical, reproduce the blocked tensor's
MPV family, satisfy the cyclic-sector relations, have nonzero bond dimensions,
and obey the corner-letter identity. The normality and non-repetition
conclusions of Lemma bdcf are stated separately below, for example in
`sectorBlocked_isNormal_of_isPeriodic` and
`not_gaugePhaseEquiv_of_orthogonal_cyclicSector_traces`. -/
theorem exists_cyclic_sector_decomp_with_letter_and_isometry_after_blocking_of_isPeriodic
    [NeZero D] (A : MPSTensor d D) {m : ℕ}
    (hP : IsPeriodic m A) :
    ∃ (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
      (P : Fin m → MatrixAlg D)
      (φ : (k : Fin m) →
        Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k))
      (V : (k : Fin m) → Matrix (Fin D) (Fin (dim k)) ℂ),
      (∀ k, ∑ i : Fin (blockPhysDim d m), (blocks k i)ᴴ * blocks k i = 1) ∧
      SameMPV₂ (blockTensor A m) (toTensorFromBlocks (μ := fun _ => 1) blocks) ∧
      (∀ k, IsOrthogonalProjection (P k)) ∧
      (∑ k : Fin m, P k = 1) ∧
      (∀ k,
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ)
          (P (cyclicNextOfPos hP.period_pos k)) = P k) ∧
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
      (∀ k, dim k ≠ 0) ∧
      (∀ k (i : Fin (blockPhysDim d m)),
        (φ k (blocks k i)).1 = P k * (blockTensor A m) i * P k) ∧
      (∀ k, (V k)ᴴ * V k = 1) ∧
      (∀ k, V k * (V k)ᴴ = P k) ∧
      (∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k X).1 = V k * X * (V k)ᴴ) := by
  letI : NeZero m := ⟨Nat.ne_of_gt hP.period_pos⟩
  obtain ⟨K, h_unitalK, hIrrK, ρ, hρ_pd, h_adjfix, rfl⟩ :=
    conjTranspose_kraus_setup A hP.leftCanonical hP.irreducible
  obtain ⟨ω, hωprim⟩ := hP.primitiveRoot
  have hM : (1 : Matrix (Fin D) (Fin D) ℂ).PosDef := Matrix.PosDef.one
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
  obtain ⟨dim, blocks, P, φ, V, hLC, hMPV, hPproj, hPsum, hCyclic, hComm, hTrace,
    hIntertwine, hMul, hStar, hLetter, hV_iso, hV_range, hEmbed, hNondeg⟩ :=
    exists_cyclic_sector_decomp_after_blocking_with_letter_and_isometry
      A hP.leftCanonical hP.irreducible ρ hρ_pd h_adjfix hIrrK hωprim hperiph_range
  have hCyclic' :
      ∀ k,
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ)
          (P (cyclicNextOfPos hP.period_pos k)) = P k := by
    intro k
    simpa [cyclicNextOfPos, Fin.add_def] using hCyclic k
  exact ⟨dim, blocks, P, φ, V, hLC, hMPV, hPproj, hPsum, hCyclic', hComm, hTrace,
    hIntertwine, hMul, hStar, hNondeg, hLetter, hV_iso, hV_range, hEmbed⟩

/-- A periodic tensor of period `m`, after blocking by `m`, admits a cyclic-sector
decomposition whose compression maps send each sector letter to the
corresponding ambient corner.

This is the projection of
`exists_cyclic_sector_decomp_with_letter_and_isometry_after_blocking_of_isPeriodic`
that forgets the support isometries. -/
theorem exists_cyclic_sector_decomp_with_letter_after_blocking_of_isPeriodic
    [NeZero D] (A : MPSTensor d D) {m : ℕ}
    (hP : IsPeriodic m A) :
    ∃ (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
      (P : Fin m → MatrixAlg D)
      (φ : (k : Fin m) →
        Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k)),
      (∀ k, ∑ i : Fin (blockPhysDim d m), (blocks k i)ᴴ * blocks k i = 1) ∧
      SameMPV₂ (blockTensor A m) (toTensorFromBlocks (μ := fun _ => 1) blocks) ∧
      (∀ k, IsOrthogonalProjection (P k)) ∧
      (∑ k : Fin m, P k = 1) ∧
      (∀ k,
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ)
          (P (cyclicNextOfPos hP.period_pos k)) = P k) ∧
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
      (∀ k, dim k ≠ 0) ∧
      ∀ k (i : Fin (blockPhysDim d m)),
        (φ k (blocks k i)).1 = P k * (blockTensor A m) i * P k := by
  obtain ⟨dim, blocks, P, φ, _V, hLC, hMPV, hPproj, hPsum, hCyclic, hComm, hTrace,
    hIntertwine, hMul, hStar, hNondeg, hLetter, _hV_iso, _hV_range, _hEmbed⟩ :=
    exists_cyclic_sector_decomp_with_letter_and_isometry_after_blocking_of_isPeriodic A hP
  exact ⟨dim, blocks, P, φ, hLC, hMPV, hPproj, hPsum, hCyclic, hComm, hTrace,
    hIntertwine, hMul, hStar, hNondeg, hLetter⟩

/-- A periodic tensor of period `m`, after blocking by `m`, admits a cyclic
sector decomposition.

Source: arXiv:1708.00029, Lemma bdcf, lines 404--423. This theorem is the
projection of
`exists_cyclic_sector_decomp_with_letter_after_blocking_of_isPeriodic` that
forgets the explicit corner-letter identity. -/
theorem exists_cyclic_sector_decomp_after_blocking_of_isPeriodic
    [NeZero D] (A : MPSTensor d D) {m : ℕ} [NeZero m]
    (hP : IsPeriodic m A) :
    ∃ (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k)),
      (∀ k, ∑ i : Fin (blockPhysDim d m), (blocks k i)ᴴ * blocks k i = 1) ∧
      SameMPV₂ (blockTensor A m) (toTensorFromBlocks (μ := fun _ => 1) blocks) ∧
      IsCyclicSectorDecomp A blocks ∧
      (∀ k, dim k ≠ 0) := by
  obtain ⟨dim, blocks, P, φ, hLC, hMPV, hPproj, hPsum, hCyclic, hComm, hTrace,
    hIntertwine, hMul, hStar, hNondeg, _hLetter⟩ :=
    exists_cyclic_sector_decomp_with_letter_after_blocking_of_isPeriodic A hP
  have hCyclic' :
      ∀ k, transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k := by
    intro k
    simpa [cyclicNextOfPos, Fin.add_def] using hCyclic k
  exact ⟨dim, blocks, hLC, hMPV,
    ⟨P, φ, hPproj, hPsum, hCyclic', hComm, hTrace, hIntertwine, hMul, hStar⟩,
    hNondeg⟩

/-- Corner primitivity and irreducibility for a cyclic sector.

This isolates the channel-level input behind
`primitive_and_irreducible_sectorBlocks_of_cyclicDecomp`: on each cyclic corner,
the `m`-step adjoint transfer map is primitive and irreducible. The later
compression identification converts these corner statements into the
corresponding statements for the compressed sector tensor. -/
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
  have hM : (1 : MatrixAlg D).PosDef := Matrix.PosDef.one
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
    hLift_cyclicDecomp_mps
      (A := A) (m := m) hIrr hP.leftCanonical P hPproj hPsum hCyclic hMulLeft hMulRight
  have hCornerIrr : IsIrreducibleOnCorner (P u) (T ^ m) :=
    isIrreducible_restriction_of_cyclic_decomp (T := T)
      hIrr P hPproj hPsum (by simpa [T] using hCyclic) (by simpa [T] using hLift) u
  exact ⟨hInv, by simpa [T] using hCornerPrim, by simpa [T] using hCornerIrr⟩

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

The proof combines the unconditional corner result from
`cornerRestriction_primitive_and_irreducible_of_cyclicDecomp` with the
compression identification provided by
`compressedSector_adjointTransferMap_cornerBridge_of_cyclicDecomp`.
The first supplies primitivity and irreducibility for the `m`-step adjoint
transfer map on the corner `P u`; the second identifies the compressed adjoint
sector tensor with the corresponding corner restriction; irreducibility of the
adjoint transfer map then gives irreducibility of the ordinary transfer map.

This lemma is invoked by the Case 2 and Case 3 arguments of the periodic
overlap dichotomy. -/
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

/-- The self-overlap of a blocked tensor at length `N` is the self-overlap of
the original tensor at length `N * L`. -/
theorem mpvOverlap_blockTensor_self_eq
    [NeZero D] (A : MPSTensor d D) (L N : ℕ) :
    mpvOverlap (d := blockPhysDim d L) (blockTensor (d := d) (D := D) A L)
        (blockTensor (d := d) (D := D) A L) N =
      mpvOverlap (d := d) A A (N * L) := by
  rw [← trace_mixedTransferMap_pow_eq_mpvOverlap
      (A := blockTensor (d := d) (D := D) A L)
      (B := blockTensor (d := d) (D := D) A L) N]
  rw [← trace_mixedTransferMap_pow_eq_mpvOverlap (A := A) (B := A) (N * L)]
  simp [mixedTransferMap_self, transferMap_blockTensor, pow_mul, Nat.mul_comm]

/-- A same-dimension gauge-phase equivalence between two compressed sector blocks
produces a nonzero off-diagonal eigenvector of the ambient blocked transfer map.

Source: arXiv:1708.00029, Lemma bdcf, lines 409--421.  The paper phrases this
step using a corner partial isometry.  For the spectral contradiction below, the
load-bearing datum is the resulting nonzero (u, v)-corner eigenvector of the
period transfer map.  We obtain that eigenvector as the product ρXᴴ, where ρ is
a positive fixed point of the first compressed transfer map and X is the gauge
matrix.  The rectangular support isometries then embed this coordinate
eigenvector into the two ambient corners. -/
private lemma exists_offDiag_eigenvector_of_gaugePhase_same_dim
    [NeZero D] {d₀ D₀ : ℕ} [NeZero D₀]
    (C : MPSTensor d₀ D) (Au Av : MPSTensor d₀ D₀)
    (hAu_left : IsLeftCanonical Au) (hAv_left : IsLeftCanonical Av)
    (hAv_irr : IsIrreducibleTensor Av)
    {Pu Pv : MatrixAlg D}
    (hComm_u : ∀ i : Fin d₀, Pu * C i = C i * Pu)
    (hComm_v : ∀ i : Fin d₀, Pv * C i = C i * Pv)
    {Vu Vv : Matrix (Fin D) (Fin D₀) ℂ}
    (hVu_iso : Vuᴴ * Vu = 1) (hVv_iso : Vvᴴ * Vv = 1)
    (hVu_range : Vu * Vuᴴ = Pu) (hVv_range : Vv * Vvᴴ = Pv)
    (hLetter_u : ∀ i : Fin d₀, Vu * Au i * Vuᴴ = Pu * C i * Pu)
    (hLetter_v : ∀ i : Fin d₀, Vv * Av i * Vvᴴ = Pv * C i * Pv)
    (hGPE : GaugePhaseEquiv Au Av) :
    ∃ (U : MatrixAlg D) (ζ : ℂ), ‖ζ‖ = 1 ∧ U ≠ 0 ∧
      U = Pu * U * Pv ∧ transferMap (d := d₀) (D := D) C U = ζ • U := by
  classical
  obtain ⟨X, η, hη_ne, hAv_eq⟩ := hGPE
  have hη_norm : ‖η‖ = 1 :=
    gaugePhase_scalar_norm_eq_one_of_leftCanonical_irreducible
      hAu_left hAv_left hAv_irr hη_ne hAv_eq
  obtain ⟨ρ, _hρ_psd, hρ_ne, hρ_fix⟩ :=
    exists_posSemidef_fixedPoint Au hAu_left (NeZero.pos D₀)
  let Y : Matrix (Fin D₀) (Fin D₀) ℂ := ρ * X.valᴴ
  have hY_ne : Y ≠ 0 := by
    intro hY_zero
    apply hρ_ne
    have hcancel :=
      congr_arg (fun Z : Matrix (Fin D₀) (Fin D₀) ℂ => Z * X⁻¹.valᴴ) hY_zero
    have hright_unit : X.valᴴ * X⁻¹.valᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Units.inv_mul]
      simp
    have hright : X.valᴴ * (X.val)⁻¹ᴴ = 1 := by
      simpa [Units.val_inv_eq_inv_val] using hright_unit
    simpa [Y, Matrix.mul_assoc, hright] using hcancel
  have hright_unit : X.valᴴ * X⁻¹.valᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Units.inv_mul]
    simp
  have hright : X.valᴴ * (X.val)⁻¹ᴴ = 1 := by
    simpa [Units.val_inv_eq_inv_val] using hright_unit
  have hρ_sum : (∑ i : Fin d₀, Au i * ρ * (Au i)ᴴ) = ρ := by
    simpa [transferMap_apply] using hρ_fix
  have hMixed : mixedTransferMap Au Av Y = (star η) • Y := by
    calc
      mixedTransferMap Au Av Y =
          ∑ i : Fin d₀, Au i * (ρ * X.valᴴ) * (Av i)ᴴ := by
        simp [mixedTransferMap_apply, Y]
      _ = ∑ i : Fin d₀, (star η) • (Au i * ρ * (Au i)ᴴ * X.valᴴ) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [hAv_eq i]
        simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
          Matrix.mul_smul]
        congr 1
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc X.valᴴ X⁻¹.valᴴ ((Au i)ᴴ * X.valᴴ), hright_unit]
        simp
      _ = (star η) • ((∑ i : Fin d₀, Au i * ρ * (Au i)ᴴ) * X.valᴴ) := by
        rw [← Finset.smul_sum]
        congr 1
        simp [Finset.sum_mul, Matrix.mul_assoc]
      _ = (star η) • Y := by
        rw [hρ_sum]
  have hPuVu : Pu * Vu = Vu := by
    calc
      Pu * Vu = (Vu * Vuᴴ) * Vu := by rw [hVu_range]
      _ = Vu * (Vuᴴ * Vu) := by simp [Matrix.mul_assoc]
      _ = Vu := by rw [hVu_iso, Matrix.mul_one]
  have hPvVv : Pv * Vv = Vv := by
    calc
      Pv * Vv = (Vv * Vvᴴ) * Vv := by rw [hVv_range]
      _ = Vv * (Vvᴴ * Vv) := by simp [Matrix.mul_assoc]
      _ = Vv := by rw [hVv_iso, Matrix.mul_one]
  have hC_Vu : ∀ i : Fin d₀, C i * Vu = Vu * Au i := by
    intro i
    calc
      C i * Vu = C i * (Pu * Vu) := by rw [hPuVu]
      _ = (C i * Pu) * Vu := by simp [Matrix.mul_assoc]
      _ = (Pu * C i) * Vu := by rw [hComm_u i]
      _ = (Pu * C i) * (Pu * Vu) := by rw [hPuVu]
      _ = (Pu * C i * Pu) * Vu := by simp [Matrix.mul_assoc]
      _ = (Vu * Au i * Vuᴴ) * Vu := by rw [← hLetter_u i]
      _ = Vu * Au i := by simp [Matrix.mul_assoc, hVu_iso]
  have hC_Vv : ∀ i : Fin d₀, C i * Vv = Vv * Av i := by
    intro i
    calc
      C i * Vv = C i * (Pv * Vv) := by rw [hPvVv]
      _ = (C i * Pv) * Vv := by simp [Matrix.mul_assoc]
      _ = (Pv * C i) * Vv := by rw [hComm_v i]
      _ = (Pv * C i) * (Pv * Vv) := by rw [hPvVv]
      _ = (Pv * C i * Pv) * Vv := by simp [Matrix.mul_assoc]
      _ = (Vv * Av i * Vvᴴ) * Vv := by rw [← hLetter_v i]
      _ = Vv * Av i := by simp [Matrix.mul_assoc, hVv_iso]
  let U : MatrixAlg D := Vu * Y * Vvᴴ
  have hU_cancel : Vuᴴ * U * Vv = Y := by
    calc
      Vuᴴ * U * Vv = (Vuᴴ * Vu) * Y * (Vvᴴ * Vv) := by
        simp [U, Matrix.mul_assoc]
      _ = Y := by simp [hVu_iso, hVv_iso]
  have hU_ne : U ≠ 0 := by
    intro hU_zero
    apply hY_ne
    have hcancel :=
      congr_arg (fun Z : MatrixAlg D => Vuᴴ * Z * Vv) hU_zero
    simpa [hU_cancel] using hcancel
  have hSupp : U = Pu * U * Pv := by
    have hPuUPv : Pu * U * Pv = U := by
      calc
        Pu * U * Pv = (Vu * Vuᴴ) * (Vu * Y * Vvᴴ) * (Vv * Vvᴴ) := by
          rw [hVu_range, hVv_range]
        _ = Vu * ((Vuᴴ * Vu) * Y * (Vvᴴ * Vv)) * Vvᴴ := by
          simp [Matrix.mul_assoc]
        _ = U := by
          rw [hVu_iso, hVv_iso]
          simp [U, Matrix.mul_assoc]
    exact hPuUPv.symm
  have hEig : transferMap (d := d₀) (D := D) C U = (star η) • U := by
    calc
      transferMap (d := d₀) (D := D) C U =
          ∑ i : Fin d₀, C i * (Vu * Y * Vvᴴ) * (C i)ᴴ := by
        simp [transferMap_apply, U]
      _ = ∑ i : Fin d₀, Vu * (Au i * Y * (Av i)ᴴ) * Vvᴴ := by
        refine Finset.sum_congr rfl ?_
        intro i _
        have hright_i : Vvᴴ * (C i)ᴴ = (Av i)ᴴ * Vvᴴ := by
          have hct := congrArg Matrix.conjTranspose (hC_Vv i)
          simpa [Matrix.conjTranspose_mul] using hct
        calc
          C i * (Vu * Y * Vvᴴ) * (C i)ᴴ =
              (C i * Vu) * Y * (Vvᴴ * (C i)ᴴ) := by
            simp [Matrix.mul_assoc]
          _ = (Vu * Au i) * Y * ((Av i)ᴴ * Vvᴴ) := by
            rw [hC_Vu i, hright_i]
          _ = Vu * (Au i * Y * (Av i)ᴴ) * Vvᴴ := by
            simp [Matrix.mul_assoc]
      _ = Vu * (∑ i : Fin d₀, Au i * Y * (Av i)ᴴ) * Vvᴴ := by
        rw [← Matrix.sum_mul, ← Matrix.mul_sum]
      _ = Vu * mixedTransferMap Au Av Y * Vvᴴ := by
        simp [mixedTransferMap_apply]
      _ = (star η) • U := by
        rw [hMixed]
        simp [U, Matrix.mul_assoc]
  exact ⟨U, star η, by simpa [norm_star] using hη_norm, hU_ne, hSupp, hEig⟩

/-- Casted-left form of
`exists_offDiag_eigenvector_of_gaugePhase_same_dim`.

Source: arXiv:1708.00029, Lemma bdcf, lines 409--421.  The equality of compressed
bond dimensions is eliminated here, where the right dimension is a variable. -/
lemma exists_offDiag_eigenvector_of_gaugePhase_cast_left
    [NeZero D] {d₀ Du Dv : ℕ} [NeZero Du]
    (hdim : Dv = Du)
    (C : MPSTensor d₀ D) (Au : MPSTensor d₀ Du) (Av : MPSTensor d₀ Dv)
    (hAu_left : IsLeftCanonical Au) (hAv_left : IsLeftCanonical Av)
    (hAv_irr : IsIrreducibleTensor Av)
    {Pu Pv : MatrixAlg D}
    (hComm_u : ∀ i : Fin d₀, Pu * C i = C i * Pu)
    (hComm_v : ∀ i : Fin d₀, Pv * C i = C i * Pv)
    {Vu : Matrix (Fin D) (Fin Du) ℂ} {Vv : Matrix (Fin D) (Fin Dv) ℂ}
    (hVu_iso : Vuᴴ * Vu = 1) (hVv_iso : Vvᴴ * Vv = 1)
    (hVu_range : Vu * Vuᴴ = Pu) (hVv_range : Vv * Vvᴴ = Pv)
    (hLetter_u : ∀ i : Fin d₀, Vu * Au i * Vuᴴ = Pu * C i * Pu)
    (hLetter_v : ∀ i : Fin d₀, Vv * Av i * Vvᴴ = Pv * C i * Pv)
    (hGPE : GaugePhaseEquiv (cast (congr_arg (MPSTensor d₀) hdim.symm) Au) Av) :
    ∃ (U : MatrixAlg D) (ζ : ℂ), ‖ζ‖ = 1 ∧ U ≠ 0 ∧
      U = Pu * U * Pv ∧ transferMap (d := d₀) (D := D) C U = ζ • U := by
  cases hdim
  exact
    exists_offDiag_eigenvector_of_gaugePhase_same_dim
      C Au Av hAu_left hAv_left hAv_irr hComm_u hComm_v
      hVu_iso hVv_iso hVu_range hVv_range hLetter_u hLetter_v
      (by simpa using hGPE)

end MPSTensor
