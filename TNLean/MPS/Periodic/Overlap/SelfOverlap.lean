/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Overlap.SelfOverlapSetup
import TNLean.MPS.Periodic.Overlap.SelfOverlapNonrep

/-!
# Periodic overlap dichotomy: self-overlap

This module contains the self-overlap results from the first paragraph of
Appendix A of arXiv:1708.00029, using the cyclic-sector setup and auxiliary
non-repetition lemmas developed in `SelfOverlapSetup`.

## Main declarations

* `sectorOverlap_tendsto_delta_of_cyclicSectorDecomp`
* `blockTensor_selfOverlap_tendsto_of_cyclicSectorDecomp`
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

/-- Distinct compressed cyclic sectors cannot be gauge-phase equivalent.

This is the **non-repetition** half of Lemma bdcf of arXiv:1708.00029
(the proof is at lines 409--423): the blocks C_u = P_u A^{(m)} of a periodic
block form a basis of *non-repeated* normal tensors. The hypotheses here repackage
the Lemma bdcf hypotheses: `P` are the orthogonal projectors of the off-diagonal
decomposition (`hPproj`, `hPsum`), `hCyclic` is the adjoint-transfer shift
𝓔_A^{*}(P_{k+1}) = P_k, `hComm` is the commutation of each P_k with the
blocked letters, and `hTrace` realizes each compressed MPV as
tr(P_k · evalWord …). The orthogonality P_u P_v = 0 (u ≠ v) is the
off-diagonal support condition.

**Paper's argument (Lemma bdcf, lines 409--423).** Since `A` is a periodic
block, 𝓔_A is irreducible with peripheral spectrum {ω^r}_{r=0}^{m-1},
ω = e^{2πi/m}. The blocked map 𝓔_A^m then has 1 as its *only* modulus-one
eigenvalue (with multiplicity `m`), and its fixed-point set is exactly
{P_u Λ_A P_u}_u (with Λ_A the fixed point of 𝓔_A), while the fixed points
of the adjoint 𝓔_A^{*m} are exactly {P_u}_u. Suppose, for u ≠ v, a
gauge-phase equivalence C_u^{i} = e^{iξ} U C_v^{i} U† held, with U = P_u U P_v
(U U† = P_u, U† U = P_v). Then
𝓔_A^m(U) = Σ_i C_u^i U C_v^{i†} = e^{iξ} U Σ_i C_v^i C_v^{i†} = e^{iξ} U,
using 𝓔_{C_v}(P_v) = P_v. Thus U is a modulus-one eigenvector of 𝓔_A^m;
but the only such eigenvalue is 1 with the *diagonal* fixed points
{P_w Λ_A P_w}, whereas U = P_u U P_v is off-diagonal for u ≠ v — a
contradiction. Hence no such equivalence exists.

**Correctness — the `IsPeriodic m A` hypothesis is load-bearing.** The spectral
argument requires `A` to be a periodic (irreducible) block: that is what gives
𝓔_A the peripheral spectrum {ω^r} and makes each cyclic sector primitive. Without
it the statement is FALSE — the bare cyclic-projection data (orthogonal `P_k`
summing to `1`, the adjoint shift, blocked commutation, the trace formula) is
consistent with a *reducible* `A` (e.g. `B ⊕ B` for an irreducible period-`m`
block `B`) whose distinct sectors are gauge-phase equivalent. `hP` is supplied at
the unique call site `sectorBlocks_not_gaugePhaseEquiv_of_ne`. -/
private lemma not_gaugePhaseEquiv_of_orthogonal_cyclicSector_traces
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
    {φ : (k : Fin m) →
      Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k)}
    (hIntertwine : ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k (transferMap (d := blockPhysDim d m) (D := dim k)
          (fun i => (blocks k i)ᴴ) X)).1 =
        transferMap (d := blockPhysDim d m) (D := D)
          (fun i => (P k * blockTensor A m i)ᴴ) ((φ k X).1))
    (hMul : ∀ k (X Y : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k (X * Y)).1 = (φ k X).1 * (φ k Y).1)
    (hStar : ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k Xᴴ).1 = ((φ k X).1)ᴴ)
    (hLetter : ∀ k (i : Fin (blockPhysDim d m)),
      (φ k (blocks k i)).1 = P k * (blockTensor A m) i * P k)
    {V : (k : Fin m) → Matrix (Fin D) (Fin (dim k)) ℂ}
    (hV_iso : ∀ k, (V k)ᴴ * V k = 1)
    (hV_range : ∀ k, V k * (V k)ᴴ = P k)
    (hEmbed : ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k X).1 = V k * X * (V k)ᴴ)
    (hNondeg : ∀ k, dim k ≠ 0)
    {u v : Fin m} (_huv : u ≠ v) (hdim : dim v = dim u)
    (hOrth : P u * P v = 0) :
    ¬ GaugePhaseEquiv
      (cast (congr_arg (MPSTensor (blockPhysDim d m)) hdim.symm) (blocks u))
      (blocks v) := by
  intro hGPE
  have hCyclicDecomp : IsCyclicSectorDecomp A blocks :=
    ⟨P, φ, hPproj, hPsum, hCyclic, hComm, hTrace, hIntertwine, hMul, hStar⟩
  have hIrr_v : IsIrreducibleTensor (blocks v) :=
    (primitive_and_irreducible_sectorBlocks_of_cyclicDecomp
      A hP blocks hBlocks_lc hBlocks_mpv hCyclicDecomp v (hNondeg v)).2
  have hCorner_u : ∀ i : Fin (blockPhysDim d m),
      V u * blocks u i * (V u)ᴴ = P u * (blockTensor A m) i * P u := by
    intro i
    calc
      V u * blocks u i * (V u)ᴴ = (φ u (blocks u i)).1 := by
        exact (hEmbed u (blocks u i)).symm
      _ = P u * (blockTensor A m) i * P u := hLetter u i
  have hCorner_v : ∀ i : Fin (blockPhysDim d m),
      V v * blocks v i * (V v)ᴴ = P v * (blockTensor A m) i * P v := by
    intro i
    calc
      V v * blocks v i * (V v)ᴴ = (φ v (blocks v i)).1 := by
        exact (hEmbed v (blocks v i)).symm
      _ = P v * (blockTensor A m) i * P v := hLetter v i
  -- The gauge-phase relation gives a nonzero vector in the `(u,v)` corner; the
  -- period-transfer contradiction then forces it to vanish.
  obtain ⟨U, ζ, hζ, hU_ne, hSupp, hEig⟩ :
      ∃ (U : MatrixAlg D) (ζ : ℂ), ‖ζ‖ = 1 ∧ U ≠ 0 ∧ U = P u * U * P v ∧
        ((transferMap (d := d) (D := D) A) ^ m) U = ζ • U := by
    haveI : NeZero (dim u) := ⟨hNondeg u⟩
    obtain ⟨U, ζ, hζ, hU_ne, hSupp, hEig_block⟩ :=
      exists_offDiag_eigenvector_of_gaugePhase_cast_left
        (D := D) (d₀ := blockPhysDim d m) (Du := dim u) (Dv := dim v) hdim
        (C := blockTensor A m) (Au := blocks u) (Av := blocks v)
        (hBlocks_lc u) (hBlocks_lc v) hIrr_v
        (fun i => hComm u i) (fun i => hComm v i)
        (hV_iso u) (hV_iso v) (hV_range u) (hV_range v)
        hCorner_u hCorner_v hGPE
    refine ⟨U, ζ, hζ, hU_ne, hSupp, ?_⟩
    simpa [transferMap_blockTensor] using hEig_block
  exact hU_ne
    (offDiag_eigenvector_eq_zero_of_isPeriodic A hP hPproj hPsum hCyclic hOrth
      hζ hSupp hEig)

/-- Distinct compressed sectors of a cyclic sector decomposition are not gauge-phase
equivalent.

Mathematically, a gauge-phase equivalence would identify the two compressed MPV traces.
Through `IsCyclicSectorDecomp`, those traces are
`tr(P u · evalWord(blockTensor A m) w)` and
`tr(P v · evalWord(blockTensor A m) w)`.  The projections in a cyclic
decomposition are orthogonal corners, so for `u ≠ v` these corner states cannot
be related by an invertible gauge and nonzero scalar.

The cyclic-sector decomposition supplies the trace formula and projection data. The
missing mathematical input is orthogonal-corner rigidity: distinct cyclic corners
cannot be related by an invertible gauge and a nonzero scalar. -/
private lemma sectorBlocks_not_gaugePhaseEquiv_of_ne
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
    {P : Fin m → MatrixAlg D}
    {φ : (k : Fin m) →
      Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k)}
    (hPproj : ∀ k, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hCyclicP :
      ∀ k, transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (hComm :
      ∀ k (i : Fin (blockPhysDim d m)),
        P k * (blockTensor A m) i = (blockTensor A m) i * P k)
    (hTrace :
      ∀ k (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)),
        mpv (blocks k) σ = (P k * evalWord (blockTensor A m) (List.ofFn σ)).trace)
    (hIntertwine : ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k (transferMap (d := blockPhysDim d m) (D := dim k)
          (fun i => (blocks k i)ᴴ) X)).1 =
        transferMap (d := blockPhysDim d m) (D := D)
          (fun i => (P k * blockTensor A m i)ᴴ) ((φ k X).1))
    (hMul : ∀ k (X Y : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k (X * Y)).1 = (φ k X).1 * (φ k Y).1)
    (hStar : ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k Xᴴ).1 = ((φ k X).1)ᴴ)
    (hLetter : ∀ k (i : Fin (blockPhysDim d m)),
      (φ k (blocks k i)).1 = P k * (blockTensor A m) i * P k)
    {V : (k : Fin m) → Matrix (Fin D) (Fin (dim k)) ℂ}
    (hV_iso : ∀ k, (V k)ᴴ * V k = 1)
    (hV_range : ∀ k, V k * (V k)ᴴ = P k)
    (hEmbed : ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k X).1 = V k * X * (V k)ᴴ)
    (hNondeg : ∀ k, dim k ≠ 0)
    {u v : Fin m} (huv : u ≠ v) (hdim : dim u = dim v) :
    ¬ GaugePhaseEquiv
      (cast (congr_arg (MPSTensor (blockPhysDim d m)) hdim) (blocks u))
      (blocks v) := by
  have hPairwise : Pairwise fun i j : Fin m => P i * P j = 0 :=
    pairwise_mul_zero_of_orthogonalProjection_sum_one P hPproj hPsum
  have hOrth : P u * P v = 0 := hPairwise huv
  exact
    not_gaugePhaseEquiv_of_orthogonal_cyclicSector_traces
      A hP blocks hBlocks_lc hBlocks_mpv hPproj hPsum hCyclicP hComm hTrace
      hIntertwine hMul hStar hLetter hV_iso hV_range hEmbed hNondeg huv hdim.symm hOrth

/-- Sector-asymptotic step for the self-overlap proof.

After blocking by the period, the cyclic sector decomposition should make each
compressed sector a primitive normalized tensor, while distinct sectors are
asymptotically orthogonal.

This theorem isolates the passage from cyclic-sector decomposition data to the
overlap-asymptotic statement. -/
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
    {P : Fin m → MatrixAlg D}
    {φ : (k : Fin m) →
      Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k)}
    (hPproj : ∀ k, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hCyclicP :
      ∀ k, transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (hComm :
      ∀ k (i : Fin (blockPhysDim d m)),
        P k * (blockTensor A m) i = (blockTensor A m) i * P k)
    (hTrace :
      ∀ k (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)),
        mpv (blocks k) σ = (P k * evalWord (blockTensor A m) (List.ofFn σ)).trace)
    (hIntertwine : ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k (transferMap (d := blockPhysDim d m) (D := dim k)
          (fun i => (blocks k i)ᴴ) X)).1 =
        transferMap (d := blockPhysDim d m) (D := D)
          (fun i => (P k * blockTensor A m i)ᴴ) ((φ k X).1))
    (hMul : ∀ k (X Y : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k (X * Y)).1 = (φ k X).1 * (φ k Y).1)
    (hStar : ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k Xᴴ).1 = ((φ k X).1)ᴴ)
    (hLetter : ∀ k (i : Fin (blockPhysDim d m)),
      (φ k (blocks k i)).1 = P k * (blockTensor A m) i * P k)
    {V : (k : Fin m) → Matrix (Fin D) (Fin (dim k)) ℂ}
    (hV_iso : ∀ k, (V k)ᴴ * V k = 1)
    (hV_range : ∀ k, V k * (V k)ᴴ = P k)
    (hEmbed : ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k X).1 = V k * X * (V k)ᴴ)
    (hNondeg : ∀ k, dim k ≠ 0)
    (u v : Fin m) :
    Tendsto
      (fun k => mpvOverlap (d := blockPhysDim d m) (blocks u) (blocks v) k)
      atTop (nhds (if u = v then (1 : ℂ) else 0)) := by
  classical
  have hCyclic : IsCyclicSectorDecomp A blocks :=
    ⟨P, φ, hPproj, hPsum, hCyclicP, hComm, hTrace, hIntertwine, hMul, hStar⟩
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
          A hP blocks hBlocks_lc hBlocks_mpv hPproj hPsum hCyclicP hComm hTrace
          hIntertwine hMul hStar hLetter hV_iso hV_range hEmbed hNondeg huv hdim
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
    {P : Fin m → MatrixAlg D}
    {φ : (k : Fin m) →
      Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k)}
    (hPproj : ∀ k, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hCyclicP :
      ∀ k, transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (hComm :
      ∀ k (i : Fin (blockPhysDim d m)),
        P k * (blockTensor A m) i = (blockTensor A m) i * P k)
    (hTrace :
      ∀ k (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)),
        mpv (blocks k) σ = (P k * evalWord (blockTensor A m) (List.ofFn σ)).trace)
    (hIntertwine : ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k (transferMap (d := blockPhysDim d m) (D := dim k)
          (fun i => (blocks k i)ᴴ) X)).1 =
        transferMap (d := blockPhysDim d m) (D := D)
          (fun i => (P k * blockTensor A m i)ᴴ) ((φ k X).1))
    (hMul : ∀ k (X Y : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k (X * Y)).1 = (φ k X).1 * (φ k Y).1)
    (hStar : ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k Xᴴ).1 = ((φ k X).1)ᴴ)
    (hLetter : ∀ k (i : Fin (blockPhysDim d m)),
      (φ k (blocks k i)).1 = P k * (blockTensor A m) i * P k)
    {V : (k : Fin m) → Matrix (Fin D) (Fin (dim k)) ℂ}
    (hV_iso : ∀ k, (V k)ᴴ * V k = 1)
    (hV_range : ∀ k, V k * (V k)ᴴ = P k)
    (hEmbed : ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k X).1 = V k * X * (V k)ᴴ)
    (hNondeg : ∀ k, dim k ≠ 0) :
    Tendsto
      (fun k => mpvOverlap (d := blockPhysDim d m)
        (blockTensor (d := d) (D := D) A m)
        (blockTensor (d := d) (D := D) A m) k)
      atTop (nhds (m : ℂ)) := by
  classical
  have hOverlap_eq : ∀ N,
      mpvOverlap (d := blockPhysDim d m)
          (blockTensor (d := d) (D := D) A m)
          (blockTensor (d := d) (D := D) A m) N =
        ∑ u : Fin m, ∑ v : Fin m,
          mpvOverlap (d := blockPhysDim d m) (blocks u) (blocks v) N := by
    intro N
    exact mpvOverlap_eq_sum_of_sameMPV₂_toTensorFromBlocks_one
      (blockTensor (d := d) (D := D) A m)
      (blockTensor (d := d) (D := D) A m)
      blocks blocks hBlocks_mpv hBlocks_mpv N
  have hInner : ∀ u : Fin m,
      Tendsto
        (fun N => ∑ v : Fin m,
          mpvOverlap (d := blockPhysDim d m) (blocks u) (blocks v) N)
        atTop (nhds (∑ v : Fin m, if u = v then (1 : ℂ) else 0)) := by
    intro u
    exact tendsto_finset_sum (s := Finset.univ) fun v _ =>
      sectorOverlap_tendsto_delta_of_cyclicSectorDecomp
        A hP blocks hBlocks_lc hBlocks_mpv hPproj hPsum hCyclicP hComm hTrace
        hIntertwine hMul hStar hLetter hV_iso hV_range hEmbed hNondeg u v
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
  letI : NeZero m := ⟨Nat.ne_of_gt hP.period_pos⟩
  obtain ⟨dim, blocks, P, φ, V, hBlocks_lc, hBlocks_mpv, hPproj, hPsum, hCyclicRaw,
    hComm, hTrace, hIntertwine, hMul, hStar, hNondeg, hLetterRaw, hV_iso, hV_range,
    hEmbed⟩ :=
    exists_cyclic_sector_decomp_with_letter_and_isometry_after_blocking_of_isPeriodic A hP
  have hCyclicP :
      ∀ k, transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k := by
    intro k
    simpa [cyclicNextOfPos, Fin.add_def] using hCyclicRaw k
  have hBlocked :
      Tendsto
        (fun k => mpvOverlap (d := blockPhysDim d m)
          (blockTensor (d := d) (D := D) A m)
          (blockTensor (d := d) (D := D) A m) k)
        atTop (nhds (m : ℂ)) :=
    blockTensor_selfOverlap_tendsto_of_cyclicSectorDecomp
      A hP blocks hBlocks_lc hBlocks_mpv hPproj hPsum hCyclicP hComm hTrace
      hIntertwine hMul hStar hLetterRaw hV_iso hV_range hEmbed hNondeg
  refine hBlocked.congr' ?_
  filter_upwards with k
  rw [mpvOverlap_blockTensor_self_eq]
  simp [Nat.mul_comm]


end MPSTensor
