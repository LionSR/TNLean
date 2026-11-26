/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.PrimitiveFixedPoint.FromPeripheral
import QICLean.Algebra.Combinatorics.IndexInduction
import TNLean.MPS.Transfer.Spectrum.GaugePhase
import TNLean.MPS.CanonicalForm.Periodic.Overlap.SectorMatchContraction
import TNLean.MPS.CanonicalForm.Periodic.Overlap.NoSectorMatch

/-!
# Periodic sector-match propagation

This module proves that one matching pair of sectors propagates around the
whole periodic orbit.

## Main declarations

* `sectorMatch_propagation`
* `MPSTensor.periodicOverlap_gaugeEquiv_of_sector_match`,
  `MPSTensor.periodicOverlap_tendsto_zero_of_ne_dim`: consequences of periodic sector matching.
* `MPSTensor.rotateCfg`, `MPSTensor.sectorOverlap_succ_eq_of_cyclicSectorDecomp`: periodic overlap
  dichotomy: Case 3 transport.

## References

* De las Cuevas, Cirac, Schuch, Perez-Garcia,
  *Irreducible forms of Matrix Product States: Theory and Applications*,
  arXiv:1708.00029, Appendix A.
-/

open MPTensor

section SectorOverlapTransport

/-!
## Periodic overlap dichotomy: Case 3 transport

This module contains the one-site transport of cross-sector overlaps used in
the equal-period sector-match case of arXiv:1708.00029, Appendix A.
-/

open scoped Matrix BigOperators ComplexOrder InnerProductSpace
open Filter Matrix
open Kraus (blockPhysDim blockTensor evalWord_blockTensor)

namespace MPSTensor

variable {d D : ℕ}

/-! ### One-site rotation covariance of the cross sector overlap

The translation-operator step of arXiv:1708.00029, Appendix A (lines 985--1002)
moves the matched sector pair `(u, v)` to `(u+1, v+1)`.  Formalized below as a
single physical-site cyclic rotation of the underlying word: the single-site
off-diagonal shift `P_{k+1} A^i = A^i P_k` (eq:Aoffdiag, supplied by
`offDiag_shift_of_adjoint_cyclic_shift`) carries the cyclic index forward by one
per site, and the trace is invariant under cyclic rotation of the word, so the
cross overlap is unchanged by the simultaneous shift. -/

/-- One-site cyclic rotation of a configuration of length `L'+1`:
move the last letter to the front. -/
def rotateCfg {d L' : ℕ} : (Fin (L' + 1) → Fin d) ≃ (Fin (L' + 1) → Fin d) :=
  Equiv.arrowCongr (finRotate (L' + 1)) (Equiv.refl (Fin d))

/-- Word evaluation of the rotated configuration pulls the last letter to the front. -/
private lemma evalWord_ofFn_rotateCfg {L' : ℕ} (A : MPSTensor d D)
    (σ : Fin (L' + 1) → Fin d) :
    Kraus.evalWord A (List.ofFn (rotateCfg σ)) =
      A (σ (Fin.last L')) * Kraus.evalWord A (List.ofFn (Fin.init σ)) := by
  have hrotate : rotateCfg σ = Fin.cons (σ (Fin.last L')) (Fin.init σ) := by
    funext j
    refine Fin.cases ?_ ?_ j
    · change σ ((finRotate (L' + 1)).symm 0) = σ (Fin.last L')
      exact congrArg σ (Fin.ext (by simp))
    · intro i
      change σ ((finRotate (L' + 1)).symm i.succ) = σ i.castSucc
      exact congrArg σ (Fin.ext (by
        rw [finRotate_symm_apply]
        rw [Fin.val_sub_one_of_ne_zero (by simp)]
        simp))
  simp only [hrotate, List.ofFn_cons, Kraus.evalWord_cons]

/-- Word evaluation of the original configuration pulls the last letter to the right. -/
private lemma evalWord_ofFn_eq_init_mul_last {L' : ℕ} (A : MPSTensor d D)
    (σ : Fin (L' + 1) → Fin d) :
    Kraus.evalWord A (List.ofFn σ) =
      Kraus.evalWord A (List.ofFn (Fin.init σ)) * A (σ (Fin.last L')) := by
  rw [List.ofFn_succ']
  rw [show (List.ofFn fun i => σ (Fin.castSucc i)) = List.ofFn (Fin.init σ) from rfl]
  rw [List.concat_eq_append, Kraus.evalWord_append]
  simp

/-- **Per-configuration trace covariance** under one-site rotation (eq:Aoffdiag,
arXiv:1708.00029 lines 985--1002).  Given the single-site off-diagonal shift
`P (k+1) * A i = A i * P k`, the projector-weighted trace at index `k+1` of the
rotated word equals the projector-weighted trace at index `k` of the original
word. -/
private lemma trace_proj_evalWord_rotateCfg {L' m : ℕ} [NeZero m] (A : MPSTensor d D)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hShift : ∀ (k : Fin m) (i : Fin d), P (k + 1) * A i = A i * P k)
    (k : Fin m) (σ : Fin (L' + 1) → Fin d) :
    (P (k + 1) * Kraus.evalWord A (List.ofFn (rotateCfg σ))).trace =
      (P k * Kraus.evalWord A (List.ofFn σ)).trace := by
  rw [evalWord_ofFn_rotateCfg, evalWord_ofFn_eq_init_mul_last]
  -- `tr(P(k+1) * A(last) * W)`: apply the shift, then cycle the trace.
  rw [← Matrix.mul_assoc, hShift k (σ (Fin.last L'))]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]

/-- **Physical projector-overlap covariance** under one-site rotation.
The cross overlap built from projector-weighted traces is invariant under the
simultaneous one-step shift `(u, v) → (u+1, v+1)`, for any positive length
(arXiv:1708.00029 lines 985--1002, translation operator `T`). -/
private lemma sum_trace_proj_overlap_shift {L' m : ℕ} [NeZero m]
    (A B : MPSTensor d D)
    (P Q : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hShiftA : ∀ (k : Fin m) (i : Fin d), P (k + 1) * A i = A i * P k)
    (hShiftB : ∀ (k : Fin m) (i : Fin d), Q (k + 1) * B i = B i * Q k)
    (u v : Fin m) :
    (∑ σ : Fin (L' + 1) → Fin d,
        (P (u + 1) * Kraus.evalWord A (List.ofFn σ)).trace *
          star ((Q (v + 1) * Kraus.evalWord B (List.ofFn σ)).trace)) =
      ∑ σ : Fin (L' + 1) → Fin d,
        (P u * Kraus.evalWord A (List.ofFn σ)).trace *
          star ((Q v * Kraus.evalWord B (List.ofFn σ)).trace) := by
  rw [← Equiv.sum_comp (rotateCfg (d := d) (L' := L'))
    (fun σ => (P (u + 1) * Kraus.evalWord A (List.ofFn σ)).trace *
      star ((Q (v + 1) * Kraus.evalWord B (List.ofFn σ)).trace))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [trace_proj_evalWord_rotateCfg A P hShiftA u σ,
    trace_proj_evalWord_rotateCfg B Q hShiftB v σ]

/-- The cross overlap of two compressed cyclic sectors, expanded via the
`IsCyclicSectorDecomp` trace formula and reindexed to physical configurations
of length `N * m`. -/
private lemma sectorOverlap_eq_physical_sum {m : ℕ} [NeZero m]
    (A B : MPSTensor d D)
    {dimA dimB : Fin m → ℕ}
    (blocksA : (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB : (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (PA PB : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hTraceA : ∀ k (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)),
      mpv (blocksA k) σ = (PA k * Kraus.evalWord (blockTensor A m) (List.ofFn σ)).trace)
    (hTraceB : ∀ k (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)),
      mpv (blocksB k) σ = (PB k * Kraus.evalWord (blockTensor B m) (List.ofFn σ)).trace)
    (u v : Fin m) (N : ℕ) :
    mpvOverlap (d := blockPhysDim d m) (blocksA u) (blocksB v) N =
      ∑ τ : Fin (N * m) → Fin d,
        (PA u * Kraus.evalWord A (List.ofFn τ)).trace *
          star ((PB v * Kraus.evalWord B (List.ofFn τ)).trace) := by
  classical
  rw [mpvOverlap]
  rw [← Equiv.sum_comp (blockedConfigEquiv d N m)
    (fun τ : Fin (N * m) → Fin d =>
      (PA u * Kraus.evalWord A (List.ofFn τ)).trace *
        star ((PB v * Kraus.evalWord B (List.ofFn τ)).trace))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hTraceA u N σ, hTraceB v N σ, ofFn_blockedConfigEquiv]
  rw [← evalWord_blockTensor, ← evalWord_blockTensor]

/-- **One-step transport of the cross sector overlap** (positive lengths,
arXiv:1708.00029 lines 985--1002).  For `N ≥ 1`, the cross overlap of compressed
cyclic sectors is invariant under the simultaneous index shift
`(u, v) → (u+1, v+1)`. -/
private lemma sectorOverlap_succ_eq {m : ℕ} [NeZero m]
    (A B : MPSTensor d D)
    (hA_lc : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_lc : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    {dimA dimB : Fin m → ℕ}
    (blocksA : (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB : (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (PA PB : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hPAproj : ∀ k, IsOrthogonalProjection (PA k))
    (hPBproj : ∀ k, IsOrthogonalProjection (PB k))
    (hShiftA : ∀ k, Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (A i)ᴴ) (PA (k + 1)) =
      PA k)
    (hShiftB : ∀ k, Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (B i)ᴴ) (PB (k + 1)) =
      PB k)
    (hTraceA : ∀ k (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)),
      mpv (blocksA k) σ = (PA k * Kraus.evalWord (blockTensor A m) (List.ofFn σ)).trace)
    (hTraceB : ∀ k (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)),
      mpv (blocksB k) σ = (PB k * Kraus.evalWord (blockTensor B m) (List.ofFn σ)).trace)
    (u v : Fin m) (N : ℕ) (hN : 0 < N) :
    mpvOverlap (d := blockPhysDim d m) (blocksA (u + 1)) (blocksB (v + 1)) N =
      mpvOverlap (d := blockPhysDim d m) (blocksA u) (blocksB v) N := by
  have hLetterA := offDiag_shift_of_adjoint_cyclic_shift A hA_lc hPAproj hShiftA
  have hLetterB := offDiag_shift_of_adjoint_cyclic_shift B hB_lc hPBproj hShiftB
  rw [sectorOverlap_eq_physical_sum A B blocksA blocksB PA PB hTraceA hTraceB,
    sectorOverlap_eq_physical_sum A B blocksA blocksB PA PB hTraceA hTraceB]
  obtain ⟨L', hL'⟩ : ∃ L', N * m = L' + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.mul_ne_zero hN.ne' (NeZero.ne m))
  rw [hL']
  exact sum_trace_proj_overlap_shift A B PA PB hLetterA hLetterB u v

/-- **One-step transport of sector overlaps from cyclic-sector decompositions.**

For positive lengths, the cross overlap of the compressed cyclic sectors is
invariant under the simultaneous index shift (u, v) ↦ (u + 1, v + 1).
This is the formal overlap version of the translation-operator step in
arXiv:1708.00029, lines 985--1002. -/
lemma sectorOverlap_succ_eq_of_cyclicSectorDecomp {m : ℕ} [NeZero m]
    (A B : MPSTensor d D)
    (hA_lc : IsLeftCanonical A) (hB_lc : IsLeftCanonical B)
    {dimA dimB : Fin m → ℕ}
    (blocksA : (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB : (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (hA_cyclic : IsCyclicSectorDecomp A blocksA)
    (hB_cyclic : IsCyclicSectorDecomp B blocksB)
    (u v : Fin m) (N : ℕ) (hN : 0 < N) :
    mpvOverlap (d := blockPhysDim d m) (blocksA (u + 1)) (blocksB (v + 1)) N =
      mpvOverlap (d := blockPhysDim d m) (blocksA u) (blocksB v) N := by
  obtain ⟨PA, _φA, hPAproj, _hPAsum, hShiftA, _hCommA, hTraceA, _⟩ := hA_cyclic
  obtain ⟨PB, _φB, hPBproj, _hPBsum, hShiftB, _hCommB, hTraceB, _⟩ := hB_cyclic
  exact sectorOverlap_succ_eq A B hA_lc hB_lc blocksA blocksB PA PB
    hPAproj hPBproj hShiftA hShiftB hTraceA hTraceB u v N hN

end MPSTensor

end SectorOverlapTransport

section SectorMatchPropagation

open scoped Matrix BigOperators ComplexOrder InnerProductSpace TensorProduct Kraus
open Filter Matrix Module
open Kraus (blockPhysDim blockTensor)

namespace MPSTensor

variable {d D : ℕ}

/-! ## Case 3: Same period, sector match → gauge-equivalent (Appendix A, main case) -/

/-- From a gauge-phase match between two irreducible, transfer-primitive,
trace-preserving sectors of the same bond dimension, the cross overlap has norm
tending to `1`.  The unit modulus of the gauge phase follows from the matching
self-overlap limits (arXiv:1606.00608, Lemma equalMPS). -/
private lemma overlap_norm_tendsto_one_of_gaugePhase_cast
    {DA DB : ℕ} [NeZero DA] [NeZero DB]
    (CA : MPSTensor d DA) (CB : MPSTensor d DB)
    (hdim : DA = DB)
    (hCA_irr : Kraus.IsIrreducibleFamily CA) (hCB_irr : Kraus.IsIrreducibleFamily CB)
    (hCA_norm : ∑ i : Fin d, (CA i)ᴴ * CA i = 1)
    (hCB_norm : ∑ i : Fin d, (CB i)ᴴ * CB i = 1)
    (hCA_prim : _root_.IsPrimitive (Kraus.transferMap (ι := Fin d) (n := Fin DA) CA))
    (hCB_prim : _root_.IsPrimitive (Kraus.transferMap (ι := Fin d) (n := Fin DB) CB))
    (hMatch : GaugePhaseEquiv (cast (congr_arg (MPSTensor d) hdim) CA) CB) :
    Tendsto (fun N => ‖mpvOverlap (d := d) CA CB N‖) atTop (nhds (1 : ℝ)) := by
  classical
  subst hdim
  simp only [cast_eq] at hMatch
  have hCA_self : Tendsto (fun N => mpvOverlap (d := d) CA CA N) atTop (nhds (1 : ℂ)) :=
    overlap_tendsto_one_of_peripheralPrimitive_of_irreducible CA hCA_irr hCA_norm hCA_prim
  have hCB_self : Tendsto (fun N => mpvOverlap (d := d) CB CB N) atTop (nhds (1 : ℂ)) :=
    overlap_tendsto_one_of_peripheralPrimitive_of_irreducible CB hCB_irr hCB_norm hCB_prim
  obtain ⟨X, ζ, _hζ, hX⟩ := hMatch
  have hmpv : ∀ (N : ℕ) (σ : Fin N → Fin d), mpv CB σ = ζ ^ N * mpv CA σ :=
    mpv_eq_pow_mul_of_gaugePhase CA CB X ζ hX
  have hζnorm : ‖ζ‖ = 1 :=
    norm_eq_one_of_selfOverlap_scale (A := CA) (B := CB) (ζ := ζ)
      (by simpa using hCA_self.norm) (by simpa using hCB_self.norm)
      (mpvOverlap_self_scale_of_mpv_eq_pow_mul (A := CA) (B := CB) (ζ := ζ) hmpv)
  have hCrossNormEq : ∀ N,
      ‖mpvOverlap (d := d) CA CB N‖ = ‖mpvOverlap (d := d) CA CA N‖ := by
    intro N
    rw [mpvOverlap_eq_star_pow_mul_self_of_mpv_eq_pow_mul (A := CA) (B := CB) (ζ := ζ) hmpv N]
    simp [norm_pow, hζnorm]
  have hCA_self_norm : Tendsto (fun N => ‖mpvOverlap (d := d) CA CA N‖) atTop (nhds (1 : ℝ)) := by
    simpa using hCA_self.norm
  exact hCA_self_norm.congr fun N => (hCrossNormEq N).symm

/-- Nonzero sector dimensions propagate one step around a cyclic sector decomposition.

The corner equivalences identify a positive-dimensional matrix algebra with the corner of
`P u`, so `P u` is nonzero. If `dim (u + 1) = 0`, the corner of `P (u + 1)` is trivial and
therefore `P (u + 1) = 0`; the cyclic relation `E†(P (u + 1)) = P u` then gives a
contradiction. -/
private lemma sectorDim_ne_zero_succ_of_cyclicSectorDecomp
    (A : MPSTensor d D)
    {m : ℕ} [NeZero m]
    {dim : Fin m → ℕ}
    (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (hCyclic : IsCyclicSectorDecomp A blocks)
    {u : Fin m} (hNondeg : dim u ≠ 0) :
    dim (u + 1) ≠ 0 := by
  classical
  obtain ⟨P, φ, hPproj, _hPsum, hShift, _hComm, _hTrace, _hIntertwine, _hMul, _hStar⟩ :=
    hCyclic
  have hPu_ne : P u ≠ 0 := by
    intro hPu
    have hφ_one_zero :
        φ u (1 : Matrix (Fin (dim u)) (Fin (dim u)) ℂ) = 0 := by
      apply Subtype.ext
      have hmem := (φ u (1 : Matrix (Fin (dim u)) (Fin (dim u)) ℂ)).property
      calc
        (φ u (1 : Matrix (Fin (dim u)) (Fin (dim u)) ℂ)).1 =
            P u * (φ u (1 : Matrix (Fin (dim u)) (Fin (dim u)) ℂ)).1 * P u := hmem.symm
        _ = 0 := by simp only [hPu, zero_mul, mul_zero]
    have hone_zero : (1 : Matrix (Fin (dim u)) (Fin (dim u)) ℂ) = 0 := by
      apply (φ u).injective
      simpa only [map_zero] using hφ_one_zero
    have : NeZero (dim u) := ⟨hNondeg⟩
    exact one_ne_zero hone_zero
  intro hzero
  have hPsucc_zero : P (u + 1) = 0 := by
    let Q : cornerSubmodule (P (u + 1)) :=
      ⟨P (u + 1), by
        change P (u + 1) * P (u + 1) * P (u + 1) = P (u + 1)
        rw [(hPproj (u + 1)).2, (hPproj (u + 1)).2]⟩
    obtain ⟨X, hX⟩ := (φ (u + 1)).surjective Q
    have hXzero : X = 0 := by
      ext i j
      exact Fin.elim0 (Fin.cast hzero i)
    have hQzero : Q = 0 := by
      rw [← hX, hXzero, map_zero]
    exact congrArg Subtype.val hQzero
  have hPu_zero : P u = 0 := by
    rw [← hShift u, hPsucc_zero, map_zero]
  exact hPu_ne hPu_zero

/-- One-step cyclic gauge-transport of a sector match.

This is the one-step form of the propagation step in arXiv:1708.00029, Appendix A
(lines 985--1002, equation eq:blockedABprop).

**Paper's argument.** Starting from the blocked sector-match equation eq:Nm
(lines 978--984), the paper applies the translation operator T^l
(l = 1, …, m-1) to *both sides*; since P_{u'+l} A^{(m)} and Q_{v'+l} B^{(m)}
are again normal tensors (Lemma bdcf), Theorem 2.10 of Cirac--Perez-Garcia 2017
(thm:cf) yields, at each offset, a phase λ_{v'+l} and a unitary
U_{v'+l} = P_{u'+l} U_{v'+l} Q_{v'+l} with
P_{u'+l} A^{(m)} = e^{iλ} U_{v'+l} Q_{v'+l} B^{(m)} U_{v'+l}†
(eq:blockedABprop). Hence the offset v - u = q is constant (eq:vprop, line
1007), which is the
one-step transport (u, v) → (u+1, v+1) stated here.

**Corner transition tensors.** Rather than translate the global
equation, the cyclic-sector construction can expose one-site corner transition
tensors — the compressions `P k · A i · P (k+1)` and `Q l · B i · Q (l+1)` — and
identify their `m`-fold cyclic products with the supplied `blocksA k`/`blocksB l`,
so that the match transports along these transitions. This is a formalization of
the same step via the `IsCyclicSectorDecomp` relation 𝓔_A^{*}(P_{k+1}) = P_k; see
docs/paper-gaps/dccsp17_periodic_overlap_route_alignment.tex. -/
private lemma sectorGaugePhaseEquiv_succ_of_cyclicTransport
    (A B : MPSTensor d D)
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
  -- The translation-operator step of arXiv:1708.00029, Appendix A (lines
  -- 985--1002), realized as a one-site cyclic rotation of the word.  The
  -- single-site off-diagonal shift `P_{k+1} A^i = A^i P_k` (eq:Aoffdiag) makes
  -- the cross sector overlap invariant under `(u, v) → (u+1, v+1)`; combined
  -- with the matching self-overlaps (each sector is a normal tensor by Lemma
  -- bdcf) the unit-modulus cross overlap reappears at `(u+1, v+1)`, giving the
  -- transported gauge-phase equivalence.
  classical
  -- Nondegeneracy of the four sectors in play.
  have hNondegB_v : dimB v ≠ 0 := hdim ▸ hNondeg
  have hNondegA_succ : dimA (u + 1) ≠ 0 :=
    sectorDim_ne_zero_succ_of_cyclicSectorDecomp A blocksA hA_cyclic hNondeg
  have hNondegB_succ : dimB (v + 1) ≠ 0 :=
    sectorDim_ne_zero_succ_of_cyclicSectorDecomp B blocksB hB_cyclic hNondegB_v
  have : NeZero (dimA u) := ⟨hNondeg⟩
  have : NeZero (dimB v) := ⟨hNondegB_v⟩
  have : NeZero (dimA (u + 1)) := ⟨hNondegA_succ⟩
  have : NeZero (dimB (v + 1)) := ⟨hNondegB_succ⟩
  -- Primitivity + irreducibility of each sector (Lemma bdcf, via periodicity).
  obtain ⟨hPrimA_u, hIrrA_u⟩ :=
    primitive_and_irreducible_sectorBlocks_of_cyclicDecomp A hA blocksA hA_blocks_lc hA_mpv
      hA_cyclic u hNondeg
  obtain ⟨hPrimB_v, hIrrB_v⟩ :=
    primitive_and_irreducible_sectorBlocks_of_cyclicDecomp B hB blocksB hB_blocks_lc hB_mpv
      hB_cyclic v hNondegB_v
  obtain ⟨_hPrimA_su, hIrrA_su⟩ :=
    primitive_and_irreducible_sectorBlocks_of_cyclicDecomp A hA blocksA hA_blocks_lc hA_mpv
      hA_cyclic (u + 1) hNondegA_succ
  obtain ⟨_hPrimB_sv, hIrrB_sv⟩ :=
    primitive_and_irreducible_sectorBlocks_of_cyclicDecomp B hB blocksB hB_blocks_lc hB_mpv
      hB_cyclic (v + 1) hNondegB_succ
  -- Step A: cross overlap norm at `(u, v)` tends to `1`.
  have hNorm_uv : Tendsto (fun N => ‖mpvOverlap (d := blockPhysDim d m) (blocksA u) (blocksB v) N‖)
      atTop (nhds (1 : ℝ)) :=
    overlap_norm_tendsto_one_of_gaugePhase_cast (blocksA u) (blocksB v) hdim
      hIrrA_u hIrrB_v (hA_blocks_lc u) (hB_blocks_lc v) hPrimA_u hPrimB_v hMatch
  -- Step B: the cross overlap is invariant under `(u, v) → (u+1, v+1)` at positive lengths.
  have hShiftEq : ∀ N : ℕ, 0 < N →
      mpvOverlap (d := blockPhysDim d m) (blocksA (u + 1)) (blocksB (v + 1)) N =
        mpvOverlap (d := blockPhysDim d m) (blocksA u) (blocksB v) N := fun N hN =>
    sectorOverlap_succ_eq_of_cyclicSectorDecomp A B hA.leftCanonical hB.leftCanonical
      blocksA blocksB hA_cyclic hB_cyclic u v N hN
  -- Step C: transport the norm limit, then conclude gauge-phase equivalence at `(u+1, v+1)`.
  have hNorm_succ :
      Tendsto (fun N => ‖mpvOverlap (d := blockPhysDim d m)
        (blocksA (u + 1)) (blocksB (v + 1)) N‖) atTop (nhds (1 : ℝ)) := by
    refine hNorm_uv.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [hShiftEq N hN]
  -- The dimensions must agree, else the overlap would decay to zero.
  have hdim' : dimA (u + 1) = dimB (v + 1) := by
    by_contra hne
    have hZero : Tendsto (fun N => mpvOverlap (d := blockPhysDim d m)
        (blocksA (u + 1)) (blocksB (v + 1)) N) atTop (nhds (0 : ℂ)) :=
      mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP
        (blocksA (u + 1)) (blocksB (v + 1)) hIrrA_su hIrrB_sv
        (hA_blocks_lc (u + 1)) (hB_blocks_lc (v + 1)) hne
    have hZeroNorm : Tendsto (fun N => ‖mpvOverlap (d := blockPhysDim d m)
        (blocksA (u + 1)) (blocksB (v + 1)) N‖) atTop (nhds (0 : ℝ)) := by
      simpa using hZero.norm
    exact one_ne_zero (tendsto_nhds_unique hNorm_succ hZeroNorm)
  refine ⟨hdim', ?_⟩
  -- With matched dimensions, the unit-modulus overlap yields a gauge-phase equivalence.
  have hAcast_irr : Kraus.IsIrreducibleFamily (cast (congr_arg (MPSTensor (blockPhysDim d m)) hdim')
      (blocksA (u + 1))) :=
    (isIrreducibleFamily_cast_dim hdim' (blocksA (u + 1))).mpr hIrrA_su
  have hAcast_norm : ∑ i : Fin (blockPhysDim d m),
      (cast (congr_arg (MPSTensor (blockPhysDim d m)) hdim') (blocksA (u + 1)) i)ᴴ *
        (cast (congr_arg (MPSTensor (blockPhysDim d m)) hdim') (blocksA (u + 1)) i) = 1 :=
    (leftCanonical_cast_dim hdim' (blocksA (u + 1))).mpr (hA_blocks_lc (u + 1))
  have hNorm_succ_cast :
      Tendsto (fun N => ‖mpvOverlap (d := blockPhysDim d m)
        (cast (congr_arg (MPSTensor (blockPhysDim d m)) hdim') (blocksA (u + 1)))
        (blocksB (v + 1)) N‖) atTop (nhds (1 : ℝ)) := by
    refine hNorm_succ.congr fun N => ?_
    rw [mpvOverlap_cast_dim_left hdim' (blocksA (u + 1)) (blocksB (v + 1)) N]
  exact gaugePhaseEquiv_of_overlap_norm_tendsto_one_of_irreducible_TP
    (cast (congr_arg (MPSTensor (blockPhysDim d m)) hdim') (blocksA (u + 1))) (blocksB (v + 1))
    hAcast_irr hIrrB_sv hAcast_norm (hB_blocks_lc (v + 1)) hNorm_succ_cast

/-- One-step cyclic transport statement for sector matches.

This is the formal one-step version of the propagation step in arXiv:1708.00029,
Appendix A (lines 985--1002). The cyclic projection relation 𝓔_A^{*}(P_{k+1}) = P_k,
together with the compressed-sector realization, transports a gauge-phase
equivalence between sector pair (u, v) to one between (u + 1, v + 1). The
conclusion also propagates nondegeneracy so the step can be iterated around the
cycle. -/
private lemma sectorMatch_succ_of_cyclicSectorDecomp
    (A B : MPSTensor d D)
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
    sectorGaugePhaseEquiv_succ_of_cyclicTransport A B hA hB
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

/-- **Translation propagation** (eq:blockedABprop, arXiv:1708.00029 lines
998--1008):
Given one matching compressed sector pair at `(u₀, v₀)`, applying the
translation operator T^l for l = 1, …, m-1 yields matching for all
sector pairs `(u₀ + l, v₀ + l)`. Each offset `l` gets its own gauge
(eq:blockedABprop produces a different unitary U_{v'+l} at each sector, not a
single transported gauge); the offset v − u = q is constant (eq:vprop, line
1007).

The `hA_cyclic`/`hB_cyclic` hypotheses (see `IsCyclicSectorDecomp`)
tie the `Fin m` block indexing to the cyclic orbit structure of the
transfer map, which is essential: without them, `SameMPV₂` alone is
permutation-invariant over blocks and would not justify the shifted
conclusion `(u₀ + l, v₀ + l)`.

The nondegeneracy hypothesis `dimA u₀ ≠ 0` ensures the initial match
is substantive: for `MPSTensor _ 0`, `GaugePhaseEquiv` holds vacuously
and propagation would produce only vacuous matches.

The periodicity hypotheses (`hA`, `hB`) are the formalization of the paper's
Lemma bdcf normality input at this step (arXiv:1708.00029 lines 985--1002): they
make each compressed cyclic sector a primitive, irreducible normal tensor, so the
unit-modulus cross overlap that certifies the match can reappear at the shifted
sector pair.  They also supply the left-canonical normalization that keeps the
propagated phases unit-modulus. -/
lemma sectorMatch_propagation
    (A B : MPSTensor d D)
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
  -- Iterate the one-step transport `sectorMatch_succ_of_cyclicSectorDecomp` (which
  -- carries nondegeneracy forward) around the cycle by cyclic induction over
  -- `Fin m`, with `(u₀ + l, v₀ + l)` as the running pair (the translation-operator
  -- family of arXiv:1708.00029 lines 985--1002). The one-step input is
  -- `sectorGaugePhaseEquiv_succ_of_cyclicTransport`.
  have key : ∀ l : Fin m, ∃ (hdim : dimA (u₀ + l) = dimB (v₀ + l)),
      dimA (u₀ + l) ≠ 0 ∧
      GaugePhaseEquiv
        (cast (congr_arg (MPSTensor (blockPhysDim d m)) hdim) (blocksA (u₀ + l)))
        (blocksB (v₀ + l)) := by
    intro l
    refine Fin.cyclic_induction
      (P := fun l => ∃ (hdim : dimA (u₀ + l) = dimB (v₀ + l)),
        dimA (u₀ + l) ≠ 0 ∧
        GaugePhaseEquiv
          (cast (congr_arg (MPSTensor (blockPhysDim d m)) hdim) (blocksA (u₀ + l)))
          (blocksB (v₀ + l))) ?_ ?_ l
    · exact ⟨(add_zero u₀).symm ▸ (add_zero v₀).symm ▸ hdim₀,
        (add_zero u₀).symm ▸ hNondeg,
        gaugePhaseEquiv_cast_indices blocksA blocksB
          (add_zero u₀).symm (add_zero v₀).symm hdim₀ hMatch⟩
    · intro j hj
      obtain ⟨hdimj, hnzj, hgj⟩ := hj
      obtain ⟨hdim', hnz', hg'⟩ :=
        sectorMatch_succ_of_cyclicSectorDecomp A B hA hB blocksA blocksB
          hA_blocks_lc hB_blocks_lc hA_mpv hB_mpv hA_cyclic hB_cyclic hdimj hnzj hgj
      have eA : (u₀ + j) + 1 = u₀ + (j + 1) := by abel
      have eB : (v₀ + j) + 1 = v₀ + (j + 1) := by abel
      exact ⟨eA ▸ eB ▸ hdim', eA ▸ hnz',
        gaugePhaseEquiv_cast_indices blocksA blocksB eA eB hdim' hg'⟩
  intro l
  obtain ⟨hdim, _, hg⟩ := key l
  exact ⟨hdim, hg⟩

end MPSTensor

end SectorMatchPropagation

section SectorMatchConsequences

/-!
## Consequences of periodic sector matching

This module assembles propagation and full-cycle contraction into the
sector-match branch of the periodic-overlap dichotomy.
-/

open scoped Matrix BigOperators ComplexOrder InnerProductSpace TensorProduct
open Filter Matrix Module
open Kraus (blockPhysDim blockTensor)

namespace MPSTensor

variable {d D : ℕ}

/-- **Case 3: a matching sector implies gauge equivalence**. If two periodic tensors have
the same period and a compressed sector match exists, then they satisfy the repeated-block
relation: A^i = ξ Y B^i Y⁻¹ for a unit-modulus scalar ξ and an invertible gauge Y.

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

The specified projectors and corner identifications realize the blocked sector
tensors as the corners \(C_u^\alpha = P_u (A^{[m]})^\alpha P_u\) and
\(D_v^\alpha = Q_v (B^{[m]})^\alpha Q_v\), matching the \(C_u\)-notation
used in Lemma bdcf before the Appendix A contraction step.

This is the repeated-block consequence of the sector-match case in
arXiv:1708.00029, Appendix A, lines 961--1117. -/
theorem periodicOverlap_gaugeEquiv_of_sector_match
    (A B : MPSTensor d D)
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
    {PA PB : Fin m → MatrixAlg D}
    {φA : (k : Fin m) →
      Matrix (Fin (dimA k)) (Fin (dimA k)) ℂ ≃ₗ[ℂ] cornerSubmodule (PA k)}
    {φB : (k : Fin m) →
      Matrix (Fin (dimB k)) (Fin (dimB k)) ℂ ≃ₗ[ℂ] cornerSubmodule (PB k)}
    (hA_cyclic : IsCyclicSectorDecompWith A blocksA PA φA)
    (hB_cyclic : IsCyclicSectorDecompWith B blocksB PB φB)
    (hA_letter : ∀ k (i : Fin (blockPhysDim d m)),
      (φA k (blocksA k i)).1 = PA k * (blockTensor A m) i * PA k)
    (hB_letter : ∀ k (i : Fin (blockPhysDim d m)),
      (φB k (blocksB k i)).1 = PB k * (blockTensor B m) i * PB k)
    (hNondegA : ∀ u, dimA u ≠ 0)
    (hSomeMatch : ∃ (u₀ v₀ : Fin m) (hdim : dimA u₀ = dimB v₀),
      GaugePhaseEquiv
        (cast (congr_arg
          (MPSTensor (blockPhysDim d m)) hdim)
          (blocksA u₀))
        (blocksB v₀)) :
    RepeatedBlocks A B := by
  -- APPENDIX TWO-STAGE STRUCTURE (arXiv:1708.00029 lines 961--1117):
  --   1. `sectorMatch_propagation`: iterate the single match around the cycle
  --      (translation operator + thm:cf, lines 985--1008), reindexed to the
  --      offset form (u, u + q) with q = v₀ - u₀;
  --   2. `sectorBlocked_isNormal_of_isPeriodic` (PROVED): each sector is normal;
  --   3. `sectorTensor_proportional_of_blockedMatch`: contract the matched blocks
  --      to a global gauge with the κ/θ/φ phase assembly (lines 1023--1117).
  -- Stage 1 (`sectorGaugePhaseEquiv_succ_of_cyclicTransport`) is closed via the
  -- one-site rotation covariance of the cross sector overlap; stage 3 is the
  -- contraction `sectorTensor_proportional_of_blockedMatch`.
  classical
  obtain ⟨u₀, v₀, hdim₀, hMatch⟩ := hSomeMatch
  have hA_lc := hA.leftCanonical
  have hB_lc := hB.leftCanonical
  have hA_cyclic_exists : IsCyclicSectorDecomp A blocksA :=
    ⟨PA, φA, hA_cyclic⟩
  have hB_cyclic_exists : IsCyclicSectorDecomp B blocksB :=
    ⟨PB, φB, hB_cyclic⟩
  -- Stage 1: propagate the single match to every offset `l` around the cycle.
  have hprop := sectorMatch_propagation A B hA hB blocksA blocksB
    hA_blocks_lc hB_blocks_lc hA_mpv hB_mpv hA_cyclic_exists hB_cyclic_exists
    hdim₀ (hNondegA u₀) hMatch
  -- Stage 2: each sector of `A` is a normal tensor.
  have hNormal : ∀ u, Kraus.IsNormal (blocksA u) := fun u =>
    sectorBlocked_isNormal_of_isPeriodic A hA blocksA hA_blocks_lc hA_mpv
      hA_cyclic_exists u (hNondegA u)
  -- Stage 3: contract the (reindexed) per-sector matches into a unitary global gauge.
  obtain ⟨ξ, Uglob, hξ, hUUstar, hUstarU, hconj⟩ :=
    sectorTensor_proportional_of_blockedMatch A B hA_lc hB_lc blocksA blocksB
      hA_blocks_lc hB_blocks_lc hA_mpv hB_mpv hA_cyclic hB_cyclic hA_letter
      hB_letter (v₀ - u₀) (by
        -- Reindex `hprop` from `(u₀ + l, v₀ + l)` to
        -- `(u, u + (v₀ - u₀))` by taking `l = u - u₀`.
        intro u
        have key := hprop (u - u₀)
        have eA : u₀ + (u - u₀) = u := by abel
        have eB : v₀ + (u - u₀) = u + (v₀ - u₀) := by abel
        rw [eA, eB] at key
        exact key) hNondegA hNormal
  exact ⟨ξ, ⟨Uglob, Uglobᴴ, hUUstar, hUstarU⟩, hξ, hconj⟩

/-- When `D₁ ≠ D₂`, no `RepeatedBlocks` relation can hold (the types don't
match), so the overlap must decay. This covers the `D₁ ≠ D₂` subcase of
the main dichotomy regardless of period matching. -/
theorem periodicOverlap_tendsto_zero_of_ne_dim
    {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    {m_a m_b : ℕ}
    (hA : IsPeriodic m_a A) (hB : IsPeriodic m_b B)
    (hdim : D₁ ≠ D₂) :
    Tendsto (fun N => mpvOverlap A B N) atTop (nhds 0) := by
  have : NeZero D₁ := ⟨hA.bondDim_ne_zero⟩
  have : NeZero D₂ := ⟨hB.bondDim_ne_zero⟩
  exact mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP A B
    hA.irreducible hB.irreducible hA.leftCanonical hB.leftCanonical hdim


end MPSTensor

end SectorMatchConsequences
