/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Overlap.Case2

/-!
# Periodic overlap dichotomy: Case 3

This module contains the equal-period, sector-match case of Appendix A of
arXiv:1708.00029: a matching pair of sectors propagates around the cycle and
forces repeated blocks.

## Main declarations

* `sectorMatch_propagation`
* `sectorTensor_proportional_of_blockedMatch`
* `periodicOverlap_gaugeEquiv_of_sector_match`
* `periodicOverlap_tendsto_zero_of_ne_dim`

## References

* De las Cuevas, Cirac, Schuch, Perez-Garcia,
  *Irreducible forms of Matrix Product States: Theory and Applications*,
  arXiv:1708.00029, Appendix A.
-/

open scoped Matrix BigOperators ComplexOrder InnerProductSpace
open Filter Matrix

namespace MPSTensor

variable {d D : ℕ}

/-! ## Case 3: Same period, sector match → gauge-equivalent (Appendix A, main case) -/

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
def rotateCfg {d L' : ℕ} : (Fin (L' + 1) → Fin d) ≃ (Fin (L' + 1) → Fin d) where
  toFun σ := Fin.cons (σ (Fin.last L')) (Fin.init σ)
  invFun τ := Fin.snoc (Fin.tail τ) (τ 0)
  left_inv σ := by
    funext j
    refine Fin.lastCases ?_ ?_ j
    · simp [Fin.snoc_last, Fin.cons_zero]
    · intro i
      simp [Fin.snoc_castSucc, Fin.init]
  right_inv τ := by
    funext j
    refine Fin.cases ?_ ?_ j
    · simp [Fin.cons_zero, Fin.snoc_last]
    · intro i
      simp [Fin.cons_succ, Fin.tail]

/-- Word evaluation of the rotated configuration pulls the last letter to the front. -/
private lemma evalWord_ofFn_rotateCfg {L' : ℕ} (A : MPSTensor d D)
    (σ : Fin (L' + 1) → Fin d) :
    evalWord A (List.ofFn (rotateCfg σ)) =
      A (σ (Fin.last L')) * evalWord A (List.ofFn (Fin.init σ)) := by
  simp only [rotateCfg, Equiv.coe_fn_mk, List.ofFn_cons, evalWord_cons]

/-- Word evaluation of the original configuration pulls the last letter to the right. -/
private lemma evalWord_ofFn_eq_init_mul_last {L' : ℕ} (A : MPSTensor d D)
    (σ : Fin (L' + 1) → Fin d) :
    evalWord A (List.ofFn σ) =
      evalWord A (List.ofFn (Fin.init σ)) * A (σ (Fin.last L')) := by
  rw [List.ofFn_succ']
  rw [show (List.ofFn fun i => σ (Fin.castSucc i)) = List.ofFn (Fin.init σ) from rfl]
  rw [List.concat_eq_append, evalWord_append]
  simp [evalWord_cons, evalWord_nil]

/-- **Per-configuration trace covariance** under one-site rotation (eq:Aoffdiag,
arXiv:1708.00029 lines 985--1002).  Given the single-site off-diagonal shift
`P (k+1) * A i = A i * P k`, the projector-weighted trace at index `k+1` of the
rotated word equals the projector-weighted trace at index `k` of the original
word. -/
private lemma trace_proj_evalWord_rotateCfg {L' m : ℕ} [NeZero m] (A : MPSTensor d D)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hShift : ∀ (k : Fin m) (i : Fin d), P (k + 1) * A i = A i * P k)
    (k : Fin m) (σ : Fin (L' + 1) → Fin d) :
    (P (k + 1) * evalWord A (List.ofFn (rotateCfg σ))).trace =
      (P k * evalWord A (List.ofFn σ)).trace := by
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
        (P (u + 1) * evalWord A (List.ofFn σ)).trace *
          star ((Q (v + 1) * evalWord B (List.ofFn σ)).trace)) =
      ∑ σ : Fin (L' + 1) → Fin d,
        (P u * evalWord A (List.ofFn σ)).trace *
          star ((Q v * evalWord B (List.ofFn σ)).trace) := by
  rw [← Equiv.sum_comp (rotateCfg (d := d) (L' := L'))
    (fun σ => (P (u + 1) * evalWord A (List.ofFn σ)).trace *
      star ((Q (v + 1) * evalWord B (List.ofFn σ)).trace))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [trace_proj_evalWord_rotateCfg A P hShiftA u σ,
    trace_proj_evalWord_rotateCfg B Q hShiftB v σ]

/-- The decoding map `decodeBlock` as a bundled equivalence. -/
private noncomputable def decodeBlockEquiv (d L : ℕ) :
    Fin (blockPhysDim d L) ≃ (Fin L → Fin d) :=
  (finCongr (blockPhysDim_eq_pow d L)).trans finFunctionFinEquiv.symm

private lemma decodeBlockEquiv_apply (d L : ℕ) (i : Fin (blockPhysDim d L)) :
    decodeBlockEquiv d L i = decodeBlock d L i := rfl

/-- Bridge between blocked configurations of length `N` and physical
configurations of length `N * m`. -/
private noncomputable def blockedCfgEquiv (d N m : ℕ) :
    (Fin N → Fin (blockPhysDim d m)) ≃ (Fin (N * m) → Fin d) :=
  ((Equiv.arrowCongr (Equiv.refl (Fin N)) (decodeBlockEquiv d m)).trans
    (Equiv.curry (Fin N) (Fin m) (Fin d)).symm).trans
    (Equiv.arrowCongr finProdFinEquiv (Equiv.refl (Fin d)))

private lemma ofFn_blockedCfgEquiv (d N m : ℕ) (σ : Fin N → Fin (blockPhysDim d m)) :
    List.ofFn (blockedCfgEquiv d N m σ) = flattenBlockedWord d m (List.ofFn σ) := by
  have hfun : (blockedCfgEquiv d N m σ) =
      fun k : Fin (N * m) =>
        decodeBlock d m (σ (finProdFinEquiv.symm k).1) ((finProdFinEquiv.symm k).2) := by
    funext k
    simp [blockedCfgEquiv, Equiv.arrowCongr, Equiv.curry, decodeBlockEquiv_apply,
      Function.comp]
  rw [hfun, List.ofFn_mul]
  rw [flattenBlockedWord, List.map_ofFn]
  congr 1
  refine congrArg List.ofFn (funext fun i => ?_)
  -- The grouped index `⟨i*m+j⟩` decodes to `(i, j)` under `finProdFinEquiv`.
  have hsymm : ∀ j : Fin m,
      finProdFinEquiv.symm
          (⟨(i : ℕ) * m + (j : ℕ),
            by
              calc
                (i : ℕ) * m + (j : ℕ) < ((i : ℕ) + 1) * m := by
                  have := j.isLt; rw [Nat.add_mul, Nat.one_mul]; omega
                _ ≤ N * m := Nat.mul_le_mul_right _ (by have := i.isLt; omega)⟩ :
            Fin (N * m)) = (i, j) := by
    intro j
    rw [Equiv.symm_apply_eq]
    apply Fin.ext
    -- `finProdFinEquiv (i, j) = ⟨j + m * i, _⟩` by definition.
    change (i : ℕ) * m + (j : ℕ) = (j : ℕ) + m * (i : ℕ)
    rw [Nat.mul_comm m (i : ℕ), Nat.add_comm]
  simp only [hsymm]
  change (List.ofFn fun j : Fin m => decodeBlock d m (σ i) j) = (wordOfBlock d m ∘ σ) i
  simp [wordOfBlock, Function.comp]

/-- The cross overlap of two compressed cyclic sectors, expanded via the
`IsCyclicSectorDecomp` trace formula and reindexed to physical configurations
of length `N * m`. -/
private lemma sectorOverlap_eq_physical_sum {m : ℕ} [NeZero D] [NeZero m]
    (A B : MPSTensor d D)
    {dimA dimB : Fin m → ℕ}
    (blocksA : (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB : (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (PA PB : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hTraceA : ∀ k (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)),
      mpv (blocksA k) σ = (PA k * evalWord (blockTensor A m) (List.ofFn σ)).trace)
    (hTraceB : ∀ k (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)),
      mpv (blocksB k) σ = (PB k * evalWord (blockTensor B m) (List.ofFn σ)).trace)
    (u v : Fin m) (N : ℕ) :
    mpvOverlap (d := blockPhysDim d m) (blocksA u) (blocksB v) N =
      ∑ τ : Fin (N * m) → Fin d,
        (PA u * evalWord A (List.ofFn τ)).trace *
          star ((PB v * evalWord B (List.ofFn τ)).trace) := by
  classical
  rw [mpvOverlap]
  rw [← Equiv.sum_comp (blockedCfgEquiv d N m)
    (fun τ : Fin (N * m) → Fin d =>
      (PA u * evalWord A (List.ofFn τ)).trace *
        star ((PB v * evalWord B (List.ofFn τ)).trace))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hTraceA u N σ, hTraceB v N σ, ofFn_blockedCfgEquiv,
    ← evalWord_blockTensor, ← evalWord_blockTensor]

/-- **One-step transport of the cross sector overlap** (positive lengths,
arXiv:1708.00029 lines 985--1002).  For `N ≥ 1`, the cross overlap of compressed
cyclic sectors is invariant under the simultaneous index shift
`(u, v) → (u+1, v+1)`. -/
private lemma sectorOverlap_succ_eq {m : ℕ} [NeZero D] [NeZero m]
    (A B : MPSTensor d D)
    (hA_lc : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_lc : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    {dimA dimB : Fin m → ℕ}
    (blocksA : (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB : (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (PA PB : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hPAproj : ∀ k, IsOrthogonalProjection (PA k))
    (hPBproj : ∀ k, IsOrthogonalProjection (PB k))
    (hShiftA : ∀ k, transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (PA (k + 1)) = PA k)
    (hShiftB : ∀ k, transferMap (d := d) (D := D) (fun i => (B i)ᴴ) (PB (k + 1)) = PB k)
    (hTraceA : ∀ k (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)),
      mpv (blocksA k) σ = (PA k * evalWord (blockTensor A m) (List.ofFn σ)).trace)
    (hTraceB : ∀ k (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)),
      mpv (blocksB k) σ = (PB k * evalWord (blockTensor B m) (List.ofFn σ)).trace)
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

/-- Self-overlap of an irreducible, transfer-primitive, trace-preserving tensor
tends to `1` (arXiv:1708.00029, Appendix A, first paragraph). -/
private lemma selfOverlap_tendsto_one_of_irreducible_primitive_TP
    {D : ℕ} [NeZero D] (A : MPSTensor d D)
    (hIrr : IsIrreducibleTensor A)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : _root_.IsPrimitive (transferMap (d := d) (D := D) A)) :
    Tendsto (fun N => mpvOverlap (d := d) A A N) atTop (nhds (1 : ℂ)) := by
  obtain ⟨ρ, hρ_psd, hρ_ne, hρ_fix, _htr, hgap⟩ :=
    spectralRadius_compl_lt_one_of_peripheralPrimitive_of_irreducible
      (A := A) hIrr hNorm hPrim
  exact mpvOverlap_tendsto_one_of_transfer_spectralRadius_compl_lt_one
    A hNorm ρ hρ_fix hρ_ne hρ_psd (by simpa using hgap)

/-- From a gauge-phase match between two irreducible, transfer-primitive,
trace-preserving sectors of the same bond dimension, the cross overlap has norm
tending to `1`.  The unit modulus of the gauge phase follows from the matching
self-overlap limits (arXiv:1606.00608, Lemma equalMPS). -/
private lemma overlap_norm_tendsto_one_of_gaugePhase_cast
    {DA DB : ℕ} [NeZero DA] [NeZero DB]
    (CA : MPSTensor d DA) (CB : MPSTensor d DB)
    (hdim : DA = DB)
    (hCA_irr : IsIrreducibleTensor CA) (hCB_irr : IsIrreducibleTensor CB)
    (hCA_norm : ∑ i : Fin d, (CA i)ᴴ * CA i = 1)
    (hCB_norm : ∑ i : Fin d, (CB i)ᴴ * CB i = 1)
    (hCA_prim : _root_.IsPrimitive (transferMap (d := d) (D := DA) CA))
    (hCB_prim : _root_.IsPrimitive (transferMap (d := d) (D := DB) CB))
    (hMatch : GaugePhaseEquiv (cast (congr_arg (MPSTensor d) hdim) CA) CB) :
    Tendsto (fun N => ‖mpvOverlap (d := d) CA CB N‖) atTop (nhds (1 : ℝ)) := by
  classical
  subst hdim
  simp only [cast_eq] at hMatch
  have hCA_self : Tendsto (fun N => mpvOverlap (d := d) CA CA N) atTop (nhds (1 : ℂ)) :=
    selfOverlap_tendsto_one_of_irreducible_primitive_TP CA hCA_irr hCA_norm hCA_prim
  have hCB_self : Tendsto (fun N => mpvOverlap (d := d) CB CB N) atTop (nhds (1 : ℂ)) :=
    selfOverlap_tendsto_one_of_irreducible_primitive_TP CB hCB_irr hCB_norm hCB_prim
  obtain ⟨X, ζ, _hζ, hX⟩ := hMatch
  have hmpv : ∀ (N : ℕ) (σ : Fin N → Fin d), mpv CB σ = ζ ^ N * mpv CA σ :=
    mpv_eq_pow_mul_of_gaugePhase CA CB X ζ hX
  have hSelfScale : ∀ N : ℕ,
      mpvOverlap (d := d) CB CB N =
        (ζ * starRingEnd ℂ ζ) ^ N * mpvOverlap (d := d) CA CA N :=
    mpvOverlap_self_scale_of_mpv_eq_pow_mul (A := CA) (B := CB) (ζ := ζ) hmpv
  have hζnorm : ‖ζ‖ = 1 :=
    norm_eq_one_of_selfOverlap_scale (A := CA) (B := CB) (ζ := ζ)
      (by simpa using hCA_self.norm) (by simpa using hCB_self.norm) hSelfScale
  have hCrossNormEq : ∀ N,
      ‖mpvOverlap (d := d) CA CB N‖ = ‖mpvOverlap (d := d) CA CA N‖ := by
    intro N
    rw [mpvOverlap_eq_star_pow_mul_self_of_mpv_eq_pow_mul (A := CA) (B := CB) (ζ := ζ) hmpv N]
    simp [norm_pow, hζnorm]
  have hCA_self_norm : Tendsto (fun N => ‖mpvOverlap (d := d) CA CA N‖) atTop (nhds (1 : ℝ)) := by
    simpa using hCA_self.norm
  exact hCA_self_norm.congr fun N => (hCrossNormEq N).symm

/-- Nonzero sector dimensions propagate one step around a cyclic sector decomposition.

The proof uses only the projection-shift and trace identities in a cyclic sector decomposition:
if `dim u ≠ 0` then the projection `P u` is nonzero by the `N = 0` trace identity. If
`P (u + 1)` were zero, the cyclic relation `E†(P (u + 1)) = P u` would force `P u = 0`,
contradiction. -/
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

**Corner transition tensors (remaining step).** Rather than translate the global
equation, the cyclic-sector construction can expose one-site corner transition
tensors — the compressions `P k · A i · P (k+1)` and `Q l · B i · Q (l+1)` — and
identify their `m`-fold cyclic products with the supplied `blocksA k`/`blocksB l`,
so that the match transports along these transitions. This is a formalization of
the same step via the `IsCyclicSectorDecomp` relation 𝓔_A^{*}(P_{k+1}) = P_k; see
docs/paper-gaps/1708_periodic_overlap_route_alignment.tex. -/
private lemma sectorGaugePhaseEquiv_succ_of_cyclicTransport
    [NeZero D]
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
  haveI : NeZero (dimA u) := ⟨hNondeg⟩
  haveI : NeZero (dimB v) := ⟨hNondegB_v⟩
  haveI : NeZero (dimA (u + 1)) := ⟨hNondegA_succ⟩
  haveI : NeZero (dimB (v + 1)) := ⟨hNondegB_succ⟩
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
  obtain ⟨PA, _φA, hPAproj, _hPAsum, hShiftA, _hCommA, hTraceA, _⟩ := hA_cyclic
  obtain ⟨PB, _φB, hPBproj, _hPBsum, hShiftB, _hCommB, hTraceB, _⟩ := hB_cyclic
  have hShiftEq : ∀ N : ℕ, 0 < N →
      mpvOverlap (d := blockPhysDim d m) (blocksA (u + 1)) (blocksB (v + 1)) N =
        mpvOverlap (d := blockPhysDim d m) (blocksA u) (blocksB v) N := fun N hN =>
    sectorOverlap_succ_eq A B hA.leftCanonical hB.leftCanonical blocksA blocksB PA PB
      hPAproj hPBproj hShiftA hShiftB hTraceA hTraceB u v N hN
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
  have hAcast_irr : IsIrreducibleTensor (cast (congr_arg (MPSTensor (blockPhysDim d m)) hdim')
      (blocksA (u + 1))) :=
    (isIrreducibleTensor_cast_dim hdim' (blocksA (u + 1))).mpr hIrrA_su
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
    [NeZero D]
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

/-- **Cyclic induction on `Fin m`.** A predicate that holds at `0` and is closed
under `· + 1` holds at every index, because `+1` generates the cyclic group from
`0`. Proved by induction on `i.val`: the predecessor of a nonzero `i` is
`⟨i.val - 1, _⟩`, whose successor is `i`. -/
private lemma fin_cyclic_induction {m : ℕ} [NeZero m] {P : Fin m → Prop}
    (h0 : P 0) (hstep : ∀ i : Fin m, P i → P (i + 1)) (i : Fin m) : P i := by
  induction hi : i.val generalizing i with
  | zero => obtain rfl : i = 0 := Fin.ext (by simpa using hi); exact h0
  | succ k ih =>
    have hk : k < m := by have := i.isLt; omega
    have e : (⟨k, hk⟩ : Fin m) + 1 = i := by
      apply Fin.ext
      have hmod_one : 1 < m := by omega
      have hone : (1 : Fin m).val = 1 := by
        have : (1 : Fin m).val = 1 % m := Fin.val_one' m
        rw [this]; exact Nat.mod_eq_of_lt hmod_one
      rw [Fin.val_add, Fin.val_mk, hone, hi]
      exact Nat.mod_eq_of_lt (by have := i.isLt; omega)
    rw [← e]
    exact hstep _ (ih ⟨k, hk⟩ rfl)

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
    [NeZero D]
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
  -- family of arXiv:1708.00029 lines 985--1002). The remaining one-step obligation
  -- is `sectorGaugePhaseEquiv_succ_of_cyclicTransport`.
  have key : ∀ l : Fin m, ∃ (hdim : dimA (u₀ + l) = dimB (v₀ + l)),
      dimA (u₀ + l) ≠ 0 ∧
      GaugePhaseEquiv
        (cast (congr_arg (MPSTensor (blockPhysDim d m)) hdim) (blocksA (u₀ + l)))
        (blocksB (v₀ + l)) := by
    intro l
    refine fin_cyclic_induction
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

/-- Full-cycle contraction step for periodic-overlap Case 3.

At this point the sector transport has already been abstracted into
`hBlockMatch`, so the remaining gap is no longer the per-step
eq:blockedABprop staircase identification (lines 985--1002). What is still
needed is the contraction argument around the whole cycle, arXiv:1708.00029,
Appendix A lines 1023--1117:

* For each sector `u`, Lemma bdcf normality gives a repetition length `N₀` after
  which the blocked product F_u (eq:Fu, lines 1026--1030) is injective, with a
  right inverse Ω_u (eq:Omegauprop, lines 1035--1040).
* Concatenating and applying the Ω_u inverses contracts the repeated products to
  per-site proportionality A_u^i = κ_v · e^{iη/m} · B_v^i (eq:resultprop/
  eq:thetaACprop, lines 1063--1076).
* The phase bookkeeping is load-bearing: ∏_v κ_v = 1 (eq:prodkappaprop, line
  1079) and |κ_v| = 1 from ‖Σ_i A_u^{i†} A_u^i‖ = 1 (lines 1082--1084), so
  κ_v = e^{iθ_v} with Σ_v θ_v = 0; choosing φ_v with θ_v = φ_v − φ_{v+1}
  (lines 1093--1102) telescopes the per-sector phases into a single global phase
  ξ = η/m and a single global unitary U = Σ_u e^{iφ_{u+q}} P_u U_{u+q} Q_{u+q}
  (eq:result and lines 1110--1117), giving A^i = e^{iξ} U B^i U†.

The available chain inputs are `decompositionMap` / `exists_rightInverse` in
`MPS/Chain/OneSidedInverse.lean` (realizing Ω_u) and the two-site
proportionality theorem `tensor_proportional` in `MPS/Chain/TensorEquality.lean`.
The remaining mathematical input is the `m`-factor cyclic contraction *together
with* the κ/θ/φ phase assembly that passes from `hBlockMatch` to a global
`RepeatedBlocks` witness. See
docs/paper-gaps/1708_periodic_overlap_route_alignment.tex. -/
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
  -- Remaining obligation (arXiv:1708.00029 lines 1023--1117): an `m`-factor cyclic
  -- contraction theorem built from `decompositionMap` (the Ω_u inverses) that,
  -- together with the κ/θ/φ phase assembly (lines 1078--1117), upgrades the
  -- per-sector blocked gauge data in `hBlockMatch` to one global phase and one
  -- global gauge. The available two-site theorem is `tensor_proportional`.
  sorry

/-- **Per-site proportionality** (eq:thetaACprop, arXiv:1708.00029 lines
1073--1076):
After injectivity contraction, the sector-restricted tensors satisfy
A_u^i = κ_v · e^{iη/m} · B_v^i with ∏ κ_v = 1 and |κ_v| = 1.

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
  exact repeatedBlocks_of_blockedSectorGaugePhase
    A B hA_lc hB_lc blocksA blocksB hA_blocks_lc hB_blocks_lc
    hA_mpv hB_mpv hA_cyclic hB_cyclic q hBlockMatch hNondeg hNormal

/-- **Case 3: a matching sector implies gauge equivalence**. If two periodic tensors have
the same period and a compressed sector match exists, then they are related by a gauge
transformation with a unit-modulus phase: A^i = e^{iξ} U B^i U†.

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

This is the sector-match case of the appendix proof, arXiv:1708.00029 lines
961--1117 (conclusion A^i = e^{iξ} U B^i U† at lines 1110--1117). -/
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
  -- APPENDIX TWO-STAGE STRUCTURE (arXiv:1708.00029 lines 961--1117):
  --   1. `sectorMatch_propagation`: iterate the single match around the cycle
  --      (translation operator + thm:cf, lines 985--1008), reindexed to the
  --      offset form (u, u + q) with q = v₀ - u₀;
  --   2. `sectorBlocked_isNormal_of_isPeriodic` (PROVED): each sector is normal;
  --   3. `sectorTensor_proportional_of_blockedMatch`: contract the matched blocks
  --      to a global gauge with the κ/θ/φ phase assembly (lines 1023--1117).
  -- Stage 1 (`sectorGaugePhaseEquiv_succ_of_cyclicTransport`) is closed via the
  -- one-site rotation covariance of the cross sector overlap; the remaining
  -- obligation is the stage-3 contraction `repeatedBlocks_of_blockedSectorGaugePhase`.
  classical
  obtain ⟨u₀, v₀, hdim₀, hMatch⟩ := hSomeMatch
  have hA_lc := hA.leftCanonical
  have hB_lc := hB.leftCanonical
  -- Stage 1: propagate the single match to every offset `l` around the cycle.
  have hprop := sectorMatch_propagation A B hA hB blocksA blocksB
    hA_blocks_lc hB_blocks_lc hA_mpv hB_mpv hA_cyclic hB_cyclic
    hdim₀ (hNondegA u₀) hMatch
  -- Stage 2: each sector of `A` is a normal tensor.
  have hNormal : ∀ u, IsNormal (blocksA u) := fun u =>
    sectorBlocked_isNormal_of_isPeriodic A hA blocksA hA_blocks_lc hA_mpv hA_cyclic u
      (hNondegA u)
  -- Stage 3: contract the (reindexed) per-sector matches into a global gauge.
  refine sectorTensor_proportional_of_blockedMatch A B hA_lc hB_lc blocksA blocksB
    hA_blocks_lc hB_blocks_lc hA_mpv hB_mpv hA_cyclic hB_cyclic (v₀ - u₀) ?_ hNondegA hNormal
  -- Reindex `hprop` from the (u₀ + l, v₀ + l) form to the (u, u + (v₀ - u₀)) form
  -- by taking l = u - u₀, so u₀ + l = u and v₀ + l = u + (v₀ - u₀).
  intro u
  have key := hprop (u - u₀)
  have eA : u₀ + (u - u₀) = u := by abel
  have eB : v₀ + (u - u₀) = u + (v₀ - u₀) := by abel
  rw [eA, eB] at key
  exact key

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


end MPSTensor
