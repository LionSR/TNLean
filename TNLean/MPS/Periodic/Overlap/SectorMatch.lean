/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.Overlap.SectorOverlapTransport
import TNLean.Algebra.CornerSkolemNoether
import TNLean.Algebra.FiniteCycleCoboundary
import TNLean.Algebra.PiTensorProductPhase
import TNLean.Channel.PositiveConditionalExpectationDirectSum
import TNLean.MPS.CanonicalForm.SectorComparison.NormalityChain
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.Chain.OneSidedInverse
import TNLean.MPS.FundamentalTheorem.UnitaryGauge
import TNLean.MPS.Periodic.GlobalGauge
import TNLean.MPS.Periodic.SectorContraction

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
    [NeZero D] (A : MPSTensor d D)
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
    haveI : NeZero (dim u) := ⟨hNondeg⟩
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

/-- Per-sector `RepeatedBlocks` consequence of the propagated gauge-phase equivalences.

This auxiliary result is weaker than the Case 3 conclusion: it gives a
`RepeatedBlocks` relation for each compressed sector pair
`(blocksA u, blocksB (u + q))` after the dimension cast.  It does not assemble
the sector gauges into one global gauge for `A` and `B`; that is precisely the
remaining `Ω_u` contraction and phase-assembly step in arXiv:1708.00029,
Appendix A, lines 1023--1117. -/
private lemma sectorRepeatedBlocks_of_blockedMatch
    [NeZero D]
    (B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hB : IsPeriodic m B)
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
    (hB_mpv :
      SameMPV₂ (blockTensor B m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksB))
    (hB_cyclic : IsCyclicSectorDecomp B blocksB)
    (q : Fin m)
    (hBlockMatch : ∀ u : Fin m,
      ∃ (hdim : dimA u = dimB (u + q)),
        GaugePhaseEquiv
          (cast (congr_arg
            (MPSTensor (blockPhysDim d m)) hdim)
            (blocksA u))
          (blocksB (u + q)))
    (hNondeg : ∀ u, dimA u ≠ 0) :
    ∀ u : Fin m,
      ∃ (hdim : dimA u = dimB (u + q)),
        RepeatedBlocks
          (cast (congr_arg
            (MPSTensor (blockPhysDim d m)) hdim)
            (blocksA u))
          (blocksB (u + q)) := by
  intro u
  obtain ⟨hdim, hMatch⟩ := hBlockMatch u
  have hB_nonzero : dimB (u + q) ≠ 0 := hdim ▸ hNondeg u
  haveI : NeZero (dimB (u + q)) := ⟨hB_nonzero⟩
  obtain ⟨_hPrimB, hIrrB⟩ :=
    primitive_and_irreducible_sectorBlocks_of_cyclicDecomp B hB blocksB
      hB_blocks_lc hB_mpv hB_cyclic (u + q) hB_nonzero
  have hAcast_lc : IsLeftCanonical
      (cast (congr_arg (MPSTensor (blockPhysDim d m)) hdim) (blocksA u)) :=
    (leftCanonical_cast_dim hdim (blocksA u)).mpr (hA_blocks_lc u)
  exact ⟨hdim,
    gaugePhaseEquiv_to_repeatedBlocks_of_leftCanonical_irreducible
      hMatch hAcast_lc (hB_blocks_lc (u + q)) hIrrB⟩

/-- Common `Ω_u` right inverses for the sector blocks.

This is the Lean form of the normality input in arXiv:1708.00029, Appendix A,
lines 1026--1040, equations `eq:Fu` and `eq:Omegauprop`: after choosing one
common positive word length, every sector block has a right inverse for the
linear span of its length-`L` word products. -/
private lemma exists_common_sectorDecompositionMaps_of_isNormal_leftCanonical
    {m : ℕ} {dim : Fin m → ℕ}
    (blocks : (k : Fin m) → MPSTensor d (dim k))
    (hBlocks_lc :
      ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hNondeg : ∀ k, dim k ≠ 0)
    (hNormal : ∀ k, IsNormal (blocks k)) :
    ∃ L : ℕ, 0 < L ∧
      ∃ Ω : (k : Fin m) →
          Matrix (Fin (dim k)) (Fin (dim k)) ℂ →ₗ[ℂ] ((Fin L → Fin d) → ℂ),
        ∀ (k : Fin m) (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
          ∑ σ : Fin L → Fin d,
            (Ω k X σ) • evalWord (blocks k) (List.ofFn σ) = X := by
  obtain ⟨L, hL_pos, hL⟩ :=
    exists_common_isNBlkInjective_of_isNormal_leftCanonical
      blocks hBlocks_lc hNondeg hNormal
  refine ⟨L, hL_pos, fun k => blockDecompositionMap (hL k), ?_⟩
  intro k X
  exact blockDecompositionMap_sum (hL k) X

/-- Nonzero scalar multiplication preserves injectivity at a fixed blocking length.

This is used when normalizing the matched sector tensors in arXiv:1708.00029,
Appendix A, lines 985--1002. -/
private lemma isNBlkInjective_smul_of_ne
    {e n N : ℕ} (C : MPSTensor e n) (z : ℂ) (hz : z ≠ 0)
    (hC : IsNBlkInjective C N) :
    IsNBlkInjective (fun i => z • C i) N := by
  rw [IsNBlkInjective, eq_top_iff] at hC ⊢
  intro X hXtop
  clear hXtop
  have hX : X ∈ Submodule.span ℂ
      (Set.range fun σ : Fin N → Fin e => evalWord C (List.ofFn σ)) :=
    hC (Submodule.mem_top : X ∈ (⊤ : Submodule ℂ (MatrixAlg n)))
  induction hX using Submodule.span_induction with
  | mem X hX =>
      obtain ⟨σ, rfl⟩ := hX
      change evalWord C (List.ofFn σ) ∈ _
      rw [← inv_smul_smul₀ (pow_ne_zero N hz)
        (evalWord C (List.ofFn σ))]
      apply Submodule.smul_mem
      have hscaled : evalWord (fun i => z • C i) (List.ofFn σ) ∈
          Submodule.span ℂ (Set.range fun τ : Fin N → Fin e =>
            evalWord (fun i => z • C i) (List.ofFn τ)) :=
        Submodule.subset_span (Set.mem_range_self σ)
      simpa only [evalWord_smul, List.length_ofFn] using hscaled
  | zero => exact Submodule.zero_mem _
  | add X Y _ _ hX hY => exact Submodule.add_mem _ hX hY
  | smul z X _ hX => exact Submodule.smul_mem _ z hX

/-- Nonzero scalar multiplication preserves algebraic normality.

This is used when normalizing the matched sector tensors in arXiv:1708.00029,
Appendix A, lines 985--1002. -/
private lemma isNormal_smul_of_ne
    {e n : ℕ} (C : MPSTensor e n) (z : ℂ) (hz : z ≠ 0)
    (hC : IsNormal C) :
    IsNormal (fun i => z • C i) := by
  obtain ⟨N, hN, hC⟩ := hC
  exact ⟨N, hN, isNBlkInjective_smul_of_ne C z hz hC⟩

/-- A matched pair of compressed sectors has an ambient corner implementation.

This is equation `eq:blockedABprop` in ambient form, hence the input to
`eq:BCmprop`, in arXiv:1708.00029, Appendix A, lines 985--1024. -/
private lemma exists_ambient_corner_gauge_of_gaugePhase
    {e nA nB : ℕ} [NeZero nA]
    (CA : MPSTensor e nA) (CB : MPSTensor e nB)
    (hdim : nA = nB)
    (P Q : MatrixAlg D)
    (φP : MatrixAlg nA ≃ₗ[ℂ] cornerSubmodule P)
    (φQ : MatrixAlg nB ≃ₗ[ℂ] cornerSubmodule Q)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (hφP_mul : ∀ X Y : MatrixAlg nA,
      (φP (X * Y)).1 = (φP X).1 * (φP Y).1)
    (hφQ_mul : ∀ X Y : MatrixAlg nB,
      (φQ (X * Y)).1 = (φQ X).1 * (φQ Y).1)
    (hφP_star : ∀ X : MatrixAlg nA, (φP Xᴴ).1 = (φP X).1ᴴ)
    (hφQ_star : ∀ X : MatrixAlg nB, (φQ Xᴴ).1 = (φQ X).1ᴴ)
    (hCA_lc : IsLeftCanonical CA) (hCB_lc : IsLeftCanonical CB)
    (hCA_normal : IsNormal CA)
    (hMatch : GaugePhaseEquiv
      (cast (congr_arg (MPSTensor e) hdim) CA) CB) :
    ∃ (U : MatrixAlg D) (c : ℂ),
      U = P * U * Q ∧
      Uᴴ * U = Q ∧
      U * Uᴴ = P ∧
      ‖c‖ = 1 ∧
      ∀ i : Fin e, (φP (CA i)).1 =
        c • (U * (φQ (CB i)).1 * Uᴴ) := by
  classical
  subst nB
  simp only [cast_eq] at hMatch
  obtain ⟨X, z, hz, hCB⟩ := hMatch
  let CB' : MPSTensor e nA := fun i => z⁻¹ • CB i
  have hGauge : GaugeEquiv CA CB' := by
    refine ⟨X, fun i => ?_⟩
    simp only [CB', hCB i, smul_smul, inv_mul_cancel₀ hz, one_smul]
  have hCB'_normal : IsNormal CB' :=
    isNormal_of_gaugeEquiv hCA_normal hGauge
  have hCB_eq : CB = fun i => z • CB' i := by
    funext i
    simp [CB', hz]
  have hCB_normal : IsNormal CB := by
    rw [hCB_eq]
    exact isNormal_smul_of_ne CB' z hz hCB'_normal
  have hCA_irr : IsIrreducibleTensor CA :=
    (isNormalTensor_of_isNormal_leftCanonical CA hCA_normal hCA_lc).no_invariant_proj
  have hCB_irr : IsIrreducibleTensor CB :=
    (isNormalTensor_of_isNormal_leftCanonical CB hCB_normal hCB_lc).no_invariant_proj
  obtain ⟨W, c₀, hc₀, hW⟩ :=
    exists_unitaryConj_gaugePhase_of_leftCanonical_irreducible
      (show GaugePhaseEquiv CA CB from ⟨X, z, hz, hCB⟩)
      hCA_lc hCB_lc hCA_irr hCB_irr
  let g : MatrixAlg nA ≃ₗ[ℂ] MatrixAlg nA :=
    Matrix.unitaryReindexLinearEquiv (Equiv.refl (Fin nA)) W W.prop
  let f : cornerSubmodule Q ≃ₗ[ℂ] cornerSubmodule P :=
    φQ.symm.trans (g.trans φP)
  let mulQ (A B : cornerSubmodule Q) : cornerSubmodule Q :=
    ⟨A.1 * B.1, by
      have hQA : Q * A.1 = A.1 := by
        calc
          Q * A.1 = Q * (Q * A.1 * Q) := by rw [A.2]
          _ = (Q * Q) * A.1 * Q := by simp only [Matrix.mul_assoc]
          _ = A.1 := by rw [hQ.2, A.2]
      have hBQ : B.1 * Q = B.1 := by
        calc
          B.1 * Q = (Q * B.1 * Q) * Q := by rw [B.2]
          _ = Q * B.1 * (Q * Q) := by simp only [Matrix.mul_assoc]
          _ = B.1 := by rw [hQ.2, B.2]
      calc
        Q * (A.1 * B.1) * Q = (Q * A.1) * (B.1 * Q) := by
          simp only [Matrix.mul_assoc]
        _ = A.1 * B.1 := by rw [hQA, hBQ]⟩
  have hφQ_symm_mul (A B : cornerSubmodule Q) :
      φQ.symm (mulQ A B) = φQ.symm A * φQ.symm B := by
    apply φQ.injective
    apply Subtype.ext
    rw [LinearEquiv.apply_symm_apply, hφQ_mul,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hf_mul (A B : cornerSubmodule Q) :
      (f (mulQ A B)).1 = (f A).1 * (f B).1 := by
    simp only [f, LinearEquiv.trans_apply]
    rw [hφQ_symm_mul, show g (φQ.symm A * φQ.symm B) =
      g (φQ.symm A) * g (φQ.symm B) by
        exact Matrix.unitaryReindexLinearEquiv_mul
          (Equiv.refl (Fin nA)) W W.prop (φQ.symm A) (φQ.symm B)]
    exact hφP_mul _ _
  let starQ (A : cornerSubmodule Q) : cornerSubmodule Q :=
    ⟨A.1ᴴ, by
      change Q * A.1ᴴ * Q = A.1ᴴ
      rw [Matrix.mul_assoc]
      simpa only [Matrix.conjTranspose_mul, hQ.1.eq,
        Matrix.conjTranspose_conjTranspose] using congrArg Matrix.conjTranspose A.2⟩
  have hφQ_symm_star (A : cornerSubmodule Q) :
      φQ.symm (starQ A) = (φQ.symm A)ᴴ := by
    apply φQ.injective
    apply Subtype.ext
    rw [LinearEquiv.apply_symm_apply, hφQ_star, LinearEquiv.apply_symm_apply]
  have hf_star (A : cornerSubmodule Q) :
      (f (starQ A)).1 = (f A).1ᴴ := by
    simp only [f, LinearEquiv.trans_apply]
    rw [hφQ_symm_star, show g ((φQ.symm A)ᴴ) = (g (φQ.symm A))ᴴ by
      simpa only [Matrix.star_eq_conjTranspose] using
        Matrix.unitaryReindexLinearEquiv_star
          (Equiv.refl (Fin nA)) W W.prop (φQ.symm A)]
    exact hφP_star _
  obtain ⟨U, hU_corner, hU_star_U, hU_U_star, hU_transport⟩ :=
    exists_partial_isometry_implementing_corner_linearEquiv P Q hP hQ f
      (by
        intro A B
        simpa only [mulQ] using hf_mul A B)
      (by
        intro A
        simpa only [starQ] using hf_star A)
  have hW_star_W : (W : MatrixAlg nA)ᴴ * (W : MatrixAlg nA) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.UnitaryGroup.star_mul_self W
  have hgCB (i : Fin e) : g (CB i) = c₀ • CA i := by
    simp [g, hW i, Matrix.unitaryReindexLinearEquiv_apply,
      Matrix.mul_assoc, hW_star_W]
    rw [Matrix.star_eq_conjTranspose, ← Matrix.mul_assoc,
      hW_star_W, Matrix.one_mul]
  have htransport (i : Fin e) :
      c₀ • (φP (CA i)).1 = U * (φQ (CB i)).1 * Uᴴ := by
    calc
      c₀ • (φP (CA i)).1 = (φP (c₀ • CA i)).1 := by
        rw [map_smul]
        rfl
      _ = (f (φQ (CB i))).1 := by
        simp only [f, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, hgCB]
      _ = U * (φQ (CB i)).1 * Uᴴ := hU_transport (φQ (CB i))
  have hc₀_ne : c₀ ≠ 0 := Complex.ne_zero_of_norm_eq_one hc₀
  refine ⟨U, c₀⁻¹, hU_corner, hU_star_U, hU_U_star, ?_, ?_⟩
  · simp [norm_inv, hc₀]
  · intro i
    rw [← htransport i, smul_smul, inv_mul_cancel₀ hc₀_ne, one_smul]

/-- A cyclic corner product is supported on the right by its final corner.

This is the support identity used in the concatenation in arXiv:1708.00029,
Appendix A, lines 1041--1056. -/
private lemma cornerProd_mul_finalCorner
    {m : ℕ} [NeZero m]
    (Q : Fin m → MatrixAlg D) (B : MPSTensor d D)
    (hQ : ∀ v, IsOrthogonalProjection (Q v))
    (hQ_shift : ∀ (v : Fin m) (i : Fin d), Q v * B i = B i * Q (v + 1))
    (v : Fin m) (w : List (Fin d)) :
    cornerProd Q B v w * Q (v + w.length • (1 : Fin m)) =
      cornerProd Q B v w := by
  rw [cornerProd_eq_conj_evalWord Q B hQ hQ_shift]
  simp only [Matrix.mul_assoc, (hQ (v + w.length • (1 : Fin m))).2]

/-- Repeated ambient blocked-sector equations concatenate through the corner
partial isometries.

This is the cancellation of adjacent \(U_v^\dagger U_v=Q_v\) factors in
arXiv:1708.00029, Appendix A, lines 1041--1056. -/
private lemma cornerProd_blockMatch_partial_isometry_pow
    {m : ℕ} [NeZero m]
    (P Q : Fin m → MatrixAlg D) (A B : MPSTensor d D)
    (q : Fin m) (U : Fin m → MatrixAlg D) (c : Fin m → ℂ)
    (hP : ∀ u, IsOrthogonalProjection (P u))
    (hQ : ∀ v, IsOrthogonalProjection (Q v))
    (hQ_shift : ∀ (v : Fin m) (i : Fin d), Q v * B i = B i * Q (v + 1))
    (hU_star_U : ∀ u, (U u)ᴴ * U u = Q (u + q))
    (hBC : ∀ (u : Fin m) (w : List (Fin d)), w.length = m →
      cornerProd P A u w =
        c u • (U u * cornerProd Q B (u + q) w * (U u)ᴴ))
    (u : Fin m) (k : ℕ) :
    ∀ W : List (Fin d), W.length = (k + 1) * m →
      cornerProd P A u W =
        (c u) ^ (k + 1) •
          (U u * cornerProd Q B (u + q) W * (U u)ᴴ) := by
  induction k with
  | zero =>
      intro W hW
      rw [zero_add, one_mul] at hW
      simpa using hBC u W hW
  | succ k ih =>
      intro W hW
      set block := W.take m with hblock_def
      set rest := W.drop m with hrest_def
      have hWlen : m ≤ W.length := by rw [hW]; nlinarith [Nat.zero_le k]
      have hblock_len : block.length = m := by
        rw [hblock_def, List.length_take, Nat.min_eq_left hWlen]
      have hrest_len : rest.length = (k + 1) * m := by
        rw [hrest_def, List.length_drop, hW]
        ring_nf
        omega
      have hWeq : W = block ++ rest := (List.take_append_drop m W).symm
      have hshift_block : block.length • (1 : Fin m) = 0 := by
        rw [hblock_len]
        exact nsmul_card_one_fin
      rw [hWeq, cornerProd_append P A hP u block rest,
        hshift_block, add_zero, hBC u block hblock_len, ih rest hrest_len,
        smul_mul_smul_comm, ← pow_succ']
      congr 1
      rw [cornerProd_append Q B hQ (u + q) block rest,
        hshift_block, add_zero]
      have hblock_right :
          cornerProd Q B (u + q) block * Q (u + q) =
            cornerProd Q B (u + q) block := by
        simpa only [hshift_block, add_zero] using
          cornerProd_mul_finalCorner Q B hQ hQ_shift (u + q) block
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (U u)ᴴ (U u), hU_star_U,
        ← Matrix.mul_assoc (cornerProd Q B (u + q) block) (Q (u + q)),
        hblock_right]

/-- The first `n` entries encountered by moving cyclically from `u`.

This orders the concatenated factors in arXiv:1708.00029, Appendix A,
lines 1041--1056. -/
private def cyclicList {m : ℕ} [NeZero m] {α : Type*} (f : Fin m → α) :
    Fin m → ℕ → List α
  | _, 0 => []
  | u, n + 1 => f u :: cyclicList f (u + 1) n

/-- A cyclic list is a list generated by the corresponding finite function.

This is the indexing identity used for the concatenation in arXiv:1708.00029,
Appendix A, lines 1041--1056. -/
private lemma cyclicList_eq_ofFn
    {m : ℕ} [NeZero m] {α : Type*} (f : Fin m → α) (u : Fin m) (n : ℕ) :
    cyclicList f u n =
      List.ofFn (fun j : Fin n => f (u + j.1 • (1 : Fin m))) := by
  induction n generalizing u with
  | zero => simp [cyclicList]
  | succ n ih =>
      rw [cyclicList, List.ofFn_succ, ih]
      congr 1
      · simp
      · congr 1
        funext j
        congr 1
        rw [show (j.succ).1 = j.1 + 1 from rfl, add_nsmul, one_nsmul]
        abel

/-- One complete cyclic list starting at zero is the standard finite list. -/
private lemma cyclicList_zero_card_eq_ofFn
    {m : ℕ} [NeZero m] {α : Type*} (f : Fin m → α) :
    cyclicList f 0 m = List.ofFn f := by
  rw [cyclicList_eq_ofFn]
  congr 1
  funext j
  congr 1
  rw [zero_add]
  have hnsmul : ∀ (n : ℕ) (hn : n < m),
      n • (1 : Fin m) = ⟨n, hn⟩ := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
        rw [succ_nsmul, ih (Nat.lt_of_succ_lt hn)]
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_one']
        rw [Nat.mod_eq_of_lt (by omega : 1 < m)]
        exact Nat.mod_eq_of_lt hn
  exact hnsmul j.1 j.2

/-- Concatenating cyclic word segments multiplies their corner products in
cyclic order.

This is the word-level concatenation in arXiv:1708.00029, Appendix A,
lines 1041--1056. -/
private lemma cornerProd_cyclicList_flatten_succ
    {m : ℕ} [NeZero m]
    (P : Fin m → MatrixAlg D) (A : MPSTensor d D)
    (hP : ∀ u, IsOrthogonalProjection (P u))
    (segments : Fin m → List (Fin d))
    (hsegments : ∀ u, (segments u).length • (1 : Fin m) = 1)
    (u : Fin m) (n : ℕ) :
    cornerProd P A u (cyclicList segments u (n + 1)).flatten =
      (cyclicList (fun k => cornerProd P A k (segments k)) u (n + 1)).prod := by
  induction n generalizing u with
  | zero => simp [cyclicList]
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1) + 1 by omega, cyclicList, List.flatten_cons,
        cornerProd_append P A hP u, hsegments u, ih (u + 1), cyclicList,
        List.prod_cons]
      rw [cyclicList, cyclicList]
      simp only [List.prod_cons]

/-- Supported corner implementers telescope across a cyclic ordered product.

This is the adjacent cancellation \(U_{v+1}^\dagger U_{v+1}=Q_{v+1}\)
in arXiv:1708.00029, Appendix A, lines 1041--1056. -/
private lemma cyclic_partial_isometry_prod_succ
    {m : ℕ} [NeZero m]
    (Q : Fin m → MatrixAlg D) (q : Fin m)
    (U R : Fin m → MatrixAlg D)
    (hU_star_U : ∀ u, (U u)ᴴ * U u = Q (u + q))
    (hR_right : ∀ u, R u * Q (u + 1 + q) = R u)
    (u : Fin m) (n : ℕ) :
    (cyclicList (fun k => U k * R k * (U (k + 1))ᴴ) u (n + 1)).prod =
      U u * (cyclicList R u (n + 1)).prod *
        (U (u + (n + 1) • (1 : Fin m)))ᴴ := by
  induction n generalizing u with
  | zero => simp [cyclicList]
  | succ n ih =>
      change
        (U u * R u * (U (u + 1))ᴴ ::
          cyclicList (fun k => U k * R k * (U (k + 1))ᴴ) (u + 1) (n + 1)).prod =
        U u * (R u :: cyclicList R (u + 1) (n + 1)).prod *
          (U (u + (n + 1 + 1) • (1 : Fin m)))ᴴ
      simp only [List.prod_cons]
      rw [ih (u + 1)]
      have hindex :
          u + (n + 1 + 1) • (1 : Fin m) =
            u + 1 + (n + 1) • (1 : Fin m) := by
        rw [add_nsmul, one_nsmul]
        abel
      rw [hindex]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (U (u + 1))ᴴ (U (u + 1)),
        hU_star_U (u + 1),
        ← Matrix.mul_assoc (R u) (Q (u + 1 + q)), hR_right u]

/-- Translating the projection labels translates the starting label of a
corner product.

This is the fixed sector offset in arXiv:1708.00029, Appendix A,
equation `eq:vprop` and lines 1041--1056. -/
private lemma cornerProd_add_shift
    {m : ℕ} [NeZero m]
    (Q : Fin m → MatrixAlg D) (B : MPSTensor d D)
    (q u : Fin m) (w : List (Fin d)) :
    cornerProd (fun k => Q (k + q)) B u w =
      cornerProd Q B (u + q) w := by
  induction w generalizing u with
  | nil => rfl
  | cons i w ih =>
      simp only [cornerProd_cons, ih]
      congr 2
      abel

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

The cyclic offset `q` records the fixed displacement between matched sector orbits:
`hBlockMatch` pairs sector `u` of `A` with sector `u + q` of `B`. The hypothesis
`hNondeg` rules out zero-dimensional sectors, for which the sector match and its
contraction data would be vacuous. Finally, `hA_lc` and `hB_lc` normalize the original
tensors; comparing the resulting norm identities is what forces the gauge phases
produced by the contraction to have unit modulus.

The available chain inputs are `blockDecompositionMap` /
`IsNBlkInjective.exists_rightInverse` in `MPS/Chain/OneSidedInverse.lean`
(realizing Ω_u for a chosen injective word length) and the two-site
proportionality theorem `tensor_proportional` in `MPS/Chain/TensorEquality.lean`.
The finite-cycle phase choice in lines 1093--1102 is now isolated as
`TNLean.Algebra.exists_fin_complex_unit_cyclic_coboundary_of_prod_eq_one`; the
offset-indexed form needed for the sector match `(u, u + q)` is
`TNLean.Algebra.exists_fin_complex_unit_cyclic_coboundary_shift_of_prod_eq_one`.
The product-one scalar extraction in lines 1072--1080 is isolated as
`PiTensorProductPhase.exists_kappa_product_one_of_piTensorProduct_eq_root_smul`.
Thus the remaining mathematical input is the `m`-factor cyclic contraction
that produces the uniform product-tensor identity and the unit-modulus
normalization of the resulting sector phases; after that, the algebraic scalar
extraction and the phase-coboundary lemma perform the κ/θ/φ telescoping. See
docs/paper-gaps/1708_periodic_overlap_route_alignment.tex. -/
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
  obtain ⟨L, hL_pos, Ω, hΩ⟩ :=
    exists_common_sectorDecompositionMaps_of_isNormal_leftCanonical
      blocksA hA_blocks_lc hNondeg hNormal
  rcases hA_cyclic with
    ⟨hPA_proj, hPA_sum, hPA_shift, hPA_comm, hPA_trace, hPA_intertwine,
      hφA_mul, hφA_star⟩
  rcases hB_cyclic with
    ⟨hPB_proj, hPB_sum, hPB_shift, hPB_comm, hPB_trace, hPB_intertwine,
      hφB_mul, hφB_star⟩
  have hCornerData : ∀ u : Fin m,
      ∃ (U : MatrixAlg D) (c : ℂ),
        U = PA u * U * PB (u + q) ∧
        Uᴴ * U = PB (u + q) ∧
        U * Uᴴ = PA u ∧
        ‖c‖ = 1 ∧
        ∀ i : Fin (blockPhysDim d m), (φA u (blocksA u i)).1 =
          c • (U * (φB (u + q) (blocksB (u + q) i)).1 * Uᴴ) := by
    intro u
    obtain ⟨hdim, hMatch⟩ := hBlockMatch u
    haveI : NeZero (dimA u) := ⟨hNondeg u⟩
    exact exists_ambient_corner_gauge_of_gaugePhase
      (blocksA u) (blocksB (u + q)) hdim (PA u) (PB (u + q))
      (φA u) (φB (u + q)) (hPA_proj u) (hPB_proj (u + q))
      (hφA_mul u) (hφB_mul (u + q)) (hφA_star u) (hφB_star (u + q))
      (hA_blocks_lc u) (hB_blocks_lc (u + q)) (hNormal u) hMatch
  let U : Fin m → MatrixAlg D := fun u => (hCornerData u).choose
  let c : Fin m → ℂ := fun u => (hCornerData u).choose_spec.choose
  have hU_corner : ∀ u, U u = PA u * U u * PB (u + q) :=
    fun u => (hCornerData u).choose_spec.choose_spec.1
  have hU_star_U : ∀ u, (U u)ᴴ * U u = PB (u + q) :=
    fun u => (hCornerData u).choose_spec.choose_spec.2.1
  have hU_U_star : ∀ u, U u * (U u)ᴴ = PA u :=
    fun u => (hCornerData u).choose_spec.choose_spec.2.2.1
  have hc_norm : ∀ u, ‖c u‖ = 1 :=
    fun u => (hCornerData u).choose_spec.choose_spec.2.2.2.1
  have hBlockAmbient : ∀ (u : Fin m) (i : Fin (blockPhysDim d m)),
      PA u * (blockTensor A m) i * PA u =
        c u • (U u * (PB (u + q) * (blockTensor B m) i * PB (u + q)) *
          (U u)ᴴ) := by
    intro u i
    rw [← hA_letter u i, ← hB_letter (u + q) i]
    exact (hCornerData u).choose_spec.choose_spec.2.2.2.2 i
  let P : Fin m → MatrixAlg D := fun u => PA (-u)
  let Q : Fin m → MatrixAlg D := fun v => PB (-v)
  let q' : Fin m := -q
  let U' : Fin m → MatrixAlg D := fun u => U (-u)
  let c' : Fin m → ℂ := fun u => c (-u)
  let dimA' : Fin m → ℕ := fun u => dimA (-u)
  let blocksA' : (u : Fin m) → MPSTensor (blockPhysDim d m) (dimA' u) :=
    fun u => blocksA (-u)
  let φA' : (u : Fin m) →
      MatrixAlg (dimA' u) ≃ₗ[ℂ] cornerSubmodule (P u) :=
    fun u => φA (-u)
  have hP_proj : ∀ u, IsOrthogonalProjection (P u) := fun u => hPA_proj (-u)
  have hQ_proj : ∀ v, IsOrthogonalProjection (Q v) := fun v => hPB_proj (-v)
  have hA_offDiag :
      ∀ (k : Fin m) (i : Fin d), PA (k + 1) * A i = A i * PA k :=
    offDiag_shift_of_adjoint_cyclic_shift A hA_lc hPA_proj hPA_shift
  have hB_offDiag :
      ∀ (k : Fin m) (i : Fin d), PB (k + 1) * B i = B i * PB k :=
    offDiag_shift_of_adjoint_cyclic_shift B hB_lc hPB_proj hPB_shift
  have hP_shift : ∀ (u : Fin m) (i : Fin d), P u * A i = A i * P (u + 1) := by
    intro u i
    have h := hA_offDiag (-(u + 1)) i
    have hindex : -(u + 1) + 1 = -u := by abel
    rw [hindex] at h
    exact h
  have hQ_shift : ∀ (v : Fin m) (i : Fin d), Q v * B i = B i * Q (v + 1) := by
    intro v i
    have h := hB_offDiag (-(v + 1)) i
    have hindex : -(v + 1) + 1 = -v := by abel
    rw [hindex] at h
    exact h
  have hU'_corner : ∀ u, U' u = P u * U' u * Q (u + q') := by
    intro u
    have h := hU_corner (-u)
    have hindex : -(u + q') = -u + q := by simp only [q']; abel
    change U (-u) = PA (-u) * U (-u) * PB (-(u + q'))
    rw [hindex]
    exact h
  have hU'_star_U : ∀ u, (U' u)ᴴ * U' u = Q (u + q') := by
    intro u
    have h := hU_star_U (-u)
    have hindex : -(u + q') = -u + q := by simp only [q']; abel
    change (U (-u))ᴴ * U (-u) = PB (-(u + q'))
    rw [hindex]
    exact h
  have hU'_U_star : ∀ u, U' u * (U' u)ᴴ = P u := by
    intro u
    exact hU_U_star (-u)
  have hc'_norm : ∀ u, ‖c' u‖ = 1 := fun u => hc_norm (-u)
  have hBlockAmbient' : ∀ (u : Fin m) (i : Fin (blockPhysDim d m)),
      P u * (blockTensor A m) i * P u =
        c' u • (U' u * (Q (u + q') * (blockTensor B m) i * Q (u + q')) *
          (U' u)ᴴ) := by
    intro u i
    have h := hBlockAmbient (-u) i
    have hindex : -(u + q') = -u + q := by simp only [q']; abel
    change PA (-u) * (blockTensor A m) i * PA (-u) =
      c (-u) • (U (-u) *
        (PB (-(u + q')) * (blockTensor B m) i * PB (-(u + q'))) *
          (U (-u))ᴴ)
    rw [hindex]
    exact h
  have hBC : ∀ (u : Fin m) (w : List (Fin d)), w.length = m →
      cornerProd P A u w =
        c' u • (U' u * cornerProd Q B (u + q') w * (U' u)ᴴ) := by
    intro u w hw
    induction w using List.ofFnRec with
    | _ n σ =>
        simp only [List.length_ofFn] at hw
        subst n
        let i : Fin (blockPhysDim d m) := (decodeBlockEquiv d m).symm σ
        have hword : wordOfBlock d m i = List.ofFn σ := by
          simp [wordOfBlock, i]
        rw [← hword,
          cornerProd_eq_blockDiagCorner P A hP_proj hP_shift,
          cornerProd_eq_blockDiagCorner Q B hQ_proj hQ_shift]
        exact hBlockAmbient' u i
  let segments
      (σ : Fin m → Fin d) (ρ : Fin m → (Fin (m * L) → Fin d))
      (k : Fin m) : List (Fin d) :=
    σ k :: List.ofFn (ρ k)
  let combinedWord
      (σ : Fin m → Fin d) (ρ : Fin m → (Fin (m * L) → Fin d)) :
      List (Fin d) :=
    (cyclicList (segments σ ρ) 0 m).flatten
  have hsegments :
      ∀ (σ : Fin m → Fin d) (ρ : Fin m → (Fin (m * L) → Fin d))
        (k : Fin m),
        (segments σ ρ k).length • (1 : Fin m) = 1 := by
    intro σ ρ k
    simp only [segments, List.length_cons, List.length_ofFn, add_nsmul, one_nsmul,
      mul_nsmul, nsmul_card_one_fin, nsmul_zero, zero_add]
  have hcombinedWord_length :
      ∀ (σ : Fin m → Fin d) (ρ : Fin m → (Fin (m * L) → Fin d)),
        (combinedWord σ ρ).length = (m * L + 1) * m := by
    intro σ ρ
    simp only [combinedWord, cyclicList_zero_card_eq_ofFn, List.length_flatten,
      List.map_ofFn, List.sum_ofFn, segments]
    simp only [Function.comp_apply, List.length_cons, List.length_ofFn]
    simp
    exact Nat.mul_comm m (m * L + 1)
  have hcombinedWord_corner :
      ∀ (σ : Fin m → Fin d) (ρ : Fin m → (Fin (m * L) → Fin d)),
        cornerProd P A 0 (combinedWord σ ρ) =
          (List.ofFn (fun k => cornerLetter P A k (σ k) *
            cornerProd P A (k + 1) (List.ofFn (ρ k)))).prod := by
    intro σ ρ
    have hm : m.pred + 1 = m := Nat.succ_pred_eq_of_pos (NeZero.pos m)
    have hconcat :=
      cornerProd_cyclicList_flatten_succ P A hP_proj (segments σ ρ)
        (hsegments σ ρ) 0 m.pred
    rw [hm, cyclicList_zero_card_eq_ofFn] at hconcat
    rw [cyclicList_zero_card_eq_ofFn] at hconcat
    change cornerProd P A 0 (cyclicList (segments σ ρ) 0 m).flatten = _
    rw [cyclicList_zero_card_eq_ofFn, hconcat]
    apply congrArg List.prod
    apply List.ofFn_inj.mpr
    funext k
    simp only [segments, cornerProd_cons, cornerLetter, Matrix.mul_assoc,
      corner_mul_cornerProd P A (k + 1) (List.ofFn (ρ k)) (hP_proj (k + 1))]
  have hcombinedMatch :
      ∀ (σ : Fin m → Fin d) (ρ : Fin m → (Fin (m * L) → Fin d)),
        (List.ofFn (fun k => cornerLetter P A k (σ k) *
          cornerProd P A (k + 1) (List.ofFn (ρ k)))).prod =
            (c' 0) ^ (m * L + 1) •
              (U' 0 * cornerProd Q B q' (combinedWord σ ρ) * (U' 0)ᴴ) := by
    intro σ ρ
    rw [← hcombinedWord_corner σ ρ]
    simpa only [zero_add] using
      cornerProd_blockMatch_partial_isometry_pow P Q A B q' U' c'
        hP_proj hQ_proj hQ_shift hU'_star_U hBC 0 (m * L)
        (combinedWord σ ρ) (hcombinedWord_length σ ρ)
  let Ω' : (u : Fin m) →
      MatrixAlg (dimA' u) →ₗ[ℂ]
        ((Fin L → Fin (blockPhysDim d m)) → ℂ) :=
    fun u => Ω (-u)
  have hΩ' : ∀ (u : Fin m) (X : MatrixAlg (dimA' u)),
      ∑ σ : Fin L → Fin (blockPhysDim d m),
        Ω' u X σ • evalWord (blocksA' u) (List.ofFn σ) = X :=
    fun u X => hΩ (-u) X
  have hφA'_mul : ∀ (u : Fin m) (X Y : MatrixAlg (dimA' u)),
      (φA' u (X * Y)).1 = (φA' u X).1 * (φA' u Y).1 :=
    fun u X Y => hφA_mul (-u) X Y
  have hA'_letter : ∀ (u : Fin m) (i : Fin (blockPhysDim d m)),
      (φA' u (blocksA' u i)).1 =
        P u * (blockTensor A m) i * P u :=
    fun u i => hA_letter (-u) i
  obtain ⟨Ωhat, hΩhat⟩ :=
    exists_ambientCornerRightInverse_of_sectorRightInverse
      P A blocksA' φA' hP_proj hP_shift hφA'_mul hA'_letter
      L hL_pos Ω' hΩ'
  -- Remaining obligation (arXiv:1708.00029 lines 1023--1117): an `m`-factor cyclic
  -- contraction theorem built from the common `L` and the sum-form right inverses
  -- `Ω u` satisfying `hΩ`; after producing the uniform product-tensor identity,
  -- it applies `PiTensorProductPhase.exists_kappa_product_one_of_piTensorProduct_eq_root_smul`
  -- and the unit-modulus argument from left-canonical normalization, then uses
  -- `TNLean.Algebra.exists_fin_complex_unit_cyclic_coboundary_shift_of_prod_eq_one`
  -- for the offset-indexed κ/θ/φ telescoping (lines 1093--1102). This upgrades the
  -- per-sector blocked gauge-phase equivalences in `hBlockMatch` to one global
  -- phase and one global gauge. The available two-site theorem is `tensor_proportional`.
  sorry

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

The specified projectors and corner identifications realize the blocked sector
tensors as the corners \(C_u^\alpha = P_u (A^{[m]})^\alpha P_u\) and
\(D_v^\alpha = Q_v (B^{[m]})^\alpha Q_v\), matching the \(C_u\)-notation
used in Lemma bdcf before the Appendix A contraction step.

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
  -- one-site rotation covariance of the cross sector overlap; the remaining
  -- obligation is the stage-3 contraction `sectorTensor_proportional_of_blockedMatch`.
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
  have hNormal : ∀ u, IsNormal (blocksA u) := fun u =>
    sectorBlocked_isNormal_of_isPeriodic A hA blocksA hA_blocks_lc hA_mpv
      hA_cyclic_exists u (hNondegA u)
  -- Stage 3: contract the (reindexed) per-sector matches into a global gauge.
  refine sectorTensor_proportional_of_blockedMatch A B hA_lc hB_lc blocksA blocksB
    hA_blocks_lc hB_blocks_lc hA_mpv hB_mpv hA_cyclic hB_cyclic hA_letter
    hB_letter (v₀ - u₀) ?_ hNondegA hNormal
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
