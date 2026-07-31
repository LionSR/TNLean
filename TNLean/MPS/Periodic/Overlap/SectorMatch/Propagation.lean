/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.Overlap.SectorOverlapTransport

/-!
# Periodic sector-match propagation

This module proves that one matching pair of sectors propagates around the
whole periodic orbit.

## Main declarations

* `sectorMatch_propagation`

## References

* De las Cuevas, Cirac, Schuch, Perez-Garcia,
  *Irreducible forms of Matrix Product States: Theory and Applications*,
  arXiv:1708.00029, Appendix A.
-/

open scoped Matrix BigOperators ComplexOrder InnerProductSpace TensorProduct
open Filter Matrix Module

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

**Corner transition tensors.** Rather than translate the global
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
  -- family of arXiv:1708.00029 lines 985--1002). The one-step input is
  -- `sectorGaugePhaseEquiv_succ_of_cyclicTransport`.
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

end MPSTensor
