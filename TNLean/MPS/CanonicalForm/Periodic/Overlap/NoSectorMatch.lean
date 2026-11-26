/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.DirectSum.BlockAssembly
import TNLean.MPS.Transfer.Spectrum.GaugePhase
import TNLean.MPS.CanonicalForm.Periodic.Overlap.SelfOverlapNonrep
import TNLean.MPS.CanonicalForm.Periodic.CyclicSectors.GaugePhase
import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Periodic overlap dichotomy: Case 2

This module contains the equal-period, no-sector-match case of Appendix A of
arXiv:1708.00029: after blocking by the common period, absence of a sector match
forces the overlap to tend to $0$.

## Main declarations

* `sectorBlocked_isNormal_of_isPeriodic`
* `exists_sector_match_of_gaugePhaseEquiv`
* `periodicOverlap_tendsto_zero_of_no_sector_match`
* `MPSTensor.periodicOverlap_tendsto_zero_of_ne_period`: periodic overlap dichotomy: Case 1.

## References

* De las Cuevas, Cirac, Schuch, Perez-Garcia,
  *Irreducible forms of Matrix Product States: Theory and Applications*,
  arXiv:1708.00029, Appendix A.
-/

open scoped Matrix BigOperators ComplexOrder InnerProductSpace
open Filter Matrix

section DifferentPeriod

/-!
## Periodic overlap dichotomy: Case 1

This module contains the different-period case of Appendix A of
arXiv:1708.00029: if two periodic tensors have different periods, then their
overlap tends to $0$.

### Main declarations

* `periodicOverlap_tendsto_zero_of_ne_period`

### References

* De las Cuevas, Cirac, Schuch, Perez-Garcia,
  *Irreducible forms of Matrix Product States: Theory and Applications*,
  arXiv:1708.00029, Appendix A.
-/

namespace MPSTensor

variable {d D : ℕ}

/-! ## Case 1: Different periods → orthogonal (Appendix A, first case) -/

/-- The conjugation `Y ↦ X Y Xᴴ` as a linear equivalence on matrices. -/
private noncomputable def glConjEquiv (X : GL (Fin D) ℂ) :
    Matrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  (X.mulLeftLinearEquiv ℂ (Matrix (Fin D) (Fin D) ℂ)).trans
    ((star X).mulRightLinearEquiv ℂ)

/-- **GaugePhaseEquiv preserves periods.**

If two periodic tensors (same bond dimension) are gauge-phase equivalent,
they must have the same period.

arXiv:0909.5347, via eigenvalue uniqueness (Wolf Theorem 6.3). This is the
load-bearing step of the substitute proof route for different-period decay — the
peripheral spectrum in place of the paper's lcm-blocking and one-site translation
argument — documented in docs/paper-gaps/dccsp17_periodic_overlap_route_alignment.tex. -/
private theorem period_eq_of_gaugePhaseEquiv_of_isPeriodic
    {A B : MPSTensor d D}
    {m_a m_b : ℕ} (hA : IsPeriodic m_a A) (hB : IsPeriodic m_b B)
    (hGPE : GaugePhaseEquiv A B) : m_a = m_b := by
  have : NeZero D := ⟨hA.bondDim_ne_zero⟩
  obtain ⟨X, ζ, hζ_ne, hBi⟩ := hGPE
  -- Transfer map scaling: B = ζ • (X A X⁻¹) implies E_B = |ζ|² E_{XAX⁻¹}
  have hEB_eq : ∀ Y, Kraus.transferMap (ι := Fin d) (n := Fin D) B Y =
      (ζ * starRingEnd ℂ ζ) •
        (X.val * Kraus.transferMap (ι := Fin d) (n := Fin D) A
          (X⁻¹.val * Y * X⁻¹.valᴴ) * X.valᴴ) := by
    intro Y
    simp only [Kraus.transferMap_apply]
    simp_rw [hBi]
    simp only [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm,
      smul_smul, ← Finset.smul_sum, Matrix.conjTranspose_mul,
      Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc]
    congr 1; exact mul_comm _ _
  have hζ_norm : ‖ζ‖ = 1 :=
    gaugePhase_scalar_norm_eq_one_of_leftCanonical_irreducible
      hA.leftCanonical hB.leftCanonical hB.irreducible hζ_ne hBi
  have hζζ_real : ζ * starRingEnd ℂ ζ = (↑(‖ζ‖ ^ 2) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h_eig_eq : ‖ζ‖ ^ 2 = 1 := by
    rw [hζ_norm]
    norm_num
  have hRepeated : RepeatedBlocks A B :=
    repeatedBlocks_of_gaugePhaseData_norm_one X hζ_norm hBi
  -- Peripheral eigenvalue equality via conjugation
  have hSpec : peripheralEigenvalues (Kraus.transferMap (ι := Fin d) (n := Fin D) A) =
      peripheralEigenvalues (Kraus.transferMap (ι := Fin d) (n := Fin D) B) := by
    have hEB_is_conj : Kraus.transferMap (ι := Fin d) (n := Fin D) B =
        (glConjEquiv X).conj (Kraus.transferMap (ι := Fin d) (n := Fin D) A) := by
      apply LinearMap.ext; intro Y
      rw [hEB_eq, hζζ_real, show (↑(‖ζ‖ ^ 2) : ℂ) = (1 : ℂ) from by simp [h_eig_eq],
        one_smul,
        show (glConjEquiv X).conj (Kraus.transferMap (ι := Fin d) (n := Fin D) A) Y =
          X.val * (Kraus.transferMap (ι := Fin d) (n := Fin D) A
            (X⁻¹.val * (Y * X⁻¹.valᴴ)) * X.valᴴ) from by
          rw [LinearEquiv.conj_apply_apply]
          simp only [glConjEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply,
            Units.mulLeftLinearEquiv_apply, Units.mulRightLinearEquiv_apply,
            Units.symm_mulLeftLinearEquiv_apply, Units.symm_mulRightLinearEquiv_apply]
          simp [Matrix.star_eq_conjTranspose, Matrix.mul_assoc, Finset.mul_sum, Finset.sum_mul]]
      simp only [Matrix.mul_assoc]
    rw [hEB_is_conj]
    exact (peripheralEigenvalues_conj (glConjEquiv X)
      (Kraus.transferMap (ι := Fin d) (n := Fin D) A)).symm
  exact IsPeriodic.period_eq_of_repeatedBlocks hA hB hRepeated hSpec

/-- If two periodic tensors have different periods `m_a ≠ m_b`, their overlap
decays to zero.

Source: arXiv:1708.00029, Appendix A, lines 917--950. There the different-period
decay is obtained by blocking at p = lcm(m_a, m_b) and using that, by
Lemma bdcf, the blocks P_u A^{(p)} and Q_v B^{(p)} are non-repeated normal
tensors, so that applying the one-site translation operator to Q_v B^{(p)}
versus Q_{v+1} B^{(p)} yields a contradiction unless the overlap vanishes.

**Local fix (route substitution, different-period decay via the peripheral
spectrum):** the Lean proof realizes the *same* obstruction through the
peripheral-spectrum form rather than the paper's lcm-blocking + translation
argument. If D₁ = D₂ and
B i = ζ X (A i) X⁻¹, then
𝓔_B(Y) = ζ · (conj ζ) · X 𝓔_A(X⁻¹ Y X⁻ᴴ) Xᴴ. Eigenvalue uniqueness for an irreducible CP
map (Wolf, *Quantum Channels & Operations*, Thm 6.3) forces |ζ| = 1, so the
peripheral spectra of 𝓔_A and 𝓔_B agree. An `m`-periodic tensor has peripheral
spectrum {e^{2πi r/m} : 0 ≤ r < m}, so agreement forces m_a = m_b; hence
different periods exclude gauge-phase equivalence, and equal-or-orthogonal (the
irreducible trace-preserving overlap dichotomy) gives the decay. This is a
mathematically equivalent substitute for the paper's step, documented in
docs/paper-gaps/dccsp17_periodic_overlap_route_alignment.tex. -/
theorem periodicOverlap_tendsto_zero_of_ne_period
    {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    {m_a m_b : ℕ}
    (hA : IsPeriodic m_a A) (hB : IsPeriodic m_b B)
    (hne : m_a ≠ m_b) :
    Tendsto (fun N => mpvOverlap A B N) atTop (nhds 0) := by
  have : NeZero D₁ := ⟨hA.bondDim_ne_zero⟩
  have : NeZero D₂ := ⟨hB.bondDim_ne_zero⟩
  by_cases hD : D₁ = D₂
  · subst hD
    exact mpvOverlap_tendsto_zero_of_irreducible_TP A B
      hA.irreducible hB.irreducible hA.leftCanonical hB.leftCanonical
      (fun hGPE => hne (period_eq_of_gaugePhaseEquiv_of_isPeriodic hA hB hGPE))
  · exact mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP A B
      hA.irreducible hB.irreducible hA.leftCanonical hB.leftCanonical hD


end MPSTensor

end DifferentPeriod

section NoSectorMatch

open Kraus (blockPhysDim wordOfBlock blockTensor)

namespace MPSTensor

variable {d D : ℕ}

/-! ## Case 2: Same period, no sector match → orthogonal (Appendix A, second case) -/

/-- Case-2 normality lemma for the compressed blocked sector tensors.

The intended mathematical content is arXiv:1708.00029, lemma lem:bdcf,
lines 377--384: after blocking by the period, each cyclic sector is a normal
tensor. The statement uses the compressed sector tensor on the corner bond
space, as produced by `exists_cyclic_sector_decomp_after_blocking_of_isPeriodic`.

The nontriviality hypothesis `dim u ≠ 0` excludes the degenerate
zero-dimensional "missing sector" case. An `MPSTensor _ 0` may satisfy
block-injectivity/normality vacuously, so this assumption focuses the statement
on genuine nonempty sectors.

The `hBlocks_mpv` hypothesis ties the compressed block decomposition back to
the original blocked tensor, and `hCyclic` ensures the block indexing
follows the cyclic orbit structure of the transfer map's peripheral
spectrum (see `IsCyclicSectorDecomp`).

The orbit-lift / corner-irreducibility input is supplied unconditionally by
`SelfOverlap.primitive_and_irreducible_sectorBlocks_of_cyclicDecomp`. -/
lemma sectorBlocked_isNormal_of_isPeriodic
    (A : MPSTensor d D) {m : ℕ} [NeZero m]
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
    Kraus.IsNormal (blocks u) := by
  have : NeZero (dim u) := ⟨hNonzero⟩
  obtain ⟨hPrim, hIrr⟩ :=
    primitive_and_irreducible_sectorBlocks_of_cyclicDecomp
      A hP blocks hBlocks_lc hBlocks_mpv hCyclic u hNonzero
  exact isNormal_of_tp_primitive_irreducible (blocks u) (hBlocks_lc u) hPrim hIrr

/-- Gauge-phase equivalence is preserved by physical blocking.

If `B i = ζ · X A i X⁻¹`, then every blocked letter is a word of length `L`,
so `blockTensor B L` is related to `blockTensor A L` by the same gauge and
phase `ζ ^ L`. -/
private theorem gaugePhaseEquiv_blockTensor
    (A B : MPSTensor d D) (L : ℕ)
    (hGPE : GaugePhaseEquiv A B) :
    GaugePhaseEquiv (blockTensor (d := d) (n := Fin D) A L)
      (blockTensor (d := d) (n := Fin D) B L) := by
  rcases hGPE with ⟨X, ζ, hζ, hX⟩
  refine ⟨X, ζ ^ L, pow_ne_zero L hζ, ?_⟩
  intro i
  let C : MPSTensor d D := fun j =>
    (X : Matrix (Fin D) (Fin D) ℂ) * A j *
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  have hB : B = fun j => ζ • C j := by
    funext j
    simpa [C] using hX j
  have hGauge :
      Kraus.evalWord C (wordOfBlock d L i) =
        (X : Matrix (Fin D) (Fin D) ℂ) *
          Kraus.evalWord A (wordOfBlock d L i) *
          ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
    simpa [C] using
      (evalWord_gauge (A := A) (B := C) X (by intro j; rfl)
        (wordOfBlock d L i))
  calc
    blockTensor (d := d) (n := Fin D) B L i
        = Kraus.evalWord B (wordOfBlock d L i) := rfl
    _ = Kraus.evalWord (fun j => ζ • C j) (wordOfBlock d L i) := by simp [hB]
    _ = (ζ ^ (wordOfBlock d L i).length) •
          Kraus.evalWord C (wordOfBlock d L i) := by
          simpa using
            (Kraus.evalWord_smul (ζ := ζ) (K := C) (wordOfBlock d L i))
    _ = (ζ ^ L) •
          ((X : Matrix (Fin D) (Fin D) ℂ) *
            blockTensor (d := d) (n := Fin D) A L i *
            ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
          simp only [hGauge, Kraus.length_wordOfBlock, Matrix.coe_units_inv]
          rfl

/-- A periodic tensor has nonzero blocked self-overlap limit after blocking by
its period; the limit is the period itself. This restates
`periodicSelfOverlap_tendsto` for the blocked tensor. -/
private theorem blockTensor_selfOverlap_tendsto_of_isPeriodic
    (A : MPSTensor d D) {m : ℕ} [NeZero m]
    (hP : IsPeriodic m A) :
    Tendsto
      (fun N => mpvOverlap (d := blockPhysDim d m)
        (blockTensor (d := d) (n := Fin D) A m)
        (blockTensor (d := d) (n := Fin D) A m) N)
      atTop (nhds (m : ℂ)) := by
  have : NeZero D := ⟨hP.bondDim_ne_zero⟩
  have hSelf : Tendsto (fun N => mpvOverlap A A (m * N)) atTop (nhds (m : ℂ)) :=
    periodicSelfOverlap_tendsto A hP
  refine hSelf.congr' ?_
  filter_upwards with N
  rw [mpvOverlap_blockTensor_self_eq]
  simp [Nat.mul_comm]

/-- A gauge-phase equivalence between the period-blocked tensors of two
periodic tensors gives a mixed blocked overlap which does not tend to zero.

The proof uses the nonzero blocked self-overlap limits from Appendix A,
lines 908-914 of arXiv:1708.00029, to show that the gauge factor has unit
modulus. -/
private theorem gaugePhase_blockTensor_overlap_not_tendsto_zero_of_periodic
    (A B : MPSTensor d D) {m : ℕ} [NeZero m]
    (hA : IsPeriodic m A) (hB : IsPeriodic m B)
    (hGPE_block :
      GaugePhaseEquiv (blockTensor (d := d) (n := Fin D) A m)
        (blockTensor (d := d) (n := Fin D) B m)) :
    ¬ Tendsto
      (fun N => mpvOverlap (d := blockPhysDim d m)
        (blockTensor (d := d) (n := Fin D) A m)
        (blockTensor (d := d) (n := Fin D) B m) N)
      atTop (nhds (0 : ℂ)) := by
  classical
  intro hZero
  obtain ⟨X, ζ, _hζ, hX⟩ := hGPE_block
  let Ablk := blockTensor (d := d) (n := Fin D) A m
  let Bblk := blockTensor (d := d) (n := Fin D) B m
  have hA_self : Tendsto (fun N => mpvOverlap (d := blockPhysDim d m) Ablk Ablk N)
      atTop (nhds (m : ℂ)) := by
    simpa [Ablk] using blockTensor_selfOverlap_tendsto_of_isPeriodic A hA
  have hB_self : Tendsto (fun N => mpvOverlap (d := blockPhysDim d m) Bblk Bblk N)
      atTop (nhds (m : ℂ)) := by
    simpa [Bblk] using blockTensor_selfOverlap_tendsto_of_isPeriodic B hB
  have hmpv : ∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)),
      mpv Bblk σ = ζ ^ N * mpv Ablk σ :=
    mpv_eq_pow_mul_of_gaugePhase Ablk Bblk X ζ hX
  have hm_norm_ne : ‖(m : ℂ)‖ ≠ 0 := by
    simpa using (Nat.cast_ne_zero.mpr (NeZero.ne m) : (m : ℂ) ≠ 0)
  have hζnorm : ‖ζ‖ = 1 := by
    exact norm_eq_one_of_selfOverlap_scale_at_nonzero_limit
      (A := Ablk) (B := Bblk) (ζ := ζ) hm_norm_ne
      hA_self.norm hB_self.norm
      (mpvOverlap_self_scale_of_mpv_eq_pow_mul (A := Ablk) (B := Bblk) (ζ := ζ) hmpv)
  have hCrossNormEq : ∀ N,
      ‖mpvOverlap (d := blockPhysDim d m) Ablk Bblk N‖ =
        ‖mpvOverlap (d := blockPhysDim d m) Ablk Ablk N‖ := by
    intro N
    rw [mpvOverlap_eq_star_pow_mul_self_of_mpv_eq_pow_mul (A := Ablk) (B := Bblk)
      (ζ := ζ) hmpv N]
    simp [norm_pow, hζnorm]
  have hCrossNormZero : Tendsto
      (fun N => ‖mpvOverlap (d := blockPhysDim d m) Ablk Bblk N‖)
      atTop (nhds (0 : ℝ)) := by
    simpa using hZero.norm
  have hA_self_norm_zero : Tendsto
      (fun N => ‖mpvOverlap (d := blockPhysDim d m) Ablk Ablk N‖)
      atTop (nhds (0 : ℝ)) :=
    hCrossNormZero.congr hCrossNormEq
  have hLimit : (0 : ℝ) = ‖(m : ℂ)‖ :=
    tendsto_nhds_unique hA_self_norm_zero hA_self.norm
  have hm_pos : 0 < ‖(m : ℂ)‖ :=
    (norm_nonneg _).lt_of_ne (Ne.symm hm_norm_ne)
  exact (ne_of_gt hm_pos) hLimit.symm

/-- Mixed-overlap extraction after blocking.

If two blocked tensors are globally gauge-phase equivalent and both are decomposed
into cyclic compressed sectors, then some sector of the `A` decomposition has a
non-decaying overlap with some sector of the `B` decomposition.

This is the contrapositive extraction behind the same-period case in
arXiv:1708.00029, Appendix A, lines 952-960. The proof expands the total
blocked overlap, using the two block decompositions, as a finite double sum of
sector overlaps. Global gauge-phase equivalence keeps the total blocked overlap
from tending to zero, so not every mixed sector overlap can tend to zero. -/
private lemma exists_nondecaying_sectorOverlap_of_blockedGaugePhaseEquiv_cyclicDecomp
    (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA : IsPeriodic m A) (hB : IsPeriodic m B)
    {dimA dimB : Fin m → ℕ}
    (blocksA :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (hA_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksA))
    (hB_mpv :
      SameMPV₂ (blockTensor B m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksB))
    (hGPE_block :
      GaugePhaseEquiv (blockTensor (d := d) (n := Fin D) A m)
        (blockTensor (d := d) (n := Fin D) B m)) :
    ∃ u v : Fin m,
      ¬ Tendsto
        (fun N => mpvOverlap (d := blockPhysDim d m)
          (blocksA u) (blocksB v) N)
        atTop (nhds (0 : ℂ)) := by
  classical
  by_contra hNone
  simp only [not_exists, not_not] at hNone
  have hOverlap_eq : ∀ N,
      mpvOverlap (d := blockPhysDim d m)
          (blockTensor (d := d) (n := Fin D) A m)
          (blockTensor (d := d) (n := Fin D) B m) N =
        ∑ u : Fin m, ∑ v : Fin m,
          mpvOverlap (d := blockPhysDim d m) (blocksA u) (blocksB v) N := by
    intro N
    exact mpvOverlap_eq_sum_of_sameMPV₂_toTensorFromBlocks_one
      (blockTensor (d := d) (n := Fin D) A m)
      (blockTensor (d := d) (n := Fin D) B m)
      blocksA blocksB hA_mpv hB_mpv N
  have hInnerZero : ∀ u : Fin m,
      Tendsto
        (fun N => ∑ v : Fin m,
          mpvOverlap (d := blockPhysDim d m) (blocksA u) (blocksB v) N)
        atTop (nhds (0 : ℂ)) := by
    intro u
    have := tendsto_finsetSum (s := Finset.univ) fun v _ => hNone u v
    simpa using this
  have hSumZero :
      Tendsto
        (fun N => ∑ u : Fin m, ∑ v : Fin m,
          mpvOverlap (d := blockPhysDim d m) (blocksA u) (blocksB v) N)
        atTop (nhds (0 : ℂ)) := by
    have := tendsto_finsetSum (s := Finset.univ) fun u _ => hInnerZero u
    simpa using this
  have hGlobalZero :
      Tendsto
        (fun N => mpvOverlap (d := blockPhysDim d m)
          (blockTensor (d := d) (n := Fin D) A m)
          (blockTensor (d := d) (n := Fin D) B m) N)
        atTop (nhds (0 : ℂ)) :=
    hSumZero.congr fun N => (hOverlap_eq N).symm
  exact
    (gaugePhase_blockTensor_overlap_not_tendsto_zero_of_periodic
      A B hA hB hGPE_block) hGlobalZero

/-- Existence of a matching pair of compressed sectors after blocking.

After transporting global gauge-phase equivalence to the blocked tensors, the
block-sum overlap gives a non-decaying pair of sectors. Irreducibility then
forces equal dimensions and gauge-phase equivalence for that pair. -/
private lemma exists_sector_match_of_blockedGaugePhaseEquiv_cyclicDecomp
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
    (hNondegA : ∀ u, dimA u ≠ 0)
    (hNondegB : ∀ v, dimB v ≠ 0)
    (hGPE_block :
      GaugePhaseEquiv (blockTensor (d := d) (n := Fin D) A m)
        (blockTensor (d := d) (n := Fin D) B m)) :
    ∃ (u v : Fin m) (hdim : dimA u = dimB v),
      dimA u ≠ 0 ∧
      GaugePhaseEquiv
        (cast (congr_arg
          (MPSTensor (blockPhysDim d m)) hdim)
          (blocksA u))
        (blocksB v) := by
  obtain ⟨u, v, hNondecay⟩ :=
    exists_nondecaying_sectorOverlap_of_blockedGaugePhaseEquiv_cyclicDecomp
      A B hA hB blocksA blocksB hA_mpv hB_mpv hGPE_block
  have : NeZero (dimA u) := ⟨hNondegA u⟩
  have : NeZero (dimB v) := ⟨hNondegB v⟩
  have hA_irr : Kraus.IsIrreducibleFamily (blocksA u) :=
    (primitive_and_irreducible_sectorBlocks_of_cyclicDecomp
      A hA blocksA hA_blocks_lc hA_mpv hA_cyclic u (hNondegA u)).2
  have hB_irr : Kraus.IsIrreducibleFamily (blocksB v) :=
    (primitive_and_irreducible_sectorBlocks_of_cyclicDecomp
      B hB blocksB hB_blocks_lc hB_mpv hB_cyclic v (hNondegB v)).2
  have hdim : dimA u = dimB v := by
    by_contra hne
    exact hNondecay
      (mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP
        (blocksA u) (blocksB v) hA_irr hB_irr
        (hA_blocks_lc u) (hB_blocks_lc v) hne)
  refine ⟨u, v, hdim, hNondegA u, ?_⟩
  by_contra hNot
  exact hNondecay
    (mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP
      hdim (blocksA u) (blocksB v) hA_irr hB_irr
      (hA_blocks_lc u) (hB_blocks_lc v) hNot)

/-- A global gauge-phase equivalence between two periodic tensors forces at
least one compatible nonzero pair of compressed cyclic sectors to be
gauge-phase equivalent.

This is the structural step used by the no-sector-match case: the cyclic
sector decomposition is unique up to relabeling, and a global gauge-phase
equivalence carries a nonzero sector of `A` to a sector of `B`. The
nondegeneracy assumptions ensure that the returned `A` sector has nonzero
virtual dimension and that the corresponding `B` sector has positive bond
dimension. Both assumptions come from the periodic sector decomposition. -/
lemma exists_sector_match_of_gaugePhaseEquiv
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
    (hNondegA : ∀ u, dimA u ≠ 0)
    (hNondegB : ∀ v, dimB v ≠ 0)
    (hGPE : GaugePhaseEquiv A B) :
    ∃ (u v : Fin m) (hdim : dimA u = dimB v),
      dimA u ≠ 0 ∧
      GaugePhaseEquiv
        (cast (congr_arg
          (MPSTensor (blockPhysDim d m)) hdim)
          (blocksA u))
        (blocksB v) := by
  exact exists_sector_match_of_blockedGaugePhaseEquiv_cyclicDecomp
    A B hA hB blocksA blocksB hA_blocks_lc hB_blocks_lc hA_mpv hB_mpv
    hA_cyclic hB_cyclic hNondegA hNondegB
    (gaugePhaseEquiv_blockTensor A B m hGPE)

/-- If no nonzero compressed sector pair matches, then the original periodic
tensors cannot be globally gauge-phase equivalent. -/
lemma not_gaugePhaseEquiv_of_no_sector_match
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
    (hNondegA : ∀ u, dimA u ≠ 0)
    (hNondegB : ∀ v, dimB v ≠ 0)
    (hNoMatch : ∀ u v (hdim : dimA u = dimB v),
      dimA u ≠ 0 →
      ¬ GaugePhaseEquiv
        (cast (congr_arg
          (MPSTensor (blockPhysDim d m)) hdim)
          (blocksA u))
        (blocksB v)) :
    ¬ GaugePhaseEquiv A B := by
  intro hGPE
  obtain ⟨u, v, hdim, hNondeg, hMatch⟩ :=
    exists_sector_match_of_gaugePhaseEquiv
      A B hA hB blocksA blocksB hA_blocks_lc hB_blocks_lc hA_mpv hB_mpv
      hA_cyclic hB_cyclic hNondegA hNondegB hGPE
  exact hNoMatch u v hdim hNondeg hMatch

/-- Same-period / no-match statement using compressed sector tensors.

If two periodic tensors have the same period `m` but no compressed sector
pair matches (up to dimension cast and gauge-phase equivalence), their
overlap decays to zero.

The no-match condition quantifies over nondegenerate dimension equalities:
for each sector pair `(u, v)` with `dimA u ≠ 0` and any proof that
`dimA u = dimB v`, the compressed blocks are not gauge-phase equivalent.
The nondegeneracy guard `dimA u ≠ 0` is essential: when `dimA u = 0`,
gauge-phase equivalence may hold vacuously for `MPSTensor _ 0`, and without
this guard the no-match condition would be unsatisfiable whenever a
zero-dimensional sector pair exists. With this guard and the separate
assumption that every sector in both decompositions has nonzero virtual
dimension, the no-match and sector-match conditions are complementary for
the dichotomy proof. Positive virtual dimension on the `B` sectors is also
needed by the mixed-sector overlap dichotomy used to extract a sector match
from global gauge-phase equivalence.

This is the "first case" of the same-period argument in Appendix A:
block by `m`, decompose into normal sectors, and observe that all
cross-sector overlaps decay by the normal-tensor overlap dichotomy. -/
theorem periodicOverlap_tendsto_zero_of_no_sector_match
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
    (hNondegA : ∀ u, dimA u ≠ 0)
    (hNondegB : ∀ v, dimB v ≠ 0)
    (hNoMatch : ∀ u v (hdim : dimA u = dimB v),
      dimA u ≠ 0 →
      ¬ GaugePhaseEquiv
        (cast (congr_arg
          (MPSTensor (blockPhysDim d m)) hdim)
          (blocksA u))
        (blocksB v)) :
    Tendsto (fun N => mpvOverlap A B N) atTop (nhds 0) := by
  have : NeZero D := ⟨hA.bondDim_ne_zero⟩
  have h_notGPE : ¬ GaugePhaseEquiv A B :=
    not_gaugePhaseEquiv_of_no_sector_match A B hA hB blocksA blocksB
      hA_blocks_lc hB_blocks_lc hA_mpv hB_mpv hA_cyclic hB_cyclic
      hNondegA hNondegB hNoMatch
  exact mpvOverlap_tendsto_zero_of_irreducible_TP A B
    hA.irreducible hB.irreducible hA.leftCanonical hB.leftCanonical h_notGPE


end MPSTensor

end NoSectorMatch
