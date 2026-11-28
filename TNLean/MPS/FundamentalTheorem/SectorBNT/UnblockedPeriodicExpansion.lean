/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Polynomial.TailPowerSumUniqueness
import TNLean.MPS.CanonicalForm.BNT.PhaseCover
import TNLean.MPS.Tensor.DirectSum.IrreducibleDecomposition
import TNLean.MPS.FundamentalTheorem.SectorBNT.PowerSumCoefficients
import TNLean.MPS.CanonicalForm.Periodic.Overlap.Dichotomy
import TNLean.MPS.CanonicalForm.Periodic.SectorNormalization

/-!
# Periodic expansion and independence of periodic blocks

The trace-reduction step and the periodic-block facts used by the power-sum coefficient theorem
of `TNLean.MPS.FundamentalTheorem.SectorBNT.UnblockedPowerSumCoefficients`: periodic blocks with
proportional periodic vectors have equal bond dimension, every tensor is at every positive length
a power-sum combination of periodic representatives, and periodic blocks that are not repeated
have eventually independent periodic vectors.

## Main results

* `MPSTensor.dim_eq_of_mpvBlockPhaseEquiv_of_isPeriodic`
* `MPSTensor.exists_irreducible_expansion`
* `MPSTensor.exists_eventually_linearIndependent_of_periodic_blocks_not_repeated`

The statements hold over any finite physical alphabet; the proofs relabel it by
`Fin (Fintype.card β)`.
-/

open MPTensor

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {β : Type*} [Fintype β]

/-! ### Small bridges between `GaugePhaseEquiv` and `RepeatedBlocks` -/

/-- Transitivity of gauge-phase equivalence. -/
theorem gaugePhaseEquiv_trans {D : ℕ} {A B C : MPTensor β (Fin D)}
    (hAB : GaugePhaseEquiv A B) (hBC : GaugePhaseEquiv B C) : GaugePhaseEquiv A C := by
  obtain ⟨X, ζ, hζ, hX⟩ := hAB
  obtain ⟨Y, η, hη, hY⟩ := hBC
  refine ⟨Y * X, η * ζ, mul_ne_zero hη hζ, fun i => ?_⟩
  rw [hY i, hX i]
  simp [mul_smul, Matrix.mul_assoc, mul_inv_rev]

/-- A one-sided nonzero rescaling can be absorbed into the gauge-phase scalar. -/
theorem gaugePhaseEquiv_of_gaugePhaseEquiv_smul_right {D : ℕ} {A B : MPTensor β (Fin D)} {c : ℂ}
    (hc : c ≠ 0) (h : GaugePhaseEquiv A (fun i => c • B i)) : GaugePhaseEquiv A B := by
  obtain ⟨X, ζ, hζ, hX⟩ := h
  refine ⟨X, ζ / c, div_ne_zero hζ hc, fun i => ?_⟩
  have hXi : c • B i = ζ • (((X : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * A i *
      (((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))) := hX i
  have hBi : B i = c⁻¹ • (c • B i) := (inv_smul_smul₀ hc (B i)).symm
  rw [hBi, hXi, smul_smul, div_eq_inv_mul]

/-- A `RepeatedBlocks` relation gives a (reversed) gauge-phase equivalence. -/
theorem gaugePhaseEquiv_of_repeatedBlocks {D : ℕ} {A B : MPTensor β (Fin D)}
    (h : RepeatedBlocks A B) : GaugePhaseEquiv B A := by
  obtain ⟨ξ, Y, hξ, hrel⟩ := h
  exact ⟨Y, ξ, Complex.ne_zero_of_norm_eq_one hξ, hrel⟩

/-- Non-gauge-phase-equivalence (in either order) rules out `RepeatedBlocks`. -/
theorem not_repeatedBlocks_of_not_gaugePhaseEquiv {D : ℕ} {A B : MPTensor β (Fin D)}
    (h : ¬ GaugePhaseEquiv A B) : ¬ RepeatedBlocks A B := by
  intro hRep
  exact h (gaugePhaseEquiv_symm_same_dim (gaugePhaseEquiv_of_repeatedBlocks hRep))

/-- A `RepeatedBlocks` relation across a dimension cast gives a gauge-phase
equivalence with the cast transported to the other side. -/
theorem gaugePhaseEquiv_cast_symm_of_repeatedBlocks {D₁ D₂ : ℕ}
    {X : MPTensor β (Fin D₁)} {Y : MPTensor β (Fin D₂)} (h : D₁ = D₂)
    (hRep : RepeatedBlocks (cast (congr_arg (fun n ↦ MPTensor β (Fin n)) h) X) Y) :
    GaugePhaseEquiv (cast (congr_arg (fun n ↦ MPTensor β (Fin n)) h.symm) Y) X := by
  subst h
  simp only [cast_eq] at hRep ⊢
  exact gaugePhaseEquiv_of_repeatedBlocks hRep

/-! ### Dimension preserved by proportional periodic vectors -/

/-- Two periodic blocks whose periodic vectors are proportional by a power of a
nonzero scalar at every positive length have the same bond dimension.

By the periodic overlap dichotomy (arXiv:1708.00029, Proposition
`equal-or-orthogonal-generalized`) the overlap of blocks of different bond
dimension tends to zero, whereas proportionality forces
`⟨A,B⟩ * conj ⟨A,B⟩ = ⟨A,A⟩ * ⟨B,B⟩`, whose limit along common multiples of the
periods is the product of the periods. -/
theorem dim_eq_of_mpvBlockPhaseEquiv_of_isPeriodic {D₁ D₂ m_a m_b : ℕ}
    {A : MPTensor β (Fin D₁)} {B : MPTensor β (Fin D₂)}
    (hA : IsPeriodic m_a A) (hB : IsPeriodic m_b B) (h : MPVBlockPhaseEquiv A B) :
    D₁ = D₂ := by
  classical
  by_contra hD
  obtain ⟨ζ, hζ, hmpv⟩ := h
  have hdecay : Tendsto (fun N => mpvOverlap A B N) atTop (nhds 0) := by
    rcases periodicOverlapDichotomy A B hA hB with h1 | ⟨hdim, -⟩
    · exact h1
    · exact absurd hdim hD
  have hma := hA.period_pos
  have hmb := hB.period_pos
  have hg : Tendsto (fun k : ℕ => m_b * (k + 1)) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_) tendsto_id
    calc k ≤ k + 1 := Nat.le_succ k
      _ ≤ m_b * (k + 1) := Nat.le_mul_of_pos_left _ hmb
  have hg' : Tendsto (fun k : ℕ => m_a * (k + 1)) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_) tendsto_id
    calc k ≤ k + 1 := Nat.le_succ k
      _ ≤ m_a * (k + 1) := Nat.le_mul_of_pos_left _ hma
  have hf : Tendsto (fun k : ℕ => m_a * (m_b * (k + 1))) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_) hg
    exact Nat.le_mul_of_pos_left _ hma
  have hAA : Tendsto (fun k : ℕ => mpvOverlap A A (m_a * (m_b * (k + 1)))) atTop
      (nhds (m_a : ℂ)) := (periodicSelfOverlap_tendsto A hA).comp hg
  have hBB : Tendsto (fun k : ℕ => mpvOverlap B B (m_a * (m_b * (k + 1)))) atTop
      (nhds (m_b : ℂ)) := by
    refine ((periodicSelfOverlap_tendsto B hB).comp hg').congr fun k => ?_
    simp only [Function.comp]
    rw [show m_b * (m_a * (k + 1)) = m_a * (m_b * (k + 1)) by ring]
  have hAB : Tendsto (fun k : ℕ => mpvOverlap A B (m_a * (m_b * (k + 1)))) atTop (nhds 0) :=
    hdecay.comp hf
  have hkey : ∀ N : ℕ, 0 < N →
      mpvOverlap B B N * mpvOverlap A A N = mpvOverlap A B N * star (mpvOverlap A B N) := by
    intro N hN
    have hAB_eq : mpvOverlap A B N = star (ζ ^ N) * mpvOverlap A A N := by
      unfold mpvOverlap
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [hmpv N hN σ, star_mul']
      ring
    have hBB_eq : mpvOverlap B B N = ζ ^ N * star (ζ ^ N) * mpvOverlap A A N := by
      unfold mpvOverlap
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [hmpv N hN σ, star_mul']
      ring
    have hself : star (mpvOverlap A A N) = mpvOverlap A A N := by
      unfold mpvOverlap
      rw [star_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [star_mul', star_star]
      ring
    rw [hBB_eq, hAB_eq, star_mul', star_star, hself]
    ring
  have h1 : Tendsto (fun k : ℕ => mpvOverlap A B (m_a * (m_b * (k + 1))) *
      star (mpvOverlap A B (m_a * (m_b * (k + 1))))) atTop (nhds ((m_b : ℂ) * (m_a : ℂ))) :=
    (hBB.mul hAA).congr fun k =>
      hkey _ (Nat.mul_pos hma (Nat.mul_pos hmb (Nat.succ_pos k)))
  have h2 := hAB.mul hAB.star
  have := tendsto_nhds_unique h1 h2
  simp at this
  omega

/-! ### Trace reduction into periodic representatives -/

/-- **Trace reduction into periodic representative classes.**

Every MPS tensor `B` decomposes, at every positive length, into finitely many
gauge-and-scalar equivalence classes of periodic representatives: there are a
finite index set `Fin g`, periodic representatives `A j` with periods
`per j`, and finite nonzero weight multiplicities `α j` (indexed by `Fin
(copies j)`) such that `v_L(B) = ∑_j (∑_q (α j q)^L) v_L(A j)` for every
`L ≥ 1`.

This packages the trace-reduction and explicit-multiplicity construction of
`t1_unblocked.tex`, §"Trace reduction and explicit multiplicities": the
irreducible block decomposition of `B`, the periodic normalization of each
nonzero irreducible factor
(`exists_leftCanonical_periodic_scale_of_irreducible`), and the finite
gauge-phase class regrouping (`MPSTensor.mpvPhaseClassData`). -/
theorem exists_irreducible_expansion {DB : ℕ} (B : MPTensor β (Fin DB)) :
    ∃ (g : ℕ) (dimRep : Fin g → ℕ) (A : (j : Fin g) → MPTensor β (Fin (dimRep j)))
      (per : Fin g → ℕ) (copies : Fin g → ℕ) (α : (j : Fin g) → Fin (copies j) → ℂ),
      (∀ j, 0 < dimRep j) ∧
      (∀ j, IsPeriodic (per j) (A j)) ∧
      (∀ j, 0 < copies j) ∧
      (∀ j q, α j q ≠ 0) ∧
      (∀ j k : Fin g, j ≠ k → ∀ h : dimRep j = dimRep k,
        ¬ GaugePhaseEquiv (cast (congr_arg (fun n ↦ MPTensor β (Fin n)) h) (A j)) (A k)) ∧
      (∀ L : ℕ, 0 < L → ∀ σ : Fin L → β,
        mpv B σ = ∑ j : Fin g, (∑ q : Fin (copies j), (α j q) ^ L) * mpv (A j) σ) ∧
      ∑ j : Fin g, copies j * dimRep j ≤ DB := by
  classical
  obtain ⟨r, dim, blocks, hIrr, hNZ, hDimPos, hSameMPV, hDimSum⟩ :=
    exists_irreducible_blockDecomp_nonzeroBlocks B
  have hNe : ∀ k, NeZero (dim k) := fun k => ⟨(hDimPos k).ne'⟩
  choose Ã ζ0 per hζ0 hGaugeK hmpvK hPerK using
    fun k => exists_leftCanonical_periodic_scale_of_irreducible (hIrr k) (hNZ k)
  set classes := mpvPhaseClassData Ã with hclasses_def
  choose ζEnum hζEnum hmpvEnum using fun j q => classes.enum_phase j q
  set A : (j : Fin classes.g) → MPTensor β (Fin (dim (classes.repr j))) :=
    fun j => Ã (classes.repr j) with hA_def
  set α : (j : Fin classes.g) → Fin (classes.copies j) → ℂ :=
    fun j q => (ζEnum j q) * (ζ0 (classes.enum j q))⁻¹ with hα_def
  refine ⟨classes.g, fun j => dim (classes.repr j), A, fun j => per (classes.repr j),
    classes.copies, α, fun j => hDimPos (classes.repr j), fun j => hPerK (classes.repr j),
    classes.copies_pos, ?_, classes.blocks_not_equiv, ?_, ?_⟩
  · intro j q
    exact mul_ne_zero (hζEnum j q) (inv_ne_zero (hζ0 (classes.enum j q)))
  swap
  · have hdimEq : ∀ j q, dim (classes.enum j q) = dim (classes.repr j) := fun j q =>
      (dim_eq_of_mpvBlockPhaseEquiv_of_isPeriodic (hPerK (classes.repr j))
        (hPerK (classes.enum j q)) (classes.enum_phase j q)).symm
    have hreg := classes.regroup (fun k => ((dim k : ℕ) : ℂ))
    have hcast : ∑ j : Fin classes.g, classes.copies j * dim (classes.repr j) =
        ∑ k : Fin r, dim k := by
      have hc : ((∑ j : Fin classes.g, classes.copies j * dim (classes.repr j) : ℕ) : ℂ) =
          ((∑ k : Fin r, dim k : ℕ) : ℂ) := by
        push_cast
        rw [← hreg]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [hdimEq j]
      exact_mod_cast hc
    exact hcast ▸ hDimSum
  · intro L hL σ
    have hblocksEq : mpv B σ = ∑ k : Fin r, mpv (blocks k) σ := by
      have hSame := hSameMPV L hL σ
      rw [hSame, mpv_toTensorFromBlocks_eq_sum]
      simp
    have hregroup :
        ∑ k : Fin r, mpv (blocks k) σ =
          ∑ j : Fin classes.g, ∑ q : Fin (classes.copies j), mpv (blocks (classes.enum j q)) σ :=
      (classes.regroup (fun k => mpv (blocks k) σ)).symm
    rw [hblocksEq, hregroup]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hmpv_enum := hmpvEnum j q L hL σ
    have hK := hmpvK (classes.enum j q) L σ
    have hζL : (ζ0 (classes.enum j q)) ^ L ≠ 0 := pow_ne_zero L (hζ0 (classes.enum j q))
    have heq : (ζ0 (classes.enum j q)) ^ L * mpv (blocks (classes.enum j q)) σ
        = (ζEnum j q) ^ L * mpv (A j) σ := by
      rw [← hK, hmpv_enum]
    have hmulboth := congrArg (fun x => (ζ0 (classes.enum j q) ^ L)⁻¹ * x) heq
    simp only [← mul_assoc, inv_mul_cancel₀ hζL, one_mul] at hmulboth
    rw [hα_def, mul_pow, inv_pow, hmulboth]
    ring

/-! ### Matching before blocking -/

/-- Periodic blocks that are pairwise not repeated, with periods dividing `p`, have eventually
linearly independent periodic vectors at the lengths `p * N`. This is the finite-index form of
`periodicBasis_eventuallyLinearlyIndependent`. -/
theorem exists_eventually_linearIndependent_of_periodic_blocks_not_repeated
    {ι : Type*} [Finite ι] {dim : ι → ℕ}
    (A : (k : ι) → MPTensor β (Fin (dim k))) (period : ι → ℕ)
    (hPer : ∀ k, IsPeriodic (period k) (A k))
    (p : ℕ) [NeZero p] (hDiv : ∀ k, period k ∣ p)
    (hNonrep : ∀ j k : ι, j ≠ k → ∀ h : dim j = dim k,
      ¬ RepeatedBlocks (cast (congr_arg (fun n ↦ MPTensor β (Fin n)) h) (A j)) (A k)) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      LinearIndependent ℂ (fun k : ι ↦
        (EuclideanSpace.equiv (ι := Fin (p * N) → β) (𝕜 := ℂ)).symm fun σ ↦ mpv (A k) σ) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  set e := Fintype.equivFin ι with he
  obtain ⟨N₀, hLI⟩ :=
    periodicBasis_eventuallyLinearlyIndependent
      (dim := fun k => dim (e.symm k)) (fun k => A (e.symm k))
      (fun k => period (e.symm k)) (fun k => hPer (e.symm k))
      p (fun k => hDiv (e.symm k))
      (fun j k hjk h => hNonrep (e.symm j) (e.symm k)
        (fun hEq => hjk (by simpa using congrArg e hEq)) h)
  refine ⟨N₀, fun N hN => ?_⟩
  show LinearIndependent ℂ (fun k : ι => mpvState (α := β) (A k) (p * N))
  have hfun :
      ((fun k : Fin (Fintype.card ι) => mpvState (α := β) (A (e.symm k)) (p * N)) ∘ e) =
        fun k : ι => mpvState (α := β) (A k) (p * N) := by
    funext k
    exact congrArg (fun y : ι => mpvState (α := β) (A y) (p * N)) (e.symm_apply_apply k)
  rw [← hfun]
  exact (hLI N hN).comp e e.injective

end MPSTensor
