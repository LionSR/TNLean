/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.HalfChainSpectrum
import TNLean.MPS.CanonicalForm.Definitions
import QICLean.Channel.Peripheral.IrreducibleChannel
import QICLean.Channel.Schwarz.Closure
import QICLean.Kraus.InvariantProjection

/-!
# Half-chain spectrum in the unital canonical convention

For a normal tensor with \(\sum_i A_i A_i^\dagger=I\), a diagonal fixed
point \(\Lambda\) of the dual transfer map gives the limiting Gram matrix
\(G_{(\alpha,\beta),(\alpha',\beta')}=
\lambda_\beta\delta_{\alpha\alpha'}\delta_{\beta\beta'}\).
The physical normalized half-chain eigenvalues therefore converge to the
ordered spectrum of \(\Lambda\otimes\Lambda\).

The dual channel is used to establish convergence of the original tensor's
Gram matrices through an exact trace-pairing identity. The physical state and
its half-chain reduced matrix remain those of the original tensor.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 6 and its preceding
Schmidt-decomposition calculation (lines 970--993).

**Local fix (boundary index and decay):** the unital overlap carries the
weight on the second boundary index, while the geometric bound allows a radius
strictly above the subleading spectral radius. See
docs/paper-gaps/pgvwc07_half_chain_spectrum_conventions.tex.
-/

open Matrix Filter
open scoped Matrix.Norms.L2Operator ComplexOrder Topology Kraus

namespace MPSTensor

variable {d D : ℕ}

/-- Taking adjoints of the Kraus matrices swaps and transposes the half-chain
Gram matrix. This follows from the trace pairing of the two transfer maps. -/
theorem halfChainGram_conjTranspose (A : MPSTensor d D) (L : ℕ)
    (p q : Fin D × Fin D) :
    halfChainGram (fun i ↦ (A i)ᴴ) L q.swap p.swap = halfChainGram A L p q := by
  rw [halfChainGram_apply_eq_transferMap_pow, halfChainGram_apply_eq_transferMap_pow]
  change ((Kraus.mapLM fun i ↦ (A i)ᴴ) ^ L) (Matrix.single p.1 q.1 1) p.2 q.2 = _
  rw [← Kraus.traceAdjointMap_mapLM_eq_mapLM_conjTranspose, ← Matrix.traceAdjointMap_pow,
    Matrix.traceAdjointMap_apply_apply, Matrix.trace_single_mul, one_smul]

/-- In the source's unital canonical convention, the Gram matrices of the
actual half-chain family converge to the diagonal weights on the second
boundary index. Normality supplies the complementary spectral gap.
Source: PGVWC07, arXiv:quant-ph/0608197, lines 977--981. -/
theorem tendsto_halfChainGram_unital
    (A : MPSTensor d D) (hA : IsNormalTensor A)
    (lam : Fin D → ℝ) (hlam : ∀ a, 0 ≤ lam a) (htr : ∑ a, lam a = 1)
    (hU : ∑ i, A i * (A i)ᴴ = 1)
    (hfix : ∑ i, (A i)ᴴ * (Matrix.diagonal fun a ↦ (lam a : ℂ)) * A i =
      Matrix.diagonal fun a ↦ (lam a : ℂ)) :
    Tendsto (halfChainGram A) atTop
      (𝓝 (Matrix.diagonal fun p : Fin D × Fin D ↦ (lam p.2 : ℂ))) := by
  let : NeZero D := ⟨hA.bondDim_ne_zero⟩
  let K : MPSTensor d D := fun i ↦ (A i)ᴴ
  let Λ : Matrix (Fin D) (Fin D) ℂ := Matrix.diagonal fun a ↦ (lam a : ℂ)
  have hTP : Kraus.IsTP K := by
    simpa only [Kraus.IsTP, K, Matrix.conjTranspose_conjTranspose] using hU
  have hΛtr : Matrix.trace Λ = 1 := by
    simp only [Λ, Matrix.trace_diagonal, ← Complex.ofReal_sum, htr, Complex.ofReal_one]
  have hΛne : Λ ≠ 0 := by
    intro h
    have := hΛtr
    simp [h] at this
  have hΛpos : Λ.PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr fun a ↦ Complex.zero_le_real.mpr (hlam a)
  have hΛfix : Kraus.mapLM K Λ = Λ := by
    simpa only [Kraus.mapLM_apply, Kraus.map_apply, K, Λ,
      Matrix.conjTranspose_conjTranspose] using hfix
  have hIrr : IsIrreducibleMap (Kraus.mapLM K) :=
    Kraus.isIrreducibleMap_mapLM_conjTranspose A
      (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hA.no_invariant_proj)
  have hPrim : _root_.IsPrimitive (Kraus.mapLM K) := by
    apply isPrimitive_of_unique_norm_one (Kraus.mapLM K) Λ hΛfix hΛne
    intro μ hμ hnorm
    apply hA.primitive_transfer.unique_peripheral μ ?_ hnorm
    apply (Matrix.traceAdjointMap_hasEigenvalue_iff (Kraus.mapLM A) μ).mp
    simpa only [Kraus.traceAdjointMap_mapLM_eq_mapLM_conjTranspose] using hμ
  obtain ⟨hΛtr_ne, hgap⟩ :=
    spectralRadius_compl_lt_one_of_primitive_fixedPoint_of_irreducible_channel
      (Kraus.mapLM K) (Kraus.isChannel_mapLM K hTP) hIrr hPrim Λ hΛpos hΛne hΛfix
  have hG := tendsto_halfChainGram K lam htr
    (Kraus.isTracePreservingMap_mapLM_of_isTP K hTP) hΛfix hgap
  apply tendsto_pi_nhds.mpr
  intro p
  apply tendsto_pi_nhds.mpr
  intro q
  have hentry := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hG q.swap) p.swap
  simp only [K, halfChainGram_conjTranspose] at hentry
  have hlim : halfChainGramLimit lam q.swap p.swap =
      (Matrix.diagonal fun p : Fin D × Fin D ↦ (lam p.2 : ℂ)) p q := by
    by_cases hpq : p = q
    · subst hpq
      simp [halfChainGramLimit]
    · have hswap : q.swap ≠ p.swap := fun h ↦ hpq (Prod.swap_injective h).symm
      simp [halfChainGramLimit, hpq, hswap]
  rw [hlim] at hentry
  exact hentry

/-- In the unital canonical convention, the positive boundary representatives
of the original physical tensor converge to \(\Lambda\otimes\Lambda\).
Source: PGVWC07, Theorem 6. -/
theorem tendsto_halfChainSpectralMatrix_unital
    (A : MPSTensor d D) (hA : IsNormalTensor A)
    (lam : Fin D → ℝ) (hlam : ∀ a, 0 ≤ lam a) (htr : ∑ a, lam a = 1)
    (hU : ∑ i, A i * (A i)ᴴ = 1)
    (hfix : ∑ i, (A i)ᴴ * (Matrix.diagonal fun a ↦ (lam a : ℂ)) * A i =
      Matrix.diagonal fun a ↦ (lam a : ℂ)) :
    Tendsto (halfChainSpectralMatrix A) atTop (𝓝 (halfChainSpectrumLimit lam)) := by
  have h := tendsto_halfChainSpectralMatrix_of_diagonal A
    (fun p ↦ lam p.2) (fun p ↦ hlam p.2)
    (tendsto_halfChainGram_unital A hA lam hlam htr hU hfix)
  simpa only [Prod.snd_swap, mul_comm, halfChainSpectrumLimit] using h

/-- The normal-tensor form of the half-chain interpretation of the dual fixed
point, in unital convention and for the original physical ring vector.
Every decreasing ordered eigenvalue of the actual normalized reduced density
converges to that of \(\Lambda\otimes\Lambda\), with multiplicities and zero
padding after each finite dimension. Normality derives the complementary gap;
the ring norm is not assumed to be one at finite length. The source canonical
conditions and Condition C2 are treated separately in HalfChainSourceSpectrum.
Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 6, lines 987–993. -/
theorem tendsto_halfChainEigenvalues_unital
    (A : MPSTensor d D) (hA : IsNormalTensor A)
    (lam : Fin D → ℝ) (hlam : ∀ a, 0 ≤ lam a) (htr : ∑ a, lam a = 1)
    (hU : ∑ i, A i * (A i)ᴴ = 1)
    (hfix : ∑ i, (A i)ᴴ * (Matrix.diagonal fun a ↦ (lam a : ℂ)) * A i =
      Matrix.diagonal fun a ↦ (lam a : ℂ))
    (k : ℕ) :
    Tendsto (fun L ↦ halfChainEigenvalues A L k) atTop
      (𝓝 ((posSemidef_halfChainSpectrumLimit lam hlam).isHermitian.paddedEigenvalues k)) :=
  tendsto_halfChainEigenvalues_of_spectralMatrix A lam hlam htr
    (tendsto_halfChainSpectralMatrix_unital A hA lam hlam htr hU hfix) k

/-- Source-canonical rings are eventually nonzero, and their squared norms
tend to one. Thus the normalized physical eigenvalues above eventually belong
to genuine trace-one density matrices. -/
theorem halfChainNormSq_unital
    (A : MPSTensor d D) (hA : IsNormalTensor A)
    (lam : Fin D → ℝ) (hlam : ∀ a, 0 ≤ lam a) (htr : ∑ a, lam a = 1)
    (hU : ∑ i, A i * (A i)ᴴ = 1)
    (hfix : ∑ i, (A i)ᴴ * (Matrix.diagonal fun a ↦ (lam a : ℂ)) * A i =
      Matrix.diagonal fun a ↦ (lam a : ℂ)) :
    Tendsto (halfChainNormSq A) atTop (𝓝 1) ∧
      ∀ᶠ L in atTop, 0 < halfChainNormSq A L := by
  have hZ := tendsto_halfChainNormSq A lam htr
    (tendsto_halfChainSpectralMatrix_unital A hA lam hlam htr hU hfix)
  exact ⟨hZ, eventually_halfChainNormSq_pos A hZ⟩

end MPSTensor
