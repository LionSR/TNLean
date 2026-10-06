/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.InhomogeneousChoiResidual
import TNLean.MPS.Preparation.SecondOrderOverlap

/-!
# Uniform positive-part rates from Choi domination

The normalized Choi matrix of the transfer map is the transpose of the blocked physical
Gram matrix divided by the bond dimension. A uniform Choi lower bound on the actual
inhomogeneous site maps, together with a common faithful fixed state, yields a Gram error
at most `2D (1 - ε)^(N/s)` on a chain partitioned into actual contiguous blocks of at most
`s` sites. The square-root Lipschitz estimate at the faithful limiting Gram matrix gives
the same exponential rate for the positive polar factor. The quotient `N/s` is rounded down.

The sites may be fixed-length contiguous blocks, but the domination hypothesis must then
hold for the transfer maps of those actual blocks. Individual microscopic spectral gaps
are not a replacement for this hypothesis.

## Main results

* `gram_eq_smul_choi_transpose`: the exact bond-dimension normalization and index order.
* `exists_norm_polarPos_chainBlockTensor_sub_le_of_choi_domination`: uniform Gram and polar
  bounds from actual contiguous-block domination and a common faithful fixed state.

## References

* arXiv:2307.01696, eq. (8) and paragraph "Inhomogeneous short-range correlated MPS".
* Wolf, *Quantum Channels & Operations*, Theorem 8.17 (quantum Doeblin).
* arXiv:2103.13367, Supplemental Material, equations (19), (21), and (26).
-/

open Matrix MPSTensor
open scoped BigOperators ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

namespace MPSPreparation

/-- **Uniform Gram and positive-part rates for an inhomogeneous chain.** Fix a faithful
state `σ` of trace one. There is `K`, depending only on `D` and `σ`, such that for any chain
partitioned into contiguous blocks of lengths at most `s > 0`, if those actual block maps
preserve trace, fix `σ`, and have normalized Choi matrices at least `(ε/D) (σ ⊗ I)`, the Gram
error is at most `2D (1 - ε)^(N/s)` and the positive-part error is at most
`K (1 - ε)^(N/s)`, for `0 ≤ ε ≤ 1`. Here `N/s` is integer division.

The hypotheses concern actual ordered block maps; they are quantitative assumptions,
not consequences of separate spectral gaps of the individual microscopic tensors. -/
theorem exists_norm_polarPos_chainBlockTensor_sub_le_of_choi_domination
    {D : ℕ} {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {d N M : ℕ} (A : MPSChainTensor d D N)
      (ℓ : Fin M → ℕ) (hN : ∑ k, ℓ k = N) (s : ℕ), 0 < s →
      (∀ k, ℓ k ≤ s) → ∀ {ε : ℝ}, 0 ≤ ε → ε ≤ 1 →
      (∀ k, IsTracePreservingMap (Kraus.transferMap (chainBlockTensor A hN k))) →
      (∀ k, Kraus.transferMap (chainBlockTensor A hN k) σ = σ) →
      (∀ k, ChoiRectangular.choiMatrix (Kraus.transferMap (chainBlockTensor A hN k)) ≥
        ((ε : ℂ) / D) • (σ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))) →
      ‖(physicalMatrix (MPSChainTensor.blockTensor A))ᴴ *
          physicalMatrix (MPSChainTensor.blockTensor A) - σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)‖ ≤
        2 * D * (1 - ε) ^ (N / s) ∧
      ‖Matrix.polarPos (physicalMatrix (MPSChainTensor.blockTensor A)) -
          (CFC.sqrt σ)ᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)‖ ≤ K * (1 - ε) ^ (N / s) := by
  classical
  have := Matrix.neZero_of_trace_eq_one htr
  have hpd : (σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)).PosDef :=
    (Matrix.PosDef.transpose_iff.2 hσ).kronecker Matrix.PosDef.one
  obtain ⟨L, hL, hlip⟩ := hpd.isStrictlyPositive.exists_norm_sqrt_sub_sqrt_le
  refine ⟨L * (2 * D), by positivity,
    fun {d N M} A ℓ hN s hs hℓ ε hε hε1 hA hfix hchoi => ?_⟩
  let E : Fin M → Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    fun j => Kraus.transferMap (chainBlockTensor A hN j)
  have hwhole : Kraus.transferMap (MPSChainTensor.blockTensor A) = (List.ofFn E).prod := by
    rw [MPSChainTensor.transferMap_blockTensor]
    change (List.ofFn fun i => Kraus.transferMap (A i)).prod =
      (List.ofFn fun j => Kraus.transferMap (chainBlockTensor A hN j)).prod
    simp only [chainBlockTensor, MPSChainTensor.transferMap_blockTensor]
    exact prod_ofFn_blockSite ℓ hN (fun i => Kraus.transferMap (A i))
  have hfixed : Kraus.transferMap (MPSChainTensor.blockTensor A) σ = σ := by
    rw [hwhole]
    have hp : ∀ Ts : List (Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)),
        (∀ T ∈ Ts, T σ = σ) → Ts.prod σ = σ := by
      intro Ts
      induction Ts with
      | nil => intro h; rfl
      | cons T Ts ih =>
        intro h
        change T (Ts.prod σ) = σ
        rw [ih fun S hS => h S (by simp [hS])]
        exact h T (by simp)
    exact hp _ fun T hT => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hT
      exact hfix j
  let r : ℝ := 1 - ε
  have hbound := norm_gram_blockTensor_sub_transport_le_of_choi_domination A ℓ hN
    (fun _ => ε) (fun _ => σ) (fun _ => htr) hA hchoi σ hσ.posSemidef htr
  rw [hfixed, Fin.prod_const] at hbound
  have hNs : N ≤ M * s := by
    rw [← hN]
    calc ∑ k, ℓ k ≤ ∑ _ : Fin M, s := Finset.sum_le_sum (fun k _ => hℓ k)
      _ = M * s := by simp
  have hcount : N / s ≤ M := by
    calc N / s ≤ (M * s) / s := Nat.div_le_div_right hNs
      _ = M := Nat.mul_div_left M hs
  have hpow : r ^ M ≤ r ^ (N / s) :=
    pow_le_pow_of_le_one (sub_nonneg.mpr hε1) (sub_le_self 1 hε) hcount
  have hfinal := hbound.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  refine ⟨hfinal, ?_⟩
  have hsqrt := hlip _
    (Matrix.posSemidef_conjTranspose_mul_self
      (physicalMatrix (MPSChainTensor.blockTensor A))).nonneg
  rw [sqrt_transpose_kronecker_one hσ.posSemidef] at hsqrt
  exact hsqrt.trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hfinal hL)

end MPSPreparation
