/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OrderedMixingPairRate
import TNLean.MPS.Preparation.ExplicitPreparationScale

/-!
# Explicit physical scale from ordered mixing

For ordered transfer error `K exp(-r ℓ)` towards a common faithful normalized reference,
the sufficient block coefficient is `1/r`. An offset independent of the chain and ring
length gives the concrete scale `q = ⌈(1/r) log(N/ε) + b⌉` and physical depth
`T ≤ C(d,D) min(N,q)`. The pair rate is derived from the actual tensors.

This supplements arXiv:2307.01696's inhomogeneous scheme with a quantitative sufficient
condition. It does not assert optimality of the circuit-depth constant or derive mixing
from qualitative finite correlation. Nonzero targets remain an explicit hypothesis.
-/

open Matrix MPSTensor QuantumCircuit VaryingBondChain
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace MPSPreparation

/-- **Selected block coefficient `1/r` from actual ordered mixing.** The physical circuit
constant depends only on `d,D`; the offset depends only on the fixed faithful reference and
mixing constants. The actual ring is prepared exactly when the selected scale exceeds it.

The sufficient scale is a quantitative refinement associated with arXiv:2307.01696, not a
claim that the optimal physical circuit depth has the same coefficient. -/
theorem exists_isPreparedInDepth_inhomogeneous_le_min_of_ordered_mixing
    (d D : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, ∀ (σ : Matrix (Fin D) (Fin D) ℂ), σ.PosDef → σ.trace = 1 →
      ∀ (K r : ℝ), 0 < K → 0 < r → ∃ b : ℝ, 1 ≤ b ∧
        ∀ (N : ℕ) [NeZero N] (A : MPSChainTensor d D N), chainState A ≠ 0 →
          (∀ {M : ℕ} (ℓ : Fin M → ℕ) (hN : ∑ j, ℓ j = N) (j : Fin M), 0 < ℓ j →
            ‖transferMatrix ((List.ofFn fun i : Fin (ℓ j) =>
                Kraus.transferMap (A (blockSite hN j i))).prod) -
              transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ ≤
                K * Real.exp (-(r * ℓ j))) →
          ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
            let q := ⌈(1 / r) * Real.log (N / ε) + b⌉₊
            3 * D + 1 ≤ q ∧ ∃ (ψ : MPVSpace d N) (T : ℕ),
              ‖ψ‖ = 1 ∧ T ≤ C * min N q ∧ IsPreparedInDepth T (fun s => ψ s) ∧
                1 - ‖⟪ψ, (‖chainState A‖ : ℂ)⁻¹ • chainState A⟫_ℂ‖ ≤ ε := by
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_inhomogeneous_le_min_of_rate d D hd
  refine ⟨C, fun σ hσ htr K r hK hr => ?_⟩
  obtain ⟨Cp, hCp, hp⟩ := exists_isPairApproximable_of_ordered_mixing hσ htr
  let b : ℝ := max (Real.log (Cp * K)) 0 / r + 3 * D + 1
  have hb : 1 ≤ b := by
    have : 0 ≤ max (Real.log (Cp * K)) 0 / r + 3 * D := by positivity
    dsimp [b]
    linarith
  refine ⟨b, hb, fun N _ A hA hmix ε hε hε1 => ?_⟩
  have hstate : state (ofChain A) = chainState A := by
    rw [state_eq_chainState, zeroPad_ofChain]
  have h := hC N (ofChain A) (by rwa [hstate]) (Cp * K) r 1 0 (1 / r) b ε
    (mul_pos hCp hK) hr (by simp) (by simp [b]) hε hε1
  dsimp only at h ⊢
  rw [hstate] at h
  apply h
  intro hq _ hqN
  exact hp d N A K r hK hr hA hmix _ hq hqN

end MPSPreparation
