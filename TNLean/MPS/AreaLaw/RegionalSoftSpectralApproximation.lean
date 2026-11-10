/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.RegionalSoftTruncationMPO
import QICLean.Analysis.BufferedSpectralNormPerturbation

/-!
# Buffered spectral comparison for actual regional soft approximations

One Hermitian matrix product operator is constructed before every energy cutoff and buffer.
Its global operator-norm approximation gives both directed low-energy comparisons, with
no assumption on the intervening spectrum. This is an auxiliary for ALVV,
arXiv:1602.08828v2, `t:aisefficient` and `t:aisgaplessefficient`, lines 1412–1420 and 1446–1457.

**Local fix (cluster estimate and parameters):** the representation uses the corrected
interaction-label cluster estimate and independent scale at least three times order.
The comparison concerns the actual regional soft sum and its represented approximant;
it does not establish the paper's final GEN bounds or its comparison with the original
Hamiltonian. See `docs/paper-gaps/alvv16_cluster_approximation.tex`.
-/

open Matrix Finset
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.MPS.AreaLaw

/-- Actual regional soft replacements have one Hermitian approximating MPO whose buffered
spectral comparisons hold simultaneously for all cutoffs and positive buffers. The tensors
are chosen before those cutoffs, buffers and vectors. Auxiliary to ALVV,
arXiv:1602.08828v2, `t:aisefficient` and `t:aisgaplessefficient`, lines 1412–1420 and 1446–1457. -/
theorem exists_regional_softTruncations_mpo_buffered_spectral_comparison {N q m s : ℕ}
    (hq : 1 ≤ q) (hm : 0 < m)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (h i) {i.castSucc, i.succ})
    (hh : ∀ i, (h i).IsHermitian) (hnorm : ∀ i, ‖h i‖ ≤ 1)
    (I : Fin s → Finset (Fin N)) (eps : Fin s → ℝ) (t xi z : ℝ)
    (hlo : ∀ j, (eps j : ℂ) • 1 ≤ ∑ i ∈ I j, h i)
    (hscale : 3 * (m : ℝ) ≤ t) (hxi : 0 < xi) :
    let H := ∑ i, h i
    let R := fun j ↦ ∑ i ∈ I j, h i
    let G := H + (z : ℂ) • 1 + ∑ j, ((eps j : ℂ) • 1 +
      cfc (Real.softTruncation t m) (R j - (eps j : ℂ) • 1) - R j)
    let delta := xi / (max 1 s : ℕ)
    let W := t * (2 : ℝ) ^ (m + 1)
    let b := 2 * (Real.exp (1 / 3 : ℝ) - 1)
    let r := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
      Real.log (Real.log (1 + delta / W))) / (-Real.log b)⌉₊
    let D0 := 1 + N * q ^ 2
    let D := D0 + ((D0 + (r ^ 2 * q ^ r) * (m + 1)) * 2) * s
    ∃ T : Fin (N + 1) → MPOTensor q D,
      ∃ hG : G.IsHermitian, ∃ hT : (MPOTensor.traceChainOperator T 1).IsHermitian,
        ‖G - MPOTensor.traceChainOperator T 1‖ ≤ xi ∧
        ∀ c w : ℝ, 0 < w →
          let U := ‖G‖ + xi
          let a := min (c - 1) (-U)
          let n := ⌈(c - a) / (2 * xi)⌉₊
          let loss := (n : ℝ) * (2 * xi) ^ 2 / (w + xi) ^ 2
          Submodule.IsCloseTo loss
            (Submodule.spectralSpanLE hT.eigenvectorBasis hT.eigenvalues (c + w))
            (Submodule.spectralSpanLE hG.eigenvectorBasis hG.eigenvalues c) ∧
          Submodule.IsCloseTo loss
            (Submodule.spectralSpanLE hG.eigenvectorBasis hG.eigenvalues (c + w))
            (Submodule.spectralSpanLE hT.eigenvectorBasis hT.eigenvalues c) := by
  classical
  intro H R G delta W b r D0 D
  obtain ⟨T, hG, hT, herr⟩ :=
    exists_regional_softTruncations_hermitian_mpo_of_accuracy
      hq hm h hs hh hnorm I eps t xi z hlo hscale hxi
  refine ⟨T, hG, hT, herr, ?_⟩
  intro c w hw
  exact hG.isCloseTo_spectralSpanLE_pair_of_norm_sub_le hT c xi w hxi hw herr

end TNLean.MPS.AreaLaw
