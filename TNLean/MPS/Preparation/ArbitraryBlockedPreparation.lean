/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Irreducible.Ergodicity
import TNLean.MPS.CanonicalForm.BNTSectorsAfterBlocking
import TNLean.MPS.Preparation.OverlappingLogLogPreparation

/-!
# Preparation of an arbitrary tensor on a blocked chain

After a fixed positive blocking, every tensor has a double-logarithmic-depth
measurement-round preparation at each length where its periodic vector is nonzero.
The canonical sectors, faithful normalized fixed points, and strict mixed eigenvalue
bounds are all derived from the input tensor.

**Scope restriction (blocked physical sites):** the circuit acts on sites of dimension
\(d^p\), with quantum depth measured on that blocked chain. Simulation on the original
\(d\)-dimensional sites and lengths not divisible by \(p\) are not proved here. These
remaining obligations are described in
`docs/paper-gaps/mswc24_arbitrary_tensor_canonicalization.tex`.

## Main statements

* `exists_isPreparedWithMeasurementRoundsInDepth_blockTensor_le_log_log`: preparation
  from an arbitrary tensor, with a blocking length fixed before length and accuracy.

## References

* Malz--Styliaris--Wei--Cirac, arXiv:2307.01696, paragraph
  "Long-range MPS using measurements" and Supplemental Material, eqs. (S2)--(S4).
* Cirac--Pérez-García--Schuch--Verstraete, arXiv:1606.00608, Section 2.3 and Appendix A.
-/

open Matrix MPSTensor QuantumCircuit
open scoped BigOperators ComplexOrder InnerProductSpace

namespace MPSPreparation

/-- An arbitrary tensor admits a double-logarithmic-depth measurement-round preparation
on a fixed blocked chain, at every blocked length at least two with a nonzero periodic
vector. Both the blocking length and the depth constant are fixed before the accuracy
and chain length. No canonical-form or spectral-gap hypothesis is supplied.

Source: arXiv:2307.01696, paragraph "Long-range MPS using measurements". The original-site
and all-length conclusions of that paragraph require the further steps stated in the
module's scope restriction. -/
theorem exists_isPreparedWithMeasurementRoundsInDepth_blockTensor_le_log_log
    {d D : ℕ} (A : MPSTensor d D) :
    ∃ p : ℕ, 0 < p ∧ ∃ c : ℝ,
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N],
        2 ≤ N → mpvState (blockTensor A p) N ≠ 0 →
        ∃ (ψ : MPVSpace (blockPhysDim d p) N) (T : ℕ),
          ‖ψ‖ = 1 ∧ (T : ℝ) ≤ c * Real.log (Real.log (N / ε) + 1) ∧
          IsPreparedWithMeasurementRoundsInDepth T (fun x => ψ x) ∧
          1 - ‖⟪ψ, normalizedMPVState (blockTensor A p) N⟫_ℂ‖ ≤ ε := by
  classical
  obtain ⟨p, hp, P, hSame, hNormal, hLeft, _hLI, hNequiv⟩ :=
    exists_normal_leftCanonical_sectors_after_blocking A
  letI : ∀ j, NeZero (P.basisDim j) := fun j =>
    ⟨(hNormal j).bondDim_ne_zero⟩
  have hFixed : ∀ j, ∃ σ : Matrix (Fin (P.basisDim j)) (Fin (P.basisDim j)) ℂ,
      σ.PosDef ∧ σ.trace = 1 ∧ Kraus.transferMap (P.basis j) σ = σ := by
    intro j
    obtain ⟨σ, hmem, hpos, hfix, _⟩ :=
      IsChannel.exists_unique_density_fixedPoint_of_irreducible
        (Kraus.transferMap (P.basis j))
        (Kraus.isChannel_mapLM (P.basis j) (hLeft j))
        (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily (P.basis j)
          (hNormal j).no_invariant_proj) (NeZero.pos (P.basisDim j))
    exact ⟨σ, hpos, hmem.2, hfix⟩
  choose σ hσ htr hfix using hFixed
  have hN : ∀ j, Kraus.IsNormal (P.basis j) := fun j => (hNormal j).isNormal
  have hMix : ∀ j j', j ≠ j' → ∀ μ,
      Module.End.HasEigenvalue (Kraus.mixedMapLM (P.basis j) (P.basis j')) μ → ‖μ‖ < 1 := by
    intro j j' hj μ hμ
    exact mixedMap_eigenvalue_norm_lt_one_of_normal_inequivalent
      (P.basis j) (P.basis j') (hN j) (hN j') (hLeft j) (hLeft j')
      (hNequiv j j' hj) hμ
  obtain ⟨c, hc⟩ := exists_isPreparedWithMeasurementRoundsInDepth_le_log_log_of_mpv_eq_sum
    (blockTensor A p) hN hLeft hσ htr hfix hMix P.coeff (by
      intro N _ x
      exact (hSame N (NeZero.pos N) x).trans (P.mpv_toTensor_eq_sum_coeff x))
  exact ⟨p, hp, c, hc⟩

end MPSPreparation
