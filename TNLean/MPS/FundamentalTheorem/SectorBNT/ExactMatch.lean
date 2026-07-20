/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.ProportionalMatch.Core

/-!
# Exact block matching for BNT canonical forms

Two BNT canonical forms with the same positive-length MPV family have exact
single-sector matches. The exact case is the scalar-one specialization of the
eventually proportional sector matcher.
-/

open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-- Exact single-block matching without a per-sector unit-modulus hypothesis.

This is the equal-MPV specialization of the CPSV16 proportional matching step:
arXiv:1606.00608, §II.C lines 349–352 and Appendix MPV lines 1167–1192. -/
theorem exists_block_match_exact
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (j₀ : Fin P.basisCount)
    (hEqual : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∃ k₀ : Fin Q.basisCount,
      ∃ h : P.basisDim j₀ = Q.basisDim k₀,
        GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (P.basis j₀)) (Q.basis k₀) ∧
        ¬ Tendsto (fun N : ℕ =>
          mpvOverlap (d := d) (P.basis j₀) (Q.basis k₀) N) atTop (𝓝 0) := by
  exact exists_block_match_exact_of_eventuallyProportional
    hP hQ j₀ hEqual.toNonzeroProportionalMPV₂.eventually

end MPSTensor
