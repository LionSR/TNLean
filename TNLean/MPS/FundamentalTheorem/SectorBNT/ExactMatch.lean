/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.ProportionalMatch.Core

/-!
# Exact block matching for BNT canonical forms

Two BNT canonical forms with the same positive-length MPV family have exact
single-sector matches: for each sector of one decomposition, some sector of the
other has the same bond dimension, is gauge-phase equivalent after the dimension
cast, and has non-decaying overlap. This is the equal-MPV specialization of the
proportional sector matcher.
-/

open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-- Exact single-block matching without a per-sector unit-modulus hypothesis.

Equality at every positive length gives eventual nonzero proportionality with
scalar one, so this follows from the proportional single-block matcher. -/
theorem exists_block_match_exact
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (j₀ : Fin P.basisCount)
    (hEqual : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∃ k₀ : Fin Q.basisCount,
      ∃ h : P.basisDim j₀ = Q.basisDim k₀,
        GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (P.basis j₀)) (Q.basis k₀) ∧
        ¬ Tendsto (fun N : ℕ => mpvOverlap (d := d) (P.basis j₀) (Q.basis k₀) N)
          atTop (𝓝 0) := by
  exact exists_block_match_exact_of_eventuallyProportional hP hQ j₀
    hEqual.toNonzeroProportionalMPV₂.eventually

end MPSTensor
