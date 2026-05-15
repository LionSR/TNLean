/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.PaperBNT.CoeffIdentity
import TNLean.MPS.FundamentalTheorem.PaperBNT.StrongInduction

/-!
# Paper-faithful BNT equal-MPV sector data theorem

This module assembles Phase D's full-basis matching and eventual exact
coefficient identity into the sector-data conclusion of the CPSV16/CPSV21
fundamental theorem on the paper-faithful `IsBNTCanonicalForm` surface.

Paper anchors:

* CPSV16 §II.C lines 1182–1186: full BNT basis matching by the `Lem1`
  contradiction and symmetry argument.
* CPSV16 §II.C lines 1187–1188: exact power-sum coefficient comparison,
  recovering copy multiplicities and weights up to the matched phase.
* CPSV21 Definition 4.3 lines 1846–1884: per-block spectral-radius-one
  normalization, formalized in Phase D as `weight_unit_exists_per_block`.

The theorem below exposes the sector-level data needed before assembling
the global CPSV16 gauge `⊕_j (𝟙_{r_j} ⊗ Y_j)`.  It does not use
`dropSector` recursion, partial-union combined LI, or asymptotic-difference
multiset recovery.
-/

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-- **Paper-faithful equal-MPV sector-data theorem (Phase D).**

If two paper-faithful BNT sector decompositions generate the same MPV family,
then their BNT basis sectors are bijectively matched by gauge-phase
equivalence.  For each matched sector, the copy multiplicities agree and the
raw copy weights agree after multiplying by the inverse of the gauge phase and
permuting the copies.

This is the Lean sector-data counterpart of CPSV16 §II.C lines 1184–1188. -/
theorem ft_paper_bnt_equal_sector_data
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    ∃ (β : Fin Q.basisCount ≃ Fin P.basisCount),
      (∀ k, ∃ h : P.basisDim (β k) = Q.basisDim k,
        GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (P.basis (β k))) (Q.basis k)) ∧
      (∀ k, P.copies (β k) = Q.copies k) ∧
      ∃ ζ : Fin Q.basisCount → ℂ, (∀ k, ‖ζ k‖ = 1) ∧
        ∀ k, ∃ τ : Fin (Q.copies k) ≃ Fin (P.copies (β k)),
          ∀ q : Fin (Q.copies k), Q.weight k q = (ζ k)⁻¹ * P.weight (β k) (τ q) := by
  classical
  obtain ⟨β, hβMatchFull⟩ := bijective_match_of_sameMPV hP hQ hEqual
  let hMatch : ∀ k : Fin Q.basisCount, ∃ h : P.basisDim (β k) = Q.basisDim k,
      GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (P.basis (β k))) (Q.basis k) :=
    fun k => by
      obtain ⟨h, hGPE, _hNondecay⟩ := hβMatchFull k
      exact ⟨h, hGPE⟩
  have hCoeff := coeff_identity_via_global_gauge hP hQ hEqual β hMatch
  let ζ : Fin Q.basisCount → ℂ := fun k => (hCoeff k).choose
  have hζ_norm : ∀ k : Fin Q.basisCount, ‖ζ k‖ = 1 := fun k =>
    (hCoeff k).choose_spec.1
  have hCoeff_eventual : ∀ k : Fin Q.basisCount,
      ∃ N₀, ∀ N > N₀, P.coeff N (β k) = (ζ k) ^ N * Q.coeff N k := fun k =>
    (hCoeff k).choose_spec.2
  have hWeightData : ∀ k : Fin Q.basisCount,
      ∃ (hCopies : P.copies (β k) = Q.copies k)
        (τ : Fin (P.copies (β k)) ≃ Fin (Q.copies k)),
        ∀ q : Fin (P.copies (β k)),
          Q.weight k (τ q) = (ζ k)⁻¹ * P.weight (β k) q := by
    intro k
    obtain ⟨N₀, hCoeff_k⟩ := hCoeff_eventual k
    have hζ_ne : ζ k ≠ 0 := by
      intro hzero
      have hnorm := hζ_norm k
      simp [hzero] at hnorm
    exact matched_sector_weight_equiv (P := P) (Q := Q)
      (j₀ := β k) (k₀' := k) (ζ := ζ k) hζ_ne (N₀ := N₀) hCoeff_k
  let hCopies : ∀ k : Fin Q.basisCount, P.copies (β k) = Q.copies k := fun k =>
    (hWeightData k).choose
  refine ⟨β, hMatch, hCopies, ζ, hζ_norm, ?_⟩
  intro k
  obtain ⟨hC, τPQ, hτPQ⟩ := hWeightData k
  refine ⟨τPQ.symm, ?_⟩
  intro q
  have hpoint := hτPQ (τPQ.symm q)
  simpa using hpoint

end MPSTensor
