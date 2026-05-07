/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.SectorWeightComparison
import TNLean.MPS.BNT.Basic
import TNLean.MPS.BNT.PermutationRigidityPrimitive
import TNLean.MPS.Overlap.CastLemmas
import TNLean.MPS.SharedInfra.GaugePhase

import Mathlib.Data.Fintype.BigOperators

/-!
# Sector decomposition comparison theorems

This chapter compares two finite sector decompositions that describe the same
matrix-product vector family.  It combines the coefficient comparison, the
recovery of sector weights from power sums, and the equal-case corollaries
needed to match sectors up to permutation and nonzero phase factors.

## References

- [PGVWC07] Pérez-García, Verstraete, Wolf, Cirac, *Matrix Product State Representations*,
  Quantum Inf. Comput. 7 (2007), arXiv:quant-ph/0608197.
- [CPSV17] Cirac, Pérez-García, Schuch, Verstraete, *Fundamental Theorems for PEPS*,
  arXiv:1606.00608 (2017).
- [CPSV21] Cirac, Pérez-García, Schuch, Verstraete, *Matrix product states and projected
  entangled pair states: Concepts, symmetries, theorems*, Rev. Mod. Phys. 93 (2021),
  arXiv:2011.12127.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-- **BNT linear-independence hypothesis for sector bases.**

`HasBNTSectorData P` asserts that the basis of the sector decomposition `P` is
a basis of normal tensors in the sense of Definition 4.2 of arXiv:2011.12127: for all
sufficiently large system sizes `N`, the MPV states `mpvState (P.basis j) N`
are linearly independent.  The statement records only the eventual condition;
no witness is included.

Mathematically, this is the eventual linear-independence hypothesis on the basis
sector MPV families. In comparison theorems for two sector decompositions, it
lets equality of total MPVs determine the scalar coefficients after the basis
blocks have been matched, even when the two decompositions use different bases. -/
def HasBNTSectorData (P : SectorDecomposition d) : Prop :=
  ∃ N0 : ℕ, ∀ N > N0,
    LinearIndependent ℂ (fun j : Fin P.basisCount => mpvState (P.basis j) N)

/-! ## Equal-case fundamental theorem for sector decompositions

The following theorems compare sector decompositions over a common basis of normal
tensors. Equality of the total matrix-product vectors gives equality of the
sector coefficient functions, and Newton identities recover the multisets of
sector weights inside each basis block.

The result formalized here is the BNT coefficient comparison that recovers both
multiplicities and sector weights. A global gauge-equivalence statement for the
assembled tensors still requires a theorem deriving the coefficient and phase
hypotheses required by the proportional decomposition theorem from bare equality
of matrix-product vectors. In sector form the coefficients are finite sums of powers
of unit-modulus weights, so convergence is not automatic without a dominant
weight, normalization, or an explicit common-phase comparison.
-/

/-- **Phase matching and total MPV equality recover multiplicities and sector weights.**

Assume two sector decompositions `P` and `Q` have basis blocks matched by a
permutation `perm`, and the matched basis MPVs differ by nonzero phase powers.
If the total tensors are `SameMPV₂` and the basis of `P` is eventually linearly
independent, then the multiplicities are forced to agree. After absorbing the same
phases into the weights of `Q`, the per-basis sector weight multisets agree.

This is the coefficient-extraction part of the comparison: equality of multiplicities
is recovered from the exponent-zero case of the power-sum identity after eventual
coefficient equality has been extrapolated to all exponents. -/
lemma fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_phaseMatch_exists_copies
    (P Q : SectorDecomposition d)
    (perm : Fin P.basisCount ≃ Fin Q.basisCount)
    (hPhase : ∀ j : Fin P.basisCount,
      ∃ ζ : ℂ, ζ ≠ 0 ∧
        ∀ (N : ℕ) (σ : Fin N → Fin d),
          mpv (Q.basis (perm j)) σ = ζ ^ N * mpv (P.basis j) σ)
    (hLI : ∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ (fun j : Fin P.basisCount => mpvState (P.basis j) N))
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    ∃ hCopies : ∀ j : Fin P.basisCount, P.copies j = Q.copies (perm j),
      ∃ ζ : Fin P.basisCount → ℂ,
        (∀ j, ζ j ≠ 0) ∧
        ∀ j : Fin P.basisCount,
          Finset.univ.val.map (P.weight j) =
            Finset.univ.val.map
              (fun q => ζ j * Q.weight (perm j) (Fin.cast (hCopies j) q)) := by
  classical
  let ζFn : Fin P.basisCount → ℂ := fun j => (hPhase j).choose
  have hζ_ne : ∀ j : Fin P.basisCount, ζFn j ≠ 0 :=
    fun j => (hPhase j).choose_spec.1
  have hζ_mpv : ∀ (j : Fin P.basisCount) (N : ℕ) (σ : Fin N → Fin d),
      mpv (Q.basis (perm j)) σ = (ζFn j) ^ N * mpv (P.basis j) σ :=
    fun j N σ => (hPhase j).choose_spec.2 N σ
  let T : SectorWeightData P.basisCount := {
    copies := fun j => Q.copies (perm j)
    copies_pos := fun j => Q.copies_pos (perm j)
    weight := fun j q => ζFn j * Q.weight (perm j) q
    weight_ne_zero := fun j q => mul_ne_zero (hζ_ne j) (Q.weight_ne_zero (perm j) q)
  }
  let Q' : SectorDecomposition d := {
    basisCount := P.basisCount
    basisDim := P.basisDim
    basis := P.basis
    sectors := T
  }
  have hTransport : SameMPV₂ Q'.toTensor Q.toTensor := by
    intro N σ
    calc
      mpv Q'.toTensor σ
          = ∑ j : Fin P.basisCount,
              ∑ q : Fin (Q.copies (perm j)),
                (ζFn j * Q.weight (perm j) q) ^ N * mpv (P.basis j) σ := by
              simpa [Q', T] using Q'.mpv_toTensor_eq_sum_sectors (N := N) σ
      _ = ∑ j : Fin P.basisCount,
            ∑ q : Fin (Q.copies (perm j)),
              (Q.weight (perm j) q) ^ N * mpv (Q.basis (perm j)) σ := by
            refine Finset.sum_congr rfl fun j _ => ?_
            refine Finset.sum_congr rfl fun q _ => ?_
            calc
              (ζFn j * Q.weight (perm j) q) ^ N * mpv (P.basis j) σ
                  = (Q.weight (perm j) q) ^ N * ((ζFn j) ^ N * mpv (P.basis j) σ) := by
                      rw [mul_pow]
                      ring
              _ = (Q.weight (perm j) q) ^ N * mpv (Q.basis (perm j)) σ := by
                      rw [hζ_mpv j N σ]
      _ = ∑ k : Fin Q.basisCount,
            ∑ q : Fin (Q.copies k),
              (Q.weight k q) ^ N * mpv (Q.basis k) σ := by
            let f : Fin P.basisCount → ℂ := fun j =>
              ∑ q : Fin (Q.copies (perm j)),
                (Q.weight (perm j) q) ^ N * mpv (Q.basis (perm j)) σ
            let g : Fin Q.basisCount → ℂ := fun k =>
              ∑ q : Fin (Q.copies k),
                (Q.weight k q) ^ N * mpv (Q.basis k) σ
            have hfg : ∀ j, f j = g (perm j) := by
              intro j
              rfl
            simpa [f, g] using (Fintype.sum_equiv perm f g hfg)
      _ = mpv Q.toTensor σ := by
            simpa using (Q.mpv_toTensor_eq_sum_sectors (N := N) σ).symm
  have hEqual' : SameMPV₂ P.toTensor Q'.toTensor := by
    intro N σ
    exact (hEqual N σ).trans (hTransport N σ).symm
  have hRecovered :
      ∃ hCopies' : ∀ j : Fin P.basisCount, P.sectors.copies j = T.copies j,
        ∀ j : Fin P.basisCount,
          Finset.univ.val.map (P.weight j) =
            Finset.univ.val.map (fun q => T.weight j (Fin.cast (hCopies' j) q)) :=
    SectorWeightData.exists_copies_eq_and_weight_multiset_eq_of_sameMPV_bnt
      (basis := P.basis) (S := P.sectors) (T := T) hLI (by
        intro N σ
        have hExpandP := P.mpv_toTensor_eq_sum_coeff σ (N := N)
        have hExpandQ' := Q'.mpv_toTensor_eq_sum_coeff σ (N := N)
        calc ∑ j, P.sectors.coeff N j * mpv (P.basis j) σ
            = mpv P.toTensor σ := hExpandP.symm
          _ = mpv Q'.toTensor σ := hEqual' N σ
          _ = ∑ j, T.coeff N j * mpv (P.basis j) σ := hExpandQ')
  obtain ⟨hCopies', hMultiset⟩ := hRecovered
  let hCopies : ∀ j : Fin P.basisCount, P.copies j = Q.copies (perm j) := fun j => by
    change P.sectors.copies j = T.copies j
    exact hCopies' j
  refine ⟨hCopies, ζFn, hζ_ne, ?_⟩
  intro j
  have hproof : hCopies' j = hCopies j := Subsingleton.elim _ _
  simpa [T, hproof] using hMultiset j

/-- **Sector comparison for different bases reduces to the shared-basis case after phase matching.**

Assume two sector decompositions `P` and `Q` have basis blocks matched by a permutation `perm`,
matching multiplicities, and per-basis MPV relations
`mpv (Q.basis (perm j)) σ = ζ_j^N * mpv (P.basis j) σ`. If the total tensors are
`SameMPV₂`, then after absorbing the phases `ζ_j` into the sector weights on the `Q` side,
the per-basis sector weight multisets agree. -/
lemma fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_phaseMatch
    (P Q : SectorDecomposition d)
    (perm : Fin P.basisCount ≃ Fin Q.basisCount)
    (hCopies : ∀ j : Fin P.basisCount, P.copies j = Q.copies (perm j))
    (hPhase : ∀ j : Fin P.basisCount,
      ∃ ζ : ℂ, ζ ≠ 0 ∧
        ∀ (N : ℕ) (σ : Fin N → Fin d),
          mpv (Q.basis (perm j)) σ = ζ ^ N * mpv (P.basis j) σ)
    (hLI : ∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ (fun j : Fin P.basisCount => mpvState (P.basis j) N))
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    ∃ ζ : Fin P.basisCount → ℂ,
      (∀ j, ζ j ≠ 0) ∧
      ∀ j : Fin P.basisCount,
        Finset.univ.val.map (P.weight j) =
          Finset.univ.val.map
            (fun q => ζ j * Q.weight (perm j) (Fin.cast (hCopies j) q)) := by
  obtain ⟨hCopies', ζ, hζ_ne, hMultiset⟩ :=
    fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_phaseMatch_exists_copies
      P Q perm hPhase hLI hEqual
  refine ⟨ζ, hζ_ne, ?_⟩
  intro j
  have hproof : hCopies' j = hCopies j := Subsingleton.elim _ _
  simpa [hproof] using hMultiset j

/-- **Cast-compatible MPV scaling gives the phase-matched sector comparison.**

This lemma isolates the weaker hypotheses actually consumed by the
phase-absorption argument: after matching basis dimensions, each block pair
only needs a nonzero phase `ζ` relating the MPVs of the matched basis tensors. -/
lemma fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_mpvScaling_matched_basis
    (P Q : SectorDecomposition d)
    (perm : Fin P.basisCount ≃ Fin Q.basisCount)
    (hCopies : ∀ j : Fin P.basisCount, P.copies j = Q.copies (perm j))
    (hBasis : ∀ j : Fin P.basisCount,
      ∃ hdim : P.basisDim j = Q.basisDim (perm j),
        ∃ ζ : ℂ, ζ ≠ 0 ∧
          ∀ (N : ℕ) (σ : Fin N → Fin d),
            mpv (Q.basis (perm j)) σ =
              ζ ^ N * mpv (cast (congr_arg (MPSTensor d) hdim) (P.basis j)) σ)
    (hLI : ∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ (fun j : Fin P.basisCount => mpvState (P.basis j) N))
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    ∃ ζ : Fin P.basisCount → ℂ,
      (∀ j, ζ j ≠ 0) ∧
      ∀ j : Fin P.basisCount,
        Finset.univ.val.map (P.weight j) =
          Finset.univ.val.map
            (fun q => ζ j * Q.weight (perm j) (Fin.cast (hCopies j) q)) := by
  have hPhase : ∀ j : Fin P.basisCount,
      ∃ ζ : ℂ, ζ ≠ 0 ∧
        ∀ (N : ℕ) (σ : Fin N → Fin d),
          mpv (Q.basis (perm j)) σ = ζ ^ N * mpv (P.basis j) σ := by
    intro j
    obtain ⟨hdim, ζ, hζne, hmpv⟩ := hBasis j
    refine ⟨ζ, hζne, ?_⟩
    intro N σ
    rw [hmpv N σ, mpv_cast_dim hdim (P.basis j) N σ]
  exact fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_phaseMatch
    P Q perm hCopies hPhase hLI hEqual

/-- **Gauge-phase matched sector bases give the phase-matched sector comparison.**

This lemma converts blockwise gauge-phase equivalence into the corresponding
power-law scaling of matrix-product vectors, then uses the sector comparison for
a supplied permutation of basis blocks. Thus the
phase-absorption step is already available once the basis permutation,
multiplicity equality, and per-block phase factors have been supplied. -/
lemma fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_matched_basis
    (P Q : SectorDecomposition d)
    (perm : Fin P.basisCount ≃ Fin Q.basisCount)
    (hCopies : ∀ j : Fin P.basisCount, P.copies j = Q.copies (perm j))
    (hBasis : ∀ j : Fin P.basisCount,
      ∃ hdim : P.basisDim j = Q.basisDim (perm j),
        GaugePhaseEquiv (d := d)
          (cast (congr_arg (MPSTensor d) hdim) (P.basis j))
          (Q.basis (perm j)))
    (hLI : ∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ (fun j : Fin P.basisCount => mpvState (P.basis j) N))
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    ∃ ζ : Fin P.basisCount → ℂ,
      (∀ j, ζ j ≠ 0) ∧
      ∀ j : Fin P.basisCount,
        Finset.univ.val.map (P.weight j) =
          Finset.univ.val.map
            (fun q => ζ j * Q.weight (perm j) (Fin.cast (hCopies j) q)) := by
  have hScaling : ∀ j : Fin P.basisCount,
      ∃ hdim : P.basisDim j = Q.basisDim (perm j),
        ∃ ζ : ℂ, ζ ≠ 0 ∧
        ∀ (N : ℕ) (σ : Fin N → Fin d),
          mpv (Q.basis (perm j)) σ =
            ζ ^ N * mpv (cast (congr_arg (MPSTensor d) hdim) (P.basis j)) σ := by
    intro j
    obtain ⟨hdim, hGPE⟩ := hBasis j
    obtain ⟨X, ζ, hζne, hX⟩ := hGPE
    refine ⟨hdim, ζ, hζne, ?_⟩
    intro N σ
    exact mpv_eq_pow_mul_of_gaugePhase _ _ X ζ hX N σ
  exact fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_mpvScaling_matched_basis
    P Q perm hCopies hScaling hLI hEqual

/-! ## Basis matching witness for two sector decompositions with different bases

The sector-comparison theorems above take four separate hypotheses: a permutation
of sector bases, equality of multiplicities, per-block dimension equality, and
per-block gauge-phase equivalence. The structures below collect these into a
single witness. Overlap/span hypotheses or common-cover phase hypotheses produce the
witness; the sector comparison then recovers the corresponding weight multisets.
-/

/-- Basis matching before sector multiplicities have been recovered.

This structure captures the part of the BNT comparison for two sector decompositions
with different bases, supplied by the overlap-dichotomy argument: a permutation of
basis blocks, equality of their bond dimensions, and gauge-phase equivalence of the
matched blocks. It does not include equality of multiplicities; that equality is recovered
from total MPV equality by
`SectorBasisPreMatching.exists_sectorBasisMatching_of_sameMPV`. -/
structure SectorBasisPreMatching (P Q : SectorDecomposition d) where
  /-- Permutation matching basis indices of `P` and `Q`. -/
  perm : Fin P.basisCount ≃ Fin Q.basisCount
  /-- Matched basis blocks share the same bond dimension. -/
  dim_eq : ∀ j : Fin P.basisCount, P.basisDim j = Q.basisDim (perm j)
  /-- Matched basis blocks are gauge-phase equivalent after dimension transport. -/
  basis_equiv : ∀ j : Fin P.basisCount,
    GaugePhaseEquiv (d := d)
      (cast (congr_arg (MPSTensor d) (dim_eq j)) (P.basis j))
      (Q.basis (perm j))

/-- Witness matching two sector decompositions block-by-block.

This structure collects the four hypotheses required by
`fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_matched_basis`:

* a basis permutation,
* per-block multiplicity agreement,
* per-block bond-dimension equality, and
* per-block gauge-phase equivalence of the (dimension-transported) basis blocks.

**Formalization note.** The overlap/span route produces this witness when the
corresponding comparison hypotheses are available. For sector decompositions
obtained after blocking, those hypotheses may instead be supplied by an equivalent
common-phase BNT-cover comparison. -/
structure SectorBasisMatching (P Q : SectorDecomposition d) where
  /-- Permutation matching basis indices of `P` and `Q`. -/
  perm : Fin P.basisCount ≃ Fin Q.basisCount
  /-- Matched basis blocks carry the same multiplicity. -/
  copies_eq : ∀ j : Fin P.basisCount, P.copies j = Q.copies (perm j)
  /-- Matched basis blocks share the same bond dimension. -/
  dim_eq : ∀ j : Fin P.basisCount, P.basisDim j = Q.basisDim (perm j)
  /-- Matched basis blocks are gauge-phase equivalent after dimension transport. -/
  basis_equiv : ∀ j : Fin P.basisCount,
    GaugePhaseEquiv (d := d)
      (cast (congr_arg (MPSTensor d) (dim_eq j)) (P.basis j))
      (Q.basis (perm j))

private lemma sectorBasisMatchExists_of_fields
    {P Q : SectorDecomposition d}
    (perm : Fin P.basisCount ≃ Fin Q.basisCount)
    (dim_eq : ∀ j : Fin P.basisCount, P.basisDim j = Q.basisDim (perm j))
    (basis_equiv : ∀ j : Fin P.basisCount,
      GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) (dim_eq j)) (P.basis j))
        (Q.basis (perm j))) :
    ∀ j : Fin P.basisCount,
      ∃ hdim : P.basisDim j = Q.basisDim (perm j),
        GaugePhaseEquiv (d := d)
          (cast (congr_arg (MPSTensor d) hdim) (P.basis j))
          (Q.basis (perm j)) :=
  fun j => ⟨dim_eq j, basis_equiv j⟩

namespace SectorBasisMatching

variable {P Q : SectorDecomposition d}

/-- Reformulate the per-block hypotheses in the existential form consumed by
`fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_matched_basis`. -/
lemma basis_match_exists (M : SectorBasisMatching P Q) :
    ∀ j : Fin P.basisCount,
      ∃ hdim : P.basisDim j = Q.basisDim (M.perm j),
        GaugePhaseEquiv (d := d)
          (cast (congr_arg (MPSTensor d) hdim) (P.basis j))
          (Q.basis (M.perm j)) :=
  sectorBasisMatchExists_of_fields M.perm M.dim_eq M.basis_equiv

end SectorBasisMatching

namespace SectorBasisPreMatching

variable {P Q : SectorDecomposition d}

/-- Reformulate pre-matching hypotheses in the existential form used by the theorem with
a supplied permutation of basis blocks. -/
lemma basis_match_exists (M : SectorBasisPreMatching P Q) :
    ∀ j : Fin P.basisCount,
      ∃ hdim : P.basisDim j = Q.basisDim (M.perm j),
        GaugePhaseEquiv (d := d)
          (cast (congr_arg (MPSTensor d) hdim) (P.basis j))
          (Q.basis (M.perm j)) :=
  sectorBasisMatchExists_of_fields M.perm M.dim_eq M.basis_equiv

/-- Gauge-phase pre-matching gives the MPV phase-scaling relation for each basis block. -/
lemma phase_match_exists (M : SectorBasisPreMatching P Q) :
    ∀ j : Fin P.basisCount,
      ∃ ζ : ℂ, ζ ≠ 0 ∧
        ∀ (N : ℕ) (σ : Fin N → Fin d),
          mpv (Q.basis (M.perm j)) σ = ζ ^ N * mpv (P.basis j) σ := by
  intro j
  obtain ⟨X, ζ, hζne, hX⟩ := M.basis_equiv j
  refine ⟨ζ, hζne, ?_⟩
  intro N σ
  rw [mpv_eq_pow_mul_of_gaugePhase _ _ X ζ hX N σ,
    mpv_cast_dim (M.dim_eq j) (P.basis j) N σ]

/-- Promote a basis pre-matching to a full sector basis matching.

The new information is equality of multiplicities. It follows from total MPV equality
and BNT linear independence by recovering the exponent-zero power sums for the
matched sector coefficients. -/
lemma exists_sectorBasisMatching_of_sameMPV
    (M : SectorBasisPreMatching P Q)
    (hLI : HasBNTSectorData P)
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    ∃ M' : SectorBasisMatching P Q, M'.perm = M.perm := by
  obtain ⟨hCopies, _ζ, _hζ_ne, _hMultiset⟩ :=
    fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_phaseMatch_exists_copies
      P Q M.perm M.phase_match_exists hLI hEqual
  refine ⟨{
    perm := M.perm
    copies_eq := hCopies
    dim_eq := M.dim_eq
    basis_equiv := M.basis_equiv
  }, rfl⟩

end SectorBasisPreMatching

/-- Single-family primitive overlap-orthogonality hypotheses for a sector basis.

This is the part of `SectorBasisOverlapSpanHypotheses` that can be checked one
sector decomposition at a time: positive basis dimensions, left-canonical
normalization, self-overlap convergence to `1`, and off-diagonal overlap
convergence to `0`. It intentionally omits one-site injectivity and the
finite-length span comparison between two different bases, because those are
separate inputs in the after-blocking comparison. -/
structure SectorBasisOverlapOrthoHypotheses (P : SectorDecomposition d) : Prop where
  /-- The basis blocks have nonzero bond dimension. -/
  dim_pos : ∀ j : Fin P.basisCount, 0 < P.basisDim j
  /-- The basis blocks are left-canonical. -/
  normalized :
    ∀ j : Fin P.basisCount, (∑ i : Fin d, (P.basis j i)ᴴ * (P.basis j i)) = 1
  /-- Each basis block has self-overlap tending to one. -/
  self_overlap : ∀ j : Fin P.basisCount,
    Filter.Tendsto (fun N => mpvOverlap (d := d) (P.basis j) (P.basis j) N)
      Filter.atTop (nhds (1 : ℂ))
  /-- Distinct basis blocks have asymptotically zero overlap. -/
  off_overlap : ∀ i j : Fin P.basisCount, i ≠ j →
    Filter.Tendsto (fun N => mpvOverlap (d := d) (P.basis i) (P.basis j) N)
      Filter.atTop (nhds 0)

/-- Primitive overlap-rigidity hypotheses for two sector bases.

This structure collects the analytic inputs used by
`exists_sectorBasisMatching_of_overlapOrtho_span_sameMPV`: nonzero bond
dimensions, injectivity, left-canonical normalization, asymptotic self/orthogonal
overlaps, and equality of the finite-length MPV spans. It deliberately does
not contain a permutation or equality of multiplicities; those are produced by the
overlap rigidity theorem and the BNT coefficient comparison. -/
structure SectorBasisOverlapSpanHypotheses (P Q : SectorDecomposition d) : Prop where
  /-- The left basis blocks have nonzero bond dimension. -/
  left_dim_pos : ∀ j : Fin P.basisCount, 0 < P.basisDim j
  /-- The right basis blocks have nonzero bond dimension. -/
  right_dim_pos : ∀ k : Fin Q.basisCount, 0 < Q.basisDim k
  /-- The left basis blocks are injective. -/
  left_injective : ∀ j : Fin P.basisCount, IsInjective (P.basis j)
  /-- The right basis blocks are injective. -/
  right_injective : ∀ k : Fin Q.basisCount, IsInjective (Q.basis k)
  /-- The left basis blocks are left-canonical. -/
  left_normalized :
    ∀ j : Fin P.basisCount, (∑ i : Fin d, (P.basis j i)ᴴ * (P.basis j i)) = 1
  /-- The right basis blocks are left-canonical. -/
  right_normalized :
    ∀ k : Fin Q.basisCount, (∑ i : Fin d, (Q.basis k i)ᴴ * (Q.basis k i)) = 1
  /-- Each left basis block has self-overlap tending to one. -/
  left_self_overlap : ∀ j : Fin P.basisCount,
    Filter.Tendsto (fun N => mpvOverlap (d := d) (P.basis j) (P.basis j) N)
      Filter.atTop (nhds (1 : ℂ))
  /-- Distinct left basis blocks have asymptotically zero overlap. -/
  left_off_overlap : ∀ i j : Fin P.basisCount, i ≠ j →
    Filter.Tendsto (fun N => mpvOverlap (d := d) (P.basis i) (P.basis j) N)
      Filter.atTop (nhds 0)
  /-- Each right basis block has self-overlap tending to one. -/
  right_self_overlap : ∀ k : Fin Q.basisCount,
    Filter.Tendsto (fun N => mpvOverlap (d := d) (Q.basis k) (Q.basis k) N)
      Filter.atTop (nhds (1 : ℂ))
  /-- Distinct right basis blocks have asymptotically zero overlap. -/
  right_off_overlap : ∀ k l : Fin Q.basisCount, k ≠ l →
    Filter.Tendsto (fun N => mpvOverlap (d := d) (Q.basis k) (Q.basis l) N)
      Filter.atTop (nhds 0)
  /-- The finite-length spans of the two sector bases agree. -/
  span_eq : ∀ N,
    Submodule.span ℂ (Set.range (fun j : Fin P.basisCount =>
      mpvState (d := d) (P.basis j) N)) =
    Submodule.span ℂ (Set.range (fun k : Fin Q.basisCount =>
      mpvState (d := d) (Q.basis k) N))

namespace SectorBasisOverlapOrthoHypotheses

variable {P Q : SectorDecomposition d}

/-- Combine the single-family overlap-orthogonality hypotheses for two sector bases
with the one-site injectivity and finite-length span comparison inputs needed by
the primitive overlap-rigidity theorem. -/
lemma to_overlapSpan
    (HP : SectorBasisOverlapOrthoHypotheses P)
    (HQ : SectorBasisOverlapOrthoHypotheses Q)
    (hP_inj : ∀ j : Fin P.basisCount, IsInjective (P.basis j))
    (hQ_inj : ∀ k : Fin Q.basisCount, IsInjective (Q.basis k))
    (hspan : ∀ N,
      Submodule.span ℂ (Set.range (fun j : Fin P.basisCount =>
        mpvState (d := d) (P.basis j) N)) =
      Submodule.span ℂ (Set.range (fun k : Fin Q.basisCount =>
        mpvState (d := d) (Q.basis k) N))) :
    SectorBasisOverlapSpanHypotheses P Q where
  left_dim_pos := HP.dim_pos
  right_dim_pos := HQ.dim_pos
  left_injective := hP_inj
  right_injective := hQ_inj
  left_normalized := HP.normalized
  right_normalized := HQ.normalized
  left_self_overlap := HP.self_overlap
  left_off_overlap := HP.off_overlap
  right_self_overlap := HQ.self_overlap
  right_off_overlap := HQ.off_overlap
  span_eq := hspan

end SectorBasisOverlapOrthoHypotheses

/-- Produce a sector basis matching from the primitive overlap-rigidity hypotheses.

The overlap-rigidity theorem gives the basis permutation, dimension equalities,
and gauge-phase equivalences. The preceding pre-matching result then recovers
the equality of sector multiplicities from total MPV equality. -/
theorem exists_sectorBasisMatching_of_overlapOrtho_span_sameMPV
    (P Q : SectorDecomposition d)
    [∀ j : Fin P.basisCount, NeZero (P.basisDim j)]
    [∀ k : Fin Q.basisCount, NeZero (Q.basisDim k)]
    (hP_inj : ∀ j, IsInjective (P.basis j))
    (hQ_inj : ∀ k, IsInjective (Q.basis k))
    (hP_norm : ∀ j, (∑ i : Fin d, (P.basis j i)ᴴ * (P.basis j i)) = 1)
    (hQ_norm : ∀ k, (∑ i : Fin d, (Q.basis k i)ᴴ * (Q.basis k i)) = 1)
    (hP_self : ∀ j,
      Filter.Tendsto (fun N => mpvOverlap (d := d) (P.basis j) (P.basis j) N)
        Filter.atTop (nhds (1 : ℂ)))
    (hP_off : ∀ i j, i ≠ j →
      Filter.Tendsto (fun N => mpvOverlap (d := d) (P.basis i) (P.basis j) N)
        Filter.atTop (nhds 0))
    (hQ_self : ∀ k,
      Filter.Tendsto (fun N => mpvOverlap (d := d) (Q.basis k) (Q.basis k) N)
        Filter.atTop (nhds (1 : ℂ)))
    (hQ_off : ∀ k l, k ≠ l →
      Filter.Tendsto (fun N => mpvOverlap (d := d) (Q.basis k) (Q.basis l) N)
        Filter.atTop (nhds 0))
    (hspan : ∀ N,
      Submodule.span ℂ (Set.range (fun j : Fin P.basisCount =>
        mpvState (d := d) (P.basis j) N)) =
      Submodule.span ℂ (Set.range (fun k : Fin Q.basisCount =>
        mpvState (d := d) (Q.basis k) N)))
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    Nonempty (SectorBasisMatching P Q) := by
  obtain ⟨_hCount, perm, hBasis⟩ :=
    exists_eq_numBlocks_and_equiv_gaugePhase_of_overlapOrtho
      (A := P.basis) (B := Q.basis)
      hP_inj hQ_inj hP_norm hQ_norm hP_self hP_off hQ_self hQ_off hspan
  let M₀ : SectorBasisPreMatching P Q := {
    perm := perm
    dim_eq := fun j => (hBasis j).choose
    basis_equiv := fun j => (hBasis j).choose_spec
  }
  have hLI : HasBNTSectorData P := by
    have hEventually := eventually_linearIndependent_of_overlap_tendsto_orthonormal
      P.basis hP_self hP_off
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 hEventually
    exact ⟨N0, fun N hN => hN0 N (le_of_lt hN)⟩
  obtain ⟨M, _hperm⟩ := M₀.exists_sectorBasisMatching_of_sameMPV hLI hEqual
  exact ⟨M⟩

namespace SectorBasisOverlapSpanHypotheses

variable {P Q : SectorDecomposition d}

/-- Convert the combined primitive overlap-rigidity hypotheses into a sector basis
matching. The produced witness is not part of the hypotheses: it is obtained by
`exists_sectorBasisMatching_of_overlapOrtho_span_sameMPV`. -/
lemma exists_sectorBasisMatching
    (H : SectorBasisOverlapSpanHypotheses P Q)
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    Nonempty (SectorBasisMatching P Q) := by
  letI : ∀ j : Fin P.basisCount, NeZero (P.basisDim j) :=
    fun j => ⟨Nat.ne_of_gt (H.left_dim_pos j)⟩
  letI : ∀ k : Fin Q.basisCount, NeZero (Q.basisDim k) :=
    fun k => ⟨Nat.ne_of_gt (H.right_dim_pos k)⟩
  exact exists_sectorBasisMatching_of_overlapOrtho_span_sameMPV P Q
    H.left_injective H.right_injective H.left_normalized H.right_normalized
    H.left_self_overlap H.left_off_overlap H.right_self_overlap H.right_off_overlap
    H.span_eq hEqual

end SectorBasisOverlapSpanHypotheses

/-- **Sector comparison for two decompositions with different bases, via a basis matching witness.**

Corollary of `fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_matched_basis`
obtained by expressing the matching hypotheses as a `SectorBasisMatching`.
The matching can be extracted from `SectorBasisOverlapSpanHypotheses`.

**Formalization note.** For after-blocking sector decompositions, those hypotheses may
instead be supplied by equivalent common-phase BNT-cover hypotheses. -/
theorem fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_sectorMatching
    {P Q : SectorDecomposition d}
    (M : SectorBasisMatching P Q)
    (hLI : ∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ (fun j : Fin P.basisCount => mpvState (P.basis j) N))
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    ∃ ζ : Fin P.basisCount → ℂ,
      (∀ j, ζ j ≠ 0) ∧
      ∀ j : Fin P.basisCount,
        Finset.univ.val.map (P.weight j) =
          Finset.univ.val.map
            (fun q => ζ j * Q.weight (M.perm j) (Fin.cast (M.copies_eq j) q)) :=
  fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_matched_basis
    P Q M.perm M.copies_eq M.basis_match_exists hLI hEqual

end MPSTensor
