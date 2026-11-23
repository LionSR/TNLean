/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.Lattice.Chain
import QICLean.ManyBody.Entropy.SupportedMarginalTails
import QICLean.Entropy.Surprisal.FilterMoment
import QICLean.ManyBody.Sites.RegionState
import QICLean.ManyBody.Sites.Placement
import QICLean.ManyBody.Entropy.QuditRegionEntropy
import QICLean.ManyBody.Hamiltonian.GroundSpace
import QICLean.ManyBody.Hamiltonian.Models
import QICLean.ManyBody.Entropy.ZeroEntropy
import QICLean.ManyBody.Entropy.MovementEtaRegional
import QICLean.ManyBody.Entropy.RegionEntropyInequalities
import QICLean.ManyBody.Entropy.RegionStrongSubadditivity

/-!
# Finite-range Hamiltonians on the chain of `L` sites

A support of range `R` is a nonempty set of sites of the chain of diameter at most `R`,
that is, contained in `R + 1` consecutive positions. A finite-range Hamiltonian is an
interaction `ManyBody.ChainInteraction L q R`, one term per support acting as the identity off
it, whose terms are Hermitian and of operator norm at most `J`; both are hypotheses of the
statements that use them. A gapped ground vector is a unit eigenvector `Ω` of the sum with
`H - E₀ ≥ Δ (1 - |Ω⟩⟨Ω|)`.

The marginal tail bound of the area-law manuscript holds on any finite tensor product;
the chain model instantiates it directly, with the cut budget
`ℬ_A = 1 + ∑ log² (e q^{|X|})` over the supports split by the cut `A`. The budget is
QICLean's `ManyBody.cutLogBudget` of the family of chain supports with local dimension `q`.

## Main results

* `ManyBody.ChainInteraction.surprisalTail_regionState_le`: the marginal tail bound for a gapped
  ground vector at every cut.

## References

* TNLean note, *A one-dimensional area law and matrix product state approximation from a
  global gap* (`docs/notes/one_dimensional_note`), Section 1, `eq:ham` and `eq:gap`, and
  Section 3, Lemma 3.1 (the marginal tail bound).
* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Lemma 3.1 (`lem:tail`), `02-initial.tex`, lines 34–69.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## Splitting a range-one Hamiltonian at a cut

A range-one interaction crossing the cut after the first `k` sites is supported on the
adjacent pair at that cut. Positive interactions of norm at most one therefore give a
decomposition `H = H_L + H_R + K`, with `0 ≤ K ≤ 1`.

This is the Hamiltonian decomposition used by Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `References/1307.5143/algo53.tex`, lines 283 and 409–410.
-/

section

open ManyBody (ChainSupport IsChainSupport interval mem_interval ChainInteraction)

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

open ManyBody (IsGapped groundSpace)

namespace TNLean.MPS.AreaLaw

variable {L q R : ℕ} {J : ℝ}

/-- The Hilbert-space dimension of a support of range `R` is at most `q^{R + 1}`. -/
theorem supportDim_le (hq : 1 ≤ q) (X : ChainSupport L R) :
    Entropy.supportDim (fun _ : Fin L ↦ q) X.1 ≤ q ^ (R + 1) := by
  rw [Entropy.supportDim, Finset.prod_const]
  exact Nat.pow_le_pow_right hq X.2.card_le

/-- The Hilbert-space dimension of a support is at least one when `q ≥ 1`. -/
theorem one_le_supportDim (hq : 1 ≤ q) (X : ChainSupport L R) :
    1 ≤ Entropy.supportDim (fun _ : Fin L ↦ q) X.1 :=
  ManyBody.one_le_supportDim_const hq X.1

/-- The interaction bound is nonnegative whenever the chain contains a site.
The singleton interaction supplies the inequality.
Source: TNLean note, Section 1, `eq:ham`. -/
lemma _root_.ManyBody.ChainInteraction.norm_bound_nonneg (h : ChainInteraction L q R)
    (hhJ : ∀ X, ‖h.term X‖ ≤ J) (x : Fin L) :
    0 ≤ J := by
  classical
  let X : ChainSupport L R := ⟨{x}, by simp [IsChainSupport]⟩
  exact (norm_nonneg (h.term X)).trans (hhJ X)

/-- **The marginal tail bound on a chain.** For a gapped ground vector `Ω` with gap `Δ > 0`
of a finite-range Hamiltonian with term norms at most `J ≥ 0`, and any cut `A`, the
surprisal of the regional state on `A` satisfies, for every real `w`,
`Pr {|K - S(A)| > w} ≤ min {1, 2 e^{e/2} exp (-w / (32 √((1 + J/Δ) ℬ_A)))}`.
TNLean note, Lemma 3.1; area-law manuscript, Lemma 3.1 (`lem:tail`),
`eq:initial-tail-probability`. -/
theorem _root_.ManyBody.ChainInteraction.surprisalTail_regionState_le (h : ChainInteraction L q R)
    (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (hJ : 0 ≤ J) {E₀ Δ : ℝ} {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΔ : 0 < Δ)
    (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω}) (A : Finset (Fin L)) (w : ℝ) :
    Entropy.surprisalTail (ManyBody.regionState_isHermitian (X := fun _ ↦ Fin q) A Ω).eigenvalues
        (ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω A) w ≤
      min 1 (2 * Real.exp (Real.exp 1 / 2) *
        Real.exp (-(w / (32 * Real.sqrt ((1 + J / Δ) *
          ManyBody.cutLogBudget (fun X : ChainSupport L R ↦ X.1) (fun _ ↦ q) A))))) := by
  have heig : toEuclideanLin h.hamiltonian Ω = (E₀ : ℂ) • Ω :=
    ManyBody.mem_groundSpace_iff.mp (hspan ▸ Submodule.mem_span_singleton_self Ω)
  have hgap := hgap.posSemidef_sub_smul_one
      (ManyBody.Interaction.isHermitian_hamiltonian hh) hΩ hspan
  exact Entropy.surprisalTail_cut_le (n := fun _ : Fin L ↦ q) (B := A) h.mem hh hJ
    hhJ hΩ hΔ heig hgap (ManyBody.regionState_eq_partialTraceRight_cutVector A Ω).symm
    (ManyBody.regionState_isHermitian A Ω) w

end TNLean.MPS.AreaLaw

end

section

open ManyBody (ChainSupport IsChainSupport interval mem_interval ChainInteraction)

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- Positive range-one interactions of norm at most one split at every cut as
`H = H_L + H_R + K`, with the two parts supported on their respective sides and
`0 ≤ K ≤ 1`. Source: LVV13, `algo53.tex`, line 283 and lines 409–410. -/
theorem _root_.ManyBody.ChainInteraction.exists_cut_decomposition_of_range_one {L q : ℕ}
    (h : ChainInteraction L q 1) (hhJ : ∀ X, ‖h.term X‖ ≤ 1)
        (hpos : ∀ X, (h.term X).PosSemidef) (k : ℕ) :
    ∃ HL HR K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
      h.hamiltonian = HL + HR + K ∧
      ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) HL (interval L 0 k) ∧
      ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) HR (interval L 0 k)ᶜ ∧
      K.PosSemidef ∧ (1 - K).PosSemidef := by
  classical
  let A := interval L 0 k
  let S := Finset.univ.filter fun X : ChainSupport L 1 ↦ X.1 ⊆ A
  let U := Finset.univ.filter fun X : ChainSupport L 1 ↦ ¬X.1 ⊆ A
  let T := U.filter fun X ↦ X.1 ⊆ Aᶜ
  let C := U.filter fun X ↦ ¬X.1 ⊆ Aᶜ
  have hcross (X : ChainSupport L 1) (hXC : X ∈ C) :
      X.1 = interval L (k - 1) (k + 1) := by
    have hnotL := (Finset.mem_filter.mp (Finset.mem_filter.mp hXC).1).2
    have hnotR := (Finset.mem_filter.mp hXC).2
    apply X.2.eq_interval_of_splits_of_range_one
    constructor
    · obtain ⟨x, hx, hxA⟩ := Finset.not_subset.mp hnotR
      exact ⟨x, hx, by simpa [A, mem_interval] using hxA⟩
    · obtain ⟨y, hy, hyA⟩ := Finset.not_subset.mp hnotL
      refine ⟨y, hy, ?_⟩
      have : ¬y.val < k := by simpa [A, mem_interval] using hyA
      omega
  have hcard : C.card ≤ 1 := Finset.card_le_one.mpr fun X hX Y hY ↦
    Subtype.ext ((hcross X hX).trans (hcross Y hY).symm)
  let K := ∑ X ∈ C, h.term X
  have hK : K.PosSemidef := posSemidef_sum C fun X _ ↦ hpos X
  have hKn : ‖K‖ ≤ 1 := by
    calc
      ‖K‖ ≤ ∑ _ ∈ C, (1 : ℝ) := norm_sum_le_of_le C fun X _ ↦ hhJ X
      _ ≤ 1 := by simpa using (show (C.card : ℝ) ≤ 1 by exact_mod_cast hcard)
  have hK1 : (1 - K).PosSemidef :=
    Matrix.le_iff.mp ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hK.nonneg).mp hKn)
  let HL := ∑ X ∈ S, h.term X
  let HR := ∑ X ∈ T, h.term X
  refine ⟨HL, HR, K, ?_, ?_, ?_, hK, hK1⟩
  · have hSU : h.hamiltonian = HL + ∑ X ∈ U, h.term X :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun X : ChainSupport L 1 ↦ X.1 ⊆ A) h.term).symm
    have hTC : (∑ X ∈ U, h.term X) = HR + K :=
      (Finset.sum_filter_add_sum_filter_not U (fun X ↦ X.1 ⊆ Aᶜ) h.term).symm
    rw [hSU, hTC, add_assoc]
  · change _ ∈ ManyBody.supportedOperators _ _
    exact sum_mem fun X hX ↦ ManyBody.IsSupportedOn.mono (h.mem X) (Finset.mem_filter.mp hX).2
  · change _ ∈ ManyBody.supportedOperators _ _
    exact sum_mem fun X hX ↦ ManyBody.IsSupportedOn.mono (h.mem X) (Finset.mem_filter.mp hX).2

end TNLean.MPS.AreaLaw

end
