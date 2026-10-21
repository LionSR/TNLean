/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolSweepPlacement
import TNLean.Lattice.Compression.SeparateArityCompression
import TNLean.Lattice.Compression.IdentityBondCutRank
import QICLean.Analysis.RectangularTraceNormAlgebra
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Useful columns and block cut ranks after uniform compression

For a family of actual distributed constructions, retain the resource hypotheses of
uniform compression. Assume also its preparation-derived conclusion that participants
of one original gate have block levels at distance at most two. Compression gives one
operator network per family member, with uniform constants chosen before that member.
At any member for which the total trace-norm error is less than one, select one nonzero
product-basis column. The same column, with its actual fixed-input endpoint tensors,
has the crossing-alphabet rank bound at every party cut. Normalizing it preserves these
ranks and gives the existing phase-error estimate.

At whole-block prefixes, a separate arity bound a and lifetime bound b give
degree at most 2b(a-1). The common-original-gate conclusion gives at most
8(2b(a-1)) tagged crossing links, hence any specified upper bound χ. Each actual star or
sample alphabet is bounded by the same rounded uniform dimension, giving its χ-th power as a block
cut-rank bound. Scalar physical outputs, parallel links and empty cut families remain.

This is an auxiliary consequence of compression and a derived placement conclusion.
It does not construct the physical preparation, prove original-site coordinate or
within-block estimates, or assert an MPS representation or Theorem B.

Source: the one-dimensional note, Part II, proof of Theorem B,
`part2b_mps_protocol.tex`, lines 587–615; polynomial-PEPS Theorem 5.2 and
Remark 5.3, `04-compression.tex`, lines 137–175 and 602–611; Lemma 8.1,
`07-assembly.tex`, lines 67–94.
-/

noncomputable section
open scoped BigOperators Matrix

namespace TNLean.PEPS.Approximation.DistributedOperatorContraction

open TNLean.PEPS.DependentBondNetwork

private theorem rank_flattening_normalize_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {P : V → Type*} [∀ v, Fintype (P v)]
    (ψ : EuclideanSpace ℂ ((v : V) → P v)) (hψ : ψ ≠ 0) (S : Finset V) :
    (WholeGroup.flattening (⇑(((‖ψ‖ : ℂ)⁻¹) • ψ)) S).rank =
      (WholeGroup.flattening (⇑ψ) S).rank := by
  classical
  have hc : (‖ψ‖ : ℂ)⁻¹ ≠ 0 := inv_ne_zero <| by
    exact_mod_cast (norm_ne_zero_iff.mpr hψ)
  have hscale : WholeGroup.flattening (⇑(((‖ψ‖ : ℂ)⁻¹) • ψ)) S =
      ((‖ψ‖ : ℂ)⁻¹) • WholeGroup.flattening (⇑ψ) S := by
    ext x y
    rfl
  rw [hscale]
  exact Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hc)

open Classical in
/-- A useful actual column retains the input-fixed endpoint tensors and all their
cut-rank bounds. One choice of the product-basis input works for every cut.
Source: polynomial-PEPS Lemma 8.1, `07-assembly.tex`, lines 67–94, and the
one-dimensional note, Part II, proof of Theorem B, lines 587–604. -/
theorem exists_useful_column_of_sub_pure_le
    {Party Gate : Type} [Fintype Party] [DecidableEq Party] [DecidableEq Gate]
    (gates : Finset Gate) (participants : Gate → Finset Party) (root : Gate → Party)
    (hroot : ∀ g ∈ gates, root g ∈ participants g)
    (Label : Gate → Type) [∀ g, Fintype (Label g)] (k : ℕ)
    {Out : Party → Type*} [∀ j, Fintype (Out j)] [∀ j, DecidableEq (Out j)]
    (c : (g : Gate) → Label g → ℂ)
    (T : (j : Party) → GateLabelsAt gates participants Label j →
      (SampleAt gates participants j → Fin k) → Matrix (Out j) (Out j) ℂ)
    (Ω : EuclideanSpace ℂ ((j : Party) → Out j)) (hΩ : ‖Ω‖ = 1) (ε : ℝ)
    (hσ : Matrix.rectangularTraceNorm
      (contractedOperator gates participants root hroot Label k c T -
        Matrix.euclideanOuterProduct Ω Ω) ≤ ε) (hε : ε < 1) :
    ∃ (z : (j : Party) → Out j) (ψ : EuclideanSpace ℂ ((j : Party) → Out j)),
      (∀ x, ψ x = network (src gates participants root) (tgt gates participants root)
        (alphabet gates participants root Label k)
        (fixInput (src gates participants root) (tgt gates participants root)
          (alphabet gates participants root Label k)
          (endpointTensor gates participants root hroot Label k c T) z) (fun _ ↦ 1) x) ∧
      ψ = Matrix.toEuclideanLin (contractedOperator gates participants root hroot Label k c T)
        (EuclideanSpace.single z 1) ∧
      ψ ≠ 0 ∧ ‖((‖ψ‖ : ℂ)⁻¹) • ψ‖ = 1 ∧
      (∃ θ : ℝ, ‖((‖ψ‖ : ℂ)⁻¹) • ψ - Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * ε) ∧
      ∀ S : Finset Party,
        (WholeGroup.flattening (⇑ψ) S).rank ≤
          ∏ e : {e : Link gates participants root //
            WholeGroup.IsLink (src gates participants root) (tgt gates participants root) S Sᶜ e},
            Fintype.card (alphabet gates participants root Label k e) ∧
        (WholeGroup.flattening (⇑(((‖ψ‖ : ℂ)⁻¹) • ψ)) S).rank =
          (WholeGroup.flattening (⇑ψ) S).rank := by
  classical
  let e := Fintype.equivFin ((j : Party) → Out j)
  have htrace : Matrix.traceNorm (Matrix.reindex e e
      (operatorNetworkMatrix (src gates participants root) (tgt gates participants root)
        (alphabet gates participants root Label k)
        (endpointTensor gates participants root hroot Label k c T) (fun _ ↦ 1) -
          Matrix.vecMulVec (⇑Ω) (star ⇑Ω))) ≤ ε := by
    rw [← Matrix.rectangularTraceNorm_square, Matrix.rectangularTraceNorm_reindex]
    exact hσ
  obtain ⟨z, ψ, hket, hcol, hne, hphase⟩ :=
    exists_fixInput_network_of_traceNorm_sub_pure_le
      (src gates participants root) (tgt gates participants root)
      (alphabet gates participants root Label k)
      (endpointTensor gates participants root hroot Label k c T) (fun _ ↦ 1)
      e Ω hΩ htrace hε
  have hcol' : ψ = Matrix.toEuclideanLin
      (contractedOperator gates participants root hroot Label k c T)
        (EuclideanSpace.single z 1) := hcol
  refine ⟨z, ψ, hket, hcol', hne, ?_, hphase, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg ψ), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]
  · intro S
    refine ⟨?_, rank_flattening_normalize_eq ψ hne S⟩
    have hcoords : (⇑ψ) =
        fun x ↦ contractedOperator gates participants root hroot Label k c T x z := by
      funext x
      rw [hcol', Matrix.toEuclideanLin_single_one_apply]
    rw [hcoords]
    exact rank_flattening_contractedOperator_column_le gates participants root hroot Label k c T z S

end TNLean.PEPS.Approximation.DistributedOperatorContraction

namespace TNLean.MPS.AreaLaw.ChainSweep

open TNLean.PEPS TNLean.PEPS.DependentBondNetwork
open TNLean.PEPS.PairEffect TNLean.PEPS.Approximation
open TNLean.PEPS.Approximation.DistributedOperatorContraction

private theorem card_crossing_subtype_eq_prefixCrossingLinks
    {L w : ℕ} {Gate : Type} [DecidableEq Gate]
    (gates : Finset Gate) (participants : Gate → Finset (Party L w))
    (root : Gate → Party L w) (r : ℕ) :
    let S := Finset.univ.filter fun j : Party L w ↦ partyLevel j < r
    Fintype.card {e : Link gates participants root //
      WholeGroup.IsLink (src gates participants root) (tgt gates participants root) S Sᶜ e} =
      (prefixCrossingLinks gates participants root r).card := by
  classical
  dsimp only
  apply Fintype.card_of_subtype
  intro e
  simp only [prefixCrossingLinks, Finset.mem_filter, Finset.mem_univ, true_and,
    WholeGroup.IsLink, Finset.mem_compl, not_lt]
  tauto

open Classical in
/-- Uniform compression followed by one useful column and its normalized block cut ranks.
The per-original-gate distance hypothesis is an auxiliary preparation conclusion. All
resource and density hypotheses are those of uniform compression, with separate
arity and lifetime bounds a and b, and a numerical upper bound χ for the derived
crossings. Smallness is required only of the selected member, after
the uniform constants have been chosen.

Source: the one-dimensional note, Part II, proof of Theorem B, lines 587–615;
polynomial-PEPS Theorem 5.2, Remark 5.3 and Lemma 8.1. -/
theorem exists_uniform_sampled_block_column
    {ι : Type*} (size : ι → ℝ) (hsize : ∀ i, 2 ≤ size i)
    (length width : ι → ℕ)
    (C₀ : ∀ L, DistributedConstruction (Party (length L) (width L)))
    (a b χ : ℕ) (hab : a ≤ b) (hχ : 8 * (2 * b * (a - 1)) ≤ χ)
    (n d r u v : ℕ) (C_N C_D C_K C_S : ℝ)
    (hN₀ : ∀ L, ((C₀ L).circuit.nonprivateCount : ℝ) ≤ C_N * size L ^ n)
    (hphysical₀ : ∀ L j, ((C₀ L).physicalDimension j : ℝ) ≤ C_D * size L ^ d)
    (harity₀ : ∀ L g, ((C₀ L).circuit.participants g).card ≤ a)
    (hlifetime₀ : ∀ L j, (C₀ L).circuit.participationCount j ≤ b)
    (hmonomial₀ : ∀ L, ∃ K : ℕ, (C₀ L).circuit.IsMonomialBounded K ∧
      (K : ℝ) ≤ C_K * size L ^ u)
    (hexpansion₀ : ∀ L, (C₀ L).circuit.IsExpansionBounded r (C_S * size L ^ v))
    (Ω : ∀ L, EuclideanSpace ℂ
      ((j : Party (length L) (width L)) → Fin ((C₀ L).physicalDimension j)))
    (hΩ : ∀ L, ‖Ω L‖ = 1) (η : ι → ℝ)
    (hpure : ∀ L, Matrix.rectangularTraceNorm
      ((C₀ L).physicalDensity - Matrix.euclideanOuterProduct (Ω L) (Ω L)) ≤ η L)
    (hgate : ∀ L (g : (C₀ L).circuit.nonprivateLocations) (j l : Party (length L) (width L)),
      j ∈ (C₀ L).circuit.participants g → l ∈ (C₀ L).circuit.participants g →
        Nat.dist (partyLevel j) (partyLevel l) ≤ 2)
    (p : ℝ) (hp : 0 < p) :
    ∃ (C_p : ℝ) (α : ℕ), 0 ≤ C_p ∧ 0 < α ∧ ∀ L,
      ∃ (Gate : Type) (_ : Fintype Gate) (_ : DecidableEq Gate)
        (participants : Gate → Finset (Party (length L) (width L)))
        (root : Gate → Party (length L) (width L))
        (hroot : ∀ g ∈ (Finset.univ : Finset Gate), root g ∈ participants g)
        (Label : Gate → Type) (_ : ∀ g, Fintype (Label g)) (k : ℕ)
        (c : (g : Gate) → Label g → ℂ)
        (T : (j : Party (length L) (width L)) → GateLabelsAt
            (Finset.univ : Finset Gate) participants Label j →
          (SampleAt (Finset.univ : Finset Gate) participants j → Fin k) →
          Matrix (Fin ((C₀ L).physicalDimension j)) (Fin ((C₀ L).physicalDimension j)) ℂ),
        Matrix.rectangularTraceNorm
            (contractedOperator Finset.univ participants root hroot Label k c T -
              Matrix.euclideanOuterProduct (Ω L) (Ω L)) ≤ size L ^ (-p) + η L ∧
        Matrix.rectangularTraceNorm
            (contractedOperator Finset.univ participants root hroot Label k c T -
              (C₀ L).physicalDensity) ≤ size L ^ (-p) ∧
        1 - η L ≤ (C₀ L).physicalDensity.trace.re ∧
        (C₀ L).physicalDensity.trace.re ≤ 1 ∧
        (∀ e : Link Finset.univ participants root,
          (Fintype.card (alphabet Finset.univ participants root Label k e) : ℝ) ≤
            C_p * size L ^ α) ∧
        (∀ j, (incidentDistributedLinks Finset.univ participants root j).card ≤ (2 * b * (a - 1))) ∧
        (∀ e : Link Finset.univ participants root,
          ∀ j l, j ∈ distributedLinkParties root e.1 → l ∈ distributedLinkParties root e.1 →
            ∃ g : (C₀ L).circuit.nonprivateLocations,
              j ∈ (C₀ L).circuit.participants g ∧ l ∈ (C₀ L).circuit.participants g) ∧
        (∀ r', (prefixCrossingLinks Finset.univ participants root r').card ≤ χ) ∧
        (∀ e : Link Finset.univ participants root,
          Fintype.card (alphabet Finset.univ participants root Label k e) ≤
            max 1 ⌈C_p * size L ^ α⌉₊) ∧
        (size L ^ (-p) + η L < 1 →
          ∃ (z : (j : Party (length L) (width L)) → Fin ((C₀ L).physicalDimension j))
            (ψ : EuclideanSpace ℂ
              ((j : Party (length L) (width L)) → Fin ((C₀ L).physicalDimension j))),
            (∀ x, ψ x = network (src Finset.univ participants root)
              (tgt Finset.univ participants root) (alphabet Finset.univ participants root Label k)
              (fixInput (src Finset.univ participants root) (tgt Finset.univ participants root)
                (alphabet Finset.univ participants root Label k)
                (endpointTensor Finset.univ participants root hroot Label k c T) z)
              (fun _ ↦ 1) x) ∧
            ψ = Matrix.toEuclideanLin
              (contractedOperator Finset.univ participants root hroot Label k c T)
              (EuclideanSpace.single z 1) ∧
            ψ ≠ 0 ∧ ‖((‖ψ‖ : ℂ)⁻¹) • ψ‖ = 1 ∧
            (∃ θ : ℝ, ‖((‖ψ‖ : ℂ)⁻¹) • ψ - Complex.exp (θ * Complex.I) • Ω L‖ ≤
              2 * (size L ^ (-p) + η L)) ∧
            ∀ r' : ℕ,
              let S := Finset.univ.filter fun j : Party (length L) (width L) ↦ partyLevel j < r'
              (WholeGroup.flattening (⇑ψ) S).rank ≤
                ∏ e : {e : Link Finset.univ participants root //
                  WholeGroup.IsLink (src Finset.univ participants root)
                    (tgt Finset.univ participants root) S Sᶜ e},
                  Fintype.card (alphabet Finset.univ participants root Label k e) ∧
              (WholeGroup.flattening (⇑(((‖ψ‖ : ℂ)⁻¹) • ψ)) S).rank =
                (WholeGroup.flattening (⇑ψ) S).rank ∧
              (∏ e : {e : Link Finset.univ participants root //
                WholeGroup.IsLink (src Finset.univ participants root)
                  (tgt Finset.univ participants root) S Sᶜ e},
                Fintype.card (alphabet Finset.univ participants root Label k e)) ≤
                (max 1 ⌈C_p * size L ^ α⌉₊) ^ χ ∧
              (WholeGroup.flattening (⇑(((‖ψ‖ : ℂ)⁻¹) • ψ)) S).rank ≤
                (max 1 ⌈C_p * size L ^ α⌉₊) ^ χ) := by
  have hdec (L : ι) : (fun a b : Party (length L) (width L) ↦
      Classical.propDecidable (a = b)) =
      (@instDecidableEqSum _ _ (instDecidableEqFin _) (instDecidableEqFin _)) :=
    Subsingleton.elim _ _
  classical
  have hcompression :=
    DistributedConstruction.exists_uniform_sampled_network_sub_pure_le_of_arity_lifetime
      size hsize
      (fun L ↦ Party (length L) (width L)) C₀ a b n d r u v hab C_N C_D C_K C_S
      hN₀ hphysical₀ harity₀ hlifetime₀ hmonomial₀ hexpansion₀ Ω
      (by intro L; rw [hdec]; exact hΩ L) η
      (by intro L; rw [hdec]; exact hpure L) p hp
  obtain ⟨C_p, α, hC, hα, hfamily⟩ := hcompression
  refine ⟨C_p, α, hC, hα, fun L ↦ ?_⟩
  have hmember := hfamily L
  rw [hdec] at hmember
  obtain ⟨Gate, _, _, participants, root, hroot, Label, _, k, c, T,
    hσ, herror, hlow, hhigh, hdim, hinc, hcommon⟩ := hmember
  have hdegree : ∀ j,
      (incidentDistributedLinks Finset.univ participants root j).card ≤ 2 * b * (a - 1) := by
    simpa using hinc
  have hcross : ∀ r', (prefixCrossingLinks Finset.univ participants root r').card ≤ χ := by
    intro r'
    exact (prefixCrossingLinks_card_le_of_originalCircuit
      Finset.univ participants root (C₀ L).circuit (hgate L)
      (2 * b * (a - 1)) hdegree hcommon r').trans hχ
  let D : ℕ := max 1 ⌈C_p * size L ^ α⌉₊
  have hD : 1 ≤ D := le_max_left _ _
  have halphabet : ∀ e : Link Finset.univ participants root,
      Fintype.card (alphabet Finset.univ participants root Label k e) ≤ D := by
    intro e
    apply (Nat.cast_le (α := ℝ)).mp
    calc
      (Fintype.card (alphabet Finset.univ participants root Label k e) : ℝ)
          ≤ C_p * size L ^ α := hdim e
      _ ≤ (⌈C_p * size L ^ α⌉₊ : ℕ) := Nat.le_ceil _
      _ ≤ (D : ℝ) := by exact_mod_cast (le_max_right 1 ⌈C_p * size L ^ α⌉₊)
  refine ⟨Gate, inferInstance, inferInstance, participants, root, hroot, Label, inferInstance,
    k, c, T, hσ, herror, hlow, hhigh, hdim, hdegree, hcommon, hcross, halphabet, ?_⟩
  intro hsmall
  obtain ⟨z, ψ, hket, hcol, hne, hnorm, hphase, hrank⟩ :=
    exists_useful_column_of_sub_pure_le Finset.univ participants root hroot Label k c T
      (Ω L) (hΩ L) (size L ^ (-p) + η L) hσ hsmall
  refine ⟨z, ψ, hket, hcol, hne, hnorm, hphase, ?_⟩
  intro r'
  let S := Finset.univ.filter fun j : Party (length L) (width L) ↦ partyLevel j < r'
  let Ecut := {e : Link Finset.univ participants root //
    WholeGroup.IsLink (src Finset.univ participants root)
      (tgt Finset.univ participants root) S Sᶜ e}
  have hcard : Fintype.card Ecut ≤ χ := by
    rw [card_crossing_subtype_eq_prefixCrossingLinks Finset.univ participants root r']
    exact hcross r'
  have hproduct : (∏ e : Ecut,
      Fintype.card (alphabet Finset.univ participants root Label k e)) ≤ D ^ χ := by
    calc
      _ ≤ ∏ _e : Ecut, D := Finset.prod_le_prod fun e _ ↦ halphabet e.val
      _ = D ^ Fintype.card Ecut := by simp
      _ ≤ D ^ χ := pow_le_pow_right' hD hcard
  dsimp only [D, Ecut] at hproduct
  exact ⟨(hrank S).1, (hrank S).2, hproduct, by
    rw [(hrank S).2]
    exact (hrank S).1.trans hproduct⟩

end TNLean.MPS.AreaLaw.ChainSweep
