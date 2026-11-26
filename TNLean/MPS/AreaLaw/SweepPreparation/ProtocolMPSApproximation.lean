/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SweepPreparation.ProtocolPhysicalPreparation
import TNLean.MPS.AreaLaw.SweepPreparation.ProtocolCutCoordinates
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import QICLean.ManyBody.Hamiltonian.GroundSpace
import TNLean.MPS.AreaLaw.SweepPreparation.ProtocolSweepPlacement
import TNLean.Network.SampledApproximation.SeparateArityCompression
import TNLean.Network.DistributedContraction.IdentityBondCutRank
import QICLean.Analysis.TraceNorm.RectangularTraceNormAlgebra
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Physical matrix product state approximation by the chain-sweep protocol

The physical assumptions construct one uniform family containing every
admissible sufficiently large Hamiltonian and ground vector. Compression
selects one actual nonzero product-basis column before all cuts. Its
normalization, inverse main-coordinate image and matrix product
representation refer to the same vector throughout. The remaining finite
lengths have exact matrix product representations and are absorbed into the
same uniform polynomial prefactor.

**Scope restriction (contiguous chains):** The sites are Fin L, exactly the
chain in Theorem B. See
`docs/paper-gaps/tnlean_one_dimensional_connected_domain_scope.tex`.

**Local fix (retired auxiliary registers):** Only main registers are physical;
all auxiliary copies remain private at their actual owners. See
`docs/paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex`.

Source: the one-dimensional note, Part 0, `thm:B`, lines 229–238, and Part II,
proof of `thm:B`, lines 574–615. The crossing bound is at most 1280,
and hence satisfies the printed upper bound 1600 used in the bond estimate.

It also contains the following results.

* `TNLean.Network.DistributedOperatorContraction.exists_useful_column_of_sub_pure_le`,
  `TNLean.MPS.AreaLaw.ChainSweep.exists_uniform_sampled_block_column`: useful columns and block cut
  ranks after uniform compression.
-/

section CompressedBlockColumn

/-!
## Useful columns and block cut ranks after uniform compression

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

namespace TNLean.Network.DistributedOperatorContraction

open TNLean.Network.DependentBondNetwork

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

end TNLean.Network.DistributedOperatorContraction

namespace TNLean.MPS.AreaLaw.ChainSweep

open QuantumCircuit.Party TNLean.Network TNLean.Network.DependentBondNetwork
open TNLean.Network.DistributedOperatorContraction

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
    (X : ∀ L, Party (length L) (width L) → Type) [∀ L j, Fintype (X L j)]
    [∀ L j, DecidableEq (X L j)] (physicalDim : ∀ L, Party (length L) (width L) → ℕ)
    (V : ∀ L, Party (length L) (width L) → Type) [∀ L j, Fintype (V L j)]
    [∀ L j, DecidableEq (V L j)]
    (C₀ : ∀ L, DistributedConstruction (Party (length L) (width L)) (X L) (physicalDim L) (V L))
    (a b χ : ℕ) (hab : a ≤ b) (hχ : 8 * (2 * b * (a - 1)) ≤ χ)
    (n d r u v : ℕ) (C_N C_D C_K C_S : ℝ)
    (hN₀ : ∀ L, ((C₀ L).circuit.nonprivateCount : ℝ) ≤ C_N * size L ^ n)
    (hphysical₀ : ∀ L j, (physicalDim L j : ℝ) ≤ C_D * size L ^ d)
    (harity₀ : ∀ L g, ((C₀ L).circuit.participants g).card ≤ a)
    (hlifetime₀ : ∀ L j, (C₀ L).circuit.participation j ≤ b)
    (hmonomial₀ : ∀ L, ∃ K : ℕ, (C₀ L).circuit.IsMonomialBounded K ∧
      (K : ℝ) ≤ C_K * size L ^ u)
    (hexpansion₀ : ∀ L, (C₀ L).circuit.IsExpansionBounded r (C_S * size L ^ v))
    (Ω : ∀ L, EuclideanSpace ℂ
      ((j : Party (length L) (width L)) → Fin (physicalDim L j)))
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
          Matrix (Fin (physicalDim L j)) (Fin (physicalDim L j)) ℂ),
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
          ∃ (z : (j : Party (length L) (width L)) → Fin (physicalDim L j))
            (ψ : EuclideanSpace ℂ
              ((j : Party (length L) (width L)) → Fin (physicalDim L j))),
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
  classical
  have hcompression :=
    DistributedConstruction.exists_uniform_sampled_network_sub_pure_le_of_arity_lifetime
      size hsize (fun L ↦ Party (length L) (width L)) X physicalDim V C₀ a b n d r u v hab
      C_N C_D C_K C_S hN₀ hphysical₀ harity₀ hlifetime₀ hmonomial₀ hexpansion₀ Ω hΩ η hpure p hp
  obtain ⟨C_p, α, hC, hα, hfamily⟩ := hcompression
  refine ⟨C_p, α, hC, hα, fun L ↦ ?_⟩
  have hmember := hfamily L
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

end

end CompressedBlockColumn

section ProtocolMPSApproximation

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.MPS.AreaLaw.ChainSweep

open QuantumCircuit.Party

open ManyBody (IsGapped groundSpace ChainInteraction)
open ManyBody (cutMatrix)

/-- The protocol's density error permits column extraction and the source's
final phase error for every L≥2. Source: Part II, `thm:B`, lines 587–593. -/
private theorem protocol_error_bounds {L : ℕ} (hL : 2 ≤ L) :
    (L : ℝ) ^ (-5 : ℝ) + 52 * (L : ℝ) ^ (-11 : ℤ) < 1 ∧
      2 * ((L : ℝ) ^ (-5 : ℝ) + 52 * (L : ℝ) ^ (-11 : ℤ)) ≤ 1 / (L : ℝ) := by
  let x : ℝ := L
  have hx2 : 2 ≤ x := by
    change (2 : ℝ) ≤ (L : ℝ)
    exact_mod_cast hL
  have hx0 : 0 < x := by linarith
  have h6 : (52 : ℝ) ≤ x ^ (6 : ℕ) := by
    calc
      52 ≤ (2 : ℝ) ^ (6 : ℕ) := by norm_num
      _ ≤ x ^ (6 : ℕ) := pow_le_pow_left₀ (by norm_num) hx2 _
  have h5 : (32 : ℝ) ≤ x ^ (5 : ℕ) := by
    calc
      32 = (2 : ℝ) ^ (5 : ℕ) := by norm_num
      _ ≤ x ^ (5 : ℕ) := pow_le_pow_left₀ (by norm_num) hx2 _
  have h4 : (4 : ℝ) ≤ x ^ (4 : ℕ) := by
    calc
      4 ≤ (2 : ℝ) ^ (4 : ℕ) := by norm_num
      _ ≤ x ^ (4 : ℕ) := pow_le_pow_left₀ (by norm_num) hx2 _
  have hη : 52 / x ^ (11 : ℕ) ≤ 1 / x ^ (5 : ℕ) := by
    apply (div_le_div_iff₀ (pow_pos hx0 _) (pow_pos hx0 _)).2
    calc
      52 * x ^ (5 : ℕ) ≤ x ^ (6 : ℕ) * x ^ (5 : ℕ) :=
        mul_le_mul_of_nonneg_right h6 (pow_nonneg hx0.le _)
      _ = 1 * x ^ (11 : ℕ) := by ring
  have hε : 1 / x ^ (5 : ℕ) + 52 / x ^ (11 : ℕ) ≤ 2 / x ^ (5 : ℕ) := by
    simp only [div_eq_mul_inv, one_mul] at hη ⊢
    linarith
  have hε2 : 2 * (1 / x ^ (5 : ℕ) + 52 / x ^ (11 : ℕ)) ≤ 4 / x ^ (5 : ℕ) := by
    simp only [div_eq_mul_inv, one_mul] at hη ⊢
    linarith
  have hsmall : 2 / x ^ (5 : ℕ) < 1 :=
    (div_lt_one (pow_pos hx0 _)).2 (by linarith)
  have hfinal : 4 / x ^ (5 : ℕ) ≤ 1 / x := by
    apply (div_le_div_iff₀ (pow_pos hx0 _) hx0).2
    simpa only [one_mul, pow_succ] using mul_le_mul_of_nonneg_right h4 hx0.le
  have hrpow : x ^ (-5 : ℝ) = 1 / x ^ (5 : ℕ) := by
    simpa only [Real.rpow_ofNat, one_div] using Real.rpow_neg hx0.le (5 : ℝ)
  have hzpow : x ^ (-11 : ℤ) = 1 / x ^ (11 : ℕ) := by
    simp only [zpow_neg, zpow_ofNat, one_div]
  change x ^ (-5 : ℝ) + 52 * x ^ (-11 : ℤ) < 1 ∧
    2 * (x ^ (-5 : ℝ) + 52 * x ^ (-11 : ℤ)) ≤ 1 / x
  rw [hrpow, hzpow]
  simpa only [mul_one_div] using ⟨hε.trans_lt hsmall, hε2.trans hfinal⟩

/-- The literal inverse main-coordinate map preserves the phase-error norm.
Source: Part II, `thm:B`, block-to-site passage at lines 605–615. -/
private theorem norm_mainPullback_sub (L w q : ℕ)
    (u : EuclideanSpace ℂ
      ((p : Party L w) → Fin (physicalDimension L w q p)))
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (c : ℂ) :
    ‖WithLp.toLp 2 (fun x ↦ u (mainConfigurationEquiv L w q x)) - c • Ω‖ =
      ‖u - c • LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (mainConfigurationEquiv L w q) Ω‖ := by
  let E := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (mainConfigurationEquiv L w q)
  have hvector :
      E (WithLp.toLp 2 (fun x ↦ u (mainConfigurationEquiv L w q x)) - c • Ω) =
        u - c • E Ω := by
    rw [map_sub, map_smul]
    congr 1
    ext x
    change u ((mainConfigurationEquiv L w q)
      ((mainConfigurationEquiv L w q).symm x)) = u x
    rw [Equiv.apply_symm_apply]
  calc
    _ = ‖E (WithLp.toLp 2 (fun x ↦ u (mainConfigurationEquiv L w q x)) - c • Ω)‖ :=
      (E.norm_map _).symm
    _ = _ := congrArg norm hvector

/-- All states on chains of length at most N have an exact representation
with bond at most q^N. Source: Part II, `thm:B`, finite lengths at lines 575–578. -/
private theorem exact_isOpenMPS_of_length_le {L q N : ℕ}
    (hq : 1 ≤ q) (hLN : L ≤ N) (Ω : EuclideanSpace ℂ (Fin L → Fin q)) :
    IsOpenMPS L q (q ^ N) (fun x ↦ Ω x) := by
  classical
  apply isOpenMPS_of_internal_cutMatrix_rank_le
  intro k _ _
  calc
    (cutMatrix (leftBlock L k) Ω).rank ≤
        Fintype.card ((v : {v : Fin L // v ∈ leftBlock L k}) → Fin q) :=
      Matrix.rank_le_card_height _
    _ = q ^ Fintype.card {v : Fin L // v ∈ leftBlock L k} := by simp
    _ ≤ q ^ N := Nat.pow_le_pow_right (by omega : 0 < q)
      ((Fintype.card_subtype_le _).trans (by simpa using hLN))

/-- Theorem B by the physical chain-sweep protocol. The polynomial constants
are chosen before the length, Hamiltonian and ground state. The approximant
is a unit, nonzero open-boundary MPS, with the source's phase error.
Source: the one-dimensional note, Part 0, `thm:B`, lines 229–238;
Part II, proof of `thm:B`, lines 574–615. -/
theorem exists_protocol_isOpenMPS_norm_sub_phase_le
    (q : ℕ) (hq : 1 ≤ q) (R : ℕ) (J Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ (C : ℝ) (n : ℕ), 0 < C ∧ 0 < n ∧
      ∀ (L : ℕ), 2 ≤ L →
        ∀ (h : ChainInteraction L q R) (_ : ∀ X, (h.term X).IsHermitian) (_ : ∀ X, ‖h.term X‖ ≤ J)
          (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (E₀ : ℝ),
          ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
          groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
            ∃ (B : ℕ) (Φ : EuclideanSpace ℂ (Fin L → Fin q)),
              ‖Φ‖ = 1 ∧ Φ ≠ 0 ∧ IsOpenMPS L q B (fun x ↦ Φ x) ∧
                (B : ℝ) ≤ C * (L : ℝ) ^ n ∧
                ∃ θ : ℝ, ‖Φ - Complex.exp (θ * Complex.I) • Ω‖ ≤ 1 / (L : ℝ) := by
  classical
  obtain ⟨D, K, s, L₀, hL₀, hD, _hK, hfamily⟩ :=
    exists_uniform_preparation_family q hq R J Δ hΔ
  let ι := {a : Σ L : ℕ, ManyBody.ChainInteraction L q R ×
      EuclideanSpace ℂ (Fin L → Fin q) × ℝ //
    L₀ ≤ a.1 ∧ (∀ X, (a.2.1.term X).IsHermitian) ∧ (∀ X, ‖a.2.1.term X‖ ≤ J) ∧ ‖a.2.2.1‖ = 1 ∧
        IsGapped a.2.1.hamiltonian a.2.2.2 Δ ∧
      groundSpace a.2.1.hamiltonian a.2.2.2 = Submodule.span ℂ {a.2.2.1}}
  let length := fun i : ι ↦ i.val.1
  let width := fun i : ι ↦ ⌈D * Real.log (length i : ℝ)⌉₊
  let ground := fun i : ι ↦ i.val.2.2.1
  obtain ⟨φ, hφ, circuits, hsize, _hinput, hcount, hphysical, harity, hlifetime,
      hmonomial, hexpansion, htarget, hdensity, hgate, _houter, hwidths⟩ := hfamily
  let C₀ := fun i : ι ↦ preparationConstruction (φ i) (hφ i) (circuits i)
  let target := fun i : ι ↦ LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (mainConfigurationEquiv (length i) (width i) q) (ground i)
  obtain ⟨Cp, α, hCp, hα, hnetwork⟩ := exists_uniform_sampled_block_column
    (fun i : ι ↦ (length i : ℝ)) hsize length width _
    (fun i ↦ physicalDimension (length i) (width i) q) _ C₀
    3 40 1600 (by decide) (by decide)
    1 s 1 0 0 2 K 1 1 hcount hphysical harity hlifetime hmonomial hexpansion
    target htarget (fun i : ι ↦ 52 * (length i : ℝ) ^ (-11 : ℤ))
    hdensity hgate 5 (by norm_num)
  let n := max 1 (⌈40 * D * Real.log (q : ℝ)⌉₊ + 1600 * α)
  let Clarge := (q : ℝ) ^ 40 * (Cp + 1) ^ 1600
  let Cfinal := max Clarge ((q : ℝ) ^ L₀)
  have hClarge : 0 < Clarge :=
    mul_pos (pow_pos (by exact_mod_cast (show 0 < q by omega)) _)
      (pow_pos (by linarith) _)
  have hCfinal : 0 < Cfinal := hClarge.trans_le (le_max_left _ _)
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  refine ⟨Cfinal, n, hCfinal, hn, ?_⟩
  intro L hL h hh hhJ Ω E₀ hΩ hgap hspan
  have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  by_cases hlarge : L₀ ≤ L
  · let i : ι := ⟨⟨L, h, Ω, E₀⟩, hlarge, hh, hhJ, hΩ, hgap, hspan⟩
    let w := ⌈D * Real.log (L : ℝ)⌉₊
    have herrors := protocol_error_bounds hL
    obtain ⟨Gate, hGateFinite, hGateDecidable, participants, root, hroot,
        Label, hLabelFinite, k, c, T, _hσ, _hσρ, _hρlow, _hρhigh,
        _halphabetReal, _hdegree, _hcommonGate, _hcongestion, _halphabetNat,
        hcolumn⟩ := hnetwork i
    let := hGateFinite
    let := hGateDecidable
    let := hLabelFinite
    obtain ⟨z, ψ, _hnetworkCoefficient, _hactualColumn, _hψ,
        hunit, ⟨θ, hphase⟩, hranks⟩ := hcolumn herrors.1
    let u : EuclideanSpace ℂ
        ((p : Party L w) → Fin (physicalDimension L w q p)) :=
      ((‖ψ‖ : ℂ)⁻¹) • ψ
    let Φ : EuclideanSpace ℂ (Fin L → Fin q) :=
      WithLp.toLp 2 (fun x ↦ u (mainConfigurationEquiv L w q x))
    let B := q ^ (40 * w) * (max 1 ⌈Cp * (L : ℝ) ^ α⌉₊) ^ 1600
    have hmargin : 60 * w ≤ L := by
      have hm := (hwidths i).2
      change 3 * (20 * w) ≤ L at hm
      omega
    have hprefix (r : ℕ) (_hr : 0 < r) (_hrm : r ≤ stageCount L w) :
        (TNLean.Network.WholeGroup.flattening (fun y ↦ u y)
          (Finset.univ.filter fun p : Party L w ↦ partyLevel p < r)).rank ≤
            (max 1 ⌈Cp * (L : ℝ) ^ α⌉₊) ^ 1600 := by
      simpa only [u, C₀, preparationConstruction, length, width, i] using! (hranks r).2.2.2
    obtain ⟨hΦnorm, _hΦcuts, hΦmps, _hn, hB⟩ :=
      isOpenMPS_of_polynomial_partyPrefix_bounds 1600 hq hD hCp hα hL
        (show w = ⌈D * Real.log (L : ℝ)⌉₊ from rfl) hmargin u hunit hprefix
    have hΦne : Φ ≠ 0 := by
      apply norm_ne_zero_iff.mp
      rw [hΦnorm]
      exact one_ne_zero
    refine ⟨B, Φ, hΦnorm, hΦne, hΦmps, ?_, θ, ?_⟩
    · exact hB.trans (mul_le_mul_of_nonneg_right (le_max_left Clarge _)
        (pow_nonneg (by positivity : (0 : ℝ) ≤ L) n))
    · calc
        _ = ‖u - Complex.exp (θ * Complex.I) •
            LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
              (mainConfigurationEquiv L w q) Ω‖ :=
          norm_mainPullback_sub L w q u Ω (Complex.exp (θ * Complex.I))
        _ ≤ 2 * ((L : ℝ) ^ (-5 : ℝ) + 52 * (L : ℝ) ^ (-11 : ℤ)) := hphase
        _ ≤ 1 / (L : ℝ) := herrors.2
  · have hsmall : L ≤ L₀ := by omega
    have hmps := exact_isOpenMPS_of_length_le hq hsmall Ω
    have hΩne : Ω ≠ 0 := by
      apply norm_ne_zero_iff.mp
      rw [hΩ]
      exact one_ne_zero
    refine ⟨q ^ L₀, Ω, hΩ, hΩne, hmps, ?_, 0, ?_⟩
    · calc
        ((q ^ L₀ : ℕ) : ℝ) = (q : ℝ) ^ L₀ := by simp only [Nat.cast_pow]
        _ ≤ Cfinal := le_max_right _ _
        _ ≤ Cfinal * (L : ℝ) ^ n :=
          le_mul_of_one_le_right hCfinal.le (one_le_pow₀ hLreal)
    · simp

end TNLean.MPS.AreaLaw.ChainSweep

end

end ProtocolMPSApproximation
