/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.SeparateArityCompression
import TNLean.MPS.AreaLaw.ProtocolSweepPlacement

/-!
# The printed crossing estimate for the actual compressed chain network

The participant, lifetime and per-gate distance assumptions are auxiliary
preparation conclusions, derived from the physical data in
`SharpPhysicalCompression.lean`.

The density, tensor entries, link alphabets, incidence and crossing bounds
all concern one sampled network. No degree or crossing estimate is supplied
as a premise.

Source: one-dimensional note, Part II, proof of Theorem B,
part2b_mps_protocol.tex:594–614 and order of constants:626–632.
-/

noncomputable section
namespace TNLean.MPS.AreaLaw.ChainSweep
open TNLean.Lattice TNLean.Lattice.PartyCircuit TNLean.Lattice.Compression
attribute [local instance] Classical.propDecidable

/-- Uniform sampling of the actual three-party preparation has at most
1280 crossing links at every block cut, hence satisfies the printed bound1600.
Source: Part II, thm:B, part2b_mps_protocol.tex:594–614. -/
theorem exists_uniform_sampled_network_with_prefixCrossingLinks_le_1600
    {ι : Type*} (size : ι → ℝ) (hsize : ∀ i, 2 ≤ size i)
    (length width : ι → ℕ)
    (C₀ : ∀ L, DistributedConstruction (Party (length L) (width L)))
    (n d r u v : ℕ) (C_N C_D C_K C_S : ℝ)
    (hN₀ : ∀ L, ((C₀ L).circuit.nonprivateCount : ℝ) ≤ C_N * size L ^ n)
    (hphysical₀ : ∀ L j, ((C₀ L).physicalDimension j : ℝ) ≤ C_D * size L ^ d)
    (harity₀ : ∀ L g, ((C₀ L).circuit.participants g).card ≤ 3)
    (hlifetime₀ : ∀ L j, (C₀ L).circuit.participationCount j ≤ 40)
    (hmonomial₀ : ∀ L, ∃ K : ℕ, (C₀ L).circuit.IsMonomialBounded K ∧
      (K : ℝ) ≤ C_K * size L ^ u)
    (hexpansion₀ : ∀ L, (C₀ L).circuit.IsExpansionBounded r (C_S * size L ^ v))
    (Ω : ∀ L, EuclideanSpace ℂ
      ((j : Party (length L) (width L)) → Fin ((C₀ L).physicalDimension j)))
    (hΩ : ∀ L, ‖Ω L‖ = 1) (η : ι → ℝ)
    (hpure : ∀ L, Matrix.rectangularTraceNorm
      ((C₀ L).physicalDensity - Matrix.euclideanOuterProduct (Ω L) (Ω L)) ≤ η L)
    (hgate : ∀ L (g : (C₀ L).circuit.nonprivateLocations)
      (j l : Party (length L) (width L)),
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
        (T : (j : Party (length L) (width L)) → DistributedOperatorContraction.GateLabelsAt
            (Finset.univ : Finset Gate) participants Label j →
          (DistributedOperatorContraction.SampleAt (Finset.univ : Finset Gate)
            participants j → Fin k) →
          Matrix (Fin ((C₀ L).physicalDimension j)) (Fin ((C₀ L).physicalDimension j)) ℂ),
        Matrix.rectangularTraceNorm
            (DistributedOperatorContraction.contractedOperator Finset.univ participants root
              hroot Label k c T - Matrix.euclideanOuterProduct (Ω L) (Ω L)) ≤
            size L ^ (-p) + η L ∧
          Matrix.rectangularTraceNorm
            (DistributedOperatorContraction.contractedOperator Finset.univ participants root
              hroot Label k c T - (C₀ L).physicalDensity) ≤ size L ^ (-p) ∧
          1 - η L ≤ (C₀ L).physicalDensity.trace.re ∧
          (C₀ L).physicalDensity.trace.re ≤ 1 ∧
          (∀ e : DistributedOperatorContraction.Link Finset.univ participants root,
            (Fintype.card (DistributedOperatorContraction.alphabet Finset.univ participants
              root Label k e) : ℝ) ≤ C_p * size L ^ α) ∧
          (∀ j, (incidentDistributedLinks Finset.univ participants root j).card ≤
            160) ∧
          (∀ e : DistributedOperatorContraction.Link Finset.univ participants root,
            ∀ j l, j ∈ distributedLinkParties root e.1 → l ∈ distributedLinkParties root e.1 →
              ∃ g : (C₀ L).circuit.nonprivateLocations,
                j ∈ (C₀ L).circuit.participants g ∧ l ∈ (C₀ L).circuit.participants g) ∧
          (∀ r', (prefixCrossingLinks Finset.univ participants root r').card ≤ 1280) ∧
          (∀ r', (prefixCrossingLinks Finset.univ participants root r').card ≤ 1600) := by
  have hdec (L : ι) : (fun a b : Party (length L) (width L) ↦
      Classical.propDecidable (a = b)) =
      (@instDecidableEqSum _ _ (instDecidableEqFin _) (instDecidableEqFin _)) :=
    Subsingleton.elim _ _
  obtain ⟨C_p, α, hC, hα, hfamily⟩ :=
    DistributedConstruction.exists_uniform_sampled_network_sub_pure_le_of_arity_lifetime
      size hsize (fun L ↦ Party (length L) (width L)) C₀
      3 40 n d r u v (by decide) C_N C_D C_K C_S
      hN₀ hphysical₀ harity₀ hlifetime₀ hmonomial₀ hexpansion₀ Ω
      (by intro L; rw [hdec]; exact hΩ L) η
      (by intro L; rw [hdec]; exact hpure L) p hp
  refine ⟨C_p, α, hC, hα, fun L ↦ ?_⟩
  have hmember := hfamily L
  rw [hdec] at hmember
  obtain ⟨Gate, _, _, participants, root, hroot, Label, _, k, c, T,
    hσ, herror, hlow, hhigh, hdim, hinc, hlocal⟩ := hmember
  have hdegree (j : Party (length L) (width L)) :
      (incidentDistributedLinks Finset.univ participants root j).card ≤ 160 := by
    simpa using hinc j
  have hcross (r' : ℕ) :
      (prefixCrossingLinks Finset.univ participants root r').card ≤ 1280 := by
    simpa using prefixCrossingLinks_card_le_of_originalCircuit
      Finset.univ participants root (C₀ L).circuit (hgate L) 160 hdegree hlocal r'
  exact ⟨Gate, _, _, participants, root, hroot, Label, _, k, c, T,
    hσ, herror, hlow, hhigh, hdim, hdegree, hlocal, hcross,
    fun r' ↦ (hcross r').trans (by decide)⟩

end TNLean.MPS.AreaLaw.ChainSweep
