/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularControlledBoundaryFactor
import TNLean.PEPS.TorusComplementCycleWords
import TNLean.PEPS.TorusRegionLiftCoordinates
import TNLean.PEPS.TorusRegionRealization

/-!
# A common canonical cut factor from actual torus lift and winding data

The actual simply connected closed-cell realization supplies an integer lift,
which makes every region cycle residual trivial for commuting closure pairs.
Fixed actual complementary loops with the winding of the native boundary
routes supply the relative-word identities. Thus one complementary physical
unitary, chosen before all sectors and coefficients, separates a common normalized
maximally entangled factor and a common normalized region ancillary vector from
every coherent sum of the actual canonical cut contractions.

**Scope restriction (supplied complementary winding loops):** The torus graph
has width and height at least three, and the actual closed-cell region realization
is simply connected. Two spanning trees, boundary numbering, and complementary
loops with matching winding are supplied. Existence of these loops for the paper's
disk geometry and transport to the original physical site tensors remain separate;
see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`. No group-valued flatness,
relative-word identity, Gram formula, or tensor factorization is assumed.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807,
`Papers/1001.3807/paper_v3.tex`, lines 1935–1990 and 2043–2072.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

/-- One physical unitary and two fixed normalized factors work for all coherent
finite sums of actual canonical torus cut contractions. Region flatness follows from actual
simple connectedness, and complement relative-word identities follow from the
supplied fixed geometric loops.
Source: SCP10, Theorem 6.9 argument, lines 1935–1990 and 2043–2072. -/
theorem exists_unitary_torusControlledBoundaryFactor_of_isSimplyConnected_and_winding
    (R : Finset X) (hSC : IsSimplyConnected (torusRegionRealization R))
    (TR : SimpleGraph {v : X // v ∈ R})
    (TS : SimpleGraph {v : X // v ∈ Finset.univ \ R})
    [DecidableRel TR.Adj] [DecidableRel TS.Adj]
    (hTR : TR ≤ (Γₜ).induce (R : Set X))
    (hTS : TS ≤ (Γₜ).induce ((Finset.univ \ R : Finset X) : Set X))
    (htreeR : TR.IsTree) (htreeS : TS.IsTree)
    (oR : {v : X // v ∈ R}) (oS : {v : X // v ∈ Finset.univ \ R})
    {n : ℕ} (e : {f : Edge Γₜ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1))
    (p : {f : Edge Γₜ // IsRegionBoundaryEdge R f} →
      ((Γₜ).induce ((Finset.univ \ R : Finset X) : Set X)).Walk oS oS)
    (hwind : ∀ f, torusWalkWinding
        ((p f).map (SimpleGraph.Embedding.induce
          ((Finset.univ \ R : Finset X) : Set X)).toHom) =
      torusWalkWinding (torusBoundaryTreeRoute R TR TS hTR hTS htreeR htreeS oS (e.symm 0) f)) :
    ∃ U : Matrix (RegionHalfEdgeConfig (Γ := Γₜ) G (Finset.univ \ R))
        (RegionHalfEdgeConfig (Γ := Γₜ) G (Finset.univ \ R)) ℂ,
      U ∈ Matrix.unitaryGroup (RegionHalfEdgeConfig (Γ := Γₜ) G (Finset.univ \ R)) ℂ ∧
      ∀ (I : Type*) [Fintype I] (pairs : I → G × G)
        (_hcomm : ∀ i, Commute (pairs i).1 (pairs i).2) (μ : I → ℂ)
        (cR : RegularRegionCoordinates (Γ := Γₜ) (G := G) R TR oR)
        (cS : RegularRegionCoordinates (Γ := Γₜ) (G := G) (Finset.univ \ R) TS oS),
        let A := fun j => cR.1 (e.symm j)
        let B := fun j => cS.1 (regionBoundaryEdgeComplEquiv (G := Γₜ) R (e.symm j))
        (∑ i, μ i * ∑ θ : {f : Edge Γₜ // IsRegionBoundaryEdge R f} → G,
          regularProjectorTwistedRegionMatrix R (torusClosureEdgeAssignment (pairs i).1 (pairs i).2)
              ((regularRegionCoordinatesEquiv R TR hTR htreeR oR).symm cR) θ *
            (U * regularProjectorTwistedRegionMatrix (Finset.univ \ R)
                (torusClosureEdgeAssignment (pairs i).1 (pairs i).2))
              ((regularRegionCoordinatesEquiv (Finset.univ \ R) TS hTS htreeS oS).symm cS)
              (fun f => θ ((regionBoundaryEdgeComplEquiv (G := Γₜ) R).symm f))) =
          Matrix.omegaVec (Fintype.card (Fin n → G))
            (Fintype.equivFin (Fin n → G) (regularBoundaryRelativeEquiv n A).2,
              Fintype.equivFin (Fin n → G) (regularBoundaryRelativeEquiv n B).2) *
          regularReferenceRegionAncilla (Γ := Γₜ) (G := G) R TR oR (A 0, cR.2) *
          ((Real.sqrt (Fintype.card (Fin n → G) : ℝ) : ℂ) *
            (Real.sqrt (Fintype.card (G ×
              (({f : Edge Γₜ // f.1.1 ∈ R ∧ f.1.2 ∈ R} → G) ×
                RootedGroupLabels (G := G) oR)) : ℝ) : ℂ) *
            ((Fintype.card G : ℂ)⁻¹ ^ R.card *
              (Fintype.card G : ℂ)⁻¹ ^ (Finset.univ \ R).card) *
            ∑ i, μ i * ∑ x : G, if cS.2.2.2 = (fun f => x *
              regularRegionTreeCycleResidual (Finset.univ \ R) TS hTS htreeS oS
                (torusClosureEdgeAssignment (pairs i).1 (pairs i).2) f * x⁻¹)
              then 1 else 0) := by
  classical
  obtain ⟨L, hL⟩ := exists_isTorusRegionIntegerLift_of_isSimplyConnected R hSC oR
  let S := Finset.univ \ R
  let U := regularComplementWalkControlMatrix (G := G) R TS hTS htreeS oS
    (fun _ => oS) (fun _ => oS) p
  refine ⟨U, regularComplementWalkControlMatrix_mem_unitaryGroup
    R TS hTS htreeS oS (fun _ => oS) (fun _ => oS) p, ?_⟩
  intro I _ pairs hcomm μ cR cS
  have hflat i := regularRegionTreeCycleResidual_torusClosure_eq_one hL TR hTR htreeR oR
    (pairs i).1 (pairs i).2 (hcomm i)
  have hrelative i := regularRegionCycleWord_eval_torusClosure_of_winding_eq R TR TS hTR hTS
    htreeR htreeS oR oS (e.symm 0) p hwind (pairs i).1 (pairs i).2 (hcomm i)
  have hfactor := regularControlledProjectorCutMatrix_sum_factorization
    R TS hTS htreeS oS (fun _ => oS) (fun _ => oS) p TR hTR htreeR oR
    (fun i => torusClosureEdgeAssignment (pairs i).1 (pairs i).2) μ e hflat hrelative cR cS
  dsimp only at hfactor ⊢
  rw [← hfactor]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (μ i * ·)
  exact (regularControlledProjectorCutMatrix_eq_native_contraction
    R TS hTS htreeS oS (fun _ => oS) (fun _ => oS) p
    (regularRegionTreeGauge R TR hTR htreeR oR
      (torusClosureEdgeAssignment (pairs i).1 (pairs i).2)).1
    (torusClosureEdgeAssignment (pairs i).1 (pairs i).2)
    ((regularRegionCoordinatesEquiv R TR hTR htreeR oR).symm cR)
    ((regularRegionCoordinatesEquiv S TS hTS htreeS oS).symm cS)).symm

end TNLean.PEPS
