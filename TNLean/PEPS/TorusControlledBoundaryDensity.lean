/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularReferenceBoundaryDensity
import TNLean.PEPS.TorusControlledBoundaryFactor
import TNLean.PEPS.RegularPhysicalCutTransfer

/-!
# Common canonical torus boundary density

The actual canonical torus cut has a fixed normalized reduced density for every
nonzero coherent sum of commuting closures. The complementary controlled
operation is unitary and is chosen before the closures and their coefficients.
Its actual coefficient factorization separates one fixed boundary factor and
one fixed region ancillary vector.

**Scope restriction (SCP10 Theorem 6.9):** The actual closed-cell region is simply
connected, and fixed complementary loops with the required winding are supplied.
Existence of these loops for the paper's disk geometry and transfer to arbitrary
original site tensors remain separate; see `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
No cross-Gram identity or physical factorization is assumed.

Source: arXiv:1001.3807, lines 1935–1990 and 2027–2072.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace TNLean.PEPS

private theorem controlled_cut_sum_apply
    {V G I : Type*} [Fintype V] [LinearOrder V] {Γ : SimpleGraph V}
    [DecidableRel Γ.Adj] [Group G] [Fintype G] [DecidableEq G] [Fintype I]
    (R : Finset V) (u : I → Edge Γ → G) (μ : I → ℂ)
    (U : Matrix (RegionHalfEdgeConfig (Γ := Γ) G (Finset.univ \ R))
      (RegionHalfEdgeConfig (Γ := Γ) G (Finset.univ \ R)) ℂ)
    (α : RegionHalfEdgeConfig (Γ := Γ) G R)
    (β : RegionHalfEdgeConfig (Γ := Γ) G (Finset.univ \ R)) :
    ((∑ i, μ i • regularProjectorTwistedCutMatrix R (u i)) * U.transpose) α β =
      ∑ i, μ i * ∑ θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G,
        regularProjectorTwistedRegionMatrix R (u i) α θ *
          (U * regularProjectorTwistedRegionMatrix (Finset.univ \ R) (u i)) β
            (fun f => θ ((regionBoundaryEdgeComplEquiv (G := Γ) R).symm f)) := by
  classical
  simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.transpose_apply, regularProjectorTwistedCutMatrix]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_assoc, ← Finset.mul_sum]
  apply congrArg (μ i * ·)
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro θ _
  simp only [← Finset.mul_sum]
  apply congrArg (regularProjectorTwistedRegionMatrix R (u i) α θ * ·)
  apply Finset.sum_congr rfl
  intro β' _
  exact mul_comm _ _

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

/-- Every coherent canonical closure sum has the same reduced matrix up to its
squared norm. Simple connectedness and the fixed winding loops are geometric
hypotheses, rather than supplied flatness or mixed Gram identities.
Source: SCP10, Theorem 6.9 argument, lines 1935–1990 and 2043–2072. -/
theorem torusControlledCut_reducedMatrix_eq_trace_smul
    (R : Finset X) (hSC : IsSimplyConnected (torusRegionRealization R))
    (TR : SimpleGraph {v : X // v ∈ R})
    (TS : SimpleGraph {v : X // v ∈ Finset.univ \ R})
    [DecidableRel TR.Adj]
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
      torusWalkWinding (torusBoundaryTreeRoute R TR TS hTR hTS htreeR htreeS oS (e.symm 0) f))
    {I : Type*} [Fintype I] (pairs : I → G × G)
    (hcomm : ∀ i, Commute (pairs i).1 (pairs i).2) (μ : I → ℂ) :
    let C := ∑ i, μ i • regularProjectorTwistedCutMatrix R
      (torusClosureEdgeAssignment (pairs i).1 (pairs i).2)
    C * C.conjTranspose = (C * C.conjTranspose).trace •
      regularReferenceBoundaryDensity (G := G) R TR hTR htreeR oR e := by
  classical
  let S := Finset.univ \ R
  let u i := torusClosureEdgeAssignment (width := width) (height := height)
    (pairs i).1 (pairs i).2
  let C := ∑ i, μ i • regularProjectorTwistedCutMatrix R (u i)
  let ER := regularRegionReferenceCoordinatesEquiv (G := G) R TR hTR htreeR oR e
  let ES := regularRegionReferenceCoordinatesEquiv (G := G) S TS hTS htreeS oS
    ((regionBoundaryEdgeComplEquiv (G := Γₜ) R).symm.trans e)
  let φ := regularReferenceRegionAncilla (Γ := Γₜ) (G := G) R TR oR
  let χ : RegularReferenceRegionLabels (Γ := Γₜ) (G := G) S TS oS → ℂ := fun b =>
    (Real.sqrt (Fintype.card (Fin n → G) : ℝ) : ℂ) *
      (Real.sqrt (Fintype.card (G ×
        (({f : Edge Γₜ // f.1.1 ∈ R ∧ f.1.2 ∈ R} → G) ×
          RootedGroupLabels (G := G) oR)) : ℝ) : ℂ) *
      ((Fintype.card G : ℂ)⁻¹ ^ R.card * (Fintype.card G : ℂ)⁻¹ ^ S.card) *
      ∑ i, μ i * ∑ x : G, if b.2.2.2 = (fun f => x *
        regularRegionTreeCycleResidual S TS hTS htreeS oS (u i) f * x⁻¹) then 1 else 0
  obtain ⟨U, hU, hf⟩ :=
    exists_unitary_torusControlledBoundaryFactor_of_isSimplyConnected_and_winding
      (G := G) R hSC TR TS hTR hTS htreeR htreeS oR oS e p hwind
  have hK : C * U.transpose =
      (boundaryFactorSchmidtMatrix (D := Fin n → G) φ χ).submatrix ER ES := by
    ext α β
    rw [controlled_cut_sum_apply]
    have h := hf I pairs hcomm μ
      (regularRegionCoordinatesEquiv R TR hTR htreeR oR α)
      (regularRegionCoordinatesEquiv S TS hTS htreeS oS β)
    dsimp only [S, u] at h ⊢
    simp only [Equiv.symm_apply_apply] at h
    rw [h]
    simp only [Matrix.submatrix_apply, ER, ES, regularRegionReferenceCoordinatesEquiv,
      Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.prodAssoc_apply,
      Prod.map_fst, Prod.map_snd, Equiv.prodComm_apply, Equiv.coe_refl]
    rw [boundaryFactorSchmidtMatrix_apply, Matrix.omegaVec_apply]
    simp only [(Fintype.equivFin (Fin n → G)).injective.eq_iff, φ, χ, S, u,
      regularBoundaryRelativeEquiv, one_div]
    rfl
  have hr : C * C.conjTranspose = (star χ ⬝ᵥ χ) •
      regularReferenceBoundaryDensity (G := G) R TR hTR htreeR oR e := by
    rw [← mul_unitary_transpose_mul_conjTranspose C U hU, hK,
      boundaryFactorSchmidtMatrix_submatrix_mul_conjTranspose]
    rfl
  have ht : (C * C.conjTranspose).trace = star χ ⬝ᵥ χ := by
    rw [hr, trace_smul, (regularReferenceBoundaryDensity_properties
      (G := G) R TR hTR htreeR oR e).2.1, smul_eq_mul, mul_one]
  change C * C.conjTranspose = _
  rw [ht]
  exact hr

/-- Every nonzero coherent sum of the actual canonical commuting closures has
the same normalized reduced density, with boundary rank, flat spectrum, and von
Neumann entropy. The normalization is derived from nonvanishing of the actual
coefficient matrix. Source: SCP10, lines 2027–2072. -/
theorem torusControlledCut_normalized_reducedMatrix
    (R : Finset X) (hSC : IsSimplyConnected (torusRegionRealization R))
    (TR : SimpleGraph {v : X // v ∈ R})
    (TS : SimpleGraph {v : X // v ∈ Finset.univ \ R})
    [DecidableRel TR.Adj]
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
      torusWalkWinding (torusBoundaryTreeRoute R TR TS hTR hTS htreeR htreeS oS (e.symm 0) f))
    {I : Type*} [Fintype I] (pairs : I → G × G)
    (hcomm : ∀ i, Commute (pairs i).1 (pairs i).2) (μ : I → ℂ)
    (hne : (∑ i, μ i • regularProjectorTwistedCutMatrix R
      (torusClosureEdgeAssignment (pairs i).1 (pairs i).2)) ≠ 0) :
    let C := ∑ i, μ i • regularProjectorTwistedCutMatrix R
      (torusClosureEdgeAssignment (pairs i).1 (pairs i).2)
    let ρ := (C * C.conjTranspose).trace⁻¹ • (C * C.conjTranspose)
    0 < (C * C.conjTranspose).trace ∧
      ρ = regularReferenceBoundaryDensity (G := G) R TR hTR htreeR oR e ∧
      ρ.PosSemidef ∧ ρ.trace = 1 ∧ ρ.rank = Fintype.card G ^ n ∧
      ρ * ρ = ((Fintype.card G : ℂ) ^ n)⁻¹ • ρ ∧
      ∃ hρ : ρ.IsHermitian, vonNeumannEntropy ρ hρ = n * Real.log (Fintype.card G : ℝ) := by
  classical
  let C := ∑ i, μ i • regularProjectorTwistedCutMatrix R
    (torusClosureEdgeAssignment (pairs i).1 (pairs i).2)
  have hp := regularReferenceBoundaryDensity_properties (G := G) R TR hTR htreeR oR e
  have hs := torusControlledCut_reducedMatrix_eq_trace_smul (G := G)
    R hSC TR TS hTR hTS htreeR htreeS oR oS e p hwind pairs hcomm μ
  have hn := normalized_reducedMatrix_eq_of_scalar C
    (regularReferenceBoundaryDensity (G := G) R TR hTR htreeR oR e) hp.2.1
    (C * C.conjTranspose).trace hs hne
  dsimp only
  refine ⟨hn.1, hn.2, ?_⟩
  rw [hn.2]
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, hp.1.isHermitian,
    vonNeumannEntropy_regularReferenceBoundaryDensity R TR hTR htreeR oR e⟩

/-- All nonnegative finite Rényi orders of each nonzero coherent canonical
closure sum equal the common boundary entropy, including orders zero and one.
Source: SCP10, lines 2027–2037. -/
theorem torusControlledCut_normalized_renyiEntropy
    (R : Finset X) (hSC : IsSimplyConnected (torusRegionRealization R))
    (TR : SimpleGraph {v : X // v ∈ R})
    (TS : SimpleGraph {v : X // v ∈ Finset.univ \ R})
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
      torusWalkWinding (torusBoundaryTreeRoute R TR TS hTR hTS htreeR htreeS oS (e.symm 0) f))
    {I : Type*} [Fintype I] (pairs : I → G × G)
    (hcomm : ∀ i, Commute (pairs i).1 (pairs i).2) (μ : I → ℂ)
    (hne : (∑ i, μ i • regularProjectorTwistedCutMatrix R
      (torusClosureEdgeAssignment (pairs i).1 (pairs i).2)) ≠ 0) :
    let C := ∑ i, μ i • regularProjectorTwistedCutMatrix R
      (torusClosureEdgeAssignment (pairs i).1 (pairs i).2)
    let ρ := (C * C.conjTranspose).trace⁻¹ • (C * C.conjTranspose)
    ∃ hρ : ρ.IsHermitian, ∀ α : ℝ, 0 ≤ α →
      renyiEntropy ρ hρ α = n * Real.log (Fintype.card G : ℝ) := by
  classical
  obtain ⟨_, _, hp, ht, hrank, hflat, _⟩ :=
    torusControlledCut_normalized_reducedMatrix (G := G)
      R hSC TR TS hTR hTS htreeR htreeS oR oS e p hwind pairs hcomm μ hne
  refine ⟨hp.isHermitian, ?_⟩
  intro α hα
  have hr : 0 < (Fintype.card G : ℝ) ^ n := pow_pos (Nat.cast_pos.mpr Fintype.card_pos) n
  have he := renyiEntropy_of_mul_self_eq_inv_smul_of_rank hp ht hr hα
    (by simpa only [Complex.ofReal_pow, Complex.ofReal_natCast] using hflat)
    (by exact_mod_cast hrank)
  simpa only [Real.log_pow] using he

end TNLean.PEPS
