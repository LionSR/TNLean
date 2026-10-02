/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FlatDensityRenyiEntropy
import TNLean.PEPS.RegularPhysicalDensity
import TNLean.PEPS.RegularTorusEntropy
import TNLean.PEPS.TorusControlledBoundaryDensity

/-!
# Reduced density of original torus closure superpositions

The original site maps carry the actual canonical cut to the physical cut.
Their product Gram factors are derived locally and are independent of all
closure labels and coherent coefficients. The density transfer therefore uses
one physical embedding for the whole closure family.

**Scope restriction (geometric winding data):** The common-density theorem
assumes actual simple connectedness, rooted spanning trees, and fixed complement
loops with matching winding, in the native simple-graph regime where both torus
dimensions are at least three. Exterior routing from the paper's full disk
hypotheses remains separate; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
No physical range surjectivity or global Gram identity is assumed.

Source: SCP10, arXiv:1001.3807, lines 1765–1820 and 1935–2072.
-/

open scoped BigOperators Matrix ComplexOrder

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

/-- One positive physical normalization transfers every actual torus coherent
cut density. No commutativity, geometry, or global Gram premise is used in this
algebraic identity. Source: SCP10, lines 1765–1820 and 1935–1990. -/
theorem IsGIsometric.exists_torusPhysicalCut_density_transfer
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (R : Finset X) :
    ∃ c : ℝ, 0 < c ∧ ∀ {I : Type*} [Fintype I] (pairs : I → G × G) (μ : I → ℂ),
      let C := ∑ i, μ i • regularProjectorTwistedCutMatrix R
        (torusClosureEdgeAssignment (pairs i).1 (pairs i).2)
      let M : Matrix (RegionPhysicalConfig (d := d) R)
          (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
        fun σ τ => torusClosureSuperpositionCut a pairs μ R (σ, τ)
      (Matrix.trace (M * M.conjTranspose))⁻¹ • (M * M.conjTranspose) =
        normalizedPhysicalImageDensity c
          (regionPhysicalProductMatrix R (fun v =>
            Matrix.of fun s α => torusIncidentSite a v α s))
          ((Matrix.trace (C * C.conjTranspose))⁻¹ • (C * C.conjTranspose)) := by
  classical
  obtain ⟨cR, cS, hcR, _, _, h⟩ := exists_positive_regularPhysicalCut_density_transfer
    (torusIncidentSite a) (fun v => ha.isGIsometric_torusIncidentSite v) R
  refine ⟨cR, hcR, ?_⟩
  intro I _ pairs μ
  have htransfer := (h (fun i => torusClosureEdgeAssignment (pairs i).1 (pairs i).2) μ).2.2
  have hM : (fun σ τ => torusClosureSuperpositionCut a pairs μ R (σ, τ)) =
      ∑ i, μ i • regularPhysicalCutMatrix
        (regularTwistedSite (torusIncidentSite a)
          (torusClosureEdgeAssignment (pairs i).1 (pairs i).2)) R := by
    ext σ τ
    simp only [torusClosureSuperpositionCut, Finset.sum_apply, Pi.smul_apply,
      Matrix.sum_apply, Matrix.smul_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (μ i • ·)
      (torusGClosure_assembleRegion_eq_regularPhysicalCutMatrix
        a (pairs i).1 (pairs i).2 R σ τ)
  simpa only [← hM, normalizedPhysicalImageDensity] using htransfer

/-- Every nonzero coherent superposition of original regular G-isometric torus
closures has one fixed physical reduced density, with boundary rank and flat
spectrum. The fixed complementary winding loops are geometric data, rather than
a supplied factorization or mixed Gram identity.
Source: SCP10, Theorem 6.9 argument, lines 1935–1990 and 2027–2072. -/
theorem IsGIsometric.exists_torusPhysicalCut_common_density_of_isSimplyConnected_and_winding
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a))
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
      torusWalkWinding (torusBoundaryTreeRoute R TR TS hTR hTS htreeR htreeS oS (e.symm 0) f)) :
    ∃ ρ : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ,
      ∀ {I : Type*} [Fintype I] (pairs : I → G × G)
        (_hcomm : ∀ i, Commute (pairs i).1 (pairs i).2) (μ : I → ℂ),
        torusClosureSuperpositionCut a pairs μ R ≠ 0 →
        let M : Matrix (RegionPhysicalConfig (d := d) R)
            (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
          fun σ τ => torusClosureSuperpositionCut a pairs μ R (σ, τ)
        0 < (M * M.conjTranspose).trace ∧
          (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose) = ρ ∧
          ρ.PosSemidef ∧ ρ.trace = 1 ∧ ρ.rank = Fintype.card G ^ n ∧
          ρ * ρ = ((Fintype.card G : ℂ) ^ n)⁻¹ • ρ ∧
          ∃ hρ : ρ.IsHermitian,
            vonNeumannEntropy ρ hρ = n * Real.log (Fintype.card G : ℝ) ∧
              ∀ α : ℝ, 0 ≤ α →
                renyiEntropy ρ hρ α = n * Real.log (Fintype.card G : ℝ) := by
  classical
  obtain ⟨cR, cS, hcR, _, hGram, htransfer⟩ :=
    exists_positive_regularPhysicalCut_density_transfer (torusIncidentSite a)
      (fun v => ha.isGIsometric_torusIncidentSite v) R
  let T := regionPhysicalProductMatrix R (fun v => Matrix.of fun s α => torusIncidentSite a v α s)
  let P := regionPhysicalProductMatrix R
    (fun v => regularLegProjector (G := G) (IncidentEdge Γₜ v))
  let ρ₀ := regularReferenceBoundaryDensity (G := G) R TR hTR htreeR oR e
  refine ⟨normalizedPhysicalImageDensity cR T ρ₀, ?_⟩
  intro I _ pairs hcomm μ hne
  let u i := torusClosureEdgeAssignment (width := width) (height := height)
    (pairs i).1 (pairs i).2
  let C := ∑ i, μ i • regularProjectorTwistedCutMatrix R (u i)
  let M : Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
    fun σ τ => torusClosureSuperpositionCut a pairs μ R (σ, τ)
  have hMne : M ≠ 0 := by
    intro hz
    apply hne
    funext q
    exact congrFun (congrFun hz q.1) q.2
  have hM : M = ∑ i, μ i • regularPhysicalCutMatrix
      (regularTwistedSite (torusIncidentSite a) (u i)) R := by
    ext σ τ
    simp only [M, torusClosureSuperpositionCut, Finset.sum_apply, Pi.smul_apply,
      Matrix.sum_apply, Matrix.smul_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (μ i • ·)
      (torusGClosure_assembleRegion_eq_regularPhysicalCutMatrix
        a (pairs i).1 (pairs i).2 R σ τ)
  have hImage : M = T * C *
      (regionPhysicalProductMatrix (Finset.univ \ R)
        (fun v => Matrix.of fun s α => torusIncidentSite a v α s)).transpose := by
    rw [hM]
    simp only [T, C, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
      regularPhysicalCutMatrix_eq_physicalImage_regularProjectorTwistedCutMatrix
        (torusIncidentSite a) (fun v => (ha.isGIsometric_torusIncidentSite v).1)]
  have hCne : C ≠ 0 := by
    intro hz
    apply hMne
    rw [hImage, hz, Matrix.mul_zero, Matrix.zero_mul]
  have hn := torusControlledCut_normalized_reducedMatrix (G := G)
    R hSC TR TS hTR hTS htreeR htreeS oR oS e p hwind pairs hcomm μ hCne
  have hnEq : (C * C.conjTranspose).trace⁻¹ • (C * C.conjTranspose) = ρ₀ := hn.2.1
  have hPC : P * C = C := by
    simp only [P, C, Matrix.mul_sum, Matrix.mul_smul,
      regionPhysicalProductMatrix_mul_regularProjectorTwistedCutMatrix]
  have hPρ : P * ρ₀ = ρ₀ := by
    have hs : P * ((C * C.conjTranspose).trace⁻¹ • (C * C.conjTranspose)) =
        (C * C.conjTranspose).trace⁻¹ • (C * C.conjTranspose) := by
      rw [Matrix.mul_smul, ← Matrix.mul_assoc, hPC]
    rw [hnEq] at hs
    exact hs
  have hρ := regularReferenceBoundaryDensity_properties (G := G) R TR hTR htreeR oR e
  have hG : (T.conjTranspose * T) * ρ₀ = (cR : ℂ) • ρ₀ := by
    rw [hGram, Matrix.smul_mul, hPρ]
  have hflat : ρ₀ * ρ₀ = (((Fintype.card G : ℝ) ^ n : ℝ) : ℂ)⁻¹ • ρ₀ := by
    simpa only [Complex.ofReal_pow, Complex.ofReal_natCast] using hρ.2.2.2
  have hp := normalizedPhysicalImageDensity_properties T ρ₀ cR hcR hρ.1 hρ.2.1 hG
    ((Fintype.card G : ℝ) ^ n) hflat
  have heq := (htransfer u μ).2.2
  rw [← hM] at heq
  have hnorm : (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose) =
      normalizedPhysicalImageDensity cR T ρ₀ := by
    change (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose) =
      (cR : ℂ)⁻¹ • (T * ((C * C.conjTranspose).trace⁻¹ • (C * C.conjTranspose)) *
        T.conjTranspose) at heq
    rw [hnEq] at heq
    exact heq
  change 0 < (M * M.conjTranspose).trace ∧ _
  refine ⟨?_, hnorm, hp.1, hp.2.1, ?_, ?_, hp.1.isHermitian, ?_, ?_⟩
  · have htrace := mt Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp hMne
    exact lt_of_le_of_ne (Matrix.posSemidef_self_mul_conjTranspose M).trace_nonneg
      (Ne.symm htrace)
  · exact hp.2.2.1.trans hρ.2.2.1
  · simpa only [Complex.ofReal_pow, Complex.ofReal_natCast] using hp.2.2.2
  · simpa only [Real.log_pow] using vonNeumannEntropy_normalizedPhysicalImageDensity
      T ρ₀ cR hcR hρ.1 hρ.2.1 hG ((Fintype.card G : ℝ) ^ n) hflat
  · intro α hα
    have hr : 0 < (Fintype.card G : ℝ) ^ n :=
      pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _
    have hrank : ((normalizedPhysicalImageDensity cR T ρ₀).rank : ℝ) =
        (Fintype.card G : ℝ) ^ n := by
      rw [hp.2.2.1, hρ.2.2.1]
      norm_cast
    simpa only [Real.log_pow] using renyiEntropy_of_mul_self_eq_inv_smul_of_rank
      hp.1 hp.2.1 hr hα hp.2.2.2 hrank

end TNLean.PEPS
