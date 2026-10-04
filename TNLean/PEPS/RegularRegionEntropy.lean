/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.BoundaryNormalization
import TNLean.PEPS.RegularOpenRegion
import TNLean.PEPS.RegularRegionGram

/-!
# Entropy across connected cuts of a finite regular PEPS

The positive local isometry factors and the internal-bond counting factor give a positive
Gram factor for each connected region. Normalizing the actual contractions on the two
sides of a cut realizes the regular virtual boundary state in the physical system.

**Scope restriction (connected finite untwisted cut):** the entropy result concerns the
untwisted finite graph contraction, with connected induced graphs on the region and its
complement and a nonempty boundary. The torus states with inserted noncontractible group
operators in Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Theorem 6.9 remain separate;
see `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: SCP10, Lemma 6.2 and the proof of Theorem 6.9, local source
`Papers/1001.3807/paper_v3.tex`, lines 1704–1716 and 2043–2076.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G]

/-- The positive Gram factor of a connected region: local factors, one free internal
label per internal edge, and one common regular translation. -/
noncomputable def regularRegionGramFactor (c : V → ℝ) (R : Finset V) : ℝ :=
  (∏ v : {v // v ∈ R}, c v.1) *
    (Fintype.card G : ℝ) ^ (Fintype.card {f : Edge Γ // f.1.1 ∈ R ∧ f.1.2 ∈ R} + 1) /
      (Fintype.card G : ℝ) ^ R.card

/-- Positive site factors yield a positive factor for the region contraction. -/
theorem regularRegionGramFactor_pos (c : V → ℝ) (R : Finset V)
    (hc : ∀ v ∈ R, 0 < c v) : 0 < regularRegionGramFactor (Γ := Γ) (G := G) c R := by
  have hG : 0 < (Fintype.card G : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  exact div_pos (mul_pos (Finset.prod_pos fun v _ => hc v.1 v.2) (pow_pos hG _))
    (pow_pos hG _)

omit [Group G] in
/-- The real Gram factor has exactly the complex scalar appearing in the Gram matrix. -/
theorem ofReal_regularRegionGramFactor (c : V → ℝ) (R : Finset V) :
    (regularRegionGramFactor (Γ := Γ) (G := G) c R : ℂ) =
      regularRegionGramScalar (Γ := Γ) (G := G) (fun v => (c v : ℂ)) R := by
  simp only [regularRegionGramFactor, regularRegionGramScalar, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_pow, Complex.ofReal_natCast]

variable {d : ℕ}

omit [Group G] in
/-- The complementary map uses the same crossing labels as the region map. -/
theorem regularOpenComplementMatrix_eq_regularOpenRegionMatrix
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (R : Finset V)
    {b : ℕ} (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b) :
    regularOpenComplementMatrix a R e = regularOpenRegionMatrix a (Finset.univ \ R)
      ((regionBoundaryEdgeComplEquiv (G := Γ) R).symm.trans e) := by
  rfl

/-- The genuine finite PEPS vector expressed as a bipartite vector across the chosen cut. -/
noncomputable def regularPhysicalCutState
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (R : Finset V) :
    (RegionPhysicalConfig (d := d) R × RegionPhysicalConfig (d := d) (Finset.univ \ R)) → ℂ :=
  fun p => regularPhysicalCutMatrix a R p.1 p.2

variable [DecidableEq G]

/-- Local regular isometry makes the actual contraction of a connected region isometric
on its invariant boundary subspace, up to a positive factor. This includes regions with
no crossing bonds. Source: SCP10, connected untwisted contraction in Lemma 6.2 and
lines 1935–1957. -/
theorem exists_positive_gram_regularOpenRegionMatrix_of_connected
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v)) (regularSiteMap (a v)))
    (R : Finset V) (hR : (Γ.induce (R : Set V)).Connected) {b : ℕ}
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b) :
    ∃ κ : ℝ, 0 < κ ∧
      (regularOpenRegionMatrix a R e).conjTranspose * regularOpenRegionMatrix a R e =
        (κ : ℂ) • regularBoundaryProjector b := by
  classical
  choose c hc hlocal using fun v => (ha v).exists_regularSiteGram
  have hM := regularOpenRegionMatrix_gram_of_connected a (fun v => (c v : ℂ)) R hR e
    (fun v η θ => hlocal v.1 η θ)
  rw [← ofReal_regularRegionGramFactor] at hM
  exact ⟨regularRegionGramFactor (Γ := Γ) (G := G) c R,
    regularRegionGramFactor_pos c R (fun v _ => hc v), hM⟩

private theorem exists_normalization_of_cut_grams
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ g v η s, a v (fun f => g * η f) s = a v η s)
    (R : Finset V) (n : ℕ)
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1))
    {cA cB : ℝ} (hcA : 0 < cA) (hcB : 0 < cB)
    (hM : (regularOpenRegionMatrix a R e).conjTranspose * regularOpenRegionMatrix a R e =
      (cA : ℂ) • regularBoundaryProjector (n + 1))
    (hN : (regularOpenComplementMatrix a R e).conjTranspose *
        regularOpenComplementMatrix a R e = (cB : ℂ) • regularBoundaryProjector (n + 1)) :
    ∃ z : ℝ, 0 < z ∧
      let ψ := (z : ℂ) • regularPhysicalCutState a R
      let ρ := partialTraceRight (vecMulVec ψ (star ψ))
      star ψ ⬝ᵥ ψ = 1 ∧ ρ.rank = Fintype.card G ^ n ∧
        ρ * ρ = ((Fintype.card G : ℂ) ^ n)⁻¹ • ρ ∧
        vonNeumannEntropy ρ
          (posSemidef_vecMulVec_self_star ψ).partialTraceRight.isHermitian =
            (n : ℝ) * Real.log (Fintype.card G : ℝ) := by
  classical
  let M := regularOpenRegionMatrix a R e
  let N := regularOpenComplementMatrix a R e
  let A := normalizedRegularBoundaryMap cA M
  let B := normalizedRegularBoundaryMap cB N
  let z := (Real.sqrt cA)⁻¹ * (Real.sqrt cB)⁻¹ *
    (Real.sqrt (Fintype.card G ^ n : ℝ))⁻¹
  have hG : 0 < (Fintype.card G : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hz : 0 < z := mul_pos
    (mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr hcA)) (inv_pos.mpr (Real.sqrt_pos.mpr hcB)))
    (inv_pos.mpr (Real.sqrt_pos.mpr (pow_pos hG n)))
  have hA := normalizedRegularBoundaryMap_conjTranspose_mul n M hcA hM
  have hB := normalizedRegularBoundaryMap_conjTranspose_mul n N hcB hN
  have hψ : physicalRegularBoundaryState n A B = (z : ℂ) • regularPhysicalCutState a R := by
    funext p
    change physicalRegularBoundarySchmidtMatrix n A B p.1 p.2 = _
    rw [physicalRegularBoundarySchmidtMatrix_normalizedRegularBoundaryMap,
      ← regularPhysicalCutMatrix_eq_mul_projector_mul_transpose a ha R n e]
    simp only [z, Complex.ofReal_mul, Complex.ofReal_inv, Matrix.smul_apply,
      Pi.smul_apply, smul_eq_mul, regularPhysicalCutState]
  refine ⟨z, hz, ?_⟩
  dsimp only
  have hnorm : star (physicalRegularBoundaryState n A B) ⬝ᵥ
      physicalRegularBoundaryState n A B = 1 := by
    rw [Matrix.star_dotProduct_eq_trace_conjTranspose_mul, Matrix.trace_mul_comm]
    change (physicalRegularBoundarySchmidtMatrix n A B *
      (physicalRegularBoundarySchmidtMatrix n A B).conjTranspose).trace = 1
    rw [physicalRegularBoundarySchmidtMatrix_mul_conjTranspose n A B hB,
      trace_physicalRegularBoundaryDensity n A hA]
  have hent := vonNeumannEntropy_normalizedRegularBoundaryState n M N hcA hcB hM hN
  rw [hψ] at hnorm
  have hρ := partialTrace_physicalRegularBoundaryState n A B hB
  rw [hψ] at hρ
  refine ⟨hnorm, ?_, ?_, ?_⟩
  · rw [hρ]
    exact rank_physicalRegularBoundaryDensity n A hA
  · rw [hρ]
    exact physicalRegularBoundaryDensity_mul_self n A hA
  · change vonNeumannEntropy (partialTraceRight (vecMulVec
      (physicalRegularBoundaryState n A B) (star (physicalRegularBoundaryState n A B)))) _ = _
      at hent
    simpa only [hψ] using hent

omit [DecidableEq G] in
/-- Local regular isometry gives a normalized actual PEPS vector whose reduced state has
rank \(|G|^n\), flat nonzero spectrum, and entropy \(n\log|G|\), whenever the two sides of
the finite untwisted cut induce connected graphs
and there are \(n+1\) crossing bonds. No region Gram identity is assumed.
Source: SCP10, the connected untwisted case of the calculation in Theorem 6.9,
lines 2043–2076. -/
theorem exists_normalization_regularPhysicalCutState_of_connected
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v)) (regularSiteMap (a v)))
    (R : Finset V) (hR : (Γ.induce (R : Set V)).Connected)
    (hRc : (Γ.induce ((Finset.univ \ R : Finset V) : Set V)).Connected)
    (n : ℕ) (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1)) :
    ∃ z : ℝ, 0 < z ∧
      let ψ := (z : ℂ) • regularPhysicalCutState a R
      let ρ := partialTraceRight (vecMulVec ψ (star ψ))
      star ψ ⬝ᵥ ψ = 1 ∧ ρ.rank = Fintype.card G ^ n ∧
        ρ * ρ = ((Fintype.card G : ℂ) ^ n)⁻¹ • ρ ∧
        vonNeumannEntropy ρ
          (posSemidef_vecMulVec_self_star ψ).partialTraceRight.isHermitian =
            (n : ℝ) * Real.log (Fintype.card G : ℝ) := by
  classical
  have hsym : ∀ g v η s, a v (fun f => g * η f) s = a v η s := by
    intro g v η s
    exact (ha v).toIsGInjective.regularSiteMap_translation g η s
  obtain ⟨cA, hcA, hM⟩ := exists_positive_gram_regularOpenRegionMatrix_of_connected a ha R hR e
  obtain ⟨cB, hcB, hN⟩ := exists_positive_gram_regularOpenRegionMatrix_of_connected a ha
    (Finset.univ \ R) hRc ((regionBoundaryEdgeComplEquiv (G := Γ) R).symm.trans e)
  rw [← regularOpenComplementMatrix_eq_regularOpenRegionMatrix a R e] at hN
  exact exists_normalization_of_cut_grams a hsym R n e hcA hcB hM hN

end TNLean.PEPS
