/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Injectivity.Boundary.BoundaryNormalization
import TNLean.PEPS.Tensor.GraphState.RegularOpenRegion
import TNLean.PEPS.Tensor.GraphState.RegularRegionGram
import TNLean.PEPS.Injectivity.Regular.RegularRegionProjectorCoordinates

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

It also contains the following results.

* `TNLean.PEPS.isGInjective_regularOpenRegionMatrix_of_connected`: G-injectivity of an actual
  connected regular block.
* `TNLean.PEPS.regularOpenRegionMatrix_invariant`,
  `TNLean.PEPS.isGIsometric_regularOpenRegionMatrix_of_connected`: regular isometry of an actual
  connected block.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open ManyBody (Edge)

section RegularRegionEntropy

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
    {b : ℕ} (e : {f : Edge Γ // ManyBody.IsRegionBoundaryEdge R f} ≃ Fin b) :
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
    (e : {f : Edge Γ // ManyBody.IsRegionBoundaryEdge R f} ≃ Fin b) :
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
    (e : {f : Edge Γ // ManyBody.IsRegionBoundaryEdge R f} ≃ Fin (n + 1))
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
    (n : ℕ) (e : {f : Edge Γ // ManyBody.IsRegionBoundaryEdge R f} ≃ Fin (n + 1)) :
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

end RegularRegionEntropy

section RegularRegionIsometry

/-!
## Regular isometry of an actual connected block

Contracting a connected region of regular isometric sites gives an isometric map
on the invariant boundary subspace, up to the positive scalar contributed by the
site factors and the internal cycles. The statement uses the genuine open-region
map: no Gram identity for the block is supplied as a hypothesis.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Lemma 6.2 and the
blocking discussion, `Papers/1001.3807/paper_v3.tex`, lines 1709–1716 and 1825–1880.
The positive-factor convention is that of `IsGIsometric`, documented in
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`. This also applies to
regions with internal cycles or no crossing bonds.

### References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
attribute [local instance] Representation.invertibleFintypeCardComplex

omit [DecidableEq G] in
/-- The actual blocked physical map is invariant under the regular boundary action.
Source: SCP10, virtual symmetry of a block in the blocking discussion, lines 1825–1840. -/
theorem regularOpenRegionMatrix_invariant
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ g v η s, a v (fun f => g * η f) s = a v η s)
    (R : Finset V) {b : ℕ}
    (e : {f : Edge Γ // ManyBody.IsRegionBoundaryEdge R f} ≃ Fin b) (g : G) :
    Matrix.mulVecLin (regularOpenRegionMatrix a R e) ∘ₗ
      regularBoundaryRepresentation b g = Matrix.mulVecLin (regularOpenRegionMatrix a R e) := by
  classical
  ext x σ
  simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    regularBoundaryRepresentation_apply]
  simp only [LinearMap.single_apply, Pi.single_apply, inv_smul_eq_iff]
  simpa using regularOpenRegionMatrix_translation a ha R e g σ x

omit [DecidableEq G] in
/-- Contracting an actual connected region of regular isometric sites preserves
isometry on the invariant boundary space, with its derived positive factor.
Source: SCP10, Lemma 6.2 and blocking, lines 1709–1716 and 1825–1880. -/
theorem isGIsometric_regularOpenRegionMatrix_of_connected
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V)
    (hR : (Γ.induce (R : Set V)).Connected) {b : ℕ}
    (e : {f : Edge Γ // ManyBody.IsRegionBoundaryEdge R f} ≃ Fin b) :
    IsGIsometric (regularBoundaryRepresentation b)
      (Matrix.mulVecLin (regularOpenRegionMatrix a R e)) := by
  classical
  obtain ⟨c, hc, h⟩ := exists_positive_gram_regularOpenRegionMatrix_of_connected a ha R hR e
  apply isGIsometric_of_coordinateAdjoint_comp
    (fun g => regularOpenRegionMatrix_invariant a
      (fun g v η s => (ha v).toIsGInjective.regularSiteMap_translation g η s) R e g) hc
  apply LinearMap.toMatrix'.injective
  simp only [LinearMap.toMatrix'_comp, coordinateAdjoint, map_smul]
  simp only [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  exact h

end TNLean.PEPS

end RegularRegionIsometry

section RegularRegionInjectivity

/-!
## G-injectivity of an actual connected regular block

Local inverses expose the canonical projector contraction. In spanning-tree
coordinates, a row with identity reference, vertex, and cycle labels is a
nonzero multiple of the boundary projector. Hence the actual block is injective
on the invariant boundary space whenever its local tensors are G-injective.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Lemma 5.2 and the
blocking discussion, `Papers/1001.3807/paper_v3.tex`, lines 1300–1350 and
1825–1840. This is the regular-representation connected-region consequence;
no local isometry or block Gram identity is assumed.

**Scope restriction (regular bonds):** The source allows semi-regular virtual
representations; this connected-region result uses regular group coordinates.
The scope is documented in `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

### References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
attribute [local instance] Representation.invertibleFintypeCardComplex

private theorem regularLegProjector_numbering {ι : Type*} [Fintype ι] [DecidableEq ι]
    {b : ℕ} (e : ι ≃ Fin b) (y x : Fin b → G) :
    regularLegProjector ι (fun f => y (e f)) (fun f => x (e f)) =
      regularBoundaryProjector b y x := by
  classical
  rw [← regularLegProjector_fin b, regularLegProjector_apply, regularLegProjector_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  have h : (fun f => y (e f)) = g • (fun f => x (e f)) ↔ y = g • x := by
    change y ∘ e = (g • x) ∘ e ↔ y = g • x
    exact e.surjective.right_cancellable
  simp only [h]

private theorem canonical_boundary_row (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})
    {b : ℕ} (e : {f : Edge Γ // ManyBody.IsRegionBoundaryEdge R f} ≃ Fin b)
    (y x : Fin b → G) :
    regularProjectorOpenRegionMatrix R
        ((regularRegionCoordinatesEquiv R T hT htree o).symm
          (fun f => y (e f), 1, ⟨1, rfl⟩, 1)) (fun f => x (e f)) =
      (Fintype.card G : ℂ) * (Fintype.card G : ℂ)⁻¹ ^ R.card *
        regularBoundaryProjector b y x := by
  rw [regularProjectorOpenRegionMatrix_coordinates]
  simp only [ite_true, mul_one]
  rw [regularLegProjector_numbering]

omit [DecidableEq G] in
/-- An actual connected block of regular G-injective sites is G-injective
on its invariant boundary space. Internal cycles and empty boundaries are allowed.
Source: SCP10, Lemma 5.2 and its following observation, lines 1318–1358;
the regular blocking discussion, lines 1825–1840. -/
theorem isGInjective_regularOpenRegionMatrix_of_connected
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V)
    (hR : (Γ.induce (R : Set V)).Connected) {b : ℕ}
    (e : {f : Edge Γ // ManyBody.IsRegionBoundaryEdge R f} ≃ Fin b) :
    IsGInjective (regularBoundaryRepresentation b)
      (Matrix.mulVecLin (regularOpenRegionMatrix a R e)) := by
  classical
  refine ⟨fun g => regularOpenRegionMatrix_invariant a
    (fun g v η s => (ha v).regularSiteMap_translation g η s) R e g, ?_⟩
  intro x hInv hx
  choose F hF using fun v => (ha v).exists_regularProjectorCoefficients
  have hcan := congrArg (fun M => M *ᵥ x)
    (regionPhysicalProductMatrix_mul_regularOpenRegionMatrix a F hF R e)
  rw [← Matrix.mulVec_mulVec, show regularOpenRegionMatrix a R e *ᵥ x = 0 from hx,
    Matrix.mulVec_zero] at hcan
  obtain ⟨T, hT, htree⟩ := hR.exists_isTree_le
  let o : {v : V // v ∈ R} := Classical.choice hR.nonempty
  ext y
  have hrow := congrFun hcan ((regularRegionCoordinatesEquiv R T hT htree o).symm
    (fun f => y (e f), 1, ⟨1, rfl⟩, 1))
  simp only [Pi.zero_apply, Matrix.mulVec, dotProduct,
    canonical_boundary_row R T hT htree o e y, mul_assoc, ← Finset.mul_sum] at hrow
  change 0 = (Fintype.card G : ℂ) * ((Fintype.card G : ℂ)⁻¹ ^ R.card *
    (regularBoundaryProjector b *ᵥ x) y) at hrow
  rw [regularBoundaryProjector_mulVec_of_mem_invariants b x hInv] at hrow
  have hκ : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simpa [hκ] using hrow.symm

end TNLean.PEPS

end RegularRegionInjectivity
