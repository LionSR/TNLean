/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularAnchoredTreeGauge
import TNLean.PEPS.RegularTwistedRegionEntropy
import TNLean.PEPS.FixedBoundaryFactorDensity

/-!
# Noncentral density from an untwisted boundary component

The complement has a connected induced graph and an untwisted component
containing every complementary boundary endpoint. Its anchored tree gauge
preserves all incident operators and the actual closed physical vector.
The resulting complementary tree supplies the connected untwisted graph
required by the noncentral projected-Gram calculation. Thus every nonzero
actual cut has the vacuum normalized density.

This is a conditional contraction step for SCP10, arXiv:1001.3807v3,
Lemma 6.14 and Theorem 6.9, lines 1935–1990 and 2199–2214. Geometric
construction of the untwisted boundary component for native flux detours
is separate. See `docs/paper-gaps/scp10_anchored_twist_density.tex`.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace TNLean.PEPS

private theorem normalized_reduced_of_scaled_state
    {P Q : Type*} [Fintype P] [Fintype Q]
    (M : Matrix P Q ℂ) (ρ : Matrix P P ℂ) (hρ : ρ.trace = 1)
    (z : ℝ) (hz : 0 < z) (hne : M ≠ 0)
    (h : partialTraceRight (vecMulVec ((z : ℂ) • fun p : P × Q => M p.1 p.2)
      (star ((z : ℂ) • fun p : P × Q => M p.1 p.2))) = ρ) :
    (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose) = ρ := by
  rw [Matrix.partialTraceRight_vecMulVec_eq] at h
  change ((z : ℂ) • M) * ((z : ℂ) • M).conjTranspose = ρ at h
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul] at h
  have hzC : (z : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hz
  have hk : star (z : ℂ) * (z : ℂ) ≠ 0 := mul_ne_zero (star_ne_zero.mpr hzC) hzC
  have hraw : M * M.conjTranspose = (star (z : ℂ) * (z : ℂ))⁻¹ • ρ := by
    rw [← h, smul_smul, inv_mul_cancel₀ hk, one_smul]
  exact (normalized_reducedMatrix_eq_of_scalar M ρ hρ _ hraw hne).2

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ Δ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}
variable {G : Type*} [Group G] [Fintype G]

private theorem normalized_reduced_eq_of_common_untwisted
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v)) (regularSiteMap (a v)))
    (R : Finset V) (hR : (Γ.induce (R : Set V)).Connected)
    (u : Edge Γ → G) (hu : ∀ e : Edge Γ, IsRegionIncidentEdge R e → u e = 1)
    (hΔ : Δ ≤ Γ) (hS : (Δ.induce ((Finset.univ \ R : Finset V) : Set V)).Connected)
    (huΔ : ∀ e : Edge Γ, Δ.Adj e.1.1 e.1.2 → u e = 1)
    {n : ℕ} (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1))
    (hne : regularPhysicalCutMatrix (regularTwistedSite a u) R ≠ 0)
    (hne₀ : regularPhysicalCutMatrix a R ≠ 0) :
    let M := regularPhysicalCutMatrix (regularTwistedSite a u) R
    let M₀ := regularPhysicalCutMatrix a R
    (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose) =
      (M₀ * M₀.conjTranspose).trace⁻¹ • (M₀ * M₀.conjTranspose) := by
  classical
  let uB : Bool → Edge Γ → G := fun b => if b then u else fun _ => 1
  have hincident : ∀ b f, IsRegionIncidentEdge R f → uB b f = 1 := by
    intro b f hf
    cases b <;> simp only [uB, Bool.false_eq_true, ↓reduceIte]
    exact hu f hf
  have htree : ∀ b (f : Edge Γ), Δ.Adj f.1.1 f.1.2 →
      f.1.1 ∉ R → f.1.2 ∉ R → uB b f = 1 := by
    intro b f hf _ _
    cases b <;> simp only [uB, Bool.false_eq_true, ↓reduceIte]
    exact huΔ f hf
  obtain ⟨cA, hcA, hA, hnormalize⟩ :=
    exists_normalization_regularTwistedPhysicalCutSuperposition n a ha R hR uB
      hincident hΔ hS htree e
  let ρ := physicalRegularBoundaryDensity n
    (normalizedRegularBoundaryMap cA (regularOpenRegionMatrix a R e))
  have hρ : ρ.trace = 1 := trace_physicalRegularBoundaryDensity n _
    (normalizedRegularBoundaryMap_conjTranspose_mul n _ hcA hA)
  have hd (b : Bool) (hb : regularPhysicalCutMatrix (regularTwistedSite a (uB b)) R ≠ 0) :
      let M := regularPhysicalCutMatrix (regularTwistedSite a (uB b)) R
      (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose) = ρ := by
    have hs : regularTwistedPhysicalCutSuperposition a uB (Pi.single b 1) R =
        regularPhysicalCutState (regularTwistedSite a (uB b)) R := by
      cases b <;> simp [regularTwistedPhysicalCutSuperposition, Pi.single_apply]
    have hsne : regularTwistedPhysicalCutSuperposition a uB (Pi.single b 1) R ≠ 0 := by
      rw [hs]
      intro hz
      apply hb
      ext σ τ
      exact congrFun hz (σ, τ)
    obtain ⟨z, hz, hresult⟩ := hnormalize (Pi.single b 1) hsne
    rw [hs] at hresult
    exact normalized_reduced_of_scaled_state _ ρ hρ z hz hb hresult.1
  have hone := regularTwistedSite_one a
  have htrue := hd true (by simpa only [uB, ↓reduceIte] using hne)
  have hfalse := hd false (by simpa only [uB, Bool.false_eq_true, ↓reduceIte, hone] using hne₀)
  simpa only [uB, Bool.false_eq_true, ↓reduceIte, hone] using htrue.trans hfalse.symm

/-- Noncentral vacuum density from one untwisted complementary boundary
component. The tree and global gauge are derived, and every Gram identity is
obtained from actual regular G-isometric sites. Connectedness of the observed
and complementary graphs and a nonempty boundary are explicit. Nonvanishing
of the two actual cuts is required here; the native flux theorem supplies it
separately. Conditional contraction step for SCP10, Lemma 6.14. -/
theorem regularPhysicalCutMatrix_normalized_reduced_eq_of_untwisted_boundary_component
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v)) (regularSiteMap (a v)))
    (R : Finset V) (hR : (Γ.induce (R : Set V)).Connected)
    (hS : (Γ.induce ((Finset.univ \ R : Finset V) : Set V)).Connected)
    (hB : Nonempty {e : Edge Γ // IsRegionBoundaryEdge R e})
    (U : SimpleGraph {v : V // v ∈ Finset.univ \ R})
    (hU : U ≤ Γ.induce ((Finset.univ \ R : Finset V) : Set V))
    (o : {v : V // v ∈ Finset.univ \ R}) (u : Edge Γ → G)
    (hu : ∀ {v w : {v : V // v ∈ Finset.univ \ R}} (h : U.Adj v w),
      regularDirectedTransport u (hU h) = 1)
    (hboundary : ∀ v : {v : V // v ∈ Finset.univ \ R},
      (∃ w ∈ R, Γ.Adj v.1 w) → U.Reachable o v)
    (hincident : ∀ e : Edge Γ, IsRegionIncidentEdge R e → u e = 1)
    (hne : regularPhysicalCutMatrix (regularTwistedSite a u) R ≠ 0)
    (hne₀ : regularPhysicalCutMatrix a R ≠ 0) :
    let M := regularPhysicalCutMatrix (regularTwistedSite a u) R
    let M₀ := regularPhysicalCutMatrix a R
    (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose) =
      (M₀ * M₀.conjTranspose).trace⁻¹ • (M₀ * M₀.conjTranspose) := by
  classical
  have hinv : ∀ g v η s, a v (fun f => g * η f) s = a v η s := by
    intro g v η s
    exact (ha v).toIsGInjective.regularSiteMap_translation g η s
  obtain ⟨T, k, hT, htree, _, hincident', hremove, hstate⟩ :=
    exists_regularComplementGauge_fixed_on_incident a hinv R hS U hU o u hu hboundary hincident
  let S := Finset.univ \ R
  let f : {v : V // v ∈ S} ↪ V := Function.Embedding.subtype _
  let Δ := T.map f
  have hΔ : Δ ≤ Γ := by
    intro v w hvw
    obtain ⟨v', w', hadj, rfl, rfl⟩ := (SimpleGraph.map_adj f T v w).mp hvw
    exact hT hadj
  have hΔS : Δ.induce (S : Set V) = T := by
    ext v w
    exact SimpleGraph.map_adj_apply
  have hconn : (Δ.induce (S : Set V)).Connected := by rw [hΔS]; exact htree.connected
  have htrivial (e : Edge Γ) (he : Δ.Adj e.1.1 e.1.2) :
      regularVertexGaugeOperators k u e = 1 := by
    obtain ⟨v, w, hadj, hv, hw⟩ := (SimpleGraph.map_adj f T _ _).mp he
    have ht : e.1.1 ∈ S := hv ▸ v.2
    have hh : e.1.2 ∈ S := hw ▸ w.2
    have hv' : (⟨e.1.1, ht⟩ : {v : V // v ∈ S}) = v := Subtype.ext hv.symm
    have hw' : (⟨e.1.2, hh⟩ : {v : V // v ∈ S}) = w := Subtype.ext hw.symm
    exact hremove ⟨e, ht, hh⟩ (by rw [hv', hw']; exact hadj)
  have hcut : regularPhysicalCutMatrix (regularTwistedSite a u) R =
      regularPhysicalCutMatrix (regularTwistedSite a (regularVertexGaugeOperators k u)) R := by
    ext σ τ
    exact hstate (assembleRegionσ R σ τ)
  let β := {e : Edge Γ // IsRegionBoundaryEdge R e}
  let : Nonempty β := hB
  have hc : 1 ≤ Fintype.card β := Fintype.card_pos
  let e : β ≃ Fin (Fintype.card β - 1 + 1) :=
    Fintype.equivFinOfCardEq (Nat.sub_add_cancel hc).symm
  rw [hcut]
  exact normalized_reduced_eq_of_common_untwisted a ha R hR _ hincident' hΔ hconn htrivial e
    (hcut ▸ hne) hne₀

end TNLean.PEPS
