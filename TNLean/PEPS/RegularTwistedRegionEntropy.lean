/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularClosureSuperposition
import TNLean.PEPS.RegularRegionEntropy
import TNLean.PEPS.RegularTwistedRegionGram

/-!
# Entropy of finite regular PEPS superpositions with complementary twists

Twists confined to the complementary region leave the first region map unchanged.
When the complementary twists have a common connected untwisted subgraph, their
projected mixed Gram matrices are scalar multiples of the invariant-boundary projector.
Every nonzero superposition of the actual physical contractions therefore has a common
normalized reduced density operator on the first region.

**Scope restriction (finite complementary twists):** the region is connected, all twists
are trivial on edges incident to it, and a common untwisted subgraph is connected in the
complement. This is an auxiliary finite-cut version of the calculation in Schuch, Cirac,
and Pérez-García, arXiv:1001.3807, Theorem 6.9, proof, lines 2043–2076. The source's
arbitrary disk cut and torus disentangling argument remain separate; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ Δ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {S : Type*} [Fintype S]

omit [Fintype G] [DecidableEq G] [Fintype V] [DecidableRel Γ.Adj] in
/-- Twists trivial on edges incident to a region leave every site in the region unchanged. -/
theorem regularTwistedSite_eq_of_trivial_on_incident
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (u : Edge Γ → G)
    (R : Finset V) (hu : ∀ f : Edge Γ, IsRegionIncidentEdge R f → u f = 1)
    (v : V) (hv : v ∈ R) (η : IncidentEdge Γ v → G) (s : Fin d) :
    regularTwistedSite a u v η s = a v η s := by
  have hlabels : regularTwistedLabels u v η = η := by
    funext f
    have hf : IsRegionIncidentEdge R f.1 := by
      rcases f.2 with h | h
      · exact Or.inl (h.symm ▸ hv)
      · exact Or.inr (h.symm ▸ hv)
    simp only [regularTwistedLabels, hu f.1 hf, one_mul, ite_self]
  exact congrArg (fun x => a v x s) hlabels

omit [DecidableEq G] in
/-- The actual region contraction is unchanged by complementary twists. -/
theorem regularTwistedOpenRegionMatrix_eq_of_trivial_on_incident
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (u : Edge Γ → G)
    (R : Finset V) (hu : ∀ f : Edge Γ, IsRegionIncidentEdge R f → u f = 1)
    {b : ℕ} (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b) :
    regularTwistedOpenRegionMatrix a u R e = regularOpenRegionMatrix a R e := by
  classical
  ext σ x
  simp only [regularTwistedOpenRegionMatrix, regularOpenRegionMatrix_apply_group]
  apply Finset.sum_congr rfl
  intro η _
  split_ifs
  · apply Finset.prod_congr rfl
    intro v _
    exact regularTwistedSite_eq_of_trivial_on_incident a u R hu v.1 v.2 _ _
  · rfl

/-- A superposition of actual twisted cut vectors is the coefficient vector of the
fixed region map and the complementary superposition. -/
theorem regularClosureSuperpositionState_eq_twistedCut_sum (n : ℕ)
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (u : S → Edge Γ → G)
    (w : S → ℂ) (R : Finset V)
    (hu : ∀ s f, IsRegionIncidentEdge R f → u s f = 1)
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1)) {c : ℂ}
    (hM : (regularOpenRegionMatrix a R e).conjTranspose * regularOpenRegionMatrix a R e =
      c • regularBoundaryProjector (n + 1)) :
    regularClosureSuperpositionState (regularOpenRegionMatrix a R e)
        (fun s => regularOpenComplementMatrix (regularTwistedSite a (u s)) R e) w =
      ∑ s, w s • regularPhysicalCutState (regularTwistedSite a (u s)) R := by
  classical
  rw [regularClosureSuperpositionState_eq_sum_of_gram n _ _ _ hM]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  funext p
  change _ = regularPhysicalCutMatrix (regularTwistedSite a (u s)) R p.1 p.2
  have hMu : regularOpenRegionMatrix (regularTwistedSite a (u s)) R e =
      regularOpenRegionMatrix a R e :=
    regularTwistedOpenRegionMatrix_eq_of_trivial_on_incident a (u s) R (hu s) e
  rw [regularPhysicalCutMatrix_eq_mul_transpose _ R e, hMu]

/-- A finite linear combination of the actual physical contractions with complementary
regular-bond twists. -/
noncomputable def regularTwistedPhysicalCutSuperposition
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (u : S → Edge Γ → G)
    (w : S → ℂ) (R : Finset V) :=
  ∑ s, w s • regularPhysicalCutState (regularTwistedSite a (u s)) R

/-- For a connected region and a complement with a common connected untwisted subgraph,
every nonzero superposition of the actual twisted PEPS contractions has the same normalized
reduced density on the region. Its rank and entropy are \(|G|^n\) and \(n\log|G|\), respectively,
and its nonzero spectrum is flat. All region and mixed Gram identities are derived from
local regular isometry. Source: SCP10, the restricted finite-cut form of Theorem 6.9,
proof, lines 2043–2076. -/
theorem exists_normalization_regularTwistedPhysicalCutSuperposition (n : ℕ)
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v)) (regularSiteMap (a v)))
    (R : Finset V) (hR : (Γ.induce (R : Set V)).Connected)
    (u : S → Edge Γ → G)
    (hu : ∀ s f, IsRegionIncidentEdge R f → u s f = 1)
    (hΔ : Δ ≤ Γ) (hRc : (Δ.induce ((Finset.univ \ R : Finset V) : Set V)).Connected)
    (huΔ : ∀ s (f : Edge Γ), Δ.Adj f.1.1 f.1.2 →
      f.1.1 ∉ R → f.1.2 ∉ R → u s f = 1)
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1)) :
    ∃ cA : ℝ, 0 < cA ∧
      (regularOpenRegionMatrix a R e).conjTranspose * regularOpenRegionMatrix a R e =
        (cA : ℂ) • regularBoundaryProjector (n + 1) ∧
      ∀ w : S → ℂ, regularTwistedPhysicalCutSuperposition a u w R ≠ 0 →
        ∃ z : ℝ, 0 < z ∧
          let ψ := (z : ℂ) • regularTwistedPhysicalCutSuperposition a u w R
          let ρ := partialTraceRight (vecMulVec ψ (star ψ))
          ρ = physicalRegularBoundaryDensity n
              (normalizedRegularBoundaryMap cA (regularOpenRegionMatrix a R e)) ∧
            star ψ ⬝ᵥ ψ = 1 ∧ ρ.rank = Fintype.card G ^ n ∧
            ρ * ρ = ((Fintype.card G : ℂ) ^ n)⁻¹ • ρ ∧
            vonNeumannEntropy ρ
              (posSemidef_vecMulVec_self_star ψ).partialTraceRight.isHermitian =
                (n : ℝ) * Real.log (Fintype.card G : ℝ) := by
  classical
  obtain ⟨cA, hcA, hM⟩ := exists_positive_gram_regularOpenRegionMatrix_of_connected a ha R hR e
  choose c hc hlocal using fun v => (ha v).exists_regularSiteGram
  let Rc := Finset.univ \ R
  let ec := (regionBoundaryEdgeComplEquiv (G := Γ) R).symm.trans e
  let N := fun s => regularOpenComplementMatrix (regularTwistedSite a (u s)) R e
  let k := fun s t => regularRegionGramScalar (Γ := Γ) (G := G) (fun v => (c v : ℂ)) Rc *
    ((∑ x : G, if ∀ f : Edge Γ, f.1.1 ∈ Rc → f.1.2 ∈ Rc → u s f * x = x * u t f
      then (1 : ℂ) else 0) / (Fintype.card G : ℂ))
  have hUntwisted : ∀ s (f : Edge Γ), Δ.Adj f.1.1 f.1.2 → u s f = 1 := by
    intro s f hf
    by_cases ht : f.1.1 ∈ R
    · exact hu s f (Or.inl ht)
    by_cases hh : f.1.2 ∈ R
    · exact hu s f (Or.inr hh)
    exact huΔ s f hf ht hh
  have hBoundary : ∀ s (f : Edge Γ), IsRegionBoundaryEdge Rc f → u s f = 1 := by
    intro s f hf
    exact hu s f (isRegionBoundaryEdge_touches R
      ((isRegionBoundaryEdge_compl_iff R f).mp hf))
  have hk : ∀ s t, regularBoundaryProjector (n + 1) * (N s).conjTranspose * N t *
      regularBoundaryProjector (n + 1) = k s t • regularBoundaryProjector (n + 1) := by
    intro s t
    have h := regularTwistedOpenRegionMatrix_projected_crossGram_of_connected
      a (fun v => (c v : ℂ)) Rc (u s) (u t) ec
      (fun v η θ => hlocal v.1 η θ) hΔ hRc
      (fun f hf => ⟨hUntwisted s f hf, hUntwisted t f hf⟩)
      (fun f hf => ⟨hBoundary s f hf, hBoundary t f hf⟩)
    simpa only [N, regularOpenComplementMatrix_eq_regularOpenRegionMatrix,
      regularTwistedOpenRegionMatrix, Matrix.mul_assoc, k, ec, Rc] using h
  refine ⟨cA, hcA, hM, ?_⟩
  intro w hne
  have hψ := regularClosureSuperpositionState_eq_twistedCut_sum n a u w R hu e hM
  change regularClosureSuperpositionState (regularOpenRegionMatrix a R e) N w =
    regularTwistedPhysicalCutSuperposition a u w R at hψ
  have hne' : regularClosureSuperpositionState (regularOpenRegionMatrix a R e) N w ≠ 0 := by
    rwa [hψ]
  obtain ⟨z, hz, hresult⟩ := exists_normalization_regularClosureSuperpositionState
    n (regularOpenRegionMatrix a R e) N w k hcA hM hk hne'
  exact ⟨z, hz, by simpa only [hψ] using hresult⟩

end TNLean.PEPS
