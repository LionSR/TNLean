/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTwistedRegionConnectivity
import TNLean.PEPS.RegularTwistedRegionCounting
import TNLean.PEPS.RegularBoundaryTransporter

/-!
# Cross-Gram operators of twisted regular-bond regions

A connected common untwisted subgraph equates the local group translations.
The remaining internal bonds impose simultaneous intertwining equations on this
common translation. Each internal bond still has one free regular-group label.
The actual cross-Gram operator is consequently a sum of boundary translations
weighted by the internal intertwiners. Restricting both boundary arguments to
the invariant subspace turns this sum into its total weight times the projector.

This is an auxiliary twisted-region calculation for Schuch, Cirac, and
Pérez-García, arXiv:1001.3807, proof of Theorem 6.9, lines 1935–1990 and 2062–2072.

**Scope restriction (twisted regions):** The bond operators are trivial on
crossing edges, and the two internal assignments share a connected common
untwisted subgraph. The source's general torus cut and disentangling argument
remain separate; see `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
No entropy assertion is made here.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ Δ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Ordering the boundary changes a filtered translation sum into the weighted
regular boundary operator. Source: SCP10, twisted-region contraction,
lines 1935–1990. -/
theorem sum_regularBoundary_filtered_translation_eq_weightedTranslation
    (R : Finset V) {b : ℕ}
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b)
    (p : G → Prop) [DecidablePred p] (x y : Fin b → G) :
    (∑ g : G, if (fun f => x (e f)) = (fun f => g * y (e f)) ∧ p g
      then (1 : ℂ) else 0) =
      regularBoundaryWeightedTranslation b (fun g => if p g then 1 else 0) x y := by
  classical
  have he (g : G) : (fun f => x (e f)) = (fun f => g * y (e f)) ↔ x = g • y := by
    simpa only [Function.comp_def, Pi.smul_apply, smul_eq_mul] using
      e.surjective.right_cancellable (g₁ := x) (g₂ := g • y)
  simp only [regularBoundaryWeightedTranslation_apply, he, ite_and]

open scoped Classical in
/-- Source: SCP10, twisted regular contraction, lines 1935–1990 and 2062–2072.
The cross-Gram matrix of two actual contractions is the normalized sum of
boundary translations intertwining all internal bond operators. -/
theorem regularTwistedOpenRegionMatrix_crossGram_of_connected
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (c : V → ℂ)
    (R : Finset V) (u w : Edge Γ → G) {b : ℕ}
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b)
    (hlocal : ∀ (v : {v : V // v ∈ R}) (η θ : IncidentEdge Γ v.1 → G),
      (∑ s : Fin d, star (a v.1 η s) * a v.1 θ s) =
        (c v.1 / (Fintype.card G : ℂ)) *
          ∑ g : G, if η = (fun f => g * θ f) then (1 : ℂ) else 0)
    (hΔ : Δ ≤ Γ) (hR : (Δ.induce (R : Set V)).Connected)
    (hUntwisted : ∀ f : Edge Γ, Δ.Adj f.1.1 f.1.2 → u f = 1 ∧ w f = 1)
    (hBoundary : ∀ f : Edge Γ, IsRegionBoundaryEdge R f → u f = 1 ∧ w f = 1) :
    (regularTwistedOpenRegionMatrix a u R e).conjTranspose *
        regularTwistedOpenRegionMatrix a w R e =
      (regularRegionGramScalar (Γ := Γ) (G := G) c R / (Fintype.card G : ℂ)) •
        regularBoundaryWeightedTranslation b (fun x =>
          if ∀ f : Edge Γ, f.1.1 ∈ R → f.1.2 ∈ R → u f * x = x * w f then 1 else 0) := by
  classical
  ext x y
  let p : G → Prop := fun g =>
    ∀ f : Edge Γ, f.1.1 ∈ R → f.1.2 ∈ R → u f * g = g * w f
  let z : ℂ := (∏ v : {v : V // v ∈ R}, c v.1) / (Fintype.card G : ℂ) ^ R.card
  have hterm (η θ : {f : Edge Γ // IsRegionIncidentEdge R f} → G) :
      (if (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
              η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = (fun f => x (e f)) ∧
            (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
              θ ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = (fun f => y (e f)) then
          z * ∑ g : G, if η = (fun f => g * θ f) ∧ p g then (1 : ℂ) else 0
        else 0) =
        z * ∑ g : G,
          if (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
                η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = (fun f => x (e f)) ∧
              (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
                θ ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = (fun f => y (e f)) ∧
              η = (fun f => g * θ f) ∧ p g then (1 : ℂ) else 0 := by
    by_cases hη : (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
      η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = (fun f => x (e f)) <;>
      by_cases hθ : (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
        θ ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = (fun f => y (e f)) <;>
      simp only [hη, hθ, true_and, false_and, ite_true, ite_false,
        Finset.sum_const_zero, mul_zero]
  calc
    _ = ∑ η : {f : Edge Γ // IsRegionIncidentEdge R f} → G,
        ∑ θ : {f : Edge Γ // IsRegionIncidentEdge R f} → G,
          if (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
                η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = (fun f => x (e f)) ∧
              (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
                θ ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = (fun f => y (e f)) then
            z * ∑ g : G, if η = (fun f => g * θ f) ∧ p g then (1 : ℂ) else 0
          else 0 := by
      rw [regularTwistedOpenRegionMatrix_crossGram_eq_sum_compatible a c R u w e hlocal]
      simp only [sum_twistedRegionLabelCompatible_eq_sum_translation
        R u w _ _ hΔ hR hUntwisted hBoundary, z, p]
    _ = z * ∑ η : {f : Edge Γ // IsRegionIncidentEdge R f} → G,
        ∑ θ : {f : Edge Γ // IsRegionIncidentEdge R f} → G, ∑ g : G,
          if (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
                η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = (fun f => x (e f)) ∧
              (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
                θ ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = (fun f => y (e f)) ∧
              η = (fun f => g * θ f) ∧ p g then (1 : ℂ) else 0 := by
      simp only [hterm, ← Finset.mul_sum]
    _ = z * ((Fintype.card G : ℂ) ^
        Fintype.card {f : Edge Γ // f.1.1 ∈ R ∧ f.1.2 ∈ R} *
        regularBoundaryWeightedTranslation b (fun g => if p g then 1 else 0) x y) := by
      rw [sum_regionBoundary_filtered_translations_eq_card,
        sum_regularBoundary_filtered_translation_eq_weightedTranslation R e]
    _ = _ := by
      have hcard : (Fintype.card G : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      simp only [z, p, regularRegionGramScalar, pow_succ, Matrix.smul_apply,
        smul_eq_mul, div_eq_mul_inv, mul_assoc]
      field_simp

open scoped Classical in
/-- On the invariant boundary, the actual cross-Gram operator is the untwisted
region scalar multiplied by the proportion of simultaneous internal intertwiners.
Source: SCP10, twisted-region contraction, lines 1935–1990 and 2062–2072. -/
theorem regularTwistedOpenRegionMatrix_projected_crossGram_of_connected
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (c : V → ℂ)
    (R : Finset V) (u w : Edge Γ → G) {b : ℕ}
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b)
    (hlocal : ∀ (v : {v : V // v ∈ R}) (η θ : IncidentEdge Γ v.1 → G),
      (∑ s : Fin d, star (a v.1 η s) * a v.1 θ s) =
        (c v.1 / (Fintype.card G : ℂ)) *
          ∑ g : G, if η = (fun f => g * θ f) then (1 : ℂ) else 0)
    (hΔ : Δ ≤ Γ) (hR : (Δ.induce (R : Set V)).Connected)
    (hUntwisted : ∀ f : Edge Γ, Δ.Adj f.1.1 f.1.2 → u f = 1 ∧ w f = 1)
    (hBoundary : ∀ f : Edge Γ, IsRegionBoundaryEdge R f → u f = 1 ∧ w f = 1) :
    regularBoundaryProjector b *
        ((regularTwistedOpenRegionMatrix a u R e).conjTranspose *
          regularTwistedOpenRegionMatrix a w R e) * regularBoundaryProjector b =
      (regularRegionGramScalar (Γ := Γ) (G := G) c R *
        ((∑ x : G, if ∀ f : Edge Γ, f.1.1 ∈ R → f.1.2 ∈ R → u f * x = x * w f
          then (1 : ℂ) else 0) / (Fintype.card G : ℂ))) • regularBoundaryProjector b := by
  classical
  rw [regularTwistedOpenRegionMatrix_crossGram_of_connected
    a c R u w e hlocal hΔ hR hUntwisted hBoundary]
  rw [Matrix.mul_smul, Matrix.smul_mul,
    regularBoundaryProjector_mul_weightedTranslation_mul_projector, smul_smul]
  congr 1
  ring

end TNLean.PEPS
