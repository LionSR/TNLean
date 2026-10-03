/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularRegionGramExpansion
import TNLean.PEPS.RegularRegionConnectivity
import TNLean.PEPS.RegularRegionCounting
import TNLean.PEPS.RegularSiteGram
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Gram operator of a connected regular-bond region

Local Gram kernels proportional to the regular-group averaging projector determine
the Gram operator of the actual contracted region. Compatibility along internal
edges equates all local group translations in a connected region. The remaining
internal bond labels are independent, so they contribute one factor of the group
order per internal edge.

The contraction uses unnormalized regular bonds. Its scalar is the product of
the local Gram scalars times the group order raised to the cycle rank. The ratio
form of this scalar is used below, avoiding subtraction of natural exponents.
This is the twist-free connected-region calculation underlying Schuch, Cirac,
and Pérez-García, arXiv:1001.3807, lines 1935–1957 and 2062–2072. Torus twists
and the entropy theorem require separate arguments.

**Scope restriction (untwisted regions):** The contraction contains no inserted
torus closure matrices. The source's twisted-sector argument in Theorem 6.9 is
separate; see `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
Only the connected-region Gram operator is asserted here.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

open scoped Classical in
/-- Source: SCP10, regular-basis contraction, lines 1935–1957 and 2062–2072.
The product of local group-averaging Gram kernels is a sum over compatible
vertex translations, with all local normalization factors retained. -/
theorem prod_regularSiteGram_eq_sum_compatible
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (c : V → ℂ)
    (R : Finset V)
    (hlocal : ∀ (v : {v : V // v ∈ R}) (η θ : IncidentEdge Γ v.1 → G),
      (∑ s : Fin d, star (a v.1 η s) * a v.1 θ s) =
        (c v.1 / (Fintype.card G : ℂ)) *
          ∑ g : G, if η = (fun f => g * θ f) then (1 : ℂ) else 0)
    (η θ : {f : Edge Γ // IsRegionIncidentEdge R f} → G) :
    (∏ v : {v : V // v ∈ R}, ∑ s : Fin d,
      star (a v.1 (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R v f⟩) s) *
        a v.1 (fun f => θ ⟨f.1, isRegionIncidentEdge_of_regionVertex R v f⟩) s) =
      ((∏ v : {v : V // v ∈ R}, c v.1) / (Fintype.card G : ℂ) ^ R.card) *
        ∑ q : {v : V // v ∈ R} → G,
          if IsRegionLabelCompatible R q η θ then (1 : ℂ) else 0 := by
  classical
  simp only [hlocal, Finset.prod_mul_distrib, Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  congr 1
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro q _
  simp only [Fintype.prod_boole, IsRegionLabelCompatible, funext_iff]
  split_ifs with h
  · exact (ite_eq_left h).symm
  · exact (ite_eq_right h).symm


/-- An ordered boundary translation sum is the group order times its averaging projector. -/
theorem sum_regularBoundary_translation_eq_card_mul_projector
    (R : Finset V) {b : ℕ}
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b) (x y : Fin b → G) :
    (∑ g : G, if (fun f => x (e f)) = (fun f => g * y (e f)) then (1 : ℂ) else 0) =
      (Fintype.card G : ℂ) * regularBoundaryProjector b x y := by
  classical
  have he (g : G) : (fun f => x (e f)) = (fun f => g * y (e f)) ↔ x = g • y := by
    simpa only [Function.comp_def, Pi.smul_apply, smul_eq_mul] using
      e.surjective.right_cancellable (g₁ := x) (g₂ := g • y)
  simp only [he]
  rw [← regularLegProjector_fin, regularLegProjector_apply]
  rw [← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]

/-- The scalar from unnormalized regular-bond contraction on a connected region.
Its ratio form equals the group order to the cycle rank times the product of
the site scalars. Source: SCP10, lines 1935–1957 and 2062–2072. -/
noncomputable def regularRegionGramScalar (c : V → ℂ) (R : Finset V) : ℂ :=
  (∏ v : {v : V // v ∈ R}, c v.1) *
    (Fintype.card G : ℂ) ^ (Fintype.card {f : Edge Γ // f.1.1 ∈ R ∧ f.1.2 ∈ R} + 1) /
      (Fintype.card G : ℂ) ^ R.card

/-- Source: SCP10, connected regular-bond contraction, lines 1935–1957 and
2062–2072. The Gram operator of the actual open-region contraction is the
invariant-boundary projector multiplied by the scalar from the local Gram
kernels and the internal bonds. No global Gram identity is assumed. -/
theorem regularOpenRegionMatrix_gram_of_connected
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (c : V → ℂ)
    (R : Finset V) (hR : (Γ.induce (R : Set V)).Connected) {b : ℕ}
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b)
    (hlocal : ∀ (v : {v : V // v ∈ R}) (η θ : IncidentEdge Γ v.1 → G),
      (∑ s : Fin d, star (a v.1 η s) * a v.1 θ s) =
        (c v.1 / (Fintype.card G : ℂ)) *
          ∑ g : G, if η = (fun f => g * θ f) then (1 : ℂ) else 0) :
    (regularOpenRegionMatrix a R e).conjTranspose * regularOpenRegionMatrix a R e =
      regularRegionGramScalar (Γ := Γ) (G := G) c R • regularBoundaryProjector b := by
  classical
  ext x y
  let z : ℂ := (∏ v : {v : V // v ∈ R}, c v.1) / (Fintype.card G : ℂ) ^ R.card
  have hterm (η θ : {f : Edge Γ // IsRegionIncidentEdge R f} → G) :
      (if (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
              η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = (fun f => x (e f)) ∧
            (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
              θ ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = (fun f => y (e f)) then
          z * ∑ g : G, if η = (fun f => g * θ f) then (1 : ℂ) else 0
        else 0) =
        z * ∑ g : G,
          if (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
                η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = (fun f => x (e f)) ∧
              (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
                θ ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = (fun f => y (e f)) ∧
              η = (fun f => g * θ f) then (1 : ℂ) else 0 := by
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
            z * ∑ g : G, if η = (fun f => g * θ f) then (1 : ℂ) else 0
          else 0 := by
      rw [regularOpenRegionMatrix_gram_apply_group]
      simp only [prod_regularSiteGram_eq_sum_compatible a c R hlocal,
        sum_regionLabelCompatible_eq_sum_translation R hR, z]
    _ = z * ∑ η : {f : Edge Γ // IsRegionIncidentEdge R f} → G,
        ∑ θ : {f : Edge Γ // IsRegionIncidentEdge R f} → G, ∑ g : G,
          if (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
                η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = (fun f => x (e f)) ∧
              (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
                θ ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = (fun f => y (e f)) ∧
              η = (fun f => g * θ f) then (1 : ℂ) else 0 := by
      simp only [hterm, ← Finset.mul_sum]
    _ = z * ((Fintype.card G : ℂ) ^
        Fintype.card {f : Edge Γ // f.1.1 ∈ R ∧ f.1.2 ∈ R} *
        ((Fintype.card G : ℂ) * regularBoundaryProjector b x y)) := by
      rw [sum_regionBoundary_translations_eq_card,
        sum_regularBoundary_translation_eq_card_mul_projector R e]
    _ = _ := by
      simp only [z, regularRegionGramScalar, pow_succ, div_eq_mul_inv,
        Matrix.smul_apply, smul_eq_mul]
      ring

end TNLean.PEPS
