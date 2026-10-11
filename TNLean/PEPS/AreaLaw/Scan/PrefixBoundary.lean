/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.PrefixComparison
import TNLean.PEPS.AreaLaw.Scan.AmbientDepth
import TNLean.PEPS.AreaLaw.Geometry.TemplateCutBoundary
import TNLean.PEPS.AreaLaw.EdgeBoundaryCalculus

/-!
# Physical edge boundaries of deterministic depth prefixes

The source clearance rules out compact-to-opposite-colour edges. At a positive
outer front every crossing edge meets the last included row. At depth zero,
every crossing edge meets the first positive row instead. Thus the row bound
on depths one through `L` controls every full prefix, without a row estimate
at `L + 1` or a bound on the size of the target. Removing the target gives the
positive-depth prefix bound.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, Lemma 9.1(2), lines 243–257, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

/-- The scanner clearance excludes actual cut endpoints from every permitted dilation.
Source: `08-scanner.tex`, lines 43–48 and 254–255. -/
theorem disjoint_ambientDilation_boundaryEndpoints_of_clearance
    (Λ T : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (L r₀ : ℕ)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ A,
      ((2 * L + 10 * r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    {j : ℕ} (hj : j ≤ L) :
    Disjoint (ambientDilation T j) (Geometry.boundaryEndpoints Λ A) := by
  apply Finset.disjoint_left.mpr
  intro z hz hzcut
  obtain ⟨t, ht, hdist⟩ := mem_ambientDilation_iff.mp hz
  have hnear : ambientSupDistance t z ≤ (j : ℤ) := by
    simp only [ambientSupDistance, max_le_iff, abs_le]
    omega
  have hfar := hclear t ht z hzcut
  omega

private theorem card_ambientBoundary_dilation_le_of_rows
    (T : Finset (ℤ × ℤ)) {n L : ℕ} (hL : 1 ≤ L)
    (hrow : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ n)
    {j : ℕ} (hj : j ≤ L) :
    (ambientBoundary (ambientDilation T j)).card ≤ 4 * n := by
  by_cases hj0 : j = 0
  · subst j
    rw [ambientDilation_zero]
    have hfirst := hrow 1 (by omega) hL
    simp only [Nat.sub_self, ambientDilation_zero] at hfirst
    exact (card_ambientBoundary_le_outer_layer T).trans (Nat.mul_le_mul_left 4 hfirst)
  · exact (card_ambientBoundary_dilation_le_layer T j (by omega)).trans
      (Nat.mul_le_mul_left 4 (hrow j (by omega) hj))

/-- Full physical depth prefixes have at most `4n` edges. The source hypotheses
are ambient row counts and clearance at actual cut endpoints; no boundary
estimate is an input. Negative fronts give the empty prefix, and the zero front
uses the first positive row. Source: Lemma 9.1(2), lines 251–255. -/
theorem card_edgeBoundary_depthPrefix_le (Λ T : Finset (ℤ × ℤ))
    (hT : T.Nonempty) (A : Finset (Site Λ)) {n L r₀ : ℕ} (hL : 1 ≤ L)
    (hrow : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ A,
      ((2 * L + 10 * r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    {j : ℤ} (hj : j ≤ L) :
    (edgeBoundary Λ (depthPrefix A (fun x ↦ ambientDepth T hT x.val) j)).card ≤ 4 * n := by
  by_cases hj0 : 0 ≤ j
  · lift j to ℕ using hj0
    have hjL : j ≤ L := by exact_mod_cast hj
    have heq : depthPrefix A (fun x ↦ ambientDepth T hT x.val) j =
        A.filter fun x ↦ x.val ∈ ambientDilation T j := by
      ext x
      simp only [depthPrefix, Finset.mem_filter, ambientDepth_le_iff_mem_dilation]
    rw [heq]
    exact (Geometry.card_edgeBoundary_filter_le_ambientBoundary Λ A _
      (disjoint_ambientDilation_boundaryEndpoints_of_clearance Λ T A L r₀ hclear hjL)).trans
      (card_ambientBoundary_dilation_le_of_rows T hL hrow hjL)
  · have heq : depthPrefix A (fun x ↦ ambientDepth T hT x.val) j = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hd : ambientDepth T hT x.val ≤ j := (Finset.mem_filter.mp hx).2
      have hn := ambientDepth_nonneg T hT x.val
      omega
    simp [heq]

/-- Positive-depth prefixes remove the zero-depth prefix from the full prefix. -/
theorem positiveDepthPrefix_eq_sdiff {V : Type*} [DecidableEq V]
    (A : Finset V) (depth : V → ℤ) (j : ℤ) :
    positiveDepthPrefix A depth j = depthPrefix A depth j \ depthPrefix A depth 0 := by
  ext x
  simp only [positiveDepthPrefix, depthPrefix, Finset.mem_filter, Finset.mem_sdiff]
  by_cases hx : x ∈ A <;> simp [hx, not_le, and_comm]

/-- Positive-depth physical prefixes have at most `8n` edges, including the
zero and negative fronts. The two contributions are the last included row
and the first positive row. Source: Lemma 9.1(2), lines 251–255. -/
theorem card_edgeBoundary_positiveDepthPrefix_le (Λ T : Finset (ℤ × ℤ))
    (hT : T.Nonempty) (A : Finset (Site Λ)) {n L r₀ : ℕ} (hL : 1 ≤ L)
    (hrow : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ A,
      ((2 * L + 10 * r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    {j : ℤ} (hj : j ≤ L) :
    (edgeBoundary Λ (positiveDepthPrefix A (fun x ↦ ambientDepth T hT x.val) j)).card ≤
      8 * n := by
  rw [positiveDepthPrefix_eq_sdiff]
  have hjbound := card_edgeBoundary_depthPrefix_le Λ T hT A hL hrow hclear hj
  have hzero := card_edgeBoundary_depthPrefix_le Λ T hT A hL hrow hclear
    (j := 0) (by omega)
  have hdiff := card_edgeBoundary_sdiff_le Λ
    (depthPrefix A (fun x ↦ ambientDepth T hT x.val) j)
    (depthPrefix A (fun x ↦ ambientDepth T hT x.val) 0)
  omega

end TNLean.PEPS.AreaLaw.Scan
