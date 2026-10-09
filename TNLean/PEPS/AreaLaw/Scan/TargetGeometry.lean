/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BadChargeRatioBound
import TNLean.PEPS.AreaLaw.Scan.CompactCollarCounting
import TNLean.PEPS.AreaLaw.Scan.Defs
import TNLean.PEPS.AreaLaw.Scan.DesignatedSampling
import TNLean.PEPS.AreaLaw.Scan.PrefixBoundary

/-!
# Source geometry for the target marginal

At the source floor scale `L = ⌊n^(1-ell)⌋`, the actual compact truncation
set has at most `(C_T + 1) * n^2` sites. The chosen-color part of the
ambient target lies in that set and has at most `4 * n` physical boundary
edges. Only ambient row counts, the target-size bound, and clearance from
the actual cut endpoints are assumed. Holes and disconnected physical
components are allowed.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 21–48, 243–257 and 400–414, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

/-- Both length bounds follow from the floor scale and the source exponent range. -/
theorem ScannerExponents.one_le_L_le (E : ScannerExponents) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ E.L n ∧ E.L n ≤ n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨?_, (CollarScan.source_lengths_le (mu := E.mu) hn E.ell_pos.le
    (by linarith [E.mu_lt_one_sub_ell, E.ell_pos])).1⟩
  unfold ScannerExponents.L
  apply (Nat.one_le_floor_iff _).mpr
  exact Real.one_le_rpow hnR (by linarith [E.ell_lt_one])

namespace CollarScan

variable {Λ : Finset (ℤ × ℤ)} {I : Type*} (S : CollarScan (Site Λ) I)

/-- The source target supplies the volume, containment and boundary inputs for
truncation and the target cut budget. Neither conclusion is a premise.
Source: `08-scanner.tex`, lines 21–48 and 243–257. -/
theorem source_target_geometry (E : ScannerExponents) (T : Finset (ℤ × ℤ))
    (hT : T.Nonempty) {C_T : ℝ} (hn : 1 ≤ S.n)
    (hsize : (T.card : ℝ) ≤ C_T * (S.n : ℝ) ^ 2)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ E.L S.n →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * E.L S.n + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) :
    ((S.truncationSet (E.L S.n)).card : ℝ) ≤ (C_T + 1) * (S.n : ℝ) ^ 2 ∧
      (S.A.filter fun x ↦ x.val ∈ T) ⊆ S.truncationSet (E.L S.n) ∧
      (edgeBoundary Λ (S.A.filter fun x ↦ x.val ∈ T)).card ≤ 4 * S.n := by
  classical
  obtain ⟨hLpos, hLn⟩ := E.one_le_L_le hn
  have hcard : (S.truncationSet (E.L S.n)).card ≤ T.card + S.n * E.L S.n := by
    simpa only [truncationSet, hdepth] using
      card_compact_collar_le hT S.A S.n (E.L S.n) hrows
  have hprefix : depthPrefix S.A (fun x ↦ ambientDepth T hT x.val) 0 =
      S.A.filter fun x ↦ x.val ∈ T := by
    ext x
    simp only [depthPrefix, Finset.mem_filter,
      ambientDepth_le_iff_mem_dilation T hT x.val 0, ambientDilation_zero]
  refine ⟨?_, ?_, ?_⟩
  · have hcardR : ((S.truncationSet (E.L S.n)).card : ℝ) ≤
        (T.card : ℝ) + (S.n : ℝ) * E.L S.n := by exact_mod_cast hcard
    have hLnR : (E.L S.n : ℝ) ≤ S.n := by exact_mod_cast hLn
    calc
      _ ≤ (T.card : ℝ) + (S.n : ℝ) * E.L S.n := hcardR
      _ ≤ C_T * (S.n : ℝ) ^ 2 + (S.n : ℝ) * S.n :=
        add_le_add hsize (mul_le_mul_of_nonneg_left hLnR (Nat.cast_nonneg _))
      _ = _ := by ring
  · rw [← hprefix]
    intro x hx
    obtain ⟨hxA, hxdepth⟩ := Finset.mem_filter.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨hxA, ?_⟩
    rw [hdepth]
    exact hxdepth.trans (Int.natCast_nonneg _)
  · rw [← hprefix]
    exact card_edgeBoundary_depthPrefix_le Λ T hT S.A hLpos hrows hclear
      (j := 0) (Int.natCast_nonneg _)

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
