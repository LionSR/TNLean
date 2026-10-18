/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.AreaLaw.CollarInformation
import TNLean.PEPS.AreaLaw.Scan.ActualTerminalPartitions
import TNLean.PEPS.AreaLaw.Scan.ReceivingRegions
import TNLean.PEPS.AreaLaw.Scan.StatusContainment

/-!
# Mutual information from actual terminal entropy averages

For each actual completed or pre-charge history, the exterior of a sufficiently
large collar lies on the far side of every band. The leaf entropy identity and
monotonicity of mutual information give a lower bound for the entropy difference
at that terminal. Averaging over terminal weights and the positive number of
bands gives the corresponding bound for the actual terminal entropy average.
The same physical vector occurs in every term, and the terminal tree is arbitrary.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*, proof of
Proposition 9.6, `08-scanner.tex`, lines 900–911, immutable revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This is the deterministic entropy implication; the sharp comparison, its numerical
error bound and the transfer to the original ground vector are separate results.
-/

open scoped BigOperators

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open ActualTerminals

open Classical in
/-- The actual terminal entropy average bounds mutual information with the
fixed exterior of the collar. The tree is arbitrary, so the assertion remains
valid when the selected charge point and its weights depend on the replica
count. The same physical vector occurs in every entropy and information term.

Source: OpenAI, proof of Proposition 9.6, `08-scanner.tex`, lines 900–911,
immutable revision `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This is the deterministic conversion of the leaf average, with a positive band
count; the sharp comparison and its numerical error estimate are separate inputs. -/
theorem two_mutualInformation_le_actualTerminal_entropy_average
    {Λ T : Finset (ℤ × ℤ)} {q : ℕ} {I : Type*} [Fintype I] [LinearOrder I]
    (hT : T.Nonempty) (S : CollarScan (Site Λ) I)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (hK : 0 < S.K) (L H : ℕ) (hL : 8 * S.K * S.m ≤ L)
    (Ωt : StateSpace Λ q)
    (tree : Matrix.MeanTree (terminalFamily S.K S.m S.M H)) :
    let X := S.A.filter fun x ↦ x.val ∈ T
    let β := fun _ : Site Λ ↦ Fin q
    let σ := terminalPartition S H
    let near := fun j g ↦ receiving (σ j g) false
    let Y := fun j g ↦ middle (σ j g)
    let gpre := fun j g ↦
      FiniteProduct.entropy β Ωt (near j g) +
        FiniteProduct.entropy β Ωt (near j g ∪ Y j g)ᶜ -
        FiniteProduct.entropy β Ωt (Y j g)
    let gpost := fun j g ↦
      regionalEntropy Λ q Ωt (positiveNear S.depth (σ j g)) +
        regionalEntropy Λ q Ωt (positiveNearMiddle S.depth (σ j g)) -
        regionalEntropy Λ q Ωt (Y j g)
    2 * FiniteProduct.mutualInformation β Ωt X (S.truncationSet L)ᶜ ≤
      2 * regionalEntropy Λ q Ωt X +
        ((∑ g, ∑ j, tree.weight j * gpre j g) -
          (∑ g, ∑ j, tree.weight j * gpost j g)) / (S.K : ℝ) := by
  intro X β σ near Y gpre gpost
  have hregions (j : terminalFamily S.K S.m S.M H) (g : Fin S.K) :
      near j g = X ∪ positiveNear S.depth (σ j g) ∧
      near j g ∪ Y j g = X ∪ positiveNearMiddle S.depth (σ j g) ∧
      receiving (σ j g) true = (X ∪ positiveNearMiddle S.depth (σ j g))ᶜ :=
    match j with
    | Sum.inl ⟨_, h⟩ => state_receiving_regions hT S hdepth h g
    | Sum.inr ⟨_, h⟩ => oldChargeState_receiving_regions hT S hdepth h g
  have hXdepth (x : Site Λ) (hx : x ∈ X) : S.depth x ≤ 0 :=
    hdepth ▸ (ambientDepth_le_iff_mem_dilation T hT x.val 0).mpr
      (by simpa only [ambientDilation_zero] using (Finset.mem_filter.mp hx).2)
  have hWV (j : terminalFamily S.K S.m S.M H) (g : Fin S.K) :
      (S.truncationSet L)ᶜ ⊆ receiving (σ j g) true :=
    match j with
    | Sum.inl ⟨_, h⟩ => by simpa only [σ, terminalPartition, compl_compl] using
        Finset.compl_subset_compl.mpr (S.state_far_compl_subset_truncationSet h g hL)
    | Sum.inr ⟨_, h⟩ => by simpa only [σ, terminalPartition, compl_compl] using
        Finset.compl_subset_compl.mpr (S.oldChargeState_far_compl_subset_truncationSet h g hL)
  have hleaf (j : terminalFamily S.K S.m S.M H) (g : Fin S.K) :
      2 * FiniteProduct.mutualInformation β Ωt X (S.truncationSet L)ᶜ ≤
        2 * FiniteProduct.entropy β Ωt X +
          (FiniteProduct.collarPreQuantity β Ωt X
            (positiveNear S.depth (σ j g)) (Y j g) (receiving (σ j g) true) -
           FiniteProduct.collarPostQuantity β Ωt (positiveNear S.depth (σ j g)) (Y j g)) := by
    have hr := hregions j g
    refine FiniteProduct.two_mutualInformation_le_collarLeaf β Ωt
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ (hWV j g)
    all_goals simp only [Finset.disjoint_left, Finset.ext_iff]
    all_goals simp only [Finset.ext_iff, positiveNear, positiveNearMiddle, near, Y,
      receiving, middle, Finset.mem_filter, Finset.mem_univ, Finset.mem_union,
      Finset.mem_compl, true_and] at *
    all_goals intro x
    all_goals have hσ : σ j g x = none ∨ σ j g x = some false ∨ σ j g x = some true :=
      ((show ∀ s : Option Bool, s = none ∨ s = some false ∨ s = some true from by decide) (σ j g x))
    all_goals have hxregions := hr.1 x
    all_goals rcases hσ with hs | hs | hs
    all_goals simp only [hs, reduceCtorEq, and_true, and_false, true_and, false_and,
      or_true, or_false, true_or, false_or, true_iff, false_iff, iff_true,
      not_true_eq_false, not_false_eq_true, implies_true, not_and, not_lt] at hxregions ⊢
    all_goals first | exact hXdepth x | exact hxregions
  have hP (j : terminalFamily S.K S.m S.M H) (g : Fin S.K) :
      positiveNearMiddle S.depth (σ j g) = positiveNear S.depth (σ j g) ∪ Y j g := by
    ext x
    simp only [Finset.ext_iff, positiveNear, positiveNearMiddle, near, Y,
      receiving, middle, Finset.mem_filter, Finset.mem_univ, Finset.mem_union,
      Finset.mem_compl, true_and] at *
    have hxregions := And.intro ((hregions j g).1 x) ((hregions j g).2.1 x)
    grind only
  have hineq (j : terminalFamily S.K S.m S.M H) (g : Fin S.K) :
      2 * FiniteProduct.mutualInformation β Ωt X (S.truncationSet L)ᶜ ≤
        2 * regionalEntropy Λ q Ωt X + (gpre j g - gpost j g) := by
    simpa only [gpre, gpost, regionalEntropy_eq_finiteProduct,
      FiniteProduct.collarPreQuantity, FiniteProduct.collarPostQuantity,
      ← (hregions j g).1, ← hP j g, (hregions j g).2.2, ← (hregions j g).2.1]
      using hleaf j g
  have hband (g : Fin S.K) :
      2 * FiniteProduct.mutualInformation β Ωt X (S.truncationSet L)ᶜ ≤
        2 * regionalEntropy Λ q Ωt X +
          ((∑ j, tree.weight j * gpre j g) - (∑ j, tree.weight j * gpost j g)) := by
    have hw := Finset.sum_le_sum (s := Finset.univ) fun j _ ↦
      mul_le_mul_of_nonneg_left (hineq j g) (tree.weight_nonneg j)
    simpa only [mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, tree.sum_weight, one_mul] using hw
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun g _ ↦ hband g
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hkR : (0 : ℝ) < S.K := by exact_mod_cast hK
  have hdiv : 2 * FiniteProduct.mutualInformation β Ωt X (S.truncationSet L)ᶜ -
      2 * regionalEntropy Λ q Ωt X ≤
      ((∑ g, ∑ j, tree.weight j * gpre j g) -
        (∑ g, ∑ j, tree.weight j * gpost j g)) / (S.K : ℝ) :=
    (le_div_iff₀ hkR).mpr (by nlinarith only [hsum])
  linarith only [hdiv]

end TNLean.PEPS.AreaLaw.Scan.CollarScan
